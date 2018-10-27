{-# LANGUAGE FlexibleContexts #-}
module Autosubst.GenCoq (generateCoq) where

import Autosubst.Types
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.RWS hiding ((<>))

import qualified Data.Map as M
import Text.PrettyPrint.Leijen
import Data.Maybe as Maybe
import Prelude hiding ((<$>))
import Autosubst.GenM

import Data.List as L
import Autosubst.Signature


-- Definition of the Separator
sepsym :: Doc
sepsym = text "_"

toSep :: String -> Doc
toSep x = sepsym <> text x

genSep :: String -> String -> Doc
genSep name x = text name <> toSep x

genSep' :: Doc -> String -> Doc
genSep' d x = d <> toSep x

--
-- Refactoring and aggregating
--   we need a number of top-level Coq constructions:
--
--   - the core building block appears to be a function fragment, consisting of (name, arguments, return type, body),
--     which is usually rendered as "name arguments : returnType := body"
--   - we then require a number of wrappers around these:
--     + multiple fragments separated by "with" and enclosed by "Inductive" and dot
--     + multiple fragments separated by "with" and enclosed by "Fixpoint" and dot
--     + single fragment enclosed by "Definition" and dot
--   - we also want to support generating Definitions with a tactic prefix, we either implement
--     special treatment or we define a FunctionFragment datastructure, with two rendering functions,
--     where one takes the tactic prefix and and injects it betwee nthe return type and an exact tactic ...

-- Renders a list of arguments, handles compacting and disambiguating explicit and implict arguments
-- third argument = True denotes an implicit argument
aggregate :: [(Doc,Doc,Bool)] -> [([Doc],Doc,Bool)] 
aggregate [] = []
aggregate [(x,y,z)] = [([x],y,z)]
aggregate ((x,y,z) : args) =
  let (xs,y',z') : res = aggregate args in
    if (show y) == (show y') && z == z' then (x:xs,y,z):res else ([x],y,z):(xs,y',z'):res

renderArgs :: [(Doc, Doc, Bool)] -> Doc 
renderArgs args = (sep (map (\(vars, ty, implicit) -> (if implicit then braces else parens) (cat (punctuate space vars) <> colon <+> ty)) . aggregate $ args))

-- Generation of Coq Definitions
defDoc :: String ->  Doc -> [(Doc, Doc, Bool)] -> Doc -> Doc -> Doc
defDoc defType name argList retType body = defMutDoc (text defType <+> name) argList retType (indent 2 body) <> dot

defMutDoc name argList retType body = hang 2 (name </> renderArgs argList </> colon <+> retType <+> text ":=") <$$> body

-- Generate the destruct/rename of a substitution or equality proof of subtitutions
-- useful since, implementing destruct as a proof term is rather ugly.
decompose :: Doc -> [TId] -> Doc 
decompose var [] = error "tried to generate a destruct into zero components."
decompose var [t] = text "rename" <+> var <+> text "into" <+> genSep' var t <> dot
decompose var components = text "destruct" <+> var <+> text "as" <+> encloseSep lparen (rparen <> dot) (empty <+> text "&" <+> empty) (map (genSep' var) components)

-- Generate a plain definition, with a tactic prefix and a closing exact. Then adds the required "Defined."
definedWithTacticPrefixDoc :: Doc -> [(Doc, Doc, Bool)] -> Doc -> Doc -> Doc -> Doc 
definedWithTacticPrefixDoc name argList retType tacticPrefix exactBody =
   hang 2 (text "Definition" <+> name </> renderArgs argList </> colon <+> retType <> dot <$$> tacticPrefix <$$> text "exact" <+> parens exactBody <> dot) <$$> text "Defined."

-- Generation of Coq Matches
caseDoc :: Doc -> Doc -> Doc
caseDoc pattern body = hang 4 (text "| " <> pattern <+> text "=>" </> body)

matchDoc :: Doc -> [Doc] -> Doc
matchDoc pattern xs = text "match" <+> pattern <+> text "with" <$$> (vcat xs) <$$> text "end"

-- Generation dependent on a boolean
boolDoc :: Bool -> Doc -> Doc
boolDoc b d = if b then d else empty

eitherDoc :: Bool -> Doc -> Doc -> Doc
eitherDoc b x y = if b then x else y

-- Generation of tuples accepted by Coq, no parentheses if there is just one component.
cTupled ::  [Doc] -> Doc
cTupled [] = empty
cTupled [x] = x
cTupled xs = encloseSep lparen rparen (comma <+> empty) xs

-- Generation of a mutual function via Fixpoint defined by f and the list xs.
mutualFixpointDoc :: (MonadReader Signature m, MonadError String m) => (TId -> m Doc) -> [TId] -> m Doc
mutualFixpointDoc f xs = do
  xs' <- forM xs f
  xs'' <- return (map (nest 2) xs')
  return (text "Fixpoint" <+> hcat (punctuate (line <> text " with ") xs'') <> dot)

-- same for inductive types
mutualInductiveDoc :: (MonadReader Signature m, MonadError String m) => (TId -> m Doc) -> [TId] -> m Doc
mutualInductiveDoc f xs = do
  xs' <- forM xs f
  xs'' <- return (map (nest 2) xs')
  return (text "Inductive" <+> hcat (punctuate (line <> text " with ") xs'') <> dot)

-- Repetition of a definition for different instances
liftDoc :: (MonadReader Signature m, MonadError String m) => (a -> m Doc) -> [a] -> m Doc
liftDoc f xs = do
  xs' <- forM xs f
  return (vcat (punctuate line xs'))

-- Representation of variable constructor in Coq
var :: String -> Doc
var x = genSep "var" x

-- Name for up operations in Coq
up :: Bool -> String -> String -> Doc
up b x y = (if b then text "upren" else text "up") <> toSep x <> toSep y

-- Name for cast operations in Coq
cast :: Bool -> String -> String -> Doc
cast b x y = (if b then text "castren" else text "cast") <> toSep x <> toSep y

-- Name for eq closure under casts operations in Coq
castEq :: String -> String -> Doc
castEq x y = text "eq_cast" <> toSep x <> toSep y

toVar :: Bool -> String -> Doc 
toVar b x = (if b then (text "toVarRen") else (text "toVar")) <> toSep x

-- Name for the equality predicate on subsstitutions
eqSubst :: Doc -> Doc -> Doc
eqSubst lsub rsub = text "eq_of_subst" <+> lsub <+> rsub

-- Name for eq to var projection operations in Coq
eqToVar :: String -> Doc 
eqToVar x = text "eq_toVar" <> toSep x

-- Name for lemma that eq is stable under up
eqUp :: String -> [String] -> Doc
eqUp x ys = text "eq_up" <> toSep x <> hcat (map toSep ys)

-- Name of renaming / substitution types in Coq
typeRS :: Bool -> Doc
typeRS b = if b then (text "ren") else (text "subst")

name1RS :: Bool -> Doc 
name1RS b = if b then (text "xi") else (text "sigma")

name2RS :: Bool -> Doc
name2RS b = if b then (text "zeta") else (text "tau")

name3RS :: Bool -> Doc
name3RS b = if b then (text "rho") else (text "theta")

-- Name of list of substitution successors in Coq
substList :: String -> Doc
substList x = genSep "subst_of" x

-- Name for the instantiation operation for given type, with substitution and term
instantiateDoc :: TId -> Doc -> Doc -> Doc
instantiateDoc currentType substArg termArg = genSep "subst" currentType <+> substArg <+> termArg

-- Generation of upId Lemma names
upId :: String -> String -> Doc
upId x y = text "upId" <> toSep x <> toSep y

-- Generation of conjunctions and their types
ands :: [Doc] -> Doc
ands [] = text "True"
ands [x] = x
ands (x : xs) =  x <+> text "/" <> backslash <+> parens (ands xs)

conj :: [Doc] -> Doc
conj [] = text "True"
conj [x] = x
conj (x : xs) = text "conj" <+> parens x <+> parens (ands xs)


-- Has to be called with reverse order
toApDoc :: String -> [Doc] -> Doc
toApDoc s xs = toApDoc' s (reverse xs) where
  toApDoc' s [] = text "eq_refl"
  toApDoc' s [x] = text "ap" <+> text s <+> x
  toApDoc' s (x : xs) = text "apc" <+> parens (toApDoc' s xs)  <+> parens x


-- Generation of the correct renamings
renType :: Bool -> String -> Doc
renType b x = (if b then text "ren_of" else text "subst_of") <+> substList x

-- substType :: String -> Doc
-- substType x = text "subst_of" <+> substList x

-- Generation of the names for composition of substitution and renaming.
compren :: Bool -> String -> Doc
compren b x = if b then  genSep "compren"  x else genSep "comp" x

ren :: Bool -> String -> Doc
ren b x = genSep (if b then "ren" else "subst") x

-- Generation of patterns in Coq
genPattern :: Eq a => [a] -> a -> (a -> Doc) -> (Doc -> Doc) -> Doc
genPattern xs x f g = cTupled (map (\y -> if x == y then g (f y) else f y) xs)

-- Generates wildcards everywhere in the list but on positions with value x.
getPattern :: Eq a => [a] -> a -> Doc -> Doc
getPattern xs x d =  genPattern xs x (\_ -> text "_") (\_ -> d)

typePattern :: [String] -> String -> Doc
typePattern xs s = cTupled (map (genSep s) xs)

idSPattern :: Eq a => [a] -> a -> Doc
idSPattern xs x = genPattern xs x (\_ -> text "idren") (\_ -> text "S")

-- Generation of up all Up Lemmas for a list of identifiers
upLift :: (MonadReader Signature m, MonadError String m) => (TId -> TId -> m Doc) -> [TId] -> m Doc
upLift f = liftDoc (\x -> do
                        xs <- substOf x
                        liftDoc (\y -> f x y) xs)

aligned :: String -> [TId] -> Doc
aligned s xs = hsep (map (genSep s) xs)

substArg :: Bool -> String -> [TId] -> [(Doc, Doc, Bool)]
substArg b s xs = map (\x -> (genSep s x, if b then text "ren" else  text "index ->" <+> text x, False)) xs

eq_of_subst :: Doc -> Doc -> Doc -> Doc
eq_of_subst x y z = text "@eq_of_subst" <+> x <+> y <+> z

eqDoc :: Doc -> Doc -> Doc
eqDoc x y = x <+> text "=" <+> y

letDoc :: Doc -> Doc -> Doc -> Doc
letDoc x y z = text "let" <+> x <+> text ":=" <+> y <+> text "in" <+> z

-- GENERATION OF COQ CODE

-- Generation of (mutual) inductive DATATYPES

positionDoc :: Position -> Doc
positionDoc (Position {argument = arg}) = text arg <+> text "->"

constructorDoc :: TId -> Constructor -> Doc
constructorDoc x (Constructor{name = cname, positions = pos}) =
  text "| " <> text cname <+> colon <+> (hsep (map positionDoc pos)) <+> text x

varDoc :: TId -> Doc
varDoc x = text "| " <> var x  <+> colon <+> text "index ->" <+> text x

indDoc :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
indDoc x = do
  cs <- constructors x
  open <- isOpen x
  let body = vcat (boolDoc open (varDoc x) : map (constructorDoc x) cs)
  return $ defMutDoc (text x) [] (text "Type") body

typeDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc
typeDoc = mutualInductiveDoc indDoc


-- RENAMINGS

-- Generation of substOf

substOfIndDoc :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
substOfIndDoc x = do
  xs <- substOf x
  let body = brackets $ hcat $ (punctuate semi) $ map (\x -> text x <> text ": Type") xs
  return $ defDoc "Definition" (substList x) [] (text "list Type") body

substOfDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc
substOfDoc = liftDoc substOfIndDoc


-- Generation of toVar maps.
-- If the boolean flag is True, generate the version for renamings.
toVarDoc' ::  (MonadReader Signature m, MonadError String m) => Bool -> TId -> m Doc
toVarDoc' b x = do
  xs <- substOf x
  let argType = typeRS b
      argName = name1RS b
      funName = toVar b x
      args = [(argName, renType b x, False)]
      pattern = getPattern xs x argName
      body = letDoc pattern argName argName
  return $ defDoc "Definition" funName args (text "_") body

toVarDoc :: (MonadReader Signature m, MonadError String m) => Bool -> [TId] -> m Doc
toVarDoc b = liftDoc (toVarDoc' b)

-- Project a toVar equality from a full subsitution equality
toVarEqDoc' :: (MonadReader Signature m, MonadError String m) => TId -> m Doc 
toVarEqDoc' ty = do
  succTy <- substOf ty
  b <- isOpen ty
  let substType = renType False ty
      substName1 = name1RS False
      substName2 = name2RS False
      eqAssumptionType = eqSubst substName1 substName2
      eqAssumptionName = text "E"
      idType = text "index"
      idName = text "n"
      defName = eqToVar ty
      retType = toVar False ty <+> substName1 <+> idName <+> equals <+> toVar False ty <+> substName2 <+> idName
      args = [(substName1, substType, True), (substName2, substType, True), (eqAssumptionName, eqAssumptionType, False), (idName,idType,False)]
      destructs = decompose substName1 succTy </> decompose substName2 succTy </> decompose eqAssumptionName succTy
      exactBody = (genSep' eqAssumptionName ty) <+> idName
  -- return $ boolDoc (not (null succTy)) (definedWithTacticPrefixDoc defName args retType destructs exactBody)
  return $ boolDoc b (definedWithTacticPrefixDoc defName args retType destructs exactBody)

toVarEqDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc 
toVarEqDoc = liftDoc toVarEqDoc'

-- Generation of Casts (including closure of ext. equality under casts)
castDoc' :: (MonadReader Signature m, MonadError String m) => Bool -> TId -> TId -> m Doc
castDoc' b from to = do
  succFrom <- substOf from
  succTo <- substOf to
  let argType = typeRS b
      argName = name1RS b
      name = cast b from to
      retType = renType b to
      args = [(argName, renType b from, False)]
      xs = map (\x -> if (L.elem x succTo) then genSep' argName x else text "_") succFrom
      ys = map (genSep' argName) $ L.filter (\x -> L.elem x succTo) succFrom
      body = letDoc (cTupled xs) argName (cTupled ys)
  return $ boolDoc (not (null succTo)) (defDoc "Definition" name args retType body)

castDoc :: (MonadReader Signature m, MonadError String m) => Bool -> [TId] -> m Doc
castDoc b fromList = liftDoc (\x -> do
                                  xs <- arguments x
                                  liftDoc (castDoc' b x) (filter (\y -> y /= x) xs)
                                  ) fromList

castEqDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId -> m Doc 
castEqDoc' from to = do
  succFrom <- substOf from
  succTo <- substOf to
  let substType = renType False from
      substName1 = name1RS False
      substName2 = name2RS False
      eqAssumptionType = eqSubst substName1 substName2
      eqAssumptionName = text "E"
      defName = castEq from to
      retType = eqSubst (parens (cast False from to <+> substName1)) (parens (cast False from to <+> substName2))
      args = [(substName1, substType, True), (substName2, substType, True), (eqAssumptionName, eqAssumptionType, False)]
      destructs = decompose substName1 succFrom </> decompose substName2 succFrom </> decompose eqAssumptionName succFrom
      exactBody = conj $ map (genSep' eqAssumptionName) succTo
  return $ boolDoc (not (null succTo)) (definedWithTacticPrefixDoc defName args retType destructs exactBody)

castEqDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc
castEqDoc = liftDoc (\x -> do
                        xs <- arguments x
                        liftDoc (castEqDoc' x) (filter (\y -> y /= x) xs)
                    )

-- Generation of up-functions for renamings.
upRenDoc :: (MonadReader Signature m, MonadError String m) =>  [TId] -> m Doc
upRenDoc = upLift upRenDoc'
 where upRenDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId  -> m Doc
       upRenDoc' x y = do
         xs <- substOf x
         let name = up True x y
             args = [(text "xi", renType True x, False)]
             retType = renType True x
             ys = genPattern xs y (genSep "xi") (\x -> text "up_ren" <+> x)
             body = letDoc (typePattern xs "xi")(text "xi") ys
         return $ defDoc "Definition" name args retType body


-- Generation of the renaming and substiutions.
-- If b is True, then the version for renamings is generated.
varSubstDoc :: Bool -> TId -> Doc
varSubstDoc b x = caseDoc (var x <+> text "x")
                  (boolDoc b (var x) <+>
                   parens (parens (genSep' (eitherDoc b (text "toVarRen") (text "toVar") ) x <+> (name1RS b)) <+> text "x"))

positionSubstDoc :: (MonadReader Signature m, MonadError String m) => Bool -> TId -> Position -> Doc -> m Doc
positionSubstDoc b x (Position{binders = bs, argument = arg}) argName = do
  argList <- substOf arg
  return (if (argList == [])
             then argName
             else let renName = name1RS b
                      renType = typeRS b
                      main_ren = if (x == arg) then renName else parens (cast b x arg <+> renName)
                      up_ren = foldl (\v arg -> parens (up b x arg <+> v)) main_ren bs
                  in parens (genSep' renType arg <+> up_ren <+> argName))



constructorSubstDoc ::  (MonadReader Signature m, MonadError String m) => Bool -> TId -> Constructor -> m Doc
constructorSubstDoc b x (Constructor{name = cname, positions = pos}) = do
  (old, new) <- foldM (\(xs, ys) p -> do
                             pText <- positionSubstDoc b x p (text "s" <> int (length xs))
                             return $ (text "s" <> int (length xs)  : xs, parens pText : ys)) ([], []) pos
  return $ caseDoc (text cname <+> sep (reverse old)) (text cname <+> sep (reverse new))


-- Generation of renaming for a type.
renDoc :: (MonadReader Signature m, MonadError String m) => Bool -> [TId] -> m Doc
renDoc b = mutualFixpointDoc (renDoc' b)
  where
    renDoc' :: (MonadReader Signature m, MonadError String m) => Bool -> TId -> m Doc
    renDoc' b x = do
      let argType = name1RS b
          argName = typeRS b
      cs <- constructors x
      open <- isOpen x
      xs <- mapM (constructorSubstDoc b x) cs
      let funName = genSep' argName x
          args = [(argType, renType b x, False), (text "s", text x, False)]
          retType = text x
          body = matchDoc (text "s") (boolDoc open (varSubstDoc b x) : xs)
      return $ defMutDoc funName args retType body


-- Generation of SUBSTITUTIONS

toCastDoc :: Bool -> String -> String -> Doc -> Doc
toCastDoc b from to s = if (from == to) then s else parens (cast b from to <+> s)


-- Generation of ups for compositions.

upDoc :: (MonadReader Signature m, MonadError String m) =>  [TId] -> m Doc
upDoc = upLift upDoc'
  where upDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId -> m Doc
        upDoc' x y = do
          xs <- substOf x
          let funName = up False x y
              args = [(text "sigma", renType False x, False)]
              retType = renType False x
              sigmaList = idSPattern xs y
              matchList = typePattern xs "sigma"
              resList = genPattern xs y (genSep "sigma") (\z -> text "scons" <+> (parens (var y <+> int 0)) <+> z)
              body = matchDoc (compren True x <+> text "sigma" <+> sigmaList) [caseDoc matchList resList]
          return $ defDoc "Definition" funName args retType body


-- Generation of Canonical Instances

substMixinDoc :: TId ->  Doc
substMixinDoc x = let
  name = genSep "substMixin" x
  retType = text "substMixin" <+> text x
  body =  text "{|" <//>
          text "subst_of_substType :=" <+> substList x <> text ";" <//>
          text "inst_of_substType :=" <+> genSep "subst" x <//>
          text "|}"
  in defDoc "Definition" name [] retType body

substTypeDoc :: TId ->  Doc
substTypeDoc x = let
  name = genSep "substType" x
  retType = text"substType"
  body = text "Eval hnf in @Pack" <+> text x <+> genSep "substMixin" x <+> text x
  in defDoc "Canonical Structure" name [] retType body


-- Do we really want this?
compDoc :: (MonadReader Signature m, MonadError String m) => Bool -> TId -> m Doc
compDoc b x = do
  xs <- substOf x
  let fName = compren b x
      retType = renType False x
      tau = if b then "xi" else "tau"
      args = [(text "sigma", renType False x, False), (text tau, renType b x, False)]
      cases = cTupled $ map (\x -> text "fun x =>" <+> x) $ map (\y -> genSep' (typeRS b) y <+> toCastDoc b x y (text tau) <+> (parens (genSep "sigma" y <+> text "x"))) xs
      body = matchDoc (text "sigma") [caseDoc (typePattern xs "sigma") cases]
  return $ defDoc "Definition" fName args retType body


-- Generation of LEFT IDENTITY LEMMA

upIdDoc :: (MonadReader Signature m, MonadError String m) =>  [TId] -> m Doc
upIdDoc =  upLift upIdDoc'
  where upIdDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId -> m Doc
        upIdDoc' x y = do
          xs <- substOf x
          let (sigmas, taus) = (typePattern xs "sigma", typePattern xs "tau")
              eqs = map (\x -> (genSep "E" x, genSep "sigma" x <+> text "==" <+> var x, False)) xs
              ren' = idSPattern xs y
              fName = upId x y
              args = substArg False "sigma" xs ++ eqs
              tauEqs = map (\x -> genSep "tau" x <+> text "==" <+> var x) xs
              retType = eq_of_subst (substList x) (parens (up False x y <+> sigmas)) (typePattern xs "var")
              tupleBody = map (\z -> let
                           ren = genSep "ren" z <+> toCastDoc True x z ren'
                           body' = text "ap" <+> parens ren <+> (parens $ genSep "E" z <+> text "n")
                           in if (z == y)
                              then matchDoc (text "n" <+> text "return" <+> parens ( matchDoc ((up False x y ) <+> sigmas) [caseDoc taus (genSep "tau" z <+> text "n =" <+> var z <+> text " n")])) [caseDoc (int 0) (text "eq_refl"), caseDoc (text "S n") body']
                              else body') xs
              tupleComp = map (\x -> text "fun n =>"  <+> x) tupleBody
          return $ defDoc "Definition" fName args retType (conj tupleComp)


posIdDoc :: (MonadReader Signature m, MonadError String m) => TId -> Position -> Doc -> m Doc
posIdDoc x (Position{binders = bs, argument = arg}) s = do
  args <- substOf arg
  let sigmas = map (\x -> text "_") args
      base = if (args == [])
             then text "eq_refl"
             else genSep "id" arg <+> hsep sigmas <+>  aligned "E" args <+> s
      body = foldl (\f b -> matchDoc (upId arg b <+> hsep sigmas <+> aligned "E" args) [caseDoc (conj (map (genSep "E") args)) f]) base bs
  return body


consIdDoc :: (MonadReader Signature m, MonadError String m) => TId -> Constructor -> m Doc
consIdDoc x (Constructor {name = cname, positions = pos}) = do
 (old, new) <- foldM (\(xs, ys) p -> do
                             pText <- posIdDoc x p (text "s" <> int (length xs))
                             return $ (text "s" <> int (length xs)  : xs, parens pText : ys)) ([], []) pos
 return (caseDoc (text cname <+> sep (reverse old)) (toApDoc cname (reverse new)))


idDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc
idDoc = mutualFixpointDoc idDoc'
  where idDoc' :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
        idDoc' x = do
          xs <- substOf x
          cs <- constructors x
          b <- isOpen x
          conCases <- mapM (consIdDoc x) cs
          let fName = genSep "id" x
              eqs = map (\x -> (genSep "E" x, genSep "sigma" x <+> text "==" <+> var x, False)) xs
              args = substArg False "sigma" xs ++ eqs ++ [(text "s", text x, False)]
              retType = eqDoc (genSep "subst" x <+> typePattern xs "sigma" <+> text "s") (text "s")
              varCase = boolDoc b $ caseDoc (var x <+> text "n") (genSep "E" x <+> text "n")
              cases = varCase : conCases
              body = matchDoc (text "s") cases
          return $ defMutDoc fName args retType body


-- Generation of toSubst
toSubstDoc :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
toSubstDoc x = do
  xs <- substOf x
  let fName = genSep "toSubst" x
      args = [(text "xi", renType True x, False)]
      retType = renType False x
      cases = cTupled $ map (\y -> text "fun x =>" <+> var y <+> parens (genSep "xi" y <+> text "x")) xs
      caseBody = [caseDoc (typePattern xs "xi") cases]
      body = matchDoc (text "xi") caseBody
  return $ defDoc "Definition" fName args retType body


-- Generation of COMPOSITION LEMMAS

posCompRenRenDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> Position -> Doc -> m Doc
posCompRenRenDoc b1 b2 x (Position{binders = bs, argument = arg}) s = do
   xs <- substOf arg
   let (t1, t2) = (typeRS b1, typeRS b2)
       xi1 = if b1 then "xi" else "sigma"
       xi2 = if b2 then "zeta" else "tau"
       xi3 = if (not (b1&&b2)) then "rho" else "theta"
       fName = text "compTrans" <> sepsym <> t1 <> sepsym <> t2 <> toSep arg
       upName = text "up" <> sepsym <> t1 <> sepsym <> t2
       genXi s = map (\x -> if (elem x bs) then parens (text "up_ren" <+> genSep s x) else genSep s x) xs
       eqs = map (\x -> if (elem x bs) then parens (upName <+> genSep xi1 x <+> genSep xi2 x <+> genSep xi3 x <+> genSep "E" x) else genSep "E" x) xs
       body = if (xs == []) then text "eq_refl" else fName <+> hsep (genXi xi1) <+> hsep (genXi xi2) <+> hsep (genXi xi3) <+> hsep eqs <+> s
   return body

consCompRenRenDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> Constructor -> m Doc
consCompRenRenDoc b1 b2 x (Constructor {name = cname, positions = pos}) = do
  (old, new) <- foldM (\(xs, ys) p -> do
                              pText <- posCompRenRenDoc b1 b2 x p (text "s" <> int (length xs))
                              return $ (text "s" <> int (length xs)  : xs, parens pText : ys)) ([], []) pos
  return (caseDoc (text cname <+> sep (reverse old)) (toApDoc cname (reverse new)))

compTransRenRenDoc' :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> m Doc
compTransRenRenDoc' b1 b2 x = do
  xs <- substOf x
  cs <- constructors x
  b <- isOpen x
  cases' <- mapM (consCompRenRenDoc b1 b2 x) cs
  let (t1, t2, t3) = (typeRS b1, typeRS b2, typeRS (b1||b2))
      xi1 = if b1 then  "xi" else "sigma"
      xi2 = if b2 then  "zeta" else  "tau"
      xi3 = if (not (b1 && b2)) then "rho" else "theta"
      comp = if (b1 && b2) then text "funcomp" else compren b1 x
      fName = text "compTrans" <> sepsym <> t1 <> sepsym <> t2 <> toSep x
 --     (xi1, xi2, xi3) = (typePattern xs xi1, , typePattern xs xi3)
      xis = map (\x -> (x, text "ren", False)) (map (genSep xi1) xs) ++ map (\x -> (x, text "ren", False)) (map (genSep xi2) xs) ++ map (\x -> (x, text "ren", False)) (map (genSep xi3) xs)
      eqs = map (\x -> (genSep "E" x, comp <+> parens (genSep xi1 x) <+> parens (genSep xi2 x)  <+> text "==" <+> genSep xi3 x, False)) xs
      args = xis ++ eqs ++ [(text "s", text x, False)]
      retType = genSep' t2 x <+> typePattern xs xi2 <+> parens (genSep' t1 x <+>  typePattern xs xi1 <+> text "s") <+> text "=" <+> genSep' t3 x <+> typePattern xs xi3 <+> text "s"
      varCase = boolDoc b $ caseDoc (var x <+> text "n") (text "ap" <+> var x <+> parens (genSep "E" x <+> text "n"))
      cases = varCase : cases'
      body = matchDoc (text "s") cases
  return $ defMutDoc fName args retType body

compTransRenRenDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> [TId] -> m Doc
compTransRenRenDoc b1 b2 = mutualFixpointDoc (compTransRenRenDoc' b1 b2)

-- Proving Associativity
upT :: Bool -> Bool -> String -> String-> Doc
upT b1 b2 x y = text "up" <> sepsym <> typeRS b1 <> sepsym <> typeRS b2 <> toSep x <> toSep y


-- Don't I want to have just the function up_ren_ren_x_y
posCompDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> Position -> Doc -> m Doc
posCompDoc b1 b2 x (Position{binders = bs, argument = arg}) s = do
   xs <- substOf arg
   let (t1, t2) = (typeRS b1, typeRS b2)
       xi1 = if b1 then "xi" else "sigma"
       xi2 = if b2 then "zeta" else "tau"
       xi3 = if (b1&&b2) then "rho" else "theta"
       fName = text "compTrans" <> sepsym <> t1 <> sepsym <> t2 <> toSep arg
       names s = hsep $ map (genSep s) xs -- Will not be necessary in the updated version.
       upName z = if (b1&&b2)
                  then cTupled [text "up" <> sepsym <> t1 <> sepsym <> t2 <+> genSep xi1 x <+> genSep xi2 x <+> genSep xi3 x <+> genSep "E" x | x <- xs]
                  else upT b1 b2 x z <+> names xi1 <+> names xi2 <+> names xi3 <+> names "E"
       cases = if (b1&&b2)
               then cTupled (map (genSep "E") xs)
               else conj (map (genSep"E") xs)
       (xi1s, xi2s, xi3s) = (map (genSep xi1) xs, map (genSep xi2) xs, map (genSep xi3) xs)
       spaces b s = if b then hsep (map (\x -> if (elem x bs) then parens (text "up_ren" <+> genSep s x) else genSep s x) xs) else hsep (map (\x -> text "_") xs)
       base = if (xs == [])
              then text "eq_refl"
              else fName <+>  spaces b1 xi1 <+> spaces b2 xi2 <+> spaces (b1&&b2) xi3 <+> names "E" <+> s
       upped s binder b = up b x binder <+> cTupled (map (genSep s) xs)
       body = foldl (\v b -> matchDoc (upName b) [caseDoc cases v]) base bs
   return body

consCompDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> Constructor -> m Doc
consCompDoc b1 b2 x (Constructor {name = cname, positions = pos}) = do
  (old, new) <- foldM (\(xs, ys) p -> do
                              pText <- posCompDoc b1 b2 x p (text "s" <> int (length xs))
                              return $ (text "s" <> int (length xs)  : xs, parens pText : ys)) ([], []) pos
  return (caseDoc (text cname <+> sep (reverse old)) (toApDoc cname (reverse new)))


compTrans :: Bool -> Bool -> String -> Doc
compTrans b1 b2 x = text "compTrans" <> sepsym <> typeRS b1 <> sepsym <> typeRS b2 <> toSep x

-- Generate the composition lemmas.
-- b1 and b2 indicate whether the first / second argument are renaming (if True) or a substitution (if False).
compTransDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> [TId] -> m Doc
compTransDoc b1 b2 = mutualFixpointDoc (compTransDoc' b1 b2)
  where compTransDoc' :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> m Doc
        compTransDoc' b1 b2 x = do
          xs <- substOf x
          cs <- constructors x
          b <- isOpen x
          cases' <- mapM (consCompDoc b1 b2 x) cs -- Generation of constructor arguments.
          let fName = compTrans b1 b2 x
              xi1 = if b1 then  "xi" else "sigma"
              xi2 = if b2 then  "zeta" else  "tau"
              xi3 = if (b1 && b2) then "rho" else "theta"
              comp x = do
                xs <- substOf x
                return $ if (b1 && b2) -- Not needed anymore in the new version. (Therefore not cleaned up.)
                         then text "funcomp"  <+> parens (genSep xi1 x) <+> parens (genSep xi2 x)
                         else
                           if b1 then parens (text "fun x => " <+> genSep xi2 x  <+> parens (genSep xi1 x <+> text "x"))
                           else if b2 then parens ( text "fun x => " <+> genSep "ren" x <+> cTupled (map (genSep xi2) xs)  <+> parens (genSep xi1 x <+> text "x"))
                           else parens ( text "fun x => " <+> genSep "subst" x <+> cTupled (map (genSep xi2) xs)  <+> parens (genSep xi1 x <+> text "x"))
          eqs <- mapM (\x -> do
                        xs <- comp x
                        return (genSep "E" x, xs <+> text "==" <+> genSep xi3 x, False)) xs
          let args = substArg b1 xi1 xs ++ substArg b2 xi2 xs ++ substArg (b1&&b2) xi3 xs  ++ eqs ++ [(text "s", text x, False)]
              retType = eqDoc (ren b2 x <+> typePattern xs xi2 <+> parens (ren b1 x <+>  typePattern xs xi1 <+> text "s"))
                        (ren (b1&&b2) x <+> typePattern xs xi3 <+> text "s")
          let varCase = boolDoc b $ caseDoc (var x <+> text "n") (boolDoc (b1&&b2) (text "ap" <+> var x) <+> parens (genSep "E" x <+> text "n"))
              cases = varCase : cases'
              body = matchDoc (text "s") cases
          return $ defMutDoc fName args retType body


compE :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> m Doc
compE b1 b2 x = do
  xs <- substOf x
  let (t1, t2, t3) = (typeRS b1, typeRS b2, typeRS (b1&&b2))
      xi1 = if b1 then "xi" else "sigma"
      xi2 = if b2 then "zeta" else "tau"
      fName = text "compE" <> sepsym <> t1 <> sepsym <> t2 <> toSep x
      comp x = do
        xs <- substOf x
        return $ if ((not b1) && not b2)
          then (text "fun n =>" <+> genSep "subst" x <+> parens (cTupled (map (genSep xi2) xs)) <+> parens (genSep xi1 x <+> text "n"))
          else if ((not b1) && b2) then (text "fun n =>" <+> genSep "ren" x <+> parens (cTupled (map (genSep xi2) xs)) <+> parens (genSep xi1 x <+> text "n"))
                 else text "funcomp" <+> genSep xi1 x <+> genSep xi2 x
      compName = text "compE" <> sepsym <> t1 <> sepsym <> t2 <> toSep x
      (xi1T, xi2T) = (substArg b1 xi1 xs, substArg b2 xi2 xs)
  comps <- mapM (\x -> do
                    xs <- comp x
                    return (parens xs)) xs
  let eqs = map (\_ -> parens (text "fun _ => eq_refl")) xs
      args = xi1T ++ xi2T ++ [(text "s", text x, False)]
      retType = genSep' t2 x <+> typePattern xs xi2 <+> parens (genSep' t1 x <+> typePattern xs xi1 <+> text "s") <+> text "=" <+> genSep' t3 x <+> cTupled comps  <+> text "s"
      body = text "compTrans" <> sepsym <> t1 <> sepsym <> t2 <> toSep x <+> hsep (map (genSep xi1) xs) <+> hsep (map (genSep xi2) xs) <+> hsep comps <+> hsep eqs <+> text "s"
  return $ defDoc "Definition" fName args retType body


upSubstDoc' :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> TId -> TId -> m Doc
upSubstDoc' b1 b2 x y = do
    xs <- substOf x
    let xi1 = if b1 then "xi" else "sigma"
        xi2 = if b2 then "rho" else "theta"
    eqs <- mapM (\z -> do
                   zs <- substOf z
                   return (genSep "E" z, parens ( text "fun x => " <+> if b1 then (genSep xi2 z  <+> parens (genSep xi1 z <+> text "x")) else ( ren b2 z <+> cTupled (map (genSep xi2) zs)  <+> parens (genSep xi1 z <+> text "x"))) <+> text "==" <+> genSep "tau" z, False)) xs
    let fName = text "up" <> sepsym <> typeRS b1 <> sepsym <>  typeRS b2 <> toSep x <> toSep y
        (sigmas, taus, xis) = (map (genSep xi1) xs, map (genSep "tau") xs, map (genSep xi2) xs)
        args = substArg b1 xi1 xs ++ substArg b2 xi2 xs ++ substArg False "tau" xs ++ eqs
        ren' = idSPattern xs y
        retType = eq_of_subst (substList x)
                (parens (compren b2 x <+> (if b1 then parens (genSep "toSubst" x <+> (parens (up b1 x y <+> cTupled sigmas))) else parens (up b1 x y <+> cTupled sigmas))  <+> parens (up b2 x y <+> cTupled xis)))
                (parens (up False x y <+> cTupled taus))
        matchReturn z = text "return" <+>
                      matchDoc (compren b2 x <+> (if b1 then parens (genSep "toSubst" x <+> (parens (up b1 x y <+> cTupled sigmas))) else parens (up b1 x y <+> cTupled sigmas))  <+> parens (up b2 x y <+> cTupled xis) <> text "," <+> up False x y <+> cTupled taus)
                      [caseDoc (cTupled sigmas <> text "," <+> cTupled taus) (genSep xi1 z <+> text "n" <+> text "=" <+> genSep "tau" z <+> text "n")]
    tupleBody <- mapM (\z -> do
                         zs <- substOf z
                         let
                           eq1 = text "compE_ren" <> sepsym <> typeRS b2 <> toSep z <+> hsep (map (\x -> if (x == y) then text "S" else text "idren") zs) <+> (if b2 then hsep (map (\x -> if (x == y) then  parens (text "up_ren" <+> genSep xi2 x) else genSep xi2 x) zs) else  hsep (map (\x -> text "_") zs))  <+> parens (genSep "sigma" z <+> text "n")
                           eq2 = genSep (if b2 then "compE_ren_ren" else "compE_subst_ren") z <+> hsep (map (genSep xi2) zs) <+> hsep (map (\x -> if (x == y) then text "S" else text "idren") zs) <+> parens (genSep "sigma" z <+> text "n")
                           eq3 = text "ap" <+> parens (genSep "ren" z <+> cTupled (map (\x -> if (x == y) then text "S" else text "idren") zs )) <+> (parens $ genSep "E" z <+> text "n")
                           body_changed = text "eq_trans" <+> parens eq1 <+> parens ( text "eq_trans" <+>  parens (text "eq_sym" <+> parens eq2) <+> parens eq3)
                           in if (z == y)
                              then return $ matchDoc (text "n" <+> matchReturn z) [caseDoc (int 0) (text "eq_refl"), caseDoc (text "S n") body_changed]
                              else return body_changed) xs
    let tupleBody' = map (\z -> let
                           ren = genSep "ren" z <+> toCastDoc True x z ren'
                           body' = text "ap" <+> parens ren <+> (parens $ genSep "E" z <+> text "n")
                           in if (z == y)
                              then matchDoc (text "n" <+> matchReturn z) [caseDoc (int 0) (text "eq_refl"), caseDoc (text "S n") body']
                              else body') xs
        tupleComp = map (\x -> text "fun n =>"  <+> x) (if b1 then tupleBody' else tupleBody)
    return $ defDoc "Definition" fName args retType (conj tupleComp)


upSubstDoc :: (MonadReader Signature m, MonadError String m) => Bool -> Bool -> [TId] -> m Doc
upSubstDoc b1 b2 = upLift (upSubstDoc' b1 b2)


tabulate :: Int -> (Int -> a) -> [a]
tabulate n f = if (n == 0) then [] else tabulate (n-1) f  ++ [f (n-1)]


-- Generation of Extensionality Lemmas

matchRet :: Doc -> Doc -> [(Doc, Doc)] -> Doc
matchRet v retType cases = text "match" <+> v <+> text "return" <+> retType </> encloseSep (text "with" <+> empty) (empty <+> text "end") (empty <+> text "|" <+> empty) (map (\(p,b) -> p <+> text "=>" <+> b) cases)

upExtDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId -> m Doc 
upExtDoc' currentType upType = do
  succ <- substOf currentType
  let substType = renType False currentType
      substName1 = name1RS False
      substName2 = name2RS False
      eqAssumptionType = eqSubst substName1 substName2
      eqAssumptionName = text "E"
      defName = eqUp currentType [upType] -- why is there only one uptype here
      retType = eqSubst (parens (up False currentType upType <+> substName1)) (parens (up False currentType upType <+> substName2))
      args = [(substName1, substType, True), (substName2, substType, True), (eqAssumptionName, eqAssumptionType, False)]
      destructs = decompose substName1 succ </> decompose substName2 succ </> decompose eqAssumptionName succ
      indexAbstraction v = text "fun" <+> text v <> colon <+> text "index" <+> text "=>" -- we may want to factor this out !
      idCase ty = indexAbstraction "i" <+> text "ap" <+> text "_" <+> parens (genSep' eqAssumptionName ty <+> text "i")
      upComponent s ty = (var ty <+> text "0" <+> text ".:" <+> (genSep' s ty) <+> text ">>>" <+> (genSep "ren" ty) <+> (toCastDoc True currentType ty (idSPattern succ upType)))
      upCase ty = indexAbstraction "i" <+> matchRet
                  (text "i")
                  (parens (upComponent substName1 ty) <+> text "i" <+> equals <+> parens (upComponent substName2 ty) <+> text "i")
                  [(text "0", text "eq_refl"),(text "S" <+> text "j", text "ap" <+> text "_" <+> parens (genSep' eqAssumptionName ty <+> text "j"))]
      exactBody = conj $ map (\t -> if t == upType then upCase t else idCase t) succ
  return $ boolDoc (not (null succ)) (definedWithTacticPrefixDoc defName args retType destructs exactBody)

upExtDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc 
upExtDoc = upLift upExtDoc'

extNameDoc :: TId -> Doc
extNameDoc currentType = genSep "subst_eq" currentType

toEqCastDoc :: String -> String -> Doc -> Doc
toEqCastDoc from to s = if (from == to) then s else parens (castEq from to <+> s)

eqUpInstDoc :: TId -> [TId] -> Doc -> Doc
eqUpInstDoc _    [] eq = eq
eqUpInstDoc from to eq = parens (eqUp from to <+> eq)

posExtDoc :: (MonadReader Signature m, MonadError String m) => TId -> Position -> Doc -> m Doc
posExtDoc currentType (Position{binders = bs, argument = arg}) s = do
  argSucc <- substOf arg -- used to figure out, if arg has a subsitution operation, below argSucc = [] means no subst
  return $ if not (null argSucc) then (extNameDoc arg <+> eqUpInstDoc arg bs (toEqCastDoc currentType arg (text "E")) <+> s) else text "eq_refl" -- BUG: we may need to return eq_refl here


consExtDoc :: (MonadReader Signature m, MonadError String m) => TId -> Constructor -> m Doc
consExtDoc currentType (Constructor {name = cName, positions = pos}) = do
  (cParamsRev, recCallArgs) <- foldM (\(xs, ys) p -> do
                          pText <- posExtDoc currentType p (text "s" <> int (length xs))
                          return $ (text "s" <> int (length xs)  : xs, parens pText : ys)) ([], []) pos
  return (caseDoc (text cName <+> sep (reverse cParamsRev)) (genSep "congr" cName <+> sep (reverse recCallArgs)))


extDoc :: (MonadReader Signature m, MonadError String m) => [TId] -> m Doc
extDoc = mutualFixpointDoc extDoc'
  where extDoc' :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
        extDoc' currentType = do
          cs <- constructors currentType
          b <- isOpen currentType
          conCases <- mapM (consExtDoc currentType) cs
          let substType = renType False currentType
              substName1 = name1RS False
              substName2 = name2RS False
              eqAssumptionType = eqSubst substName1 substName2
              eqAssumptionName = text "E"
              termArgType = text currentType
              termArgName = text "s"
              functionName = extNameDoc currentType
              retType = eqDoc (instantiateDoc currentType substName1 termArgName) (instantiateDoc currentType substName2 termArgName)
              args = [(substName1, substType, True), (substName2, substType, True), (eqAssumptionName, eqAssumptionType, False), (termArgName, termArgType, False)]
              varCase = boolDoc b $ caseDoc (var currentType <+> text "n") (eqToVar currentType <+> eqAssumptionName <+> text "n")
              cases = varCase : conCases
              body = matchDoc (text "s") cases
          return $ defMutDoc functionName args retType body

-- Generation of Congruence Lemmas
congrDoc :: Constructor -> Doc
congrDoc (Constructor {name = cname, positions = pos}) = let
  fName = genSep "congr" cname
  n = length pos
  (old, new) = (tabulate n (\x -> text "s"  <> int x), tabulate n (\x -> text "t" <> int x))
  args = map (\(a,b) -> (a,b,True)) (zip old (map (\(Position {argument = name}) -> text name) pos) ++ zip new (map (\(Position {argument = name}) -> text name) pos)) ++
    tabulate n (\x -> (text "E" <> int x, eqDoc (text "s"  <> int x) (text "t" <> int x), False))
  retType = eqDoc (text cname <+> hsep old) (text cname <+> hsep new)
  body = toApDoc cname (tabulate n (\x -> text "E"  <> int x))
  in (defDoc "Definition" fName args retType body)



-- Generation of Automation

classGen :: Doc -> [(Doc, Doc, Bool)] -> [Doc] -> Doc -> Doc -> Doc 
classGen name args argMode eqName body = let
  classDef = text "Class" <+> name <+> renderArgs args <+> text ":=" <+> eqName <+> text ":" <+> body <+> text "."
  hintDef = text "Hint Mode" <+> name <+> hsep argMode <+> text ": typeclass_instance."
  in classDef <> linebreak <> hintDef

-- TODO: GIVE PRIORITY - with option? - TODO: Check this possibility and the syntax of options.
instanceGen :: Doc -> [(Doc, Doc, Bool)] -> Doc -> Doc -> Doc
instanceGen name args body proof = text "Instance" <+> name <+> renderArgs args <+> text ":" <+> body <> text "." 
                                   <> linebreak <> proof


positionRewDoc :: (MonadReader Signature m, MonadError String m) => TId -> Position -> m Doc
positionRewDoc x (Position{binders = bs, argument = arg}) = do
  argList <- substOf arg
  return (if (argList == [])
             then text "sigma" 
             else let main_ren = if (x == arg)
                                 then text "sigma"
                                 else parens (toCastDoc False x arg (text "sigma"))
                      up_ren = foldl (\v arg -> parens (up False x arg <+> v)) main_ren bs
                  in parens up_ren)


upRewDoc :: (MonadReader Signature m, MonadError String m) =>  [TId] -> m Doc
upRewDoc = upLift upRewDoc'
  where upRewDoc' :: (MonadReader Signature m, MonadError String m) => TId -> TId -> m Doc
        upRewDoc' x y = do
          xs <- substOf x
          let ids = parens (cTupled (map (\z -> (if y == z then text "S" else text "id") <+> text ">>>" <+> ( genSep "var" z)) xs))
          return $ instanceGen (genSep "AsimplSubstUp" x <> toSep y)
            (map (\x -> (genSep "sigma" x, text "index ->" <+> text x, False)) xs ++
             map (\x -> (genSep "tau" x, text "index ->" <+> text x, False)) xs ++
             map (\z -> (genSep "E" z, text "AsimplGen" <+> parens ((if (y == z) then genSep "var" y <+> text "0 .:" else empty) <+> ( genSep "sigma" z <+> text ">>>" <+>  parens (genSep "subst" z <+> parens ( toCastDoc False x z ids)))) <+> genSep "tau" z, False)) xs)
            (genSep "AsimplSubst" x <+> parens (up False x y <+> cTupled (map (genSep "sigma") xs)) <+> cTupled (map (genSep "tau") xs))
             (text "Admitted.")


constructorRewDoc ::  (MonadReader Signature m, MonadError String m) => TId -> Constructor -> m Doc
constructorRewDoc x (Constructor{name = cname, positions = pos}) = do
   (old, new, supernew, thetas) <- foldM (\(xs, ys, zs, thetas) (Position {binders = binders, argument = argument}) -> do
                              pText <- positionRewDoc x (Position binders argument) --  <> int (length xs))
                              return $ (text "s" <> int (length xs)  : xs,
                                        (text "E" <> sepsym <> int (length xs), genSep "AsimplInst" argument <+> (text "s" <> int (length xs)) <+> (text "theta" <> sepsym <> int (length xs))  <+> (text "s" <> int (length xs) <> text "'"), False) : ys,
                                        (text "E" <> sepsym <> int (length xs) <> text "'", genSep "AsimplSubst" argument <+> pText <+> (text "theta" <> sepsym <> int (length xs)), False) : zs,
                                        (text "theta" <> sepsym <> int (length xs), renType False argument, False): thetas))
                                ([], [], [], []) pos
   return $ instanceGen (genSep "asimplInst" cname)
     (map (\x -> (x, text "_", False)) (reverse old) ++ map (\x -> (x <> text "'", text "_", False)) (reverse old)
      ++ [(text "sigma", renType False x, False)]
      ++ (reverse thetas)
      ++ (reverse supernew) 
      ++ (reverse new) )--- ARGUMENTS
     (genSep "AsimplInst" x <+> parens (text cname <+> sep (reverse old)) <+> text "sigma" <+> parens (text cname <+> sep (map (\x -> x <> text "'") (reverse old))))
     (text "Admitted.")


generateAutomationClasses ::  (MonadReader Signature m, MonadError String m) => TId -> m Doc
generateAutomationClasses x = do
  xs <- substOf x
  cs <- constructors x
  b <- isOpen x
  let asimplInstClass = classGen (genSep "AsimplInst" x)
        [(text "s", text x, False), (text "sigma", renType False x, False),  (text "t", text x, False)] -- arguments
        [text "+", text "+", text "-"] -- mode of arguments
        (genSep "asimplInstEqn" x)  
        ((parens (genSep "subst" x <+> text "sigma")) <+> text "s = t") -- body
      asimplSubstClass = classGen (genSep "AsimplSubst" x)
        [(text "sigma", renType False x, False), (text "tau", renType False x, False)]
        [text "+", text "-"]
        (genSep "asimplSubstEqn" x)
        (matchDoc (text "sigma, tau") [caseDoc (cTupled (map (genSep "sigma") xs) <> text "," <+> cTupled (map (genSep "tau") xs)) (ands (map (\x -> parens ( text "forall x," <+> genSep "sigma" x <+> text "x =" <+> genSep "tau" x <+> text "x")) xs))])
      asimplCompClass = classGen (genSep "AsimplComp" x) -- We assume the given arguments to be normalized.
        [(text "sigma", renType False x, False), (text "tau", renType False x, False), (text "theta", renType False x, False)]
        [text "+", text "+", text "-"]
        (genSep "asimplCompEqn" x)
        (matchDoc (genSep "comp" x <+> text "sigma tau," <+> text "theta") [caseDoc (cTupled (map (genSep "sigma_tau") xs) <> text "," <+> cTupled (map (genSep "theta") xs)) (ands (map (\x -> parens (text "forall x," <+> genSep "sigma_tau" x <+> text "x =" <+> genSep "theta" x <+> text "x")) xs))])
  return (asimplInstClass <$$$> asimplSubstClass <$$$> asimplCompClass)

generateOpaqueDoc :: Doc -> Doc
generateOpaqueDoc d = text "Typeclasses Opaque" <+> d <> text "."
    
generateAutomation :: (MonadReader Signature m, MonadError String m) => TId -> m Doc
generateAutomation x = do
  xs <- substOf x
  cs <- constructors x
  b <- isOpen x
  asimplInstCongr' <- mapM (constructorRewDoc x) cs
  asimplSubstUp <- upRewDoc xs
  let asimplCast' y  = do
          ys <- substOf y
          return (instanceGen (genSep "AsimplCast" x <> toSep y)
                  (map (\z -> (genSep "sigma" z, text "index ->" <+> text z, False)) xs ++ [(text "tau", renType False y, False), (text "E", genSep "AsimplSubst" y <+> cTupled (map (genSep "sigma") (filter (\z -> elem z ys) xs)) <+> text "tau", False)]) 
                  (genSep "AsimplSubst" y <+> parens (toCastDoc False x y (cTupled (map (genSep "sigma") xs))) <+> text "tau")
                  (text "Proof. apply E. Qed.")
                 <$$> generateOpaqueDoc (genSep "cast" x <> sepsym <> text y)
                 )
  asimplCast <- (mapM asimplCast' (filter (\y -> x /= y) xs))
  let
    asimplToVar = instanceGen (genSep "AsimplToVar" x)
                  (map (\x -> (genSep "sigma" x, text "index ->" <+> text x, False)) xs)
                  (text "AsimplGen" <+> parens (genSep "toVar" x <+> cTupled (map (genSep "sigma") xs)) <+> genSep "sigma" x)
                  (text "Proof. intros x. reflexivity. Qed.")
    asimplRenTo = instanceGen (genSep "AsimplRenTo" x)
                  [(text "xi", text "index -> index", False)]
                  (text "AsimplGen" <+> parens (genSep "renTo" x <+> text "xi") <+> parens (text "xi >>>" <+> genSep "var" x))
                  (text "Proof. intros x. reflexivity. Qed.")
    -- Registering the type for Asimpl. 
    asimplGen = instanceGen (genSep "AsimplAsimplInst" x)
                [(text "s", text x, False), (text "t", text x, False),
                 (text "sigma", renType False x, False), (text "sigma'", renType False x, False),
                 (text "E_sigma", genSep "AsimplSubst" x <+> text "sigma sigma'", False),
                 (text "E", genSep "AsimplInst" x <+> text "s sigma' t", False)] 
                (text "Asimpl" <+> parens (genSep "subst" x <+> text "sigma s") <+> text "t") 
                (text "Proof. rewrite <- E. apply" <+> genSep "subst_eq" x <> text ". assumption. Qed.")
    -- Inst.            
    asimplInstRefl = instanceGen (genSep "AsimplInstRefl" x)
                     [(text "s", text x, False), (text "sigma", renType False x, False)]
                     (genSep "AsimplInst" x <+> text "s" <+> text "sigma" <+> parens (text "s." <> text "[" <+>text "sigma" <+> text "]") <+> text "|100")   -- INSERT PRIORITY 100
                     (text "Proof. reflexivity. Qed.")
    asimplInstVar = instanceGen (genSep "AsimplInstVar" x)
                    [(text "x", text "index", False), (text "y", text "index", False),
                      (text "sigma", renType False x, False),
                      (text "sigma'", text "index ->" <+> text x, False),
                      (text "s", text x, False),
                      (text "E", text "AsimplIndex x y", False),
                      (text "E'", text "AsimplGen" <+>  parens (genSep "toVar" x <+> text "sigma") <+> text "sigma'", False),
                      (text "E''", text "AsimplVarInst" <+> text "y" <+> text "sigma'" <+>text "s", False)] -- Args
                    (genSep "AsimplInst" x <+> parens (genSep "var" x <+> text "x") <+> text "sigma" <+> text "s")
                    (text "Proof. rewrite E. rewrite <- E''. apply E'.  Qed.")
    asimplInstCongr = vsep asimplInstCongr'
    asimplId = instanceGen (genSep "AsimplId" x)
                [(text "s", text x, False)]
                (genSep "AsimplInst" x <+> text "s" <+> cTupled (map (genSep "var") xs) <+> text "s") 
                (text "Proof. apply" <+> genSep "id" x <> text "; reflexivity. Qed.") 
    asimplInstInst = instanceGen (genSep "AsimplInstInst" x)
                      [(text "s", text x, False), (text "t", text x, False), (text "sigma", renType False x, False), (text "sigma'", renType False x, False), (text "tau", renType False x, False), (text "sigma_tau", renType False x, False), (text "E1", genSep "AsimplSubst" x <+> text "sigma sigma'", False), (text "E2", genSep "AsimplComp" x <+> text "sigma' tau sigma_tau", False), (text "E3", genSep "AsimplInst" x <+> text "s sigma_tau t", False)] -- ARGS
                      (genSep "AsimplInst" x <+> parens (genSep "subst" x <+> text "sigma" <+> text "s") <+> text "tau" <+> text "t")
                      (text "Admitted.")
     -- Subst.  - T
    asimplSubstRefl = instanceGen (genSep "AsimplSubstRefl" x)
                        [(text "sigma", renType False x, False)]
                        (genSep "AsimplSubst" x <+> text "sigma sigma | 100") 
                        (text "Admitted.") --  (text "Proof. destruct sigma; repeat split; intros x; reflexivity. Qed.")
    asimplSubstComp = instanceGen (genSep "AsimplSubstComp" x)
                       [(text "sigma", renType False x, False), (text "sigma'", renType False x, False), (text "tau", renType False x, False), (text "tau'", renType False x, False), (text "theta", renType False x, False), (text "E_sigma", genSep "AsimplSubst" x <+> text "sigma sigma'", False), (text "E_tau", genSep "AsimplSubst" x <+> text "tau tau'", False), (text "E", genSep "AsimplComp" x <+> text "sigma' tau' theta", False)] -- ARGS
                       (genSep "AsimplSubst" x <+> parens (genSep "comp" x <+> text "sigma tau") <+> text "theta"  <+> text "|90") -- STATEMENT
                       (text "Admitted.")
    asimplSubstCongr = instanceGen (genSep "AsimplSubstCongr" x)
                       (map (\x -> (genSep "sigma" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "tau" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "E" x, text "AsimplGen" <+> genSep "sigma" x <+> genSep "tau" x, False)) xs
                       ) --  ARGUMENTS
                       (genSep "AsimplSubst" x <+> cTupled (map (genSep "sigma") xs) <+>  cTupled (map (genSep "tau") xs) <+> text "|95") -- STATEMTN
                       (text "Proof. repeat split; assumption. Qed.")
     -- Component Composition  -
    asimplCompRefl = instanceGen (genSep "AsimplCompRefl" x)
                       [(text "sigma", renType False x, False), (text "tau", renType False x, False)]
                       (genSep "AsimplComp" x <+> text "sigma tau" <+> parens (genSep "comp" x <+> text "sigma tau") <+> text "| 100")  
                       (text "Admitted.") -- (text "Proof. destruct sigma; destruct tau; repeat split; intros x; reflexivity. Qed.")
    asimplCompCongr = instanceGen (genSep "AsimplCompCongr" x)
                       (map (\x -> (genSep "sigma" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "theta" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "tau" x, renType False x, False)) xs
                        ++ [(text "tau", renType False x, False)]
                        ++ map (\y -> (genSep "E" y, genSep "AsimplSubst" y <+>parens (toCastDoc False x y (text "tau")) <+> genSep "tau" y, False)) xs
                        ++ map (\y -> (genSep "E" y <> text "'", text "AsimplComp" <+> genSep "sigma" y <+> parens (genSep "subst" y <+> genSep "tau" y ) <+> genSep "theta" y, False)) xs)
                      (genSep "AsimplComp" x <+> cTupled (map (genSep "sigma") xs) <+> text "tau"  <+> cTupled (map (genSep "theta") xs))
                      (text "Admitted.")
    asimplCompCongr' = instanceGen (genSep "AsimplCompCongr'" x)
                       (map (\x -> (genSep "sigma" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "theta" x, text "index ->" <+> text x, False)) xs
                        ++ map (\x -> (genSep "tau" x, renType False x, False)) xs
                        ++ [(text "tau", renType False x, False)]
                        ++ map (\y -> (genSep "E" y, genSep "AsimplSubst" y <+>parens (toCastDoc False x y (text "tau")) <+> genSep "tau" y, False)) xs
                        ++ map (\y -> (genSep "E" y <> text "'", text "AsimplComp" <+> genSep "sigma" y <+> parens (genSep "subst" y <+> genSep "tau" y ) <+> genSep "theta" y, False)) xs)
                      (text "AsimplComp" <+> parens (genSep "subst" x <+> cTupled (map (genSep "sigma") xs)) <+> parens (genSep "subst" x <+> text "tau")  <+> parens (genSep "subst" x <+> cTupled (map (genSep "theta") xs)))
                      (text "Admitted.")
    asimplCompIdL = instanceGen (genSep "AsimplCompIdL" x)
                     [(text "sigma", renType False x, False), (text "tau", text "index ->" <+> text x, False),
                      (text "E", text "AsimplGen" <+> parens (genSep "toVar" x <+> text "sigma") <+> text "tau", False)]
                     (text "AsimplComp" <+> genSep "var" x <+> parens (genSep "subst" x <+> text "sigma") <+>text "tau")
                    (text "Admitted.")                                                                  
    asimplCompIdR = instanceGen (genSep "AsimplCompIdR" x)
                     [(text "sigma", text "index ->" <+> text x, False)]
                     (text "AsimplComp" <+> text "sigma" <+> parens (genSep "subst" x <+> cTupled (map (genSep "var") xs)) <+> text "sigma")
                    (text "Proof. intros x. apply" <+> genSep "id" x <> text "; reflexivity. Qed.")
    asimplCompAsso = instanceGen (genSep "AsimplCompAsso" x)
                      [(text "sigma", renType False x, False), (text "tau", renType False x, False), (text "theta", renType False x, False), (text "tau_theta", renType False x, False), (text "sigma_tau_theta", renType False x, False), (text "E", genSep "AsimplComp" x <+> text "tau theta tau_theta", False), (text "E'", genSep "AsimplComp" x <+> text "sigma tau_theta sigma_tau_theta", False)]
                      (genSep "AsimplComp" x <+> parens (genSep "comp" x <+> text "sigma tau") <+> text "theta sigma_tau_theta")
                     (text "Admitted.")
    asimplRefl = instanceGen (genSep "AsimplRefl" x)
               [(text "s", text x, False)]
               (text "Asimpl s s | 100")
               (text "Proof. reflexivity. Qed.")
    asimplGenComp = instanceGen (genSep "AsimplGenComp" x)
                  [(text "sigma", text "index ->" <+> text x , False), (text "sigma'", text "index ->" <+> text x , False), (text "tau", renType False x , False), (text "tau'", renType False x, False), (text "theta", text "index ->" <+> text x , False),
                   (text "E", text "AsimplGen sigma sigma'", False), (text "E'", genSep "AsimplSubst" x <+> text "tau tau'", False), (text "E''", text "AsimplComp sigma'" <+> parens (genSep "subst" x <+> text "tau'") <+> text "theta", False)
                  ]
                  (text "AsimplGen (sigma >>>" <+> parens (genSep "subst" x <+> text "tau") <+> text ") theta")
                  (text "Proof. intros x. rewrite <- E''. simpl. rewrite E. now apply" <+> genSep "subst_eq" x <+> text ". Qed.")
  upRewText <- upRewDoc [x]                  
  return (vsep asimplCast <$$$> boolDoc b asimplToVar <$$$>
          asimplGen <$$$> asimplInstRefl <$$$> boolDoc b asimplInstVar <$$$> asimplInstCongr <$$$> asimplId <$$$> asimplInstInst             
         <$$$> asimplSubstRefl <$$$> asimplSubstComp <$$$> asimplSubstCongr 
         <$$$> asimplCompRefl 
         <$$$> boolDoc b asimplCompIdL <$$$> asimplCompIdR <$$$> asimplCompAsso <$$$> asimplCompCongr <$$$> asimplCompCongr' <$$$> asimplRefl <$$$> asimplGenComp
         <$$$> upRewText
         <$$$> boolDoc b (generateOpaqueDoc (genSep "toVar" x))
         )
      


-- Embedding in the monadic structure

generateCoqId :: [TId] -> GenM ()
generateCoqId xs = do
  specDocText <- typeDoc xs
  substDocText <- substOfDoc xs
  xs <- filterM (\y -> do
                       ys <- substOf y
                       return (not (null ys))
                   ) xs
  varDocText <- toVarDoc True xs
  castrenDocText <- castDoc True xs
  upRenDocText <- upRenDoc xs
  renText <- renDoc True xs
  varSubstText <- toVarDoc False xs
  varEqText <- toVarEqDoc xs
  compRenText <- liftDoc (compDoc True) xs
  upDocText <- upDoc xs
  castDocText <- castDoc False xs
  castEqDocText <- castEqDoc xs
  substText <- renDoc False xs
  compositionText <- liftDoc (compDoc False) xs
  mixinText <- liftDoc (\x -> return (substMixinDoc x)) xs
  canText <- liftDoc (\x -> return (substTypeDoc x)) xs
  congrText <- liftDoc (\x -> do
                         cs <- constructors x
                         liftDoc (\x -> return (congrDoc x)) cs) xs
  upIdText <- upIdDoc xs
  idText <- idDoc xs
  toSubstText <- liftDoc toSubstDoc xs
  compText <- compTransRenRenDoc True True xs
  compEText <- liftDoc (compE True True) xs
  upRenSubstText <- upSubstDoc True False xs
  compText2 <- compTransDoc True False xs
  compEText2 <- liftDoc (compE True False) xs
  upSubstRenText <- upSubstDoc False True xs
  compText3 <- compTransDoc  False True xs
  compEText3 <- liftDoc (compE False True) xs
  upSubstSubstText <- upSubstDoc False False xs
  compText4 <- compTransDoc False False xs
  compEText4 <- liftDoc (compE False False) xs
  upExtText <- upExtDoc xs
  extText <- extDoc xs
  automation <- liftDoc generateAutomation xs
  automationClasses <- liftDoc generateAutomationClasses xs
  tell (specDocText <$$$> congrText <$$$> substDocText <$$$>  (if null xs then empty else varDocText <$$$> castrenDocText <$$$> upRenDocText <$$$> renText <$$$> varSubstText <$$$> varEqText <$$$> compRenText <$$$> upDocText <$$$> castDocText <$$$> castEqDocText <$$$> substText <$$$> compositionText <$$$> mixinText <$$$> canText <$$$> upIdText <$$$> idText <$$$> toSubstText <$$$> compText <$$$> compEText <$$$> upRenSubstText <$$$> compText2 <$$$> compEText2 <$$$> upSubstRenText <$$$> compText3 <$$$> compEText3 <$$$> upSubstSubstText <$$$> compText4 <$$$> compEText4 <$$$> upExtText <$$$> extText <$$$> automationClasses <$$$> automation <$$$> empty))


headerDoc :: (MonadReader Signature m, MonadError String m) => [[TId]] -> m Doc
headerDoc components = do
  openTypes <- filterM isOpen (L.concat components)
  substTypes <- mapM (\x -> do
                         xs <- substOf x
                         return ((text "subst_of" <+> genSep "subst_of" x) <+> text ":=" <+> cTupled (map (\x -> text "index ->" <+> text x) xs))
                     ) (L.concat components)
  let introText = text "This code was automatically generated by Autosubst 2.0 Beta."
      typesText =  text "The following inductive types were generated:"  <$$> vsep (map (\x -> text x <+> text ": Type") (L.concat components))
      varText = text "The following variable constructors were generated:" <$$> vsep (map (\x -> genSep "var" x <+> text ": Type") openTypes)
      substText = text "Autosubst 2 uses vectors of substitutions. The types of the generated substiutions are listed below:" <$$> vsep substTypes
      instText = text "Autosubst 2 furthermore generated the following instantiation operations:" <$$> vsep (map (\x -> genSep "subst" x <+> (text ": subst_of" <+> genSep "subst_of" x) <+> text "->" <+> text x  <+> text "->" <+> text x <> text "," <$$> text "also accessible as" <+> text "s.[sigma]") (L.concat components))
      dotText = text "See the generated dot-graph for further details."
      autoText = text "Automation has been extended to include the generated definitions. The tactic asimpl simplifies goals containing substiution expressions, autosubst corresponds to now asimpl."
      feedbackText = text "If Autosubst 2 does not behave as expected, we are grateful for a short mail to autosubst@ps.uni-saarland.de." <$$> text "Thank you!"
  return $ text "(*" <+> introText <$$$> typesText <$$$> varText <$$$> substText <$$$> instText <$$$> dotText <$$$> autoText <$$$> feedbackText <$$> text "*)"

generateCoq :: GenM ()
generateCoq = do
  spec <- components
  headerText <- headerDoc spec
  let header = headerText <$$$> text "Require Export Autosubst2." <$$>  text "Set Implicit Arguments." <$$> text "Require Import Lists.List." <$$> text "Import ListNotations." <$$> text "Set Typeclasses Filtered Unification."
  tell (header <$$$> empty)
  mapM generateCoqId spec
  return ()



(<$$$>) :: Doc -> Doc -> Doc
x <$$$> y = x <> linebreak <> linebreak <> y
