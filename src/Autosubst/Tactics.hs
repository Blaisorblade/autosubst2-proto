{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Tactics where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS       hiding ((<>))
import           Data.List               as L
import           Text.PrettyPrint.Leijen


import           Autosubst.Coq
import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Types



-- Handling of Vector Objects
toVar :: TId -> SubstTy -> GenM Term
toVar x ts = do
  xs <- substOf x
  return $ snd $ head $ filter (\(y, _) -> x == y) (zip xs (sty_terms ts))

castSubst :: TId -> TId -> SubstTy -> GenM SubstTy
castSubst x y (SubstScope xs) = fmap SubstScope (cast x y xs)
castSubst x y (SubstRen xs)   = fmap SubstRen (cast x y xs)
castSubst x y (SubstSubst xs) = fmap SubstSubst (cast x y xs)
castSubst x y (SubstEq xs f)  = liftM2 SubstEq (cast x y xs) (return f)
castSubst x y (SubstConst xs) = return $ SubstConst xs

up :: TId -> (TId -> TId -> a -> a) -> [a] -> TId -> GenM [a]
up x f n b = do
  xs <- substOf x
  return  $ map (\(p, n_i) -> f p b n_i)
            (zip xs n)

ups :: TId -> (TId -> TId -> a -> a) -> [a] -> [TId] -> GenM [a]
ups x f = foldM (up x f)

genType :: TId -> SubstTy -> Term
genType x xs = idApp x (sty_terms xs)

upRenT :: TId -> TId -> Term -> Term
upRenT y z xi = if y == z then TermApp up_ren_ [xi] else xi

upRen :: TId -> [TId] -> Terms -> GenM Terms
upRen x ys xs = ups x (\z y xi -> idApp (upRen_ y z) [xi]) xs ys

upScope :: TId -> [TId] -> Terms -> GenM Terms
upScope x ys xs = ups x (\z y n -> if z == y then succ_ n else n) xs ys

upSubstS :: TId -> [TId] -> Terms -> GenM Terms
upSubstS x ys xs = ups x (\z y xi -> idApp (up_ y z) [xi]) xs ys

up' :: TId -> (TId -> TId -> a -> GenM a) -> [a] -> TId -> GenM [a]
up' x f n b = do
  xs <- substOf x
  mapM (\(p, n_i) -> f p b n_i) (zip xs n)

upEq :: TId -> [TId] -> Terms -> (TId -> TId -> Term -> GenM Term)-> GenM Terms
upEq x ys xs f = foldM (up' x f) xs ys

upSubst :: TId -> [TId] -> SubstTy -> GenM SubstTy
upSubst x y (SubstScope xs) = fmap SubstScope (upScope x y xs)
upSubst x y (SubstRen xs)   = fmap SubstRen (upRen x y xs)
upSubst x y (SubstSubst xs) = fmap SubstSubst (upSubstS x y xs)
upSubst x y (SubstEq xs f)  = liftM2 SubstEq (upEq x y xs f) (return f)-- m
upSubst x y (SubstConst xs) = return $ SubstConst xs

cast :: TId -> TId -> [a] -> GenM [a]
cast x y xs = do
  arg_x <- substOf x
  arg_y <- substOf y
  return $ L.foldr (\(x, v) ws -> if x `elem` arg_y then v : ws else ws) [] (zip arg_x xs)

castUpSubst :: TId -> [Binder] -> TId -> SubstTy -> GenM SubstTy
castUpSubst x bs y arg = do
  arg' <- castSubst x y arg
  upSubst y bs arg'

-- Handling of [CBinder]
explicitS_ :: CBinder -> CBinder
explicitS_ (BinderImplicitName s)            = BinderName s
explicitS_ (BinderImplicitNameType s t)      = BinderNameType s t
explicitS_ (BinderImplicitScopeNameType s t) = BinderScopeNameType s t
explicitS_ s                                 = s

explicit_ :: [CBinder] -> [CBinder]
explicit_ = map explicitS_

-- Construction of objects
finT_ :: TId -> TmScope -> GenM Term
finT_ x n = fmap fin_ (toVar x (SubstScope n))

patternSId :: TId -> TId -> GenM [Term]
patternSId x y = do
  xs <- substOf x
  up x (\y z _ -> if y == z then shift_ else (id_ TermUnderscore)) (map TermId xs) y

var :: TId -> SubstTy -> Term
var x xs = idApp (var_ x) (sty_terms xs)

renT :: Term -> Term -> Term
renT m n = TermFunction (fin_ m) (fin_ n)

substT :: Term -> SubstTy -> TId -> Term
substT m n y = TermFunction (fin_ m) (sortType y n)

equiv_ :: Term -> Term -> Term
equiv_ s t =  TermForall [BinderName "x"] (TermEq (TermApp s [TermId "x"]) (TermApp t  [TermId "x"]))

-- TODO: Rename. introPatternScope?
getPattern :: String -> [Position] -> [String]
getPattern s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)


-- Generation of arguments
introScopeTy :: (MonadReader Signature m, MonadError String m) => TId -> Term -> m Term
introScopeTy x s = do
                  args <- substOf x
                  return $ L.foldl (\t _ -> TermFunction nat t) s args

-- FRESH: introScopeVar
introScopeVar :: String -> TId -> GenM (SubstTy, [CBinder])
introScopeVar s x = do
  args <- substOf x
  let scope = map (\x -> s ++ x) args
  return (SubstScope (map TermId scope), [BinderImplicitScopeNameType scope nat])

introRenScope :: (String, String) -> TId -> GenM ((SubstTy, SubstTy), [CBinder])
introRenScope (m, n) x = do
  (m, bm) <- introScopeVar m x
  (n, bn)<- introScopeVar n x
  return ((m, n), bm ++ bn)

introScopeVarS :: String -> GenM (Term, [CBinder])
introScopeVarS s = return (TermVar (TermId s), [BinderImplicitScopeNameType [s] nat])

introRenScopeS :: (String, String) -> GenM ((Term, Term), [CBinder])
introRenScopeS (m, n) = do
  (m, b_m) <- introScopeVarS m
  (n, b_n) <- introScopeVarS n
  return ((m, n), b_m ++ b_n)

--- Generation of names for renamings.
genRenS :: String -> (Term, Term) -> GenM (Term, [CBinder])
genRenS s (m,n) = do
  s <- tfresh s
  return $ (TermId s, [BinderNameType [s] (renT m n)])

-- Generation of names for renamings.
genRen :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genRen x xi (m,n) = do
  xs <- substOf x
  let xis = map (\x -> xi ++ x) xs
  let tys = map (\(m, n) -> TermFunction (fin_ m) (fin_ n)) (zip (sty_terms m) (sty_terms n))   -- map (\(x, (m, n)) -> SingleRen (xi ++ x) m n) (zip xs (zip (sty_terms m) (sty_terms n)))
  return $ (SubstRen (map TermId xis), map (\(x,t) -> BinderNameType [x] t) (zip xis tys))

genSubst :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genSubst x sigma (m,n) = do
  xs <- substOf x
  let sigmas = map (\x -> sigma ++ x) xs
  tys <- mapM (\(y, m) -> do
      n' <- castSubst x y n
      return $ TermFunction (fin_ m) (sortType y n')) (zip xs (sty_terms m))
  return $ (SubstSubst (map TermId sigmas), map (\(x,t) -> BinderNameType [x] t) (zip sigmas tys))

introSubstScopeS :: (String, String) -> TId -> GenM ((Term, SubstTy), [CBinder])
introSubstScopeS (m,n) y = do
  (m, bm) <- introScopeVarS m
  (n, bn) <- introScopeVar n y
  return ((m, n), bm ++ bn)

genSubstS :: String -> (Term, SubstTy) -> TId -> GenM (Term, [CBinder])
genSubstS s (m, n) z = do
  s <- tfresh s
  return (TermId s, [BinderNameType [s] (substT m n z)])

genEq :: TId -> String -> Term -> Term -> GenM (Term, [CBinder])
genEq x s sigma tau = do
  s <- tfresh s
  return $ (TermId s, [BinderNameType [s] (equiv_ sigma tau)])

genEqs :: TId -> String -> Terms -> Terms -> (TId -> TId -> Term -> GenM Term) -> GenM (SubstTy, [CBinder])
genEqs x e sigma tau f = do
  xs <- substOf x
  let eq_names = map (\x -> e ++ x) xs
  let eqs =  map (\(sigma, tau) -> (equiv_ sigma tau)) (zip sigma tau)
  return $ (SubstEq (map TermId eq_names) f, map (\(s, t) -> BinderNameType [s] t) (zip eq_names eqs))
