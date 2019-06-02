{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Automation (genAutomation) where

import           Autosubst.Coq
import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import           Data.List                as L


{- Generates the most basic automation for Autosusbt 2:
Assumes
- A list of sorts which contain variables (varSorts)
- A list of all sorts (xs)
- A list of all sorts which have substitution on them (substSorts)
- A list of up pairs. (upList)
-}
genAutomation :: [TId] -> [TId] -> [TId] ->[(TId,TId)] -> GenM [Sentence]
genAutomation varSorts xs substSorts upList =
  let substFunctions = map subst_ substSorts ++ map ren_ substSorts
      upFunctions = ["up_ren"] ++ map (\(x,y) -> upRen_ x y) upList ++ map (\(x,y) -> up_ x y) upList
      monadLemmas = concatMap (\x -> ["instId_" ++ x, "rinstId_" ++ x, "compComp_" ++ x, "compComp'_" ++ x, "compRen_" ++x, "compRen'_" ++ x,
                      "renComp_" ++ x, "renComp'_" ++ x, "renRen_" ++ x, "renRen'_" ++ x]) substSorts
      varLemmas = concatMap (\x -> ["varL_" ++ x, "varLRen_" ++ x]) varSorts
      starify = map (\x -> x ++ " in *")
      unfoldLemmas = ["subst1", "ren1", "subst2", "ren2", "Subst1", "Ren1", "Subst2", "Ren2", "ids"] ++ map substtc_ substSorts ++ map rentc_ substSorts ++ map vartc_ varSorts
      foldLemmas = map vartc_ varSorts ++ map (\x -> "(@ids _ " ++ vartc_ x ++ ")") varSorts
                  -- ++ map substtc_ substSorts ++ map (\x -> "(@subst1 _ _ " ++ substtc_ x ++ ")") substSorts
                  -- ++ map rentc_ substSorts  ++ map (\x -> "(@ren1 _ " ++ rentc_ x ++ ")") substSorts
      unfold = SentenceTactic "auto_unfold"  (TacticRepeat $ TacticUnfold unfoldLemmas Nothing)
--      fold =  SentenceTactic "auto_fold"  (TacticFold foldLemmas Nothing)
      unfold_star = SentenceTacticNotation ["\"auto_unfold\"", "\"in\"", "\"*\""] (TacticRepeat $ TacticUnfold unfoldLemmas (Just "in *"))
--      fold_star = SentenceTacticNotation ["\"auto_fold\"", "\"in\"", "\"*\""] (TacticFold foldLemmas (Just "in *"))
      asimpl' = SentenceTactic "asimpl'" (TacticRewrite Nothing substFunctions upFunctions (monadLemmas ++ varLemmas))
      autocase = SentenceTacticNotation ["\"auto_case\""] (TacticId "auto_case (asimpl; cbn; eauto)")
  in do implicits <- genScopeImplicits
        instances <- genInstances substSorts varSorts
        notation <- genNotation varSorts substSorts upList
        return $ implicits  ++ instances ++ notation ++ [unfold, unfold_star, asimpl', SentenceTactic "asimpl" (TacticSeq [TacticRepeat (TacticId "try unfold_funcomp"), TacticId "auto_unfold in *", TacticId "asimpl'", TacticRepeat (TacticId "try unfold_funcomp")])
              , SentenceId "Tactic Notation \"asimpl\" \"in\" hyp(J) := revert J; asimpl; intros J."
              , autocase
              , SentenceTacticNotation ["\"asimpl\"", "\"in\"", "\"*\""] (TacticSeq [TacticId "auto_unfold in *", TacticRewrite (Just "in *") substFunctions upFunctions (monadLemmas ++ varLemmas)])
              ] ++ genSubstifyTactics substSorts

genSubstifyTactics :: [TId] ->  [Sentence]
genSubstifyTactics xs = [substify, renamify]
  where substify = SentenceTactic "substify" (TacticSeq $ [TacticId "auto_unfold"] ++  map (\x -> TacticId ("try repeat (erewrite " ++ rinstInst_ x ++ "; [|now intros])")) xs )
        renamify = SentenceTactic "renamify" (TacticSeq $ [TacticId "auto_unfold"] ++  map (\x -> TacticId ("try repeat (erewrite <- " ++ rinstInst_ x ++ "; [|intros; now asimpl])")) xs )

genScopeImplicits :: GenM [Sentence]
genScopeImplicits = do
  sorts <- components
  fmap concat $ mapM (\x -> do
              b <- isOpen x
              nec <- fmap (not . null) (substOf x)
              cs' <- constructors x
              (n, _) <- introScopeVar "n" x
              return $ if nec then (map (\(Constructor c _) -> SentenceCommand $ Arguments c (sty_terms n))
                ([Constructor (var_ x) [] | b] ++ cs')) else [])
              (concat sorts)

genNotation :: [TId] -> [TId] -> [(TId, TId)]-> GenM [Sentence]
genNotation varsorts substSorts upList = do
  upNotation <- mapM genUpNotationPrint upList
  substNotation <- mapM genSubstNotation substSorts
  return $ concat (map genNotationClass varsorts) ++ concat upNotation ++ concat substNotation

genSubstNotation :: TId -> GenM [Sentence]
genSubstNotation x = do
  xs <- substOf x
  let subst_full = SentenceNotation ("s [ " ++ stringApp (map (\y -> "sigma" ++ y) xs) " ; " ++ " ]") (idApp (subst_ x)
            ((map (\y -> TermId ("sigma" ++ y)) xs) ++ [TermId "s"])) ("at level 7, left associativity, only printing") "subst_scope"
      ren_full = SentenceNotation ("s ⟨ " ++ stringApp (map (\y -> "xi" ++ y) xs) " ; " ++ " ⟩") (idApp (ren_ x)
                ((map (\y -> TermId ("xi" ++ y)) xs) ++ [TermId "s"])) ("at level 7, left associativity, only printing") "subst_scope"
      subst_comp = SentenceNotation ("[ " ++ stringApp (map (\y -> "sigma" ++ y) xs) " ; " ++ " ]") (idApp (subst_ x)
                ((map (\y -> TermId ("sigma" ++ y)) xs) )) ("at level 1, left associativity, only printing") "fscope"
      ren_comp = SentenceNotation ("⟨ " ++ stringApp (map (\y -> "xi" ++ y) xs) " ; " ++ " ⟩") (idApp (ren_ x)
                ((map (\y -> TermId ("xi" ++ y)) xs) )) ("at level 1, left associativity, only printing") "fscope"
  return [subst_full, ren_full, subst_comp, ren_comp]

stringApp :: [String] -> String -> String
stringApp [] z     = ""
stringApp [x] z    = x
stringApp (x:xs) z = x ++ z ++ stringApp xs z

genInstances :: [TId] -> [TId] -> GenM [Sentence]
genInstances substSorts varSorts = do
  substInstances <- mapM genSubstInstance substSorts
  renInstances <- mapM genRenInstance substSorts
  varInstances <- mapM genVarInstance varSorts
  return $ substInstances ++ renInstances ++ concat varInstances

genSubstInstance :: TId -> GenM Sentence
genSubstInstance x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, b)<- genSubst x "" (m,n)
  let bs = getTypes b
  xs <- substOf x
  return $ SentenceInstance bmn (substtc_ x)  (idApp ("Subst" ++ show (length xs)) (bs ++ [genType x m, genType x n])) (idApp ("@" ++ subst_ x) (sty_terms m ++ sty_terms n))

genRenInstance :: TId -> GenM Sentence
genRenInstance x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, b)<- genRen x "" (m,n)
  let bs = getTypes b
  xs <- substOf x
  return $ SentenceInstance bmn (rentc_ x)  (idApp ("Ren" ++ show (length xs)) (bs ++ [genType x m, genType x n])) (idApp ("@" ++ ren_ x) (sty_terms m ++ sty_terms n))


genVarInstance :: TId -> GenM [Sentence]
genVarInstance x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  mx <- toVar x m
  let varI = SentenceInstance bm (vartc_ x) (idApp "Var" [fin_ mx, genType x m]) (idApp ("@" ++ var_ x) (sty_terms m))
      varIPrint = SentenceNotation ("x '__" ++ x ++ "'") (idApp "@ids" [TermUnderscore, TermUnderscore, TermId (vartc_ x), TermId "x"]) ("at level 5, only printing, format \"" ++ "x __" ++ x ++ "\"")  "subst_scope"
      varPrint = SentenceNotation ("x '__" ++ x ++ "'") (idApp (var_ x) [TermId "x"]) ("at level 5, format \"" ++ "x __" ++ x ++ "\"")  "subst_scope"
      idPrint = SentenceNotation "'var'" (TermId (var_ x)) "only printing, at level 1" "subst_scope"
  return $ [varI, varPrint, varIPrint, idPrint]

genNotationClass :: TId ->  [Sentence]
genNotationClass x =
  let cl = [SentenceClass ("Up_" ++ x) [BinderName "X", BinderName "Y"] [("up_" ++ x, TermFunction (TermId "X") (TermId "Y"))]]
      notation = [SentenceNotation ("↑__" ++ x) (TermId ("up_" ++ x) ) ("only printing") "subst_scope"]
      in (cl ++ notation)

genUpNotationPrint :: (TId, TId) -> GenM [Sentence]
genUpNotationPrint (x,y) = do
    ((m,n), bs) <- introSubstScopeS ("m", "n") y
    n' <- upSubst x [y] n
    let m' = if (x == y) then succ_ m else m
        up_not_print = SentenceNotation ("↑__" ++ x) (TermId ( up_ x y) ) ("only printing") "subst_scope"
        up_instance = SentenceInstance bs ("Up" ++ "_" ++ x ++ "_" ++ y) (idApp ("Up_" ++ y) [TermUnderscore, TermUnderscore]) (idApp ("@" ++ up_ x y) ([m] ++ sty_terms n))
    return $ [up_not_print, up_instance]
