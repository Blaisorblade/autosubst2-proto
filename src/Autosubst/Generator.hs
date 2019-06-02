{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Autosubst.Generator (genCodeT) where

import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import           Data.List                as L

-- map names
funname_ :: TId -> String
funname_ f = f

map_ :: FId -> [Term] -> Term
map_ f ts = idApp (f ++ "_map") ts

mapId_ :: FId -> [Term] -> Term
mapId_ f ts = idApp (f ++ "_id") ts

mapComp_ :: FId -> [Term] -> Term
mapComp_ f ts = idApp (f ++ "_comp") ts

mapExt_ :: FId -> [Term] -> Term
mapExt_ f ts = idApp (f ++ "_ext") ts

-- Generation of syntax from a signature
genVar :: TId -> SubstTy -> GenM [InductiveCtor]
genVar x n = do
  open_x <- isOpen x
  s <- finT_ x (sty_terms n)
  let t = [s] ==> sortType x n
  return [InductiveCtor (var_ x) (Just t) | open_x]

genArg :: TId -> SubstTy -> [Binder] -> Argument  -> GenM Term
genArg x n bs (Atom y)  = liftM2 idApp (return y) (fmap sty_terms $ castUpSubst x bs y n)
genArg x n bs (FunApp f xs) = do
  xs' <- mapM (genArg x n bs) xs
  return $ idApp (funname_ f) xs'

genCons :: TId -> SubstTy -> Constructor -> GenM InductiveCtor
genCons x n (Constructor cname pos) = do
  t <- do
    up_n_x <- mapM (\(Position bs y) -> genArg x n bs y) pos
    return $  up_n_x ==> sortType x n
  return $ InductiveCtor (constructor_ cname) (Just t)

genBody :: TId -> GenM InductiveBody
genBody x = do
  cs <- constructors x
  (n,b) <- introScopeVar "n" x
  varCons <- genVar x n
  constructors <- mapM (genCons x n) cs
  return $ InductiveBody x (explicit_ b) (TermSort Type) (varCons ++ constructors)

genCongruence :: TId -> Constructor -> GenM Definition
genCongruence x (Constructor cname pos) = do
    (m, bm) <- introScopeVar "m" x
    let s = getPattern "s" pos
    let t = getPattern "t" pos
    let bs s = mapM (\(s, Position binders arg) -> do
                                                  arg_type <-  genArg x m binders arg -- castUpSubst x bs arg m
                                                  return $ BinderImplicitNameType [s] arg_type
                                                    ) (zip s pos) -- index, pattern, binders.
    bes <- bs s
    bt <- bs t
    let eqs = zipWith TermEq (map TermId s) (map TermId t)
    let eq = TermEq (idApp cname (sty_terms m ++ map TermId s)) (idApp cname (sty_terms m ++ map TermId t))
    let beqs = map (\(n,s) -> BinderNameType ["H" ++ show n] s) (zip [1..] eqs)
    let eq' n = idApp cname (sty_terms m ++ map (\m -> if (m == n) then TermId "x" else TermUnderscore) [1..(length eqs)])
    let p = repRew (map (\n -> (TermId ("H" ++ show n), (TermAbs [BinderName "x"] (eq' n)))) [1..(length eqs)])
    return $ Definition (congr_ cname) (bm ++ bes ++ bt ++ beqs) (Just eq) p

genCongruences :: TId -> GenM [Definition]
genCongruences x = join $ fmap (mapM (genCongruence x)) (constructors x)

genUpRenS :: TId -> TId -> GenM Definition
genUpRenS y z = do
  (mn, bs) <- introRenScopeS ("m", "n")
  (xi, bxi) <- genRenS "xi" mn
  return $ Definition (upRen_ y z) (bs ++ bxi) Nothing (upRenT y z xi)

traversal :: TId -> SubstTy -> (TId -> String) -> (Term -> Term) ->  (Term -> Term) -> [CBinder] -> [SubstTy] -> (Term -> Term)  -> (TId -> [Term] -> Term) -> (FId -> [Term] -> Term) -> GenM FixpointBody
traversal x scope name no_args ret bargs args var_case sem funsem = do
  let s = "s"
  cs <- constructors x
  open_x <- isOpen x
  let underscore_pattern = TermSubst (SubstScope (map (const TermUnderscore) (sty_terms scope)))
  let var_pattern = [Equation (PatCtor (idApp (var_ x) [underscore_pattern]) [s]) (var_case (TermId s)) | open_x]
  -- computes the result for a constructor.
  let cons_pattern (Constructor cname pos) =  let s = getPattern "s" pos in
                                              let arg_map (bs:: [Binder]) arg = (case arg of
                                                                      Atom y -> (do
                                                                                                b <- hasArgs y
                                                                                                arg <- mapM (castUpSubst x bs y) args
                                                                                                return $ if b then idApp (name y) (map TermSubst arg) else (TermAbs [BinderName "x"] (no_args (TermId "x"))))
                                                                      FunApp f xs -> (do
                                                                                                  res <- mapM (arg_map bs) xs
                                                                                                  return $ funsem f res)) in do
                                              positions <- mapM (\(s, Position bs arg) -> liftM2 TermApp (arg_map bs arg) (return [TermId s])) (zip s pos)
                                              return $ Equation (PatCtor (idApp cname [underscore_pattern]) s) (sem cname positions)
  cons_pat <- mapM cons_pattern cs
  let t = TermMatch (MatchItem (TermId s) Nothing) (Just $ Todo "MBTerm") (var_pattern ++ cons_pat)
  return $ FixpointBody (name x) (bargs ++ [BinderNameType [s] (idApp x (sty_terms scope))]) (ret (TermId s)) t -- Command for BinderNameType


genRenaming :: TId -> GenM FixpointBody
genRenaming x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  toVarT <- toVar x xi
  traversal x m ren_ id (const TermUnderscore) (bs ++ bxi) [xi]
                       (\s -> TermApp (var x n) [TermApp toVarT [s]])
                       (\x s -> idApp x (sty_terms n ++ s)) map_

genRenamings :: [TId] -> GenM Fixpoint
genRenamings xs = do
  fs <- mapM genRenaming xs
  r <- recursive xs
  return $ Fixpoint r fs

upSubstT :: TId -> TId -> SubstTy -> Term -> GenM Term
upSubstT y z m sigma = do
    pat <- patternSId z y
    m <- upSubst y [z] m
    let sigma' = sigma >>> idApp (ren_ z) pat
    return $ if y == z then TermApp cons_ [TermApp (var y m) [varZero_], sigma'] else sigma'

genUpS :: TId -> TId -> GenM Definition
genUpS y z = do
  ((m,n), bs) <- introSubstScopeS ("m", "n") z
  (sigma, b_sigma) <- genSubstS "sigma" (m,n) z
  sigma <- upSubstT y z n sigma
  return $ Definition (up_ y z) (bs ++ b_sigma) Nothing sigma

genSubstitution :: TId -> GenM FixpointBody
genSubstitution x = do
  ((m, n), bmn) <- introRenScope ("m", "n") x
  (sigma, bs) <- genSubst x "sigma" (m,n)
  toVarT <- toVar x sigma
  traversal x m subst_ id (const TermUnderscore) (bmn ++ bs) [sigma]
                       (\s -> TermApp toVarT [s])
                       (\x s -> idApp x (sty_terms n ++ s)) map_

genSubstitutions :: [TId] -> GenM Fixpoint
genSubstitutions xs = do
  fs <- mapM genSubstitution xs
  r <- recursive [L.head xs]
  return $ Fixpoint r fs

genUpId :: TId -> TId -> GenM Definition
genUpId y z = do
  (m, bm) <- introScopeVar "m" z
  m_var <- toVar z m
  (sigma, b_sigma) <- genSubstS "sigma" (m_var, m) z
  (eq, b_eq) <- genEq z "Eq" sigma (var z m)
  n <- tfresh "n"
  m <- upSubst z [y] m
  let ret = equiv_ (idApp (up_ y z) [sigma]) (var z m)
  shift <- patternSId z y
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  let u = if y == z then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
  return $ Definition (upId_ y z) (bm ++ b_sigma ++ b_eq) (Just ret) (TermAbs [BinderName "n"] u)


genIdL :: TId -> GenM FixpointBody
genIdL x = do
  (m, bm) <- introScopeVar "m" x
  (sigma, bs) <- genSubst x "sigma" (m, m)
  xs <- substOf x
  eqs' <- mapM (\y -> liftM2 idApp (return $ var_ y) (fmap sty_terms (castSubst x y m))) xs
  (eqs, beqs) <- genEqs x "Eq" (sty_terms sigma) eqs' (\x y s -> return $ idApp (upId_ y x) [TermUnderscore, s]) -- TODO: Generate ID in a sensible way.
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (subst_ x) (sty_terms sigma ++ [s])) s
  traversal x m idSubst_ (\s -> TermApp eq_refl_ [s]) ret (bm ++ bs ++ beqs) [sigma, eqs]
                       (\s -> TermApp toVarT [s])
                       (idApp . congr_) mapId_

genCompRenRen :: TId -> GenM FixpointBody
genCompRenRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  (rho, brho) <- genRen x "rho" (m, l)
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (sty_terms xi) (sty_terms zeta)) (sty_terms rho) (\x y s -> return$ if x == y then idApp up_ren_ren_ [TermUnderscore, TermUnderscore, TermUnderscore, s] else s)
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (ren_ x) (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [s]])) (idApp (ren_ x) (sty_terms rho ++ [s]))
  traversal x m compRenRen_ (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> ap_ [var x l, TermApp toVarT [n]])
                  (idApp . congr_) mapComp_

genLemmaRenRenComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaRenRenComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  let sigmazeta = zipWith (>>>) (sty_terms xi) (sty_terms zeta)
  let s = "s"
  let ret = TermEq (idApp (ren_ x) (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [TermId s]])) (idApp (ren_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenRen_ x) (sty_terms xi ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (sty_terms xi)) >>> (idApp (ren_ x) (sty_terms zeta))) (idApp (ren_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("renRen_" ++ x) (sty_terms xi ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("renRen_" ++ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("renRen'_" ++ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))



genUpRenSubst :: TId -> TId -> GenM Definition
genUpRenSubst y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVarS "l"
  (m, bm) <- introScopeVar "m" z
  (xi, bxi) <- genRenS "xi" (k, l)
  (tau, btau) <- genSubstS "tau" (l, m) z
  (theta, btheta) <- genSubstS "theta" (k, m) z
  m_var <- toVar z m
  (eq, b_eq) <- genEq z "Eq" (xi >>> tau) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  let ret = equiv_ (idApp (upRen_ y z) [xi] >>> idApp (up_ y z) [tau] ) (idApp (up_ y z) [theta])
  shift <- patternSId z y
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  let u = if y == z then matchFin_ (TermId n) t eq_refl_  else t (TermId n) -- TODO: Generalize the matchFIn thing.
  return $ Definition (up_ren_subst_ y z) (bk ++ bl ++ bm ++ bxi ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genCompRenSubst :: TId -> GenM FixpointBody
genCompRenSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  (rho, brho) <- genSubst x "theta" (m, l)
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (sty_terms xi) (sty_terms zeta)) (sty_terms rho) (\x y s -> return $ idApp (up_ren_subst_ y x) [TermUnderscore, TermUnderscore, TermUnderscore, s])
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (subst_ x) (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [s]])) (idApp (subst_ x) (sty_terms rho ++ [s]))
  traversal x m compRenSubst_ (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> TermApp toVarT [n])
                  (idApp . congr_) mapComp_

genLemmaSubstRenComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstRenComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  xs <- substOf x
  let sigmazeta = zipWith (>>>) (sty_terms xi) (sty_terms zeta)
  let s = "s"
  let ret = TermEq (idApp (subst_ x) (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenSubst_ x) (sty_terms xi ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (sty_terms xi)) >>> (idApp (subst_ x) (sty_terms zeta))) (idApp (subst_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("renComp_" ++ x) (sty_terms xi ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("renComp_" ++ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("renComp'_" ++ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))



genUpSubstRen :: TId -> TId -> GenM Definition
genUpSubstRen y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (zeta, bzeta) <- genRen z "zeta" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (ren_ z) (sty_terms zeta)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  zeta' <- upSubst z [y] zeta
  pat <- patternSId z y
  let ret = equiv_ (idApp (up_ y z) [sigma] >>> idApp (ren_ z) (sty_terms zeta')) (idApp (up_ y z) [theta])
  shift <- patternSId z y
  let t n = eqTrans_ (idApp (compRenRen_ z) (pat ++ sty_terms zeta' ++ zipWith (>>>) (sty_terms zeta) pat ++ map (const (TermAbs [BinderName "x"] eq_refl_)) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ z) (sty_terms zeta ++ pat ++ zipWith (>>>) (sty_terms zeta) pat ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [idApp (ren_ z) pat, TermApp eq [n]]))
  let u = if y == z then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
  return $ Definition (up_subst_ren_ y z) (bk ++ bl ++ bm ++ bsigma ++ bzeta ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genCompSubstRen :: TId -> GenM FixpointBody
genCompSubstRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  (theta, btheta) <- genSubst x "theta" (m, l)
  xs <- substOf x
  sigmazeta <- mapM (\(y, sigma) -> do
                zeta' <- castSubst x y zeta
                return $ sigma >>> idApp (ren_ y) (sty_terms zeta')) (zip xs  (sty_terms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmazeta (sty_terms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  zeta' <- castSubst x z zeta
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_ren_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (sty_terms zeta') ++ [TermUnderscore, s])) -- ([sigma'] ++ sty_terms zeta' ++[theta', s]))
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (ren_ x) (sty_terms zeta ++ [idApp (subst_ x) $ sty_terms sigma  ++ [s]])) (idApp (subst_ x) (sty_terms theta ++ [s]))
  traversal x m compSubstRen_ (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ bzeta ++ btheta ++ beqs) [sigma, zeta, theta, eqs]
                  (\n -> TermApp toVarT [n])
                  (idApp . congr_) mapComp_


genLemmaSubstCompRen :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstCompRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  let s = "s"
  sigmazeta <- mapM (\(y, sigma) -> do
                zeta' <- castSubst x y zeta
                return $ sigma >>> idApp (ren_ y) (sty_terms zeta')) (zip xs  (sty_terms sigma))
  let ret = TermEq (idApp (ren_ x) (sty_terms zeta ++ [idApp (subst_ x) $ sty_terms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compSubstRen_ x) (sty_terms sigma ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (sty_terms sigma)) >>> (idApp (ren_ x) (sty_terms zeta))) (idApp (subst_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compRen_" ++ x) (sty_terms sigma ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("compRen_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("compRen'_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta) ret' (ProofExact proof'))



genUpSubstSubst :: TId -> TId -> GenM Definition
genUpSubstSubst y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (tau, btau) <- genSubst z "tau" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (subst_ z) (sty_terms tau)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  zeta' <- upSubst z [y] tau
  pat <- patternSId z y
  let ret = equiv_ (idApp (up_ y z) [sigma] >>> idApp (subst_ z) (sty_terms zeta')) (idApp (up_ y z) [theta])
  shift <- patternSId z y
  zs <- substOf z
  pat' <- mapM (\(tau, z') -> do
                      p' <- castSubst z z' (SubstSubst pat)
                      return $ tau >>> (idApp (ren_ z') (sty_terms p')) ) (zip (sty_terms tau) zs)
  let t n = (eqTrans_ (idApp (compRenSubst_ z) (pat ++ sty_terms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (sty_terms zeta') pat)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstRen_ z) (sty_terms tau ++ pat ++ pat' ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (ren_ z) pat), TermApp eq [n]])))
  let u = if y == z then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
  return $ Definition (up_subst_subst_ y z) (bk ++ bl ++ bm ++ bsigma ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genCompSubstSubst :: TId -> GenM FixpointBody
genCompSubstSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (tau,btau) <- genSubst x "tau" (k,l)
  (theta, btheta) <- genSubst x "theta" (m, l)
  xs <- substOf x
  sigmatau <- mapM (\(y, sigma) -> do
                tau' <- castSubst x y tau
                return $ sigma >>> idApp (subst_ y) (sty_terms tau')) (zip xs  (sty_terms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmatau (sty_terms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  tau' <- castSubst x z tau
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_subst_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (sty_terms tau') ++ [TermUnderscore, s]))  -- ([sigma'] ++ sty_terms tau' ++[theta', s]))
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (subst_ x) (sty_terms tau ++ [idApp (subst_ x) $ sty_terms sigma  ++ [s]])) (idApp (subst_ x) (sty_terms theta ++ [s]))
  traversal x m compSubstSubst_ (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ btau ++ btheta ++ beqs) [sigma, tau, theta, eqs]
                  (\n -> TermApp toVarT [n])
                  (idApp . congr_) mapComp_

genLemmaSubstComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (tau,btau) <- genSubst x "tau" (k,l)
  xs <- substOf x
  let s = "s"
  sigmatau <- mapM (\(y, sigma) -> do
                tau' <- castSubst x y tau
                return $ sigma >>> idApp (subst_ y) (sty_terms tau')) (zip xs  (sty_terms sigma))
  let ret = TermEq (idApp (subst_ x) (sty_terms tau ++ [idApp (subst_ x) $ sty_terms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmatau ++ [TermId s]))
  let proof = idApp (compSubstSubst_ x) (sty_terms sigma ++ sty_terms tau ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (sty_terms sigma)) >>> (idApp (subst_ x) (sty_terms tau))) (idApp (subst_ x) sigmatau) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compComp_" ++ x) (sty_terms sigma ++ sty_terms tau ++ [TermId "n"]))]
  return (Lemma ("compComp_" ++ x) (bkl ++ bm ++ bsigma ++ btau ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("compComp'_" ++ x) (bkl ++ bm ++ bsigma ++ btau) ret' (ProofExact proof'))


genUpExtRen :: TId -> TId -> GenM Definition
genUpExtRen y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVarS "n"
  (xi, bxi) <- genRenS "xi" (m, n)
  (zeta,bzeta) <- genRenS "zeta" (m,n)
  (eq, b_eq) <- genEq z "Eq" xi zeta
  let ret = equiv_ (idApp (upRen_ y z) [xi]) (idApp (upRen_ y z) [zeta])
  n <- tfresh "n"
  let t n = TermApp eq [n]
  let s = matchFin_ (TermId n) (\n -> ap_ [shift_, t n]) eq_refl_
  let u = if y == z then s else t (TermId n)
  return $ Definition (upExtRen_ y z) (bm ++ bn ++ bxi ++ bzeta ++ b_eq) (Just ret) (TermAbs [BinderName "n"] u)

genExtRen :: TId -> GenM FixpointBody
genExtRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  (zeta, bzeta) <- genRen x "zeta" (m,n)
  xs <- substOf x
  (eqs, beqs) <- genEqs x "Eq" (sty_terms xi) (sty_terms zeta) (\x y s -> return $ idApp (upExtRen_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Shouldn't this want SubsttTy instead of Terms?
  let ret s = TermEq (idApp (ren_ x) (sty_terms xi ++ [s])) (idApp (ren_ x) (sty_terms zeta ++ [s]))
  toVarT <- toVar x eqs
  traversal x m extRen_ (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bzeta ++ beqs) [xi, zeta, eqs]
                  (\z -> ap_ [var x n, TermApp toVarT [z]])
                  (idApp . congr_) mapExt_

genUpExt :: TId -> TId -> GenM Definition
genUpExt y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (tau,btau) <- genSubstS "tau" (m,n) z
  (eq, b_eq) <- genEq z "Eq" sigma tau
  let ret = equiv_ (idApp (up_ y z) [sigma]) (idApp (up_ y z) [tau])
  shift <- patternSId z y
  n <- tfresh "n"
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  let u = if y == z then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
  return $ Definition (upExt_ y z) (bm ++ bn ++ bsigma ++ btau ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genExt :: TId -> GenM FixpointBody
genExt x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, bsigma) <- genSubst x "sigma" (m,n)
  (tau, btau) <- genSubst x "tau" (m,n)
  xs <- substOf x
  (eqs, beqs) <- genEqs x "Eq" (sty_terms sigma) (sty_terms tau) (\x y s -> return$  idApp (upExt_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Shouldn't this want SubsttTy instead of Terms?
  let ret s = TermEq (idApp (subst_ x) (sty_terms sigma ++ [s])) (idApp (subst_ x) (sty_terms tau ++ [s]))
  toVarT <- toVar x eqs
  traversal x m ext_ (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bsigma ++ btau ++ beqs) [sigma, tau, eqs]
                  (\z ->  TermApp toVarT [z])   -- TODO: I didn't need the renaming case for Up. Dive into that.
                  (idApp . congr_) mapExt_

genUpRinstInst :: TId -> TId -> GenM Definition
genUpRinstInst y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  n_var <- toVar z n
  (xi, bxi) <- genRenS "xi" (m, n_var)
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (eq, b_eq) <- genEq z "Eq" (xi >>> var z n) sigma
  n' <- upSubst z [y] n
  let ret = equiv_ (idApp (upRen_ y z) [xi] >>> var z n') (idApp (up_ y z) [sigma])
  shift <- patternSId z y
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  n <- tfresh "n"
  let u = if y == z then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
  return $ Definition (up_rinstInst_ y z) (bm ++ bn ++ bxi ++ bsigma ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genRinstInst :: TId -> GenM FixpointBody
genRinstInst x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  (sigma, bsigma) <- genSubst x "sigma" (m,n)
  xs <- substOf x
  xis' <- mapM (\(y, xi) -> do
    n' <- castSubst x y n
    return$  xi >>> var y n') (zip xs (sty_terms xi))
  (eqs, beqs) <- genEqs x "Eq" xis' (sty_terms sigma) (\x y s -> return $  idApp (up_rinstInst_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Make this last part general: Allow a function whihc takes SubstTy arguments and then automatically gives right terms.
  let ret s = TermEq (idApp (ren_ x) (sty_terms xi ++ [s])) (idApp (subst_ x) (sty_terms sigma ++ [s]))
  toVarT <- toVar x eqs
  traversal x m rinstInst_ (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bsigma ++ beqs) [xi, sigma, eqs]
                  (\n -> TermApp toVarT [n])
                  (idApp . congr_) mapExt_

genLemmaInstId :: TId -> GenM Lemma
genLemmaInstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM sty_terms (castSubst x y m))) xs -- TODO: FUnction for vars.
  let ret = TermEq (idApp (subst_ x) vars) (id_ (idApp x (sty_terms m)))
  let proof = TermApp fext_ [TermAbs [BinderName "x"] (idApp (idSubst_ x) ( vars ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermApp (id_ (idApp x (sty_terms m))) [TermId "x"]]))]
  return $ Lemma ("instId_" ++ x) bm ret (ProofExact proof)

genLemmaRinstId :: TId -> GenM Lemma
genLemmaRinstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM sty_terms (castSubst x y m))) xs
  let ret = TermEq (idApp (ren_ x) ( map (const (id_ TermUnderscore)) xs)) (id_ (idApp x (sty_terms m)))
  let proof = eqTrans_ (idApp ("rinstInst_" ++ x) (map (const (id_ TermUnderscore)) xs)) (TermId ("instId_" ++ x))
  return $ Lemma ("rinstId_" ++ x) bm ret (ProofExact proof)

genLemmaVarL :: TId -> GenM Lemma
genLemmaVarL x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma,bsigma) <- genSubst x "sigma" (m,n)
  sigma' <- toVar x sigma
  let ret = TermEq ((var x m) >>> (idApp (subst_ x) (sty_terms sigma))) sigma'
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varL_" ++ x) (bmn ++ bsigma) ret (ProofExact proof)

genLemmaVarLRen :: TId -> GenM Lemma
genLemmaVarLRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  xi' <- (toVar x xi)
  let ret = TermEq ((var x m) >>> (idApp (ren_ x) (sty_terms xi))) (xi' >>> (var x n))
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varLRen_" ++ x) (bmn ++ bxi) ret (ProofExact proof)

genLemmaRenSubst :: TId -> GenM Lemma
genLemmaRenSubst x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  xs <- substOf x
  xis' <- mapM (\(y, xi) -> do
    n' <- castSubst x y n
    return$  xi >>> var y n') (zip xs (sty_terms xi))
  let ret = TermEq (idApp (ren_ x) (sty_terms xi)) (idApp (subst_ x) xis')
  let proof = TermApp fext_ [TermAbs [BinderName "x"] $ idApp (rinstInst_ x) (sty_terms xi ++ map (const TermUnderscore) xs ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermId "x"])]
  return (Lemma ("rinstInst_" ++ x) (bmn ++ bxi) ret (ProofExact proof))


genCodeT :: [TId] -> [(TId,TId)] -> GenM [Sentence]
genCodeT xs upList = do
  varSorts <- filterM isOpen xs -- Sorts which have variables
  hasbinders <- fmap (not. null) (substOf (head xs))
  substSorts <- filterM (const (return True)) xs
  ys <- filterM definable xs
  types <- mapM genBody ys
  congruences <- mapM genCongruences xs
  upRen <- mapM (uncurry genUpRenS) upList
  renamings <- genRenamings substSorts
  ups <- mapM (uncurry genUpS) upList
  substitutions <- genSubstitutions substSorts
  upId <- mapM (uncurry genUpId) upList
  idlemmas <- mapM genIdL substSorts
  extUpRen <- mapM (uncurry genUpExtRen) upList
  extRen <- mapM genExtRen substSorts
  extUp <- mapM (uncurry genUpExt) upList
  ext <- mapM genExt substSorts
  compRenRen <- mapM genCompRenRen substSorts
  upRenSubst <- mapM (uncurry genUpRenSubst) upList
  compRenSubst <- mapM genCompRenSubst substSorts
  upSubstRen <- mapM (uncurry genUpSubstRen) upList
  compSubstRen <- mapM genCompSubstRen substSorts
  upSubstSubst <- mapM (uncurry genUpSubstSubst) upList
  compSubstSubst <- mapM genCompSubstSubst substSorts
  upRinstInst <- mapM (uncurry genUpRinstInst) upList
  rinstInst <- mapM genRinstInst substSorts
  lemmaRinstId <- mapM genLemmaRinstId substSorts
  lemmaInstId <- mapM genLemmaInstId substSorts
  lemmaVarL <- mapM genLemmaVarL varSorts
  lemmaVarLRen <- mapM genLemmaVarLRen varSorts
  lemmaRenSubst <- mapM genLemmaRenSubst substSorts
  lemmaSubstRenRen <- mapM genLemmaRenRenComp substSorts
  lemmaSubstCompRen <- mapM genLemmaSubstCompRen substSorts
  lemmaSubstRenComp <- mapM genLemmaSubstRenComp substSorts
  lemmaSubstComp <- mapM genLemmaSubstComp substSorts
  r <- recursive xs
  let (l1, l2) = unzip lemmaSubstComp
  let (l3, l4) = unzip lemmaSubstCompRen
  let (l5, l6) = unzip lemmaSubstRenComp
  let (l7, l8) = unzip lemmaSubstRenRen
  return $ [SentenceInductive (Inductive types) | (not . null) types] ++ map SentenceDefinition (concat congruences) -- FEATURE: Different intermediate values. --}
          ++ (if hasbinders then map SentenceDefinition upRen ++ [SentenceFixpoint renamings]
          ++ map SentenceDefinition ups ++ [SentenceFixpoint substitutions]
          ++ map SentenceDefinition upId ++ [SentenceFixpoint $ Fixpoint r idlemmas]
          ++ map SentenceDefinition extUpRen ++ [SentenceFixpoint $ Fixpoint r extRen]
          ++ map SentenceDefinition extUp ++ [SentenceFixpoint $ Fixpoint r ext]
          ++ [SentenceFixpoint $ Fixpoint r compRenRen]
          ++ map SentenceDefinition upRenSubst ++ [SentenceFixpoint $ Fixpoint r compRenSubst]
          ++ map SentenceDefinition upSubstRen ++ [SentenceFixpoint $ Fixpoint r compSubstRen]
          ++ map SentenceDefinition upSubstSubst ++ [SentenceFixpoint $ Fixpoint r compSubstSubst]
          ++ map SentenceDefinition upRinstInst ++ [SentenceFixpoint $ Fixpoint r rinstInst]
          ++ map SentenceLemma (lemmaRenSubst ++  lemmaInstId ++ lemmaRinstId ++  lemmaVarL  ++ lemmaVarLRen ++l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8)
          else [])
