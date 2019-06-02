Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Definition label := string.
Definition gname := positive.

Require Export As.unscoped.

Inductive tm  : Type :=
  | tv : vl  -> tm
  | tapp : tm  -> tm  -> tm
  | tproj : tm  -> label  -> tm
 with vl  : Type :=
  | var_vl : (fin)  -> vl
  | vabs : tm  -> vl
  | vobj : dms  -> vl
 with dms  : Type :=
  | dnil : dms
  | dcons : dm  -> dms  -> dms
 with dm  : Type :=
  | dtysyn : ty  -> dm
  | dtysem : gname  -> dm
  | dvl : vl  -> dm
 with path  : Type :=
  | pv : vl  -> path
  | pself : path  -> label  -> path
 with ty  : Type :=
  | TTop : ty
  | TBot : ty
  | TAnd : ty  -> ty  -> ty
  | TOr : ty  -> ty  -> ty
  | TLater : ty  -> ty
  | TAll : ty  -> ty  -> ty
  | TMu : ty  -> ty
  | TVMem : label  -> ty  -> ty
  | TTMem : label  -> ty  -> ty  -> ty
  | TSel : path  -> label  -> ty
  | TSelA : path  -> label  -> ty  -> ty  -> ty .

Definition congr_tv  { s0 : vl  } { t0 : vl  } (H1 : s0 = t0) : tv  s0 = tv  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => tv  x) H1).

Definition congr_tapp  { s0 : tm  } { s1 : tm  } { t0 : tm  } { t1 : tm  } (H1 : s0 = t0) (H2 : s1 = t1) : tapp  s0 s1 = tapp  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => tapp  x (_)) H1)) ((ap) (fun x => tapp  (_) x) H2).

Definition congr_tproj  { s0 : tm  } { s1 : label  } { t0 : tm  } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : tproj  s0 s1 = tproj  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => tproj  x (_)) H1)) ((ap) (fun x => tproj  (_) x) H2).

Definition congr_vabs  { s0 : tm  } { t0 : tm  } (H1 : s0 = t0) : vabs  s0 = vabs  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => vabs  x) H1).

Definition congr_vobj  { s0 : dms  } { t0 : dms  } (H1 : s0 = t0) : vobj  s0 = vobj  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => vobj  x) H1).

Definition congr_dnil  : dnil  = dnil  :=
  eq_refl.

Definition congr_dcons  { s0 : dm  } { s1 : dms  } { t0 : dm  } { t1 : dms  } (H1 : s0 = t0) (H2 : s1 = t1) : dcons  s0 s1 = dcons  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => dcons  x (_)) H1)) ((ap) (fun x => dcons  (_) x) H2).

Definition congr_dtysyn  { s0 : ty  } { t0 : ty  } (H1 : s0 = t0) : dtysyn  s0 = dtysyn  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => dtysyn  x) H1).

Definition congr_dtysem  { s0 : gname  } { t0 : gname  } (H1 : s0 = t0) : dtysem  s0 = dtysem  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => dtysem  x) H1).

Definition congr_dvl  { s0 : vl  } { t0 : vl  } (H1 : s0 = t0) : dvl  s0 = dvl  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => dvl  x) H1).

Definition congr_pv  { s0 : vl  } { t0 : vl  } (H1 : s0 = t0) : pv  s0 = pv  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => pv  x) H1).

Definition congr_pself  { s0 : path  } { s1 : label  } { t0 : path  } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : pself  s0 s1 = pself  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => pself  x (_)) H1)) ((ap) (fun x => pself  (_) x) H2).

Definition congr_TTop  : TTop  = TTop  :=
  eq_refl.

Definition congr_TBot  : TBot  = TBot  :=
  eq_refl.

Definition congr_TAnd  { s0 : ty  } { s1 : ty  } { t0 : ty  } { t1 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) : TAnd  s0 s1 = TAnd  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TAnd  x (_)) H1)) ((ap) (fun x => TAnd  (_) x) H2).

Definition congr_TOr  { s0 : ty  } { s1 : ty  } { t0 : ty  } { t1 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) : TOr  s0 s1 = TOr  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TOr  x (_)) H1)) ((ap) (fun x => TOr  (_) x) H2).

Definition congr_TLater  { s0 : ty  } { t0 : ty  } (H1 : s0 = t0) : TLater  s0 = TLater  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => TLater  x) H1).

Definition congr_TAll  { s0 : ty  } { s1 : ty  } { t0 : ty  } { t1 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) : TAll  s0 s1 = TAll  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TAll  x (_)) H1)) ((ap) (fun x => TAll  (_) x) H2).

Definition congr_TMu  { s0 : ty  } { t0 : ty  } (H1 : s0 = t0) : TMu  s0 = TMu  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => TMu  x) H1).

Definition congr_TVMem  { s0 : label  } { s1 : ty  } { t0 : label  } { t1 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) : TVMem  s0 s1 = TVMem  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TVMem  x (_)) H1)) ((ap) (fun x => TVMem  (_) x) H2).

Definition congr_TTMem  { s0 : label  } { s1 : ty  } { s2 : ty  } { t0 : label  } { t1 : ty  } { t2 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : TTMem  s0 s1 s2 = TTMem  t0 t1 t2 :=
  (eq_trans) ((eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TTMem  x (_) (_)) H1)) ((ap) (fun x => TTMem  (_) x (_)) H2)) ((ap) (fun x => TTMem  (_) (_) x) H3).

Definition congr_TSel  { s0 : path  } { s1 : label  } { t0 : path  } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : TSel  s0 s1 = TSel  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TSel  x (_)) H1)) ((ap) (fun x => TSel  (_) x) H2).

Definition congr_TSelA  { s0 : path  } { s1 : label  } { s2 : ty  } { s3 : ty  } { t0 : path  } { t1 : label  } { t2 : ty  } { t3 : ty  } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : TSelA  s0 s1 s2 s3 = TSelA  t0 t1 t2 t3 :=
  (eq_trans) ((eq_trans) ((eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TSelA  x (_) (_) (_)) H1)) ((ap) (fun x => TSelA  (_) x (_) (_)) H2)) ((ap) (fun x => TSelA  (_) (_) x (_)) H3)) ((ap) (fun x => TSelA  (_) (_) (_) x) H4).

Definition upRen_vl_vl   (xi : (fin)  -> (fin) ) : _ :=
  (up_ren) xi.

Fixpoint ren_tm   (xivl : (fin)  -> (fin) ) (s : tm ) : _ :=
    match s with
    | tv  s0 => tv  ((ren_vl xivl) s0)
    | tapp  s0 s1 => tapp  ((ren_tm xivl) s0) ((ren_tm xivl) s1)
    | tproj  s0 s1 => tproj  ((ren_tm xivl) s0) ((fun x => x) s1)
    end
 with ren_vl   (xivl : (fin)  -> (fin) ) (s : vl ) : _ :=
    match s with
    | var_vl  s => (var_vl ) (xivl s)
    | vabs  s0 => vabs  ((ren_tm (upRen_vl_vl xivl)) s0)
    | vobj  s0 => vobj  ((ren_dms (upRen_vl_vl xivl)) s0)
    end
 with ren_dms   (xivl : (fin)  -> (fin) ) (s : dms ) : _ :=
    match s with
    | dnil   => dnil
    | dcons  s0 s1 => dcons  ((ren_dm xivl) s0) ((ren_dms xivl) s1)
    end
 with ren_dm   (xivl : (fin)  -> (fin) ) (s : dm ) : _ :=
    match s with
    | dtysyn  s0 => dtysyn  ((ren_ty xivl) s0)
    | dtysem  s0 => dtysem  ((fun x => x) s0)
    | dvl  s0 => dvl  ((ren_vl xivl) s0)
    end
 with ren_path   (xivl : (fin)  -> (fin) ) (s : path ) : _ :=
    match s with
    | pv  s0 => pv  ((ren_vl xivl) s0)
    | pself  s0 s1 => pself  ((ren_path xivl) s0) ((fun x => x) s1)
    end
 with ren_ty   (xivl : (fin)  -> (fin) ) (s : ty ) : _ :=
    match s with
    | TTop   => TTop
    | TBot   => TBot
    | TAnd  s0 s1 => TAnd  ((ren_ty xivl) s0) ((ren_ty xivl) s1)
    | TOr  s0 s1 => TOr  ((ren_ty xivl) s0) ((ren_ty xivl) s1)
    | TLater  s0 => TLater  ((ren_ty xivl) s0)
    | TAll  s0 s1 => TAll  ((ren_ty xivl) s0) ((ren_ty (upRen_vl_vl xivl)) s1)
    | TMu  s0 => TMu  ((ren_ty (upRen_vl_vl xivl)) s0)
    | TVMem  s0 s1 => TVMem  ((fun x => x) s0) ((ren_ty xivl) s1)
    | TTMem  s0 s1 s2 => TTMem  ((fun x => x) s0) ((ren_ty xivl) s1) ((ren_ty xivl) s2)
    | TSel  s0 s1 => TSel  ((ren_path xivl) s0) ((fun x => x) s1)
    | TSelA  s0 s1 s2 s3 => TSelA  ((ren_path xivl) s0) ((fun x => x) s1) ((ren_ty xivl) s2) ((ren_ty xivl) s3)
    end.

Definition up_vl_vl   (sigma : (fin)  -> vl ) : _ :=
  (scons) ((var_vl ) (var_zero)) ((funcomp) (ren_vl (shift)) sigma).

Fixpoint subst_tm   (sigmavl : (fin)  -> vl ) (s : tm ) : _ :=
    match s with
    | tv  s0 => tv  ((subst_vl sigmavl) s0)
    | tapp  s0 s1 => tapp  ((subst_tm sigmavl) s0) ((subst_tm sigmavl) s1)
    | tproj  s0 s1 => tproj  ((subst_tm sigmavl) s0) ((fun x => x) s1)
    end
 with subst_vl   (sigmavl : (fin)  -> vl ) (s : vl ) : _ :=
    match s with
    | var_vl  s => sigmavl s
    | vabs  s0 => vabs  ((subst_tm (up_vl_vl sigmavl)) s0)
    | vobj  s0 => vobj  ((subst_dms (up_vl_vl sigmavl)) s0)
    end
 with subst_dms   (sigmavl : (fin)  -> vl ) (s : dms ) : _ :=
    match s with
    | dnil   => dnil
    | dcons  s0 s1 => dcons  ((subst_dm sigmavl) s0) ((subst_dms sigmavl) s1)
    end
 with subst_dm   (sigmavl : (fin)  -> vl ) (s : dm ) : _ :=
    match s with
    | dtysyn  s0 => dtysyn  ((subst_ty sigmavl) s0)
    | dtysem  s0 => dtysem  ((fun x => x) s0)
    | dvl  s0 => dvl  ((subst_vl sigmavl) s0)
    end
 with subst_path   (sigmavl : (fin)  -> vl ) (s : path ) : _ :=
    match s with
    | pv  s0 => pv  ((subst_vl sigmavl) s0)
    | pself  s0 s1 => pself  ((subst_path sigmavl) s0) ((fun x => x) s1)
    end
 with subst_ty   (sigmavl : (fin)  -> vl ) (s : ty ) : _ :=
    match s with
    | TTop   => TTop
    | TBot   => TBot
    | TAnd  s0 s1 => TAnd  ((subst_ty sigmavl) s0) ((subst_ty sigmavl) s1)
    | TOr  s0 s1 => TOr  ((subst_ty sigmavl) s0) ((subst_ty sigmavl) s1)
    | TLater  s0 => TLater  ((subst_ty sigmavl) s0)
    | TAll  s0 s1 => TAll  ((subst_ty sigmavl) s0) ((subst_ty (up_vl_vl sigmavl)) s1)
    | TMu  s0 => TMu  ((subst_ty (up_vl_vl sigmavl)) s0)
    | TVMem  s0 s1 => TVMem  ((fun x => x) s0) ((subst_ty sigmavl) s1)
    | TTMem  s0 s1 s2 => TTMem  ((fun x => x) s0) ((subst_ty sigmavl) s1) ((subst_ty sigmavl) s2)
    | TSel  s0 s1 => TSel  ((subst_path sigmavl) s0) ((fun x => x) s1)
    | TSelA  s0 s1 s2 s3 => TSelA  ((subst_path sigmavl) s0) ((fun x => x) s1) ((subst_ty sigmavl) s2) ((subst_ty sigmavl) s3)
    end.

Definition upId_vl_vl  (sigma : (fin)  -> vl ) (Eq : forall x, sigma x = (var_vl ) x) : forall x, (up_vl_vl sigma) x = (var_vl ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_tm  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : tm ) : subst_tm sigmavl s = s :=
    match s with
    | tv  s0 => congr_tv ((idSubst_vl sigmavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((idSubst_tm sigmavl Eqvl) s0) ((idSubst_tm sigmavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((idSubst_tm sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with idSubst_vl  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : vl ) : subst_vl sigmavl s = s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((idSubst_tm (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((idSubst_dms (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    end
 with idSubst_dms  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : dms ) : subst_dms sigmavl s = s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((idSubst_dm sigmavl Eqvl) s0) ((idSubst_dms sigmavl Eqvl) s1)
    end
 with idSubst_dm  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : dm ) : subst_dm sigmavl s = s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((idSubst_ty sigmavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((idSubst_vl sigmavl Eqvl) s0)
    end
 with idSubst_path  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : path ) : subst_path sigmavl s = s :=
    match s with
    | pv  s0 => congr_pv ((idSubst_vl sigmavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with idSubst_ty  (sigmavl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = (var_vl ) x) (s : ty ) : subst_ty sigmavl s = s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((idSubst_ty sigmavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((idSubst_ty (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((idSubst_ty sigmavl Eqvl) s1) ((idSubst_ty sigmavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((idSubst_ty sigmavl Eqvl) s2) ((idSubst_ty sigmavl Eqvl) s3)
    end.

Definition upExtRen_vl_vl   (xi : (fin)  -> (fin) ) (zeta : (fin)  -> (fin) ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_vl xi) x = (upRen_vl_vl zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint extRen_tm   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : tm ) : ren_tm xivl s = ren_tm zetavl s :=
    match s with
    | tv  s0 => congr_tv ((extRen_vl xivl zetavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((extRen_tm xivl zetavl Eqvl) s0) ((extRen_tm xivl zetavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((extRen_tm xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with extRen_vl   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : vl ) : ren_vl xivl s = ren_vl zetavl s :=
    match s with
    | var_vl  s => (ap) (var_vl ) (Eqvl s)
    | vabs  s0 => congr_vabs ((extRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((extRen_dms (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    end
 with extRen_dms   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : dms ) : ren_dms xivl s = ren_dms zetavl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((extRen_dm xivl zetavl Eqvl) s0) ((extRen_dms xivl zetavl Eqvl) s1)
    end
 with extRen_dm   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : dm ) : ren_dm xivl s = ren_dm zetavl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((extRen_ty xivl zetavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((extRen_vl xivl zetavl Eqvl) s0)
    end
 with extRen_path   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : path ) : ren_path xivl s = ren_path zetavl s :=
    match s with
    | pv  s0 => congr_pv ((extRen_vl xivl zetavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with extRen_ty   (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (Eqvl : forall x, xivl x = zetavl x) (s : ty ) : ren_ty xivl s = ren_ty zetavl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((extRen_ty xivl zetavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((extRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((extRen_ty xivl zetavl Eqvl) s1) ((extRen_ty xivl zetavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((extRen_ty xivl zetavl Eqvl) s2) ((extRen_ty xivl zetavl Eqvl) s3)
    end.

Definition upExt_vl_vl   (sigma : (fin)  -> vl ) (tau : (fin)  -> vl ) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_vl sigma) x = (up_vl_vl tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint ext_tm   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : tm ) : subst_tm sigmavl s = subst_tm tauvl s :=
    match s with
    | tv  s0 => congr_tv ((ext_vl sigmavl tauvl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((ext_tm sigmavl tauvl Eqvl) s0) ((ext_tm sigmavl tauvl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((ext_tm sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with ext_vl   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : vl ) : subst_vl sigmavl s = subst_vl tauvl s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((ext_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((ext_dms (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    end
 with ext_dms   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : dms ) : subst_dms sigmavl s = subst_dms tauvl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((ext_dm sigmavl tauvl Eqvl) s0) ((ext_dms sigmavl tauvl Eqvl) s1)
    end
 with ext_dm   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : dm ) : subst_dm sigmavl s = subst_dm tauvl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((ext_ty sigmavl tauvl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((ext_vl sigmavl tauvl Eqvl) s0)
    end
 with ext_path   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : path ) : subst_path sigmavl s = subst_path tauvl s :=
    match s with
    | pv  s0 => congr_pv ((ext_vl sigmavl tauvl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with ext_ty   (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (Eqvl : forall x, sigmavl x = tauvl x) (s : ty ) : subst_ty sigmavl s = subst_ty tauvl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TLater  s0 => congr_TLater ((ext_ty sigmavl tauvl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((ext_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((ext_ty sigmavl tauvl Eqvl) s1) ((ext_ty sigmavl tauvl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((ext_ty sigmavl tauvl Eqvl) s2) ((ext_ty sigmavl tauvl Eqvl) s3)
    end.

Fixpoint compRenRen_tm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : tm ) : ren_tm zetavl (ren_tm xivl s) = ren_tm rhovl s :=
    match s with
    | tv  s0 => congr_tv ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((compRenRen_tm xivl zetavl rhovl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenRen_vl    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : vl ) : ren_vl zetavl (ren_vl xivl s) = ren_vl rhovl s :=
    match s with
    | var_vl  s => (ap) (var_vl ) (Eqvl s)
    | vabs  s0 => congr_vabs ((compRenRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((compRenRen_dms (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    end
 with compRenRen_dms    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : dms ) : ren_dms zetavl (ren_dms xivl s) = ren_dms rhovl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((compRenRen_dm xivl zetavl rhovl Eqvl) s0) ((compRenRen_dms xivl zetavl rhovl Eqvl) s1)
    end
 with compRenRen_dm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : dm ) : ren_dm zetavl (ren_dm xivl s) = ren_dm rhovl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((compRenRen_ty xivl zetavl rhovl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    end
 with compRenRen_path    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : path ) : ren_path zetavl (ren_path xivl s) = ren_path rhovl s :=
    match s with
    | pv  s0 => congr_pv ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenRen_ty    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (rhovl : (fin)  -> (fin) ) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : ty ) : ren_ty zetavl (ren_ty xivl s) = ren_ty rhovl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TLater  s0 => congr_TLater ((compRenRen_ty xivl zetavl rhovl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((compRenRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1) ((compRenRen_ty xivl zetavl rhovl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compRenRen_ty xivl zetavl rhovl Eqvl) s2) ((compRenRen_ty xivl zetavl rhovl Eqvl) s3)
    end.

Definition up_ren_subst_vl_vl    (xi : (fin)  -> (fin) ) (tau : (fin)  -> vl ) (theta : (fin)  -> vl ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_vl tau) (upRen_vl_vl xi)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_tm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : tm ) : subst_tm tauvl (ren_tm xivl s) = subst_tm thetavl s :=
    match s with
    | tv  s0 => congr_tv ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((compRenSubst_tm xivl tauvl thetavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenSubst_vl    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : vl ) : subst_vl tauvl (ren_vl xivl s) = subst_vl thetavl s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((compRenSubst_tm (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((compRenSubst_dms (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compRenSubst_dms    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : dms ) : subst_dms tauvl (ren_dms xivl s) = subst_dms thetavl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((compRenSubst_dm xivl tauvl thetavl Eqvl) s0) ((compRenSubst_dms xivl tauvl thetavl Eqvl) s1)
    end
 with compRenSubst_dm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : dm ) : subst_dm tauvl (ren_dm xivl s) = subst_dm thetavl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    end
 with compRenSubst_path    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : path ) : subst_path tauvl (ren_path xivl s) = subst_path thetavl s :=
    match s with
    | pv  s0 => congr_pv ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenSubst_ty    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : ty ) : subst_ty tauvl (ren_ty xivl s) = subst_ty thetavl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((compRenSubst_ty (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s2) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s3)
    end.

Definition up_subst_ren_vl_vl    (sigma : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (theta : (fin)  -> vl ) (Eq : forall x, ((funcomp) (ren_vl zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_vl_vl zetavl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_vl (shift) (upRen_vl_vl zetavl) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetavl (shift) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen_tm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : tm ) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s with
    | tv  s0 => congr_tv ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstRen_vl    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : vl ) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((compSubstRen_tm (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((compSubstRen_dms (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compSubstRen_dms    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : dms ) : ren_dms zetavl (subst_dms sigmavl s) = subst_dms thetavl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((compSubstRen_dm sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_dms sigmavl zetavl thetavl Eqvl) s1)
    end
 with compSubstRen_dm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : dm ) : ren_dm zetavl (subst_dm sigmavl s) = subst_dm thetavl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    end
 with compSubstRen_path    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : path ) : ren_path zetavl (subst_path sigmavl s) = subst_path thetavl s :=
    match s with
    | pv  s0 => congr_pv ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstRen_ty    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : ty ) : ren_ty zetavl (subst_ty sigmavl s) = subst_ty thetavl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((compSubstRen_ty (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s2) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s3)
    end.

Definition up_subst_subst_vl_vl    (sigma : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (theta : (fin)  -> vl ) (Eq : forall x, ((funcomp) (subst_vl tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_vl_vl tauvl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_vl (shift) (up_vl_vl tauvl) ((funcomp) (up_vl_vl tauvl) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauvl (shift) ((funcomp) (ren_vl (shift)) tauvl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_tm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : tm ) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s with
    | tv  s0 => congr_tv ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstSubst_vl    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : vl ) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((compSubstSubst_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((compSubstSubst_dms (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compSubstSubst_dms    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : dms ) : subst_dms tauvl (subst_dms sigmavl s) = subst_dms thetavl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((compSubstSubst_dm sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_dms sigmavl tauvl thetavl Eqvl) s1)
    end
 with compSubstSubst_dm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : dm ) : subst_dm tauvl (subst_dm sigmavl s) = subst_dm thetavl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    end
 with compSubstSubst_path    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : path ) : subst_path tauvl (subst_path sigmavl s) = subst_path thetavl s :=
    match s with
    | pv  s0 => congr_pv ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstSubst_ty    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (thetavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : ty ) : subst_ty tauvl (subst_ty sigmavl s) = subst_ty thetavl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((compSubstSubst_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s2) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s3)
    end.

Definition rinstInst_up_vl_vl   (xi : (fin)  -> (fin) ) (sigma : (fin)  -> vl ) (Eq : forall x, ((funcomp) (var_vl ) xi) x = sigma x) : forall x, ((funcomp) (var_vl ) (upRen_vl_vl xi)) x = (up_vl_vl sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_tm   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : tm ) : ren_tm xivl s = subst_tm sigmavl s :=
    match s with
    | tv  s0 => congr_tv ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | tapp  s0 s1 => congr_tapp ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((rinst_inst_tm xivl sigmavl Eqvl) s1)
    | tproj  s0 s1 => congr_tproj ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with rinst_inst_vl   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : vl ) : ren_vl xivl s = subst_vl sigmavl s :=
    match s with
    | var_vl  s => Eqvl s
    | vabs  s0 => congr_vabs ((rinst_inst_tm (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    | vobj  s0 => congr_vobj ((rinst_inst_dms (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    end
 with rinst_inst_dms   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : dms ) : ren_dms xivl s = subst_dms sigmavl s :=
    match s with
    | dnil   => congr_dnil
    | dcons  s0 s1 => congr_dcons ((rinst_inst_dm xivl sigmavl Eqvl) s0) ((rinst_inst_dms xivl sigmavl Eqvl) s1)
    end
 with rinst_inst_dm   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : dm ) : ren_dm xivl s = subst_dm sigmavl s :=
    match s with
    | dtysyn  s0 => congr_dtysyn ((rinst_inst_ty xivl sigmavl Eqvl) s0)
    | dtysem  s0 => congr_dtysem ((fun x => (eq_refl) x) s0)
    | dvl  s0 => congr_dvl ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    end
 with rinst_inst_path   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : path ) : ren_path xivl s = subst_path sigmavl s :=
    match s with
    | pv  s0 => congr_pv ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | pself  s0 s1 => congr_pself ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with rinst_inst_ty   (xivl : (fin)  -> (fin) ) (sigmavl : (fin)  -> vl ) (Eqvl : forall x, ((funcomp) (var_vl ) xivl) x = sigmavl x) (s : ty ) : ren_ty xivl s = subst_ty sigmavl s :=
    match s with
    | TTop   => congr_TTop
    | TBot   => congr_TBot
    | TAnd  s0 s1 => congr_TAnd ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TOr  s0 s1 => congr_TOr ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TLater  s0 => congr_TLater ((rinst_inst_ty xivl sigmavl Eqvl) s0)
    | TAll  s0 s1 => congr_TAll ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s1)
    | TMu  s0 => congr_TMu ((rinst_inst_ty (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    | TVMem  s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TTMem  s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1) ((rinst_inst_ty xivl sigmavl Eqvl) s2)
    | TSel  s0 s1 => congr_TSel ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA  s0 s1 s2 s3 => congr_TSelA ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((rinst_inst_ty xivl sigmavl Eqvl) s2) ((rinst_inst_ty xivl sigmavl Eqvl) s3)
    end.

Lemma rinstInst_tm   (xivl : (fin)  -> (fin) ) : ren_tm xivl = subst_tm ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_vl   (xivl : (fin)  -> (fin) ) : ren_vl xivl = subst_vl ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_vl xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_dms   (xivl : (fin)  -> (fin) ) : ren_dms xivl = subst_dms ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_dms xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_dm   (xivl : (fin)  -> (fin) ) : ren_dm xivl = subst_dm ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_dm xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_path   (xivl : (fin)  -> (fin) ) : ren_path xivl = subst_path ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_path xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_ty   (xivl : (fin)  -> (fin) ) : ren_ty xivl = subst_ty ((funcomp) (var_vl ) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ty xivl (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm  : subst_tm (var_vl ) = (@id) (tm ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_vl ) (fun n => eq_refl) (((@id) (tm )) x))). Qed.

Lemma instId_vl  : subst_vl (var_vl ) = (@id) (vl ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_vl (var_vl ) (fun n => eq_refl) (((@id) (vl )) x))). Qed.

Lemma instId_dms  : subst_dms (var_vl ) = (@id) (dms ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_dms (var_vl ) (fun n => eq_refl) (((@id) (dms )) x))). Qed.

Lemma instId_dm  : subst_dm (var_vl ) = (@id) (dm ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_dm (var_vl ) (fun n => eq_refl) (((@id) (dm )) x))). Qed.

Lemma instId_path  : subst_path (var_vl ) = (@id) (path ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_path (var_vl ) (fun n => eq_refl) (((@id) (path )) x))). Qed.

Lemma instId_ty  : subst_ty (var_vl ) = (@id) (ty ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ty (var_vl ) (fun n => eq_refl) (((@id) (ty )) x))). Qed.

Lemma rinstId_tm  : ren_tm ((@id) (_)) = (@id) (tm ) .
Proof. exact ((eq_trans) (rinstInst_tm ((@id) (_))) instId_tm). Qed.

Lemma rinstId_vl  : ren_vl ((@id) (_)) = (@id) (vl ) .
Proof. exact ((eq_trans) (rinstInst_vl ((@id) (_))) instId_vl). Qed.

Lemma rinstId_dms  : ren_dms ((@id) (_)) = (@id) (dms ) .
Proof. exact ((eq_trans) (rinstInst_dms ((@id) (_))) instId_dms). Qed.

Lemma rinstId_dm  : ren_dm ((@id) (_)) = (@id) (dm ) .
Proof. exact ((eq_trans) (rinstInst_dm ((@id) (_))) instId_dm). Qed.

Lemma rinstId_path  : ren_path ((@id) (_)) = (@id) (path ) .
Proof. exact ((eq_trans) (rinstInst_path ((@id) (_))) instId_path). Qed.

Lemma rinstId_ty  : ren_ty ((@id) (_)) = (@id) (ty ) .
Proof. exact ((eq_trans) (rinstInst_ty ((@id) (_))) instId_ty). Qed.

Lemma varL_vl   (sigmavl : (fin)  -> vl ) : (funcomp) (subst_vl sigmavl) (var_vl ) = sigmavl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_vl   (xivl : (fin)  -> (fin) ) : (funcomp) (ren_vl xivl) (var_vl ) = (funcomp) (var_vl ) xivl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : tm ) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_tm sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_vl    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : vl ) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_vl sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_dms    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : dms ) : subst_dms tauvl (subst_dms sigmavl s) = subst_dms ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_dms sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_dm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : dm ) : subst_dm tauvl (subst_dm sigmavl s) = subst_dm ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_dm sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_path    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : path ) : subst_path tauvl (subst_path sigmavl s) = subst_path ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_path sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_ty    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) (s : ty ) : subst_ty tauvl (subst_ty sigmavl s) = subst_ty ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_ty sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_tm tauvl) (subst_tm sigmavl) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmavl tauvl n)). Qed.

Lemma compComp'_vl    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_vl tauvl) (subst_vl sigmavl) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_vl sigmavl tauvl n)). Qed.

Lemma compComp'_dms    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_dms tauvl) (subst_dms sigmavl) = subst_dms ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_dms sigmavl tauvl n)). Qed.

Lemma compComp'_dm    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_dm tauvl) (subst_dm sigmavl) = subst_dm ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_dm sigmavl tauvl n)). Qed.

Lemma compComp'_path    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_path tauvl) (subst_path sigmavl) = subst_path ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_path sigmavl tauvl n)). Qed.

Lemma compComp'_ty    (sigmavl : (fin)  -> vl ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_ty tauvl) (subst_ty sigmavl) = subst_ty ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ty sigmavl tauvl n)). Qed.

Lemma compRen_tm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : tm ) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_tm sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_vl    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : vl ) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_vl sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_dms    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : dms ) : ren_dms zetavl (subst_dms sigmavl s) = subst_dms ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_dms sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_dm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : dm ) : ren_dm zetavl (subst_dm sigmavl s) = subst_dm ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_dm sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_path    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : path ) : ren_path zetavl (subst_path sigmavl s) = subst_path ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_path sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_ty    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) (s : ty ) : ren_ty zetavl (subst_ty sigmavl s) = subst_ty ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_ty sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_tm zetavl) (subst_tm sigmavl) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmavl zetavl n)). Qed.

Lemma compRen'_vl    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_vl zetavl) (subst_vl sigmavl) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_vl sigmavl zetavl n)). Qed.

Lemma compRen'_dms    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_dms zetavl) (subst_dms sigmavl) = subst_dms ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_dms sigmavl zetavl n)). Qed.

Lemma compRen'_dm    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_dm zetavl) (subst_dm sigmavl) = subst_dm ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_dm sigmavl zetavl n)). Qed.

Lemma compRen'_path    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_path zetavl) (subst_path sigmavl) = subst_path ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_path sigmavl zetavl n)). Qed.

Lemma compRen'_ty    (sigmavl : (fin)  -> vl ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_ty zetavl) (subst_ty sigmavl) = subst_ty ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ty sigmavl zetavl n)). Qed.

Lemma renComp_tm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : tm ) : subst_tm tauvl (ren_tm xivl s) = subst_tm ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_tm xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_vl    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : vl ) : subst_vl tauvl (ren_vl xivl s) = subst_vl ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_vl xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_dms    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : dms ) : subst_dms tauvl (ren_dms xivl s) = subst_dms ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_dms xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_dm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : dm ) : subst_dm tauvl (ren_dm xivl s) = subst_dm ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_dm xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_path    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : path ) : subst_path tauvl (ren_path xivl s) = subst_path ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_path xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_ty    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) (s : ty ) : subst_ty tauvl (ren_ty xivl s) = subst_ty ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_ty xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_tm tauvl) (ren_tm xivl) = subst_tm ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xivl tauvl n)). Qed.

Lemma renComp'_vl    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_vl tauvl) (ren_vl xivl) = subst_vl ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_vl xivl tauvl n)). Qed.

Lemma renComp'_dms    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_dms tauvl) (ren_dms xivl) = subst_dms ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_dms xivl tauvl n)). Qed.

Lemma renComp'_dm    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_dm tauvl) (ren_dm xivl) = subst_dm ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_dm xivl tauvl n)). Qed.

Lemma renComp'_path    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_path tauvl) (ren_path xivl) = subst_path ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_path xivl tauvl n)). Qed.

Lemma renComp'_ty    (xivl : (fin)  -> (fin) ) (tauvl : (fin)  -> vl ) : (funcomp) (subst_ty tauvl) (ren_ty xivl) = subst_ty ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ty xivl tauvl n)). Qed.

Lemma renRen_tm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : tm ) : ren_tm zetavl (ren_tm xivl s) = ren_tm ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_tm xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_vl    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : vl ) : ren_vl zetavl (ren_vl xivl s) = ren_vl ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_vl xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_dms    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : dms ) : ren_dms zetavl (ren_dms xivl s) = ren_dms ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_dms xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_dm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : dm ) : ren_dm zetavl (ren_dm xivl s) = ren_dm ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_dm xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_path    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : path ) : ren_path zetavl (ren_path xivl s) = ren_path ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_path xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_ty    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) (s : ty ) : ren_ty zetavl (ren_ty xivl s) = ren_ty ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_ty xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_tm zetavl) (ren_tm xivl) = ren_tm ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xivl zetavl n)). Qed.

Lemma renRen'_vl    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_vl zetavl) (ren_vl xivl) = ren_vl ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_vl xivl zetavl n)). Qed.

Lemma renRen'_dms    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_dms zetavl) (ren_dms xivl) = ren_dms ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_dms xivl zetavl n)). Qed.

Lemma renRen'_dm    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_dm zetavl) (ren_dm xivl) = ren_dm ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_dm xivl zetavl n)). Qed.

Lemma renRen'_path    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_path zetavl) (ren_path xivl) = ren_path ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_path xivl zetavl n)). Qed.

Lemma renRen'_ty    (xivl : (fin)  -> (fin) ) (zetavl : (fin)  -> (fin) ) : (funcomp) (ren_ty zetavl) (ren_ty xivl) = ren_ty ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ty xivl zetavl n)). Qed.

















































Instance Subst_tm   : Subst1 ((fin)  -> vl ) (tm ) (tm ) := @subst_tm   .

Instance Subst_vl   : Subst1 ((fin)  -> vl ) (vl ) (vl ) := @subst_vl   .

Instance Subst_dms   : Subst1 ((fin)  -> vl ) (dms ) (dms ) := @subst_dms   .

Instance Subst_dm   : Subst1 ((fin)  -> vl ) (dm ) (dm ) := @subst_dm   .

Instance Subst_path   : Subst1 ((fin)  -> vl ) (path ) (path ) := @subst_path   .

Instance Subst_ty   : Subst1 ((fin)  -> vl ) (ty ) (ty ) := @subst_ty   .

Instance Ren_tm   : Ren1 ((fin)  -> (fin) ) (tm ) (tm ) := @ren_tm   .

Instance Ren_vl   : Ren1 ((fin)  -> (fin) ) (vl ) (vl ) := @ren_vl   .

Instance Ren_dms   : Ren1 ((fin)  -> (fin) ) (dms ) (dms ) := @ren_dms   .

Instance Ren_dm   : Ren1 ((fin)  -> (fin) ) (dm ) (dm ) := @ren_dm   .

Instance Ren_path   : Ren1 ((fin)  -> (fin) ) (path ) (path ) := @ren_path   .

Instance Ren_ty   : Ren1 ((fin)  -> (fin) ) (ty ) (ty ) := @ren_ty   .

Instance VarInstance_vl  : Var ((fin) ) (vl ) := @var_vl  .

Notation "x '__vl'" := (var_vl x) (at level 5, format "x __vl") : subst_scope.

Notation "x '__vl'" := (@ids (_) (_) VarInstance_vl x) (at level 5, only printing, format "x __vl") : subst_scope.

Notation "'var'" := (var_vl) (only printing, at level 1) : subst_scope.

Class Up_vl X Y := up_vl : X -> Y.

Notation "↑__vl" := (up_vl) (only printing) : subst_scope.

Notation "↑__vl" := (up_vl_vl) (only printing) : subst_scope.

Instance Up_vl_vl   : Up_vl (_) (_) := @up_vl_vl   .

Notation "s [ sigmavl ]" := (subst_tm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_tm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_tm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_tm xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_vl sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_vl xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_vl sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_vl xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_dms sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_dms xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_dms sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_dms xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_dm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_dm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_dm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_dm xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_path sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_path xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_path sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_path xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_ty sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_ty xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_ty sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_ty xivl) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Subst_vl,  Subst_dms,  Subst_dm,  Subst_path,  Subst_ty,  Ren_tm,  Ren_vl,  Ren_dms,  Ren_dm,  Ren_path,  Ren_ty,  VarInstance_vl.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Subst_vl,  Subst_dms,  Subst_dm,  Subst_path,  Subst_ty,  Ren_tm,  Ren_vl,  Ren_dms,  Ren_dm,  Ren_path,  Ren_ty,  VarInstance_vl in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?rinstId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?instId_vl| progress rewrite ?rinstId_vl| progress rewrite ?compComp_vl| progress rewrite ?compComp'_vl| progress rewrite ?compRen_vl| progress rewrite ?compRen'_vl| progress rewrite ?renComp_vl| progress rewrite ?renComp'_vl| progress rewrite ?renRen_vl| progress rewrite ?renRen'_vl| progress rewrite ?instId_dms| progress rewrite ?rinstId_dms| progress rewrite ?compComp_dms| progress rewrite ?compComp'_dms| progress rewrite ?compRen_dms| progress rewrite ?compRen'_dms| progress rewrite ?renComp_dms| progress rewrite ?renComp'_dms| progress rewrite ?renRen_dms| progress rewrite ?renRen'_dms| progress rewrite ?instId_dm| progress rewrite ?rinstId_dm| progress rewrite ?compComp_dm| progress rewrite ?compComp'_dm| progress rewrite ?compRen_dm| progress rewrite ?compRen'_dm| progress rewrite ?renComp_dm| progress rewrite ?renComp'_dm| progress rewrite ?renRen_dm| progress rewrite ?renRen'_dm| progress rewrite ?instId_path| progress rewrite ?rinstId_path| progress rewrite ?compComp_path| progress rewrite ?compComp'_path| progress rewrite ?compRen_path| progress rewrite ?compRen'_path| progress rewrite ?renComp_path| progress rewrite ?renComp'_path| progress rewrite ?renRen_path| progress rewrite ?renRen'_path| progress rewrite ?instId_ty| progress rewrite ?rinstId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?varL_vl| progress rewrite ?varLRen_vl| progress (unfold up_ren, upRen_vl_vl, up_vl_vl)| progress (cbn [subst_tm subst_vl subst_dms subst_dm subst_path subst_ty ren_tm ren_vl ren_dms ren_dm ren_path ren_ty])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?instId_vl in *| progress rewrite ?rinstId_vl in *| progress rewrite ?compComp_vl in *| progress rewrite ?compComp'_vl in *| progress rewrite ?compRen_vl in *| progress rewrite ?compRen'_vl in *| progress rewrite ?renComp_vl in *| progress rewrite ?renComp'_vl in *| progress rewrite ?renRen_vl in *| progress rewrite ?renRen'_vl in *| progress rewrite ?instId_dms in *| progress rewrite ?rinstId_dms in *| progress rewrite ?compComp_dms in *| progress rewrite ?compComp'_dms in *| progress rewrite ?compRen_dms in *| progress rewrite ?compRen'_dms in *| progress rewrite ?renComp_dms in *| progress rewrite ?renComp'_dms in *| progress rewrite ?renRen_dms in *| progress rewrite ?renRen'_dms in *| progress rewrite ?instId_dm in *| progress rewrite ?rinstId_dm in *| progress rewrite ?compComp_dm in *| progress rewrite ?compComp'_dm in *| progress rewrite ?compRen_dm in *| progress rewrite ?compRen'_dm in *| progress rewrite ?renComp_dm in *| progress rewrite ?renComp'_dm in *| progress rewrite ?renRen_dm in *| progress rewrite ?renRen'_dm in *| progress rewrite ?instId_path in *| progress rewrite ?rinstId_path in *| progress rewrite ?compComp_path in *| progress rewrite ?compComp'_path in *| progress rewrite ?compRen_path in *| progress rewrite ?compRen'_path in *| progress rewrite ?renComp_path in *| progress rewrite ?renComp'_path in *| progress rewrite ?renRen_path in *| progress rewrite ?renRen'_path in *| progress rewrite ?instId_ty in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?varL_vl in *| progress rewrite ?varLRen_vl in *| progress (unfold up_ren, upRen_vl_vl, up_vl_vl in *)| progress (cbn [subst_tm subst_vl subst_dms subst_dm subst_path subst_ty ren_tm ren_vl ren_dms ren_dm ren_path ren_ty] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_tm; [|now intros]); try repeat (erewrite rinst_inst_vl; [|now intros]); try repeat (erewrite rinst_inst_dms; [|now intros]); try repeat (erewrite rinst_inst_dm; [|now intros]); try repeat (erewrite rinst_inst_path; [|now intros]); try repeat (erewrite rinst_inst_ty; [|now intros]).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_tm; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_vl; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_dms; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_dm; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_path; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_ty; [|intros; now asimpl]).
