Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Definition label := string.
Definition gname := positive.

Require Export As.fintype.

Inductive tm (nvl : nat) : Type :=
  | tv : vl (nvl) -> tm (nvl)
  | tapp : tm (nvl) -> tm (nvl) -> tm (nvl)
  | tproj : tm (nvl) -> label  -> tm (nvl)
 with vl (nvl : nat) : Type :=
  | var_vl : (fin) (nvl) -> vl (nvl)
  | vabs : tm ((S) nvl) -> vl (nvl)
  | vobj : dms ((S) nvl) -> vl (nvl)
 with vls (nvl : nat) : Type :=
  | vnil : vls (nvl)
  | vcons : vl (nvl) -> vls (nvl) -> vls (nvl)
 with dms (nvl : nat) : Type :=
  | dnil : dms (nvl)
  | dcons : label  -> dm (nvl) -> dms (nvl) -> dms (nvl)
 with dm (nvl : nat) : Type :=
  | dtysyn : ty (nvl) -> dm (nvl)
  | dtysem : gname  -> vls (nvl) -> dm (nvl)
  | dvl : vl (nvl) -> dm (nvl)
 with path (nvl : nat) : Type :=
  | pv : vl (nvl) -> path (nvl)
  | pself : path (nvl) -> label  -> path (nvl)
 with ty (nvl : nat) : Type :=
  | TTop : ty (nvl)
  | TBot : ty (nvl)
  | TAnd : ty (nvl) -> ty (nvl) -> ty (nvl)
  | TOr : ty (nvl) -> ty (nvl) -> ty (nvl)
  | TLater : ty (nvl) -> ty (nvl)
  | TAll : ty (nvl) -> ty ((S) nvl) -> ty (nvl)
  | TMu : ty ((S) nvl) -> ty (nvl)
  | TVMem : label  -> ty (nvl) -> ty (nvl)
  | TTMem : label  -> ty (nvl) -> ty (nvl) -> ty (nvl)
  | TSel : path (nvl) -> label  -> ty (nvl)
  | TSelA : path (nvl) -> label  -> ty (nvl) -> ty (nvl) -> ty (nvl).

Definition congr_tv { mvl : nat } { s0 : vl (mvl) } { t0 : vl (mvl) } (H1 : s0 = t0) : tv (mvl) s0 = tv (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => tv (mvl) x) H1).

Definition congr_tapp { mvl : nat } { s0 : tm (mvl) } { s1 : tm (mvl) } { t0 : tm (mvl) } { t1 : tm (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : tapp (mvl) s0 s1 = tapp (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => tapp (mvl) x (_)) H1)) ((ap) (fun x => tapp (mvl) (_) x) H2).

Definition congr_tproj { mvl : nat } { s0 : tm (mvl) } { s1 : label  } { t0 : tm (mvl) } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : tproj (mvl) s0 s1 = tproj (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => tproj (mvl) x (_)) H1)) ((ap) (fun x => tproj (mvl) (_) x) H2).

Definition congr_vabs { mvl : nat } { s0 : tm ((S) mvl) } { t0 : tm ((S) mvl) } (H1 : s0 = t0) : vabs (mvl) s0 = vabs (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => vabs (mvl) x) H1).

Definition congr_vobj { mvl : nat } { s0 : dms ((S) mvl) } { t0 : dms ((S) mvl) } (H1 : s0 = t0) : vobj (mvl) s0 = vobj (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => vobj (mvl) x) H1).

Definition congr_vnil { mvl : nat } : vnil (mvl) = vnil (mvl) :=
  eq_refl.

Definition congr_vcons { mvl : nat } { s0 : vl (mvl) } { s1 : vls (mvl) } { t0 : vl (mvl) } { t1 : vls (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : vcons (mvl) s0 s1 = vcons (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => vcons (mvl) x (_)) H1)) ((ap) (fun x => vcons (mvl) (_) x) H2).

Definition congr_dnil { mvl : nat } : dnil (mvl) = dnil (mvl) :=
  eq_refl.

Definition congr_dcons { mvl : nat } { s0 : label  } { s1 : dm (mvl) } { s2 : dms (mvl) } { t0 : label  } { t1 : dm (mvl) } { t2 : dms (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : dcons (mvl) s0 s1 s2 = dcons (mvl) t0 t1 t2 :=
  (eq_trans) ((eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => dcons (mvl) x (_) (_)) H1)) ((ap) (fun x => dcons (mvl) (_) x (_)) H2)) ((ap) (fun x => dcons (mvl) (_) (_) x) H3).

Definition congr_dtysyn { mvl : nat } { s0 : ty (mvl) } { t0 : ty (mvl) } (H1 : s0 = t0) : dtysyn (mvl) s0 = dtysyn (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => dtysyn (mvl) x) H1).

Definition congr_dtysem { mvl : nat } { s0 : gname  } { s1 : vls (mvl) } { t0 : gname  } { t1 : vls (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : dtysem (mvl) s0 s1 = dtysem (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => dtysem (mvl) x (_)) H1)) ((ap) (fun x => dtysem (mvl) (_) x) H2).

Definition congr_dvl { mvl : nat } { s0 : vl (mvl) } { t0 : vl (mvl) } (H1 : s0 = t0) : dvl (mvl) s0 = dvl (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => dvl (mvl) x) H1).

Definition congr_pv { mvl : nat } { s0 : vl (mvl) } { t0 : vl (mvl) } (H1 : s0 = t0) : pv (mvl) s0 = pv (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => pv (mvl) x) H1).

Definition congr_pself { mvl : nat } { s0 : path (mvl) } { s1 : label  } { t0 : path (mvl) } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : pself (mvl) s0 s1 = pself (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => pself (mvl) x (_)) H1)) ((ap) (fun x => pself (mvl) (_) x) H2).

Definition congr_TTop { mvl : nat } : TTop (mvl) = TTop (mvl) :=
  eq_refl.

Definition congr_TBot { mvl : nat } : TBot (mvl) = TBot (mvl) :=
  eq_refl.

Definition congr_TAnd { mvl : nat } { s0 : ty (mvl) } { s1 : ty (mvl) } { t0 : ty (mvl) } { t1 : ty (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : TAnd (mvl) s0 s1 = TAnd (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TAnd (mvl) x (_)) H1)) ((ap) (fun x => TAnd (mvl) (_) x) H2).

Definition congr_TOr { mvl : nat } { s0 : ty (mvl) } { s1 : ty (mvl) } { t0 : ty (mvl) } { t1 : ty (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : TOr (mvl) s0 s1 = TOr (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TOr (mvl) x (_)) H1)) ((ap) (fun x => TOr (mvl) (_) x) H2).

Definition congr_TLater { mvl : nat } { s0 : ty (mvl) } { t0 : ty (mvl) } (H1 : s0 = t0) : TLater (mvl) s0 = TLater (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => TLater (mvl) x) H1).

Definition congr_TAll { mvl : nat } { s0 : ty (mvl) } { s1 : ty ((S) mvl) } { t0 : ty (mvl) } { t1 : ty ((S) mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : TAll (mvl) s0 s1 = TAll (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TAll (mvl) x (_)) H1)) ((ap) (fun x => TAll (mvl) (_) x) H2).

Definition congr_TMu { mvl : nat } { s0 : ty ((S) mvl) } { t0 : ty ((S) mvl) } (H1 : s0 = t0) : TMu (mvl) s0 = TMu (mvl) t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => TMu (mvl) x) H1).

Definition congr_TVMem { mvl : nat } { s0 : label  } { s1 : ty (mvl) } { t0 : label  } { t1 : ty (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : TVMem (mvl) s0 s1 = TVMem (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TVMem (mvl) x (_)) H1)) ((ap) (fun x => TVMem (mvl) (_) x) H2).

Definition congr_TTMem { mvl : nat } { s0 : label  } { s1 : ty (mvl) } { s2 : ty (mvl) } { t0 : label  } { t1 : ty (mvl) } { t2 : ty (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : TTMem (mvl) s0 s1 s2 = TTMem (mvl) t0 t1 t2 :=
  (eq_trans) ((eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TTMem (mvl) x (_) (_)) H1)) ((ap) (fun x => TTMem (mvl) (_) x (_)) H2)) ((ap) (fun x => TTMem (mvl) (_) (_) x) H3).

Definition congr_TSel { mvl : nat } { s0 : path (mvl) } { s1 : label  } { t0 : path (mvl) } { t1 : label  } (H1 : s0 = t0) (H2 : s1 = t1) : TSel (mvl) s0 s1 = TSel (mvl) t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TSel (mvl) x (_)) H1)) ((ap) (fun x => TSel (mvl) (_) x) H2).

Definition congr_TSelA { mvl : nat } { s0 : path (mvl) } { s1 : label  } { s2 : ty (mvl) } { s3 : ty (mvl) } { t0 : path (mvl) } { t1 : label  } { t2 : ty (mvl) } { t3 : ty (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : TSelA (mvl) s0 s1 s2 s3 = TSelA (mvl) t0 t1 t2 t3 :=
  (eq_trans) ((eq_trans) ((eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => TSelA (mvl) x (_) (_) (_)) H1)) ((ap) (fun x => TSelA (mvl) (_) x (_) (_)) H2)) ((ap) (fun x => TSelA (mvl) (_) (_) x (_)) H3)) ((ap) (fun x => TSelA (mvl) (_) (_) (_) x) H4).

Definition upRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : _ :=
  (up_ren) xi.

Fixpoint ren_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : tm (mvl)) : _ :=
    match s with
    | tv (_) s0 => tv (nvl) ((ren_vl xivl) s0)
    | tapp (_) s0 s1 => tapp (nvl) ((ren_tm xivl) s0) ((ren_tm xivl) s1)
    | tproj (_) s0 s1 => tproj (nvl) ((ren_tm xivl) s0) ((fun x => x) s1)
    end
 with ren_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : vl (mvl)) : _ :=
    match s with
    | var_vl (_) s => (var_vl (nvl)) (xivl s)
    | vabs (_) s0 => vabs (nvl) ((ren_tm (upRen_vl_vl xivl)) s0)
    | vobj (_) s0 => vobj (nvl) ((ren_dms (upRen_vl_vl xivl)) s0)
    end
 with ren_vls { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : vls (mvl)) : _ :=
    match s with
    | vnil (_)  => vnil (nvl)
    | vcons (_) s0 s1 => vcons (nvl) ((ren_vl xivl) s0) ((ren_vls xivl) s1)
    end
 with ren_dms { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : dms (mvl)) : _ :=
    match s with
    | dnil (_)  => dnil (nvl)
    | dcons (_) s0 s1 s2 => dcons (nvl) ((fun x => x) s0) ((ren_dm xivl) s1) ((ren_dms xivl) s2)
    end
 with ren_dm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : dm (mvl)) : _ :=
    match s with
    | dtysyn (_) s0 => dtysyn (nvl) ((ren_ty xivl) s0)
    | dtysem (_) s0 s1 => dtysem (nvl) ((fun x => x) s0) ((ren_vls xivl) s1)
    | dvl (_) s0 => dvl (nvl) ((ren_vl xivl) s0)
    end
 with ren_path { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : path (mvl)) : _ :=
    match s with
    | pv (_) s0 => pv (nvl) ((ren_vl xivl) s0)
    | pself (_) s0 s1 => pself (nvl) ((ren_path xivl) s0) ((fun x => x) s1)
    end
 with ren_ty { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : ty (mvl)) : _ :=
    match s with
    | TTop (_)  => TTop (nvl)
    | TBot (_)  => TBot (nvl)
    | TAnd (_) s0 s1 => TAnd (nvl) ((ren_ty xivl) s0) ((ren_ty xivl) s1)
    | TOr (_) s0 s1 => TOr (nvl) ((ren_ty xivl) s0) ((ren_ty xivl) s1)
    | TLater (_) s0 => TLater (nvl) ((ren_ty xivl) s0)
    | TAll (_) s0 s1 => TAll (nvl) ((ren_ty xivl) s0) ((ren_ty (upRen_vl_vl xivl)) s1)
    | TMu (_) s0 => TMu (nvl) ((ren_ty (upRen_vl_vl xivl)) s0)
    | TVMem (_) s0 s1 => TVMem (nvl) ((fun x => x) s0) ((ren_ty xivl) s1)
    | TTMem (_) s0 s1 s2 => TTMem (nvl) ((fun x => x) s0) ((ren_ty xivl) s1) ((ren_ty xivl) s2)
    | TSel (_) s0 s1 => TSel (nvl) ((ren_path xivl) s0) ((fun x => x) s1)
    | TSelA (_) s0 s1 s2 s3 => TSelA (nvl) ((ren_path xivl) s0) ((fun x => x) s1) ((ren_ty xivl) s2) ((ren_ty xivl) s3)
    end.

Definition up_vl_vl { m : nat } { nvl : nat } (sigma : (fin) (m) -> vl (nvl)) : _ :=
  (scons) ((var_vl ((S) nvl)) (var_zero)) ((funcomp) (ren_vl (shift)) sigma).

Fixpoint subst_tm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : tm (mvl)) : _ :=
    match s with
    | tv (_) s0 => tv (nvl) ((subst_vl sigmavl) s0)
    | tapp (_) s0 s1 => tapp (nvl) ((subst_tm sigmavl) s0) ((subst_tm sigmavl) s1)
    | tproj (_) s0 s1 => tproj (nvl) ((subst_tm sigmavl) s0) ((fun x => x) s1)
    end
 with subst_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : vl (mvl)) : _ :=
    match s with
    | var_vl (_) s => sigmavl s
    | vabs (_) s0 => vabs (nvl) ((subst_tm (up_vl_vl sigmavl)) s0)
    | vobj (_) s0 => vobj (nvl) ((subst_dms (up_vl_vl sigmavl)) s0)
    end
 with subst_vls { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : vls (mvl)) : _ :=
    match s with
    | vnil (_)  => vnil (nvl)
    | vcons (_) s0 s1 => vcons (nvl) ((subst_vl sigmavl) s0) ((subst_vls sigmavl) s1)
    end
 with subst_dms { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : dms (mvl)) : _ :=
    match s with
    | dnil (_)  => dnil (nvl)
    | dcons (_) s0 s1 s2 => dcons (nvl) ((fun x => x) s0) ((subst_dm sigmavl) s1) ((subst_dms sigmavl) s2)
    end
 with subst_dm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : dm (mvl)) : _ :=
    match s with
    | dtysyn (_) s0 => dtysyn (nvl) ((subst_ty sigmavl) s0)
    | dtysem (_) s0 s1 => dtysem (nvl) ((fun x => x) s0) ((subst_vls sigmavl) s1)
    | dvl (_) s0 => dvl (nvl) ((subst_vl sigmavl) s0)
    end
 with subst_path { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : path (mvl)) : _ :=
    match s with
    | pv (_) s0 => pv (nvl) ((subst_vl sigmavl) s0)
    | pself (_) s0 s1 => pself (nvl) ((subst_path sigmavl) s0) ((fun x => x) s1)
    end
 with subst_ty { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : ty (mvl)) : _ :=
    match s with
    | TTop (_)  => TTop (nvl)
    | TBot (_)  => TBot (nvl)
    | TAnd (_) s0 s1 => TAnd (nvl) ((subst_ty sigmavl) s0) ((subst_ty sigmavl) s1)
    | TOr (_) s0 s1 => TOr (nvl) ((subst_ty sigmavl) s0) ((subst_ty sigmavl) s1)
    | TLater (_) s0 => TLater (nvl) ((subst_ty sigmavl) s0)
    | TAll (_) s0 s1 => TAll (nvl) ((subst_ty sigmavl) s0) ((subst_ty (up_vl_vl sigmavl)) s1)
    | TMu (_) s0 => TMu (nvl) ((subst_ty (up_vl_vl sigmavl)) s0)
    | TVMem (_) s0 s1 => TVMem (nvl) ((fun x => x) s0) ((subst_ty sigmavl) s1)
    | TTMem (_) s0 s1 s2 => TTMem (nvl) ((fun x => x) s0) ((subst_ty sigmavl) s1) ((subst_ty sigmavl) s2)
    | TSel (_) s0 s1 => TSel (nvl) ((subst_path sigmavl) s0) ((fun x => x) s1)
    | TSelA (_) s0 s1 s2 s3 => TSelA (nvl) ((subst_path sigmavl) s0) ((fun x => x) s1) ((subst_ty sigmavl) s2) ((subst_ty sigmavl) s3)
    end.

Definition upId_vl_vl { mvl : nat } (sigma : (fin) (mvl) -> vl (mvl)) (Eq : forall x, sigma x = (var_vl (mvl)) x) : forall x, (up_vl_vl sigma) x = (var_vl ((S) mvl)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Fixpoint idSubst_tm { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : tm (mvl)) : subst_tm sigmavl s = s :=
    match s with
    | tv (_) s0 => congr_tv ((idSubst_vl sigmavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((idSubst_tm sigmavl Eqvl) s0) ((idSubst_tm sigmavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((idSubst_tm sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with idSubst_vl { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : vl (mvl)) : subst_vl sigmavl s = s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((idSubst_tm (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((idSubst_dms (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    end
 with idSubst_vls { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : vls (mvl)) : subst_vls sigmavl s = s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((idSubst_vl sigmavl Eqvl) s0) ((idSubst_vls sigmavl Eqvl) s1)
    end
 with idSubst_dms { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : dms (mvl)) : subst_dms sigmavl s = s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((idSubst_dm sigmavl Eqvl) s1) ((idSubst_dms sigmavl Eqvl) s2)
    end
 with idSubst_dm { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : dm (mvl)) : subst_dm sigmavl s = s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((idSubst_ty sigmavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((idSubst_vls sigmavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((idSubst_vl sigmavl Eqvl) s0)
    end
 with idSubst_path { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : path (mvl)) : subst_path sigmavl s = s :=
    match s with
    | pv (_) s0 => congr_pv ((idSubst_vl sigmavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with idSubst_ty { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : ty (mvl)) : subst_ty sigmavl s = s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((idSubst_ty sigmavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((idSubst_ty sigmavl Eqvl) s0) ((idSubst_ty (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((idSubst_ty (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((idSubst_ty sigmavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((idSubst_ty sigmavl Eqvl) s1) ((idSubst_ty sigmavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((idSubst_path sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((idSubst_ty sigmavl Eqvl) s2) ((idSubst_ty sigmavl Eqvl) s3)
    end.

Definition upExtRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_vl xi) x = (upRen_vl_vl zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Fixpoint extRen_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : tm (mvl)) : ren_tm xivl s = ren_tm zetavl s :=
    match s with
    | tv (_) s0 => congr_tv ((extRen_vl xivl zetavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((extRen_tm xivl zetavl Eqvl) s0) ((extRen_tm xivl zetavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((extRen_tm xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with extRen_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : vl (mvl)) : ren_vl xivl s = ren_vl zetavl s :=
    match s with
    | var_vl (_) s => (ap) (var_vl (nvl)) (Eqvl s)
    | vabs (_) s0 => congr_vabs ((extRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((extRen_dms (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    end
 with extRen_vls { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : vls (mvl)) : ren_vls xivl s = ren_vls zetavl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((extRen_vl xivl zetavl Eqvl) s0) ((extRen_vls xivl zetavl Eqvl) s1)
    end
 with extRen_dms { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : dms (mvl)) : ren_dms xivl s = ren_dms zetavl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((extRen_dm xivl zetavl Eqvl) s1) ((extRen_dms xivl zetavl Eqvl) s2)
    end
 with extRen_dm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : dm (mvl)) : ren_dm xivl s = ren_dm zetavl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((extRen_ty xivl zetavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((extRen_vls xivl zetavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((extRen_vl xivl zetavl Eqvl) s0)
    end
 with extRen_path { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : path (mvl)) : ren_path xivl s = ren_path zetavl s :=
    match s with
    | pv (_) s0 => congr_pv ((extRen_vl xivl zetavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with extRen_ty { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : ty (mvl)) : ren_ty xivl s = ren_ty zetavl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((extRen_ty xivl zetavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((extRen_ty xivl zetavl Eqvl) s0) ((extRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((extRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((extRen_ty xivl zetavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((extRen_ty xivl zetavl Eqvl) s1) ((extRen_ty xivl zetavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((extRen_path xivl zetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((extRen_ty xivl zetavl Eqvl) s2) ((extRen_ty xivl zetavl Eqvl) s3)
    end.

Definition upExt_vl_vl { m : nat } { nvl : nat } (sigma : (fin) (m) -> vl (nvl)) (tau : (fin) (m) -> vl (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_vl sigma) x = (up_vl_vl tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Fixpoint ext_tm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : tm (mvl)) : subst_tm sigmavl s = subst_tm tauvl s :=
    match s with
    | tv (_) s0 => congr_tv ((ext_vl sigmavl tauvl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((ext_tm sigmavl tauvl Eqvl) s0) ((ext_tm sigmavl tauvl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((ext_tm sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with ext_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : vl (mvl)) : subst_vl sigmavl s = subst_vl tauvl s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((ext_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((ext_dms (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    end
 with ext_vls { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : vls (mvl)) : subst_vls sigmavl s = subst_vls tauvl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((ext_vl sigmavl tauvl Eqvl) s0) ((ext_vls sigmavl tauvl Eqvl) s1)
    end
 with ext_dms { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : dms (mvl)) : subst_dms sigmavl s = subst_dms tauvl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((ext_dm sigmavl tauvl Eqvl) s1) ((ext_dms sigmavl tauvl Eqvl) s2)
    end
 with ext_dm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : dm (mvl)) : subst_dm sigmavl s = subst_dm tauvl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((ext_ty sigmavl tauvl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((ext_vls sigmavl tauvl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((ext_vl sigmavl tauvl Eqvl) s0)
    end
 with ext_path { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : path (mvl)) : subst_path sigmavl s = subst_path tauvl s :=
    match s with
    | pv (_) s0 => congr_pv ((ext_vl sigmavl tauvl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with ext_ty { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : ty (mvl)) : subst_ty sigmavl s = subst_ty tauvl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((ext_ty sigmavl tauvl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((ext_ty sigmavl tauvl Eqvl) s0) ((ext_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((ext_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((ext_ty sigmavl tauvl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((ext_ty sigmavl tauvl Eqvl) s1) ((ext_ty sigmavl tauvl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((ext_path sigmavl tauvl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((ext_ty sigmavl tauvl Eqvl) s2) ((ext_ty sigmavl tauvl Eqvl) s3)
    end.

Fixpoint compRenRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : tm (mvl)) : ren_tm zetavl (ren_tm xivl s) = ren_tm rhovl s :=
    match s with
    | tv (_) s0 => congr_tv ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((compRenRen_tm xivl zetavl rhovl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : vl (mvl)) : ren_vl zetavl (ren_vl xivl s) = ren_vl rhovl s :=
    match s with
    | var_vl (_) s => (ap) (var_vl (lvl)) (Eqvl s)
    | vabs (_) s0 => congr_vabs ((compRenRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((compRenRen_dms (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    end
 with compRenRen_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : vls (mvl)) : ren_vls zetavl (ren_vls xivl s) = ren_vls rhovl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((compRenRen_vl xivl zetavl rhovl Eqvl) s0) ((compRenRen_vls xivl zetavl rhovl Eqvl) s1)
    end
 with compRenRen_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : dms (mvl)) : ren_dms zetavl (ren_dms xivl s) = ren_dms rhovl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((compRenRen_dm xivl zetavl rhovl Eqvl) s1) ((compRenRen_dms xivl zetavl rhovl Eqvl) s2)
    end
 with compRenRen_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : dm (mvl)) : ren_dm zetavl (ren_dm xivl s) = ren_dm rhovl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((compRenRen_ty xivl zetavl rhovl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((compRenRen_vls xivl zetavl rhovl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    end
 with compRenRen_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : path (mvl)) : ren_path zetavl (ren_path xivl s) = ren_path rhovl s :=
    match s with
    | pv (_) s0 => congr_pv ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenRen_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : ty (mvl)) : ren_ty zetavl (ren_ty xivl s) = ren_ty rhovl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((compRenRen_ty xivl zetavl rhovl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((compRenRen_ty xivl zetavl rhovl Eqvl) s0) ((compRenRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((compRenRen_ty (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compRenRen_ty xivl zetavl rhovl Eqvl) s1) ((compRenRen_ty xivl zetavl rhovl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((compRenRen_path xivl zetavl rhovl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compRenRen_ty xivl zetavl rhovl Eqvl) s2) ((compRenRen_ty xivl zetavl rhovl Eqvl) s3)
    end.

Definition up_ren_subst_vl_vl { k : nat } { l : nat } { mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> vl (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_vl tau) (upRen_vl_vl xi)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Fixpoint compRenSubst_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : tm (mvl)) : subst_tm tauvl (ren_tm xivl s) = subst_tm thetavl s :=
    match s with
    | tv (_) s0 => congr_tv ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((compRenSubst_tm xivl tauvl thetavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenSubst_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : vl (mvl)) : subst_vl tauvl (ren_vl xivl s) = subst_vl thetavl s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((compRenSubst_tm (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((compRenSubst_dms (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compRenSubst_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : vls (mvl)) : subst_vls tauvl (ren_vls xivl s) = subst_vls thetavl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0) ((compRenSubst_vls xivl tauvl thetavl Eqvl) s1)
    end
 with compRenSubst_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : dms (mvl)) : subst_dms tauvl (ren_dms xivl s) = subst_dms thetavl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((compRenSubst_dm xivl tauvl thetavl Eqvl) s1) ((compRenSubst_dms xivl tauvl thetavl Eqvl) s2)
    end
 with compRenSubst_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : dm (mvl)) : subst_dm tauvl (ren_dm xivl s) = subst_dm thetavl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((compRenSubst_vls xivl tauvl thetavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    end
 with compRenSubst_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : path (mvl)) : subst_path tauvl (ren_path xivl s) = subst_path thetavl s :=
    match s with
    | pv (_) s0 => congr_pv ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compRenSubst_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : ty (mvl)) : subst_ty tauvl (ren_ty xivl s) = subst_ty thetavl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((compRenSubst_ty xivl tauvl thetavl Eqvl) s0) ((compRenSubst_ty (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((compRenSubst_ty (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s1) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((compRenSubst_path xivl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s2) ((compRenSubst_ty xivl tauvl thetavl Eqvl) s3)
    end.

Definition up_subst_ren_vl_vl { k : nat } { lvl : nat } { mvl : nat } (sigma : (fin) (k) -> vl (lvl)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) (ren_vl zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_vl_vl zetavl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_vl (shift) (upRen_vl_vl zetavl) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetavl (shift) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Fixpoint compSubstRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : tm (mvl)) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s with
    | tv (_) s0 => congr_tv ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : vl (mvl)) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((compSubstRen_tm (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((compSubstRen_dms (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compSubstRen_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : vls (mvl)) : ren_vls zetavl (subst_vls sigmavl s) = subst_vls thetavl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_vls sigmavl zetavl thetavl Eqvl) s1)
    end
 with compSubstRen_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : dms (mvl)) : ren_dms zetavl (subst_dms sigmavl s) = subst_dms thetavl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((compSubstRen_dm sigmavl zetavl thetavl Eqvl) s1) ((compSubstRen_dms sigmavl zetavl thetavl Eqvl) s2)
    end
 with compSubstRen_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : dm (mvl)) : ren_dm zetavl (subst_dm sigmavl s) = subst_dm thetavl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((compSubstRen_vls sigmavl zetavl thetavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    end
 with compSubstRen_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : path (mvl)) : ren_path zetavl (subst_path sigmavl s) = subst_path thetavl s :=
    match s with
    | pv (_) s0 => congr_pv ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstRen_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : ty (mvl)) : ren_ty zetavl (subst_ty sigmavl s) = subst_ty thetavl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_ty (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((compSubstRen_ty (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s1) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((compSubstRen_path sigmavl zetavl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s2) ((compSubstRen_ty sigmavl zetavl thetavl Eqvl) s3)
    end.

Definition up_subst_subst_vl_vl { k : nat } { lvl : nat } { mvl : nat } (sigma : (fin) (k) -> vl (lvl)) (tauvl : (fin) (lvl) -> vl (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) (subst_vl tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_vl_vl tauvl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_vl (shift) (up_vl_vl tauvl) ((funcomp) (up_vl_vl tauvl) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauvl (shift) ((funcomp) (ren_vl (shift)) tauvl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : tm (mvl)) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s with
    | tv (_) s0 => congr_tv ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstSubst_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : vl (mvl)) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((compSubstSubst_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((compSubstSubst_dms (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    end
 with compSubstSubst_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : vls (mvl)) : subst_vls tauvl (subst_vls sigmavl s) = subst_vls thetavl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_vls sigmavl tauvl thetavl Eqvl) s1)
    end
 with compSubstSubst_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : dms (mvl)) : subst_dms tauvl (subst_dms sigmavl s) = subst_dms thetavl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((compSubstSubst_dm sigmavl tauvl thetavl Eqvl) s1) ((compSubstSubst_dms sigmavl tauvl thetavl Eqvl) s2)
    end
 with compSubstSubst_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : dm (mvl)) : subst_dm tauvl (subst_dm sigmavl s) = subst_dm thetavl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((compSubstSubst_vls sigmavl tauvl thetavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    end
 with compSubstSubst_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : path (mvl)) : subst_path tauvl (subst_path sigmavl s) = subst_path thetavl s :=
    match s with
    | pv (_) s0 => congr_pv ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with compSubstSubst_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : ty (mvl)) : subst_ty tauvl (subst_ty sigmavl s) = subst_ty thetavl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((compSubstSubst_ty (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s1) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((compSubstSubst_path sigmavl tauvl thetavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s2) ((compSubstSubst_ty sigmavl tauvl thetavl Eqvl) s3)
    end.

Definition rinstInst_up_vl_vl { m : nat } { nvl : nat } (xi : (fin) (m) -> (fin) (nvl)) (sigma : (fin) (m) -> vl (nvl)) (Eq : forall x, ((funcomp) (var_vl (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_vl ((S) nvl)) (upRen_vl_vl xi)) x = (up_vl_vl sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Fixpoint rinst_inst_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : tm (mvl)) : ren_tm xivl s = subst_tm sigmavl s :=
    match s with
    | tv (_) s0 => congr_tv ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | tapp (_) s0 s1 => congr_tapp ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((rinst_inst_tm xivl sigmavl Eqvl) s1)
    | tproj (_) s0 s1 => congr_tproj ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with rinst_inst_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : vl (mvl)) : ren_vl xivl s = subst_vl sigmavl s :=
    match s with
    | var_vl (_) s => Eqvl s
    | vabs (_) s0 => congr_vabs ((rinst_inst_tm (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    | vobj (_) s0 => congr_vobj ((rinst_inst_dms (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    end
 with rinst_inst_vls { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : vls (mvl)) : ren_vls xivl s = subst_vls sigmavl s :=
    match s with
    | vnil (_)  => congr_vnil
    | vcons (_) s0 s1 => congr_vcons ((rinst_inst_vl xivl sigmavl Eqvl) s0) ((rinst_inst_vls xivl sigmavl Eqvl) s1)
    end
 with rinst_inst_dms { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : dms (mvl)) : ren_dms xivl s = subst_dms sigmavl s :=
    match s with
    | dnil (_)  => congr_dnil
    | dcons (_) s0 s1 s2 => congr_dcons ((fun x => (eq_refl) x) s0) ((rinst_inst_dm xivl sigmavl Eqvl) s1) ((rinst_inst_dms xivl sigmavl Eqvl) s2)
    end
 with rinst_inst_dm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : dm (mvl)) : ren_dm xivl s = subst_dm sigmavl s :=
    match s with
    | dtysyn (_) s0 => congr_dtysyn ((rinst_inst_ty xivl sigmavl Eqvl) s0)
    | dtysem (_) s0 s1 => congr_dtysem ((fun x => (eq_refl) x) s0) ((rinst_inst_vls xivl sigmavl Eqvl) s1)
    | dvl (_) s0 => congr_dvl ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    end
 with rinst_inst_path { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : path (mvl)) : ren_path xivl s = subst_path sigmavl s :=
    match s with
    | pv (_) s0 => congr_pv ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | pself (_) s0 s1 => congr_pself ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    end
 with rinst_inst_ty { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : ty (mvl)) : ren_ty xivl s = subst_ty sigmavl s :=
    match s with
    | TTop (_)  => congr_TTop
    | TBot (_)  => congr_TBot
    | TAnd (_) s0 s1 => congr_TAnd ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TOr (_) s0 s1 => congr_TOr ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TLater (_) s0 => congr_TLater ((rinst_inst_ty xivl sigmavl Eqvl) s0)
    | TAll (_) s0 s1 => congr_TAll ((rinst_inst_ty xivl sigmavl Eqvl) s0) ((rinst_inst_ty (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s1)
    | TMu (_) s0 => congr_TMu ((rinst_inst_ty (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    | TVMem (_) s0 s1 => congr_TVMem ((fun x => (eq_refl) x) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1)
    | TTMem (_) s0 s1 s2 => congr_TTMem ((fun x => (eq_refl) x) s0) ((rinst_inst_ty xivl sigmavl Eqvl) s1) ((rinst_inst_ty xivl sigmavl Eqvl) s2)
    | TSel (_) s0 s1 => congr_TSel ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1)
    | TSelA (_) s0 s1 s2 s3 => congr_TSelA ((rinst_inst_path xivl sigmavl Eqvl) s0) ((fun x => (eq_refl) x) s1) ((rinst_inst_ty xivl sigmavl Eqvl) s2) ((rinst_inst_ty xivl sigmavl Eqvl) s3)
    end.

Lemma rinstInst_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_tm xivl = subst_tm ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_vl xivl = subst_vl ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_vl xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_vls { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_vls xivl = subst_vls ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_vls xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_dms { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_dms xivl = subst_dms ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_dms xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_dm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_dm xivl = subst_dm ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_dm xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_path { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_path xivl = subst_path ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_path xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_ty { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_ty xivl = subst_ty ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ty xivl (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mvl : nat } : subst_tm (var_vl (mvl)) = (@id) (tm (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_vl (mvl)) (fun n => eq_refl) (((@id) (tm (mvl))) x))). Qed.

Lemma instId_vl { mvl : nat } : subst_vl (var_vl (mvl)) = (@id) (vl (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_vl (var_vl (mvl)) (fun n => eq_refl) (((@id) (vl (mvl))) x))). Qed.

Lemma instId_vls { mvl : nat } : subst_vls (var_vl (mvl)) = (@id) (vls (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_vls (var_vl (mvl)) (fun n => eq_refl) (((@id) (vls (mvl))) x))). Qed.

Lemma instId_dms { mvl : nat } : subst_dms (var_vl (mvl)) = (@id) (dms (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_dms (var_vl (mvl)) (fun n => eq_refl) (((@id) (dms (mvl))) x))). Qed.

Lemma instId_dm { mvl : nat } : subst_dm (var_vl (mvl)) = (@id) (dm (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_dm (var_vl (mvl)) (fun n => eq_refl) (((@id) (dm (mvl))) x))). Qed.

Lemma instId_path { mvl : nat } : subst_path (var_vl (mvl)) = (@id) (path (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_path (var_vl (mvl)) (fun n => eq_refl) (((@id) (path (mvl))) x))). Qed.

Lemma instId_ty { mvl : nat } : subst_ty (var_vl (mvl)) = (@id) (ty (mvl)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ty (var_vl (mvl)) (fun n => eq_refl) (((@id) (ty (mvl))) x))). Qed.

Lemma rinstId_tm { mvl : nat } : ren_tm ((@id) (_)) = (@id) (tm (mvl)) .
Proof. exact ((eq_trans) (rinstInst_tm ((@id) (_))) instId_tm). Qed.

Lemma rinstId_vl { mvl : nat } : ren_vl ((@id) (_)) = (@id) (vl (mvl)) .
Proof. exact ((eq_trans) (rinstInst_vl ((@id) (_))) instId_vl). Qed.

Lemma rinstId_vls { mvl : nat } : ren_vls ((@id) (_)) = (@id) (vls (mvl)) .
Proof. exact ((eq_trans) (rinstInst_vls ((@id) (_))) instId_vls). Qed.

Lemma rinstId_dms { mvl : nat } : ren_dms ((@id) (_)) = (@id) (dms (mvl)) .
Proof. exact ((eq_trans) (rinstInst_dms ((@id) (_))) instId_dms). Qed.

Lemma rinstId_dm { mvl : nat } : ren_dm ((@id) (_)) = (@id) (dm (mvl)) .
Proof. exact ((eq_trans) (rinstInst_dm ((@id) (_))) instId_dm). Qed.

Lemma rinstId_path { mvl : nat } : ren_path ((@id) (_)) = (@id) (path (mvl)) .
Proof. exact ((eq_trans) (rinstInst_path ((@id) (_))) instId_path). Qed.

Lemma rinstId_ty { mvl : nat } : ren_ty ((@id) (_)) = (@id) (ty (mvl)) .
Proof. exact ((eq_trans) (rinstInst_ty ((@id) (_))) instId_ty). Qed.

Lemma varL_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) : (funcomp) (subst_vl sigmavl) (var_vl (mvl)) = sigmavl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : (funcomp) (ren_vl xivl) (var_vl (mvl)) = (funcomp) (var_vl (nvl)) xivl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : tm (mvl)) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_tm sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vl (mvl)) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_vl sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vls (mvl)) : subst_vls tauvl (subst_vls sigmavl s) = subst_vls ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_vls sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : dms (mvl)) : subst_dms tauvl (subst_dms sigmavl s) = subst_dms ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_dms sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : dm (mvl)) : subst_dm tauvl (subst_dm sigmavl s) = subst_dm ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_dm sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : path (mvl)) : subst_path tauvl (subst_path sigmavl s) = subst_path ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_path sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : ty (mvl)) : subst_ty tauvl (subst_ty sigmavl s) = subst_ty ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_ty sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_tm tauvl) (subst_tm sigmavl) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmavl tauvl n)). Qed.

Lemma compComp'_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vl tauvl) (subst_vl sigmavl) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_vl sigmavl tauvl n)). Qed.

Lemma compComp'_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vls tauvl) (subst_vls sigmavl) = subst_vls ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_vls sigmavl tauvl n)). Qed.

Lemma compComp'_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_dms tauvl) (subst_dms sigmavl) = subst_dms ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_dms sigmavl tauvl n)). Qed.

Lemma compComp'_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_dm tauvl) (subst_dm sigmavl) = subst_dm ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_dm sigmavl tauvl n)). Qed.

Lemma compComp'_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_path tauvl) (subst_path sigmavl) = subst_path ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_path sigmavl tauvl n)). Qed.

Lemma compComp'_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_ty tauvl) (subst_ty sigmavl) = subst_ty ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ty sigmavl tauvl n)). Qed.

Lemma compRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mvl)) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_tm sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mvl)) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_vl sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vls (mvl)) : ren_vls zetavl (subst_vls sigmavl s) = subst_vls ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_vls sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : dms (mvl)) : ren_dms zetavl (subst_dms sigmavl s) = subst_dms ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_dms sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : dm (mvl)) : ren_dm zetavl (subst_dm sigmavl s) = subst_dm ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_dm sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : path (mvl)) : ren_path zetavl (subst_path sigmavl s) = subst_path ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_path sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : ty (mvl)) : ren_ty zetavl (subst_ty sigmavl s) = subst_ty ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_ty sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetavl) (subst_tm sigmavl) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmavl zetavl n)). Qed.

Lemma compRen'_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetavl) (subst_vl sigmavl) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_vl sigmavl zetavl n)). Qed.

Lemma compRen'_vls { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vls zetavl) (subst_vls sigmavl) = subst_vls ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_vls sigmavl zetavl n)). Qed.

Lemma compRen'_dms { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_dms zetavl) (subst_dms sigmavl) = subst_dms ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_dms sigmavl zetavl n)). Qed.

Lemma compRen'_dm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_dm zetavl) (subst_dm sigmavl) = subst_dm ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_dm sigmavl zetavl n)). Qed.

Lemma compRen'_path { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_path zetavl) (subst_path sigmavl) = subst_path ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_path sigmavl zetavl n)). Qed.

Lemma compRen'_ty { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_ty zetavl) (subst_ty sigmavl) = subst_ty ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ty sigmavl zetavl n)). Qed.

Lemma renComp_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : tm (mvl)) : subst_tm tauvl (ren_tm xivl s) = subst_tm ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_tm xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vl (mvl)) : subst_vl tauvl (ren_vl xivl s) = subst_vl ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_vl xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vls (mvl)) : subst_vls tauvl (ren_vls xivl s) = subst_vls ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_vls xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : dms (mvl)) : subst_dms tauvl (ren_dms xivl s) = subst_dms ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_dms xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : dm (mvl)) : subst_dm tauvl (ren_dm xivl s) = subst_dm ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_dm xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : path (mvl)) : subst_path tauvl (ren_path xivl s) = subst_path ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_path xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : ty (mvl)) : subst_ty tauvl (ren_ty xivl s) = subst_ty ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_ty xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_tm tauvl) (ren_tm xivl) = subst_tm ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xivl tauvl n)). Qed.

Lemma renComp'_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vl tauvl) (ren_vl xivl) = subst_vl ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_vl xivl tauvl n)). Qed.

Lemma renComp'_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vls tauvl) (ren_vls xivl) = subst_vls ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_vls xivl tauvl n)). Qed.

Lemma renComp'_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_dms tauvl) (ren_dms xivl) = subst_dms ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_dms xivl tauvl n)). Qed.

Lemma renComp'_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_dm tauvl) (ren_dm xivl) = subst_dm ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_dm xivl tauvl n)). Qed.

Lemma renComp'_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_path tauvl) (ren_path xivl) = subst_path ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_path xivl tauvl n)). Qed.

Lemma renComp'_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_ty tauvl) (ren_ty xivl) = subst_ty ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ty xivl tauvl n)). Qed.

Lemma renRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mvl)) : ren_tm zetavl (ren_tm xivl s) = ren_tm ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_tm xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mvl)) : ren_vl zetavl (ren_vl xivl s) = ren_vl ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_vl xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vls (mvl)) : ren_vls zetavl (ren_vls xivl s) = ren_vls ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_vls xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : dms (mvl)) : ren_dms zetavl (ren_dms xivl s) = ren_dms ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_dms xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : dm (mvl)) : ren_dm zetavl (ren_dm xivl s) = ren_dm ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_dm xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : path (mvl)) : ren_path zetavl (ren_path xivl s) = ren_path ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_path xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : ty (mvl)) : ren_ty zetavl (ren_ty xivl s) = ren_ty ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_ty xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetavl) (ren_tm xivl) = ren_tm ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xivl zetavl n)). Qed.

Lemma renRen'_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetavl) (ren_vl xivl) = ren_vl ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_vl xivl zetavl n)). Qed.

Lemma renRen'_vls { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vls zetavl) (ren_vls xivl) = ren_vls ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_vls xivl zetavl n)). Qed.

Lemma renRen'_dms { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_dms zetavl) (ren_dms xivl) = ren_dms ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_dms xivl zetavl n)). Qed.

Lemma renRen'_dm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_dm zetavl) (ren_dm xivl) = ren_dm ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_dm xivl zetavl n)). Qed.

Lemma renRen'_path { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_path zetavl) (ren_path xivl) = ren_path ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_path xivl zetavl n)). Qed.

Lemma renRen'_ty { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_ty zetavl) (ren_ty xivl) = ren_ty ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ty xivl zetavl n)). Qed.

Arguments tv {nvl}.

Arguments tapp {nvl}.

Arguments tproj {nvl}.

Arguments var_vl {nvl}.

Arguments vabs {nvl}.

Arguments vobj {nvl}.

Arguments vnil {nvl}.

Arguments vcons {nvl}.

Arguments dnil {nvl}.

Arguments dcons {nvl}.

Arguments dtysyn {nvl}.

Arguments dtysem {nvl}.

Arguments dvl {nvl}.

Arguments pv {nvl}.

Arguments pself {nvl}.

Arguments TTop {nvl}.

Arguments TBot {nvl}.

Arguments TAnd {nvl}.

Arguments TOr {nvl}.

Arguments TLater {nvl}.

Arguments TAll {nvl}.

Arguments TMu {nvl}.

Arguments TVMem {nvl}.

Arguments TTMem {nvl}.

Arguments TSel {nvl}.

Arguments TSelA {nvl}.

Instance Subst_tm { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (tm (mvl)) (tm (nvl)) := @subst_tm (mvl) (nvl) .

Instance Subst_vl { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (vl (mvl)) (vl (nvl)) := @subst_vl (mvl) (nvl) .

Instance Subst_vls { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (vls (mvl)) (vls (nvl)) := @subst_vls (mvl) (nvl) .

Instance Subst_dms { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (dms (mvl)) (dms (nvl)) := @subst_dms (mvl) (nvl) .

Instance Subst_dm { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (dm (mvl)) (dm (nvl)) := @subst_dm (mvl) (nvl) .

Instance Subst_path { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (path (mvl)) (path (nvl)) := @subst_path (mvl) (nvl) .

Instance Subst_ty { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (ty (mvl)) (ty (nvl)) := @subst_ty (mvl) (nvl) .

Instance Ren_tm { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (tm (mvl)) (tm (nvl)) := @ren_tm (mvl) (nvl) .

Instance Ren_vl { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (vl (mvl)) (vl (nvl)) := @ren_vl (mvl) (nvl) .

Instance Ren_vls { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (vls (mvl)) (vls (nvl)) := @ren_vls (mvl) (nvl) .

Instance Ren_dms { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (dms (mvl)) (dms (nvl)) := @ren_dms (mvl) (nvl) .

Instance Ren_dm { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (dm (mvl)) (dm (nvl)) := @ren_dm (mvl) (nvl) .

Instance Ren_path { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (path (mvl)) (path (nvl)) := @ren_path (mvl) (nvl) .

Instance Ren_ty { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (ty (mvl)) (ty (nvl)) := @ren_ty (mvl) (nvl) .

Instance VarInstance_vl { mvl : nat } : Var ((fin) (mvl)) (vl (mvl)) := @var_vl (mvl) .

Notation "x '__vl'" := (var_vl x) (at level 5, format "x __vl") : subst_scope.

Notation "x '__vl'" := (@ids (_) (_) VarInstance_vl x) (at level 5, only printing, format "x __vl") : subst_scope.

Notation "'var'" := (var_vl) (only printing, at level 1) : subst_scope.

Class Up_vl X Y := up_vl : X -> Y.

Notation "↑__vl" := (up_vl) (only printing) : subst_scope.

Notation "↑__vl" := (up_vl_vl) (only printing) : subst_scope.

Instance Up_vl_vl { m : nat } { nvl : nat } : Up_vl (_) (_) := @up_vl_vl (m) (nvl) .

Notation "s [ sigmavl ]" := (subst_tm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_tm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_tm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_tm xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_vl sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_vl xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_vl sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_vl xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_vls sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xivl ⟩" := (ren_vls xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_vls sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xivl ⟩" := (ren_vls xivl) (at level 1, left associativity, only printing) : fscope.

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

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Subst_vl,  Subst_vls,  Subst_dms,  Subst_dm,  Subst_path,  Subst_ty,  Ren_tm,  Ren_vl,  Ren_vls,  Ren_dms,  Ren_dm,  Ren_path,  Ren_ty,  VarInstance_vl.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_tm,  Subst_vl,  Subst_vls,  Subst_dms,  Subst_dm,  Subst_path,  Subst_ty,  Ren_tm,  Ren_vl,  Ren_vls,  Ren_dms,  Ren_dm,  Ren_path,  Ren_ty,  VarInstance_vl in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?rinstId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?instId_vl| progress rewrite ?rinstId_vl| progress rewrite ?compComp_vl| progress rewrite ?compComp'_vl| progress rewrite ?compRen_vl| progress rewrite ?compRen'_vl| progress rewrite ?renComp_vl| progress rewrite ?renComp'_vl| progress rewrite ?renRen_vl| progress rewrite ?renRen'_vl| progress rewrite ?instId_vls| progress rewrite ?rinstId_vls| progress rewrite ?compComp_vls| progress rewrite ?compComp'_vls| progress rewrite ?compRen_vls| progress rewrite ?compRen'_vls| progress rewrite ?renComp_vls| progress rewrite ?renComp'_vls| progress rewrite ?renRen_vls| progress rewrite ?renRen'_vls| progress rewrite ?instId_dms| progress rewrite ?rinstId_dms| progress rewrite ?compComp_dms| progress rewrite ?compComp'_dms| progress rewrite ?compRen_dms| progress rewrite ?compRen'_dms| progress rewrite ?renComp_dms| progress rewrite ?renComp'_dms| progress rewrite ?renRen_dms| progress rewrite ?renRen'_dms| progress rewrite ?instId_dm| progress rewrite ?rinstId_dm| progress rewrite ?compComp_dm| progress rewrite ?compComp'_dm| progress rewrite ?compRen_dm| progress rewrite ?compRen'_dm| progress rewrite ?renComp_dm| progress rewrite ?renComp'_dm| progress rewrite ?renRen_dm| progress rewrite ?renRen'_dm| progress rewrite ?instId_path| progress rewrite ?rinstId_path| progress rewrite ?compComp_path| progress rewrite ?compComp'_path| progress rewrite ?compRen_path| progress rewrite ?compRen'_path| progress rewrite ?renComp_path| progress rewrite ?renComp'_path| progress rewrite ?renRen_path| progress rewrite ?renRen'_path| progress rewrite ?instId_ty| progress rewrite ?rinstId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?varL_vl| progress rewrite ?varLRen_vl| progress (unfold up_ren, upRen_vl_vl, up_vl_vl)| progress (cbn [subst_tm subst_vl subst_vls subst_dms subst_dm subst_path subst_ty ren_tm ren_vl ren_vls ren_dms ren_dm ren_path ren_ty])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?instId_vl in *| progress rewrite ?rinstId_vl in *| progress rewrite ?compComp_vl in *| progress rewrite ?compComp'_vl in *| progress rewrite ?compRen_vl in *| progress rewrite ?compRen'_vl in *| progress rewrite ?renComp_vl in *| progress rewrite ?renComp'_vl in *| progress rewrite ?renRen_vl in *| progress rewrite ?renRen'_vl in *| progress rewrite ?instId_vls in *| progress rewrite ?rinstId_vls in *| progress rewrite ?compComp_vls in *| progress rewrite ?compComp'_vls in *| progress rewrite ?compRen_vls in *| progress rewrite ?compRen'_vls in *| progress rewrite ?renComp_vls in *| progress rewrite ?renComp'_vls in *| progress rewrite ?renRen_vls in *| progress rewrite ?renRen'_vls in *| progress rewrite ?instId_dms in *| progress rewrite ?rinstId_dms in *| progress rewrite ?compComp_dms in *| progress rewrite ?compComp'_dms in *| progress rewrite ?compRen_dms in *| progress rewrite ?compRen'_dms in *| progress rewrite ?renComp_dms in *| progress rewrite ?renComp'_dms in *| progress rewrite ?renRen_dms in *| progress rewrite ?renRen'_dms in *| progress rewrite ?instId_dm in *| progress rewrite ?rinstId_dm in *| progress rewrite ?compComp_dm in *| progress rewrite ?compComp'_dm in *| progress rewrite ?compRen_dm in *| progress rewrite ?compRen'_dm in *| progress rewrite ?renComp_dm in *| progress rewrite ?renComp'_dm in *| progress rewrite ?renRen_dm in *| progress rewrite ?renRen'_dm in *| progress rewrite ?instId_path in *| progress rewrite ?rinstId_path in *| progress rewrite ?compComp_path in *| progress rewrite ?compComp'_path in *| progress rewrite ?compRen_path in *| progress rewrite ?compRen'_path in *| progress rewrite ?renComp_path in *| progress rewrite ?renComp'_path in *| progress rewrite ?renRen_path in *| progress rewrite ?renRen'_path in *| progress rewrite ?instId_ty in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?varL_vl in *| progress rewrite ?varLRen_vl in *| progress (unfold up_ren, upRen_vl_vl, up_vl_vl in *)| progress (cbn [subst_tm subst_vl subst_vls subst_dms subst_dm subst_path subst_ty ren_tm ren_vl ren_vls ren_dms ren_dm ren_path ren_ty] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_tm; [|now intros]); try repeat (erewrite rinst_inst_vl; [|now intros]); try repeat (erewrite rinst_inst_vls; [|now intros]); try repeat (erewrite rinst_inst_dms; [|now intros]); try repeat (erewrite rinst_inst_dm; [|now intros]); try repeat (erewrite rinst_inst_path; [|now intros]); try repeat (erewrite rinst_inst_ty; [|now intros]).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_tm; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_vl; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_vls; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_dms; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_dm; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_path; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_ty; [|intros; now asimpl]).
