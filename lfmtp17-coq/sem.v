(** * Normalization of Call-By-Value System F *)

Require Export axioms. 
From mathcomp Require Import all_ssreflect. 
Require Export SystemF_cbv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Notations *)

Notation "s .[ sigma , tau ]" := (s.[(sigma, tau)])
  (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ,  tau ]" ) : subst_scope.

Notation "'ren' xi" :=
  (xi >>> var_ty) (at level 50).

(** ** Call-by value reduction *)
 
Inductive eval : tm -> vl -> Prop :=
| eval_app (A : ty) (s t u : tm) (v1 v2 : vl) :
    eval s (lam A u) -> eval t v1 -> eval u.[var_ty, v1 .: var_vl] v2 ->
    eval (app s t) v2
| eval_tapp (A : ty) (s u : tm) (v : vl) :
    eval s (tlam u) -> eval u.[A .: var_ty, var_vl] v ->
    eval (tapp s A) v
| eval_val (v : vl) :
    eval (vt v) v.
Hint Resolve eval_val.

(** ** Syntactic typing *)

Definition ctx := seq ty.

Definition get (Gamma : ctx) (n : index) : ty :=
  nth (var_ty 0) Gamma n.
Local Notation "Gamma `_ i" := (get Gamma i).

Lemma get_map (f : ty -> ty) Gamma n :
  n < size Gamma -> (map f Gamma)`_n = f (Gamma`_n).
Proof. exact: nth_map. Qed.

Unset Elimination Schemes.
Inductive tm_ty (Gamma : ctx) : tm -> ty -> Prop :=
| ty_app (A B : ty) (s t : tm) :
    tm_ty Gamma s (arr A B) ->
    tm_ty Gamma t A ->
    tm_ty Gamma (app s t) B
| ty_tapp (A B : ty) (s : tm) :
    tm_ty Gamma s (all A) ->
    tm_ty Gamma (tapp s B) A.[B .: var_ty]
| ty_val (A : ty) (v : vl) :
    vl_ty Gamma v A ->
    tm_ty Gamma (vt v) A
with vl_ty (Gamma : ctx) : vl -> ty -> Prop :=
| ty_var (x : index) :
    x < size Gamma -> vl_ty Gamma (var_vl x) Gamma`_x
| ty_lam (A B : ty) (s : tm) :
    tm_ty (A :: Gamma) s B ->
    vl_ty Gamma (lam A s) (arr A B)
| ty_tlam (A : ty) (s : tm) :
    tm_ty (map (fun A : ty => A.[ren (+1)]) Gamma) s A ->
    vl_ty Gamma (tlam s) (all A).
Set Elimination Schemes.

Scheme tm_ty_ind := Minimality for tm_ty Sort Prop
with   vl_ty_ind := Minimality for vl_ty Sort Prop.
Combined Scheme has_ty_ind from tm_ty_ind, vl_ty_ind.

(** ** Semantic typing *)

Definition L (P : vl -> Prop) (s : tm) :=
  exists2 v, eval s v & P v.

Fixpoint V (A : ty) (rho : index -> vl -> Prop) (v : vl) {struct A} : Prop :=
  match A with
  | var_ty X => rho X v
  | arr A B =>
    match v with
    | lam C s => forall u, V A rho u -> L (V B rho) s.[var_ty, u .: var_vl]
    | _ => False
    end
  | all A =>
    match v with
    | tlam s => forall i (B : ty), L (V A (i .: rho)) s.[B .: var_ty, var_vl]
    | _ => False
    end
  end.
Notation E A rho := (L (V A rho)).

Lemma V_ren (A : ty) rho xi :
  V A.[ren xi] rho = V A (xi >>> rho).
Proof.
  elim: A rho xi => //.
  - move=> A ih1 B ih2 rho xi. fext=> -[] // C s. asimpl=>/=.
    fext=> v. by rewrite ih1 ih2.
  - move=> A ih rho xi. fext=> -[]// s.
    replace (all A).[ren xi] with (all A.[ren (0 .: (xi >>> (+1)))]) by repeat (f_equal; asimpl).
    move=>/=. fext=> i B. rewrite ih. autosubst.
Qed.

Lemma V_weak (A : ty) d rho :
  V A.[ren (+1)] (d .: rho) = V A rho.
Proof. exact: V_ren. Qed.

Lemma V_subst (A : ty) rho sigma :
  V A.[sigma] rho = V A (fun x => V (sigma x) rho).
Proof.
  elim: A rho sigma.
  - move=> x rho sigma /=. by asimpl.
  - move=> A ih1 B ih2 rho sigma. fext=> -[] // C s.
    asimpl=>/=. fext=> u. by rewrite ih1 ih2.
  - move=> A ih rho sigma. fext=> -[]//s. asimpl=>/=.
    fext=> i B. rewrite ih. repeat f_equal; fext=> -[|n] v //=.
    by rewrite V_weak.
Qed.

Lemma E_subst1 (A B : ty) rho :
  E A.[B .: var_ty] rho = E A (V B rho .: rho).
Proof.
  rewrite V_subst. repeat f_equal; by fext=> -[].
Qed.

Definition VG (Gamma : ctx) (rho : index -> vl -> Prop) (sigma : index -> vl) :=
  forall x, x < size Gamma  -> V Gamma`_x rho (sigma x).
 
Theorem soundness (Gamma : ctx) :
  (forall (s : tm) (A : ty), tm_ty Gamma s A ->
    forall sigma tau rho, VG Gamma rho tau -> E A rho s.[sigma,tau]) /\
  (forall (v : vl) (A : ty), vl_ty Gamma v A ->
    forall sigma tau rho, VG Gamma rho tau -> V A rho v.[sigma,tau]).
Proof.
  move: Gamma. apply has_ty_ind.
  - move=> Gamma A B s t _ ih1 _ ih2 sigma tau rho vg. asimpl.
    case: (ih1 sigma tau rho vg) => {ih1} -[]// C u ev1 /= h1.
    case: (ih2 sigma tau rho vg) => {ih2} v1 ev2 h2.
    case: (h1 v1 h2) => {h1 h2} v2 ev3 h3.
    exists v2. exact: eval_app ev1 ev2 ev3. exact: h3.
  - move=> Gamma A B s _ ih sigma tau rho vg. asimpl. rewrite E_subst1.
    case: (ih sigma tau rho vg) => {ih} -[]//= u ev1 h1.
    case: (h1 (V B rho) B.[sigma]) => v ev2 h2.  
    exists v. exact: eval_tapp ev1 ev2. exact: h2.
  - move=> Gamma A v _ ih sigma tau rho vg.
    eexists; asimpl. exact: eval_val. exact: ih.
  - move=> Gamma x mem sigma tau rho vg. exact: vg.
  - move=> Gamma A B s _ ih sigma tau rho vg. asimpl=> /= v h1; asimpl.
    apply: ih => -[_|x] //=. exact: vg.
  - move=> Gamma A s _ ih sigma tau rho vg. asimpl=>/= i B; asimpl.
    apply: ih => x. rewrite size_map => mem. rewrite get_map //.
    rewrite V_weak. exact: vg.
Qed.

(** ** Applications *)

Definition nilA : index -> vl -> Prop := fun _ _ => False.

Corollary soundness_nil s A :
  tm_ty [::] s A -> E A nilA s.
Proof.
  case: (soundness [::]) => H _ /H/(_ var_ty var_vl nilA).
  case/(_ _)/Wrap=> //. by asimpl.
Qed.

Corollary normalization s A :
  tm_ty [::] s A -> exists v, eval s v.
Proof.
  move=> /soundness_nil[v hv] _. by exists v.
Qed.

Corollary consistency s :
  ~tm_ty [::] s (all (var_ty 0)).
Proof.
  by move=> /soundness_nil[-[]//u ev /=/(_ (fun _ => False) (var_ty 0))[]].
Qed.