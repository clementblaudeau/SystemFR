Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.AnnotatedBool.
Require Export SystemFR.AnnotatedUnit.
Require Export SystemFR.AnnotatedNat.
Require Export SystemFR.AnnotatedIte.
Require Export SystemFR.AnnotatedArrow.
Require Export SystemFR.AnnotatedPair.
Require Export SystemFR.AnnotatedSum.
Require Export SystemFR.AnnotatedLet.
Require Export SystemFR.AnnotatedVar.
Require Export SystemFR.AnnotatedAddEquality.
Require Export SystemFR.AnnotatedFix.
Require Export SystemFR.AnnotatedEquivalent.
Require Export SystemFR.AnnotatedEquivalentContext.
Require Export SystemFR.AnnotatedEquivalentElim.
Require Export SystemFR.AnnotatedEquivalentPairExt.
Require Export SystemFR.AnnotatedSub.
Require Export SystemFR.AnnotatedRefine.
Require Export SystemFR.AnnotatedErr.
Require Export SystemFR.AnnotatedQuant.
Require Export SystemFR.DerivationHelpers.
Require Export SystemFR.AnnotatedTop.
Require Export SystemFR.AnnotatedRec.
Require Import Psatz.


Hint Resolve annotated_reducible_true : deriv.
Hint Resolve annotated_reducible_false: deriv.
Hint Resolve annotated_reducible_zero: deriv.
Hint Resolve annotated_reducible_succ: deriv.
Hint Resolve annotated_reducible_err: deriv.
Hint Resolve annotated_reducible_match: deriv.
Hint Resolve annotated_reducible_T_ite: deriv.
Hint Resolve annotated_reducible_app: deriv.
Hint Resolve annotated_reducible_lambda: deriv.
Hint Resolve annotated_reducible_pp: deriv.
Hint Resolve annotated_reducible_pi1: deriv.
Hint Resolve annotated_reducible_pi2: deriv.
Hint Resolve annotated_reducible_left: deriv.
Hint Resolve annotated_reducible_right: deriv.
Hint Resolve annotated_reducible_sum_match: deriv.
Hint Resolve annotated_reducible_let: deriv.
Hint Resolve annotated_reducible_var: deriv.
Hint Resolve annotated_reducible_weaken: deriv.
Hint Resolve annotated_reducible_unit: deriv.
Hint Rewrite tree_eq_prop: deriv.
Hint Resolve annotated_reducible_top: deriv.
Hint Resolve annotated_reducible_top_value: deriv.
Hint Resolve annotated_reducible_fold2: deriv.
Hint Rewrite is_nat_is_nat_value: deriv.

(* Judgments *)
Inductive TJ_name :=
| J_Unit
| J_Nat
| J_Match
| J_Bool
| J_If
| J_UnPrimitive
| J_BinPrimitive
| J_PP
| J_Pi1 | J_Pi2
| J_App
| J_Lambda
| J_Left | J_Right
| J_SumMatch : tree -> TJ_name
| J_Let : tree -> TJ_name
| J_Var | J_VarWeaken
| J_Fix
| J_equiv_elim
| J_drop
| J_error
| J_refine
| J_refine_unfold
| J_forall_inst
| J_Top
| J_Top_value
| J_Unfold_z
| J_Unfold_s
| J_Unfold_in
| J_Unfold_pos_in
| J_Fold
| J_Fold2.


Inductive StJ_name :=
| StJ_sub.

Inductive EJ_name :=
| E_trans
| E_sym
| E_refl
| E_context : tree -> EJ_name
| E_lambdas
| E_pair_ext
| E_refine_unfold
| E_SMT
.

Inductive compactContext :=
| Same
| New : context -> compactContext
| Append : list (nat * tree) -> compactContext
.

Inductive Judgment:=
| TJ(name: TJ_name)(Θ: (list nat))(Γ: compactContext)(t: tree)(T: tree): Judgment
| StJ(name: StJ_name)(Θ: (list nat))(Γ: compactContext)(t: tree)(T: tree): Judgment
| EJ(name: EJ_name)(Θ: (list nat))(Γ: compactContext)(t: tree)(T: tree): Judgment
.


Definition is_true (j: Judgment) (Γ: context) : Prop :=
  match j with
  | TJ  _ Θ _ t T => [[ Θ; Γ ⊨ t  : T ]]
  | StJ _ Θ _ t T => [[ Θ; Γ ⊨ t <: T ]]
  | EJ  _ Θ _ t T => [[ Θ; Γ ⊨ t  ≡ T ]]
  end.


Definition J_term1 dv :=
  match dv with
   | TJ _ _ _ t _ | StJ _ _ _ t _ | EJ _ _ _ t _ => t
  end.
Definition J_term2 dv :=
  match dv with
   | TJ _ _ _ _ t | StJ _ _ _ _ t | EJ _ _ _ _ t => t
  end.
(*

Definition J_context dv :=
  match dv with
  | TJ _ _ Γ _ _ | StJ _ _ Γ _ _ | EJ _ _ Γ _ _ => Γ
  end.
*)

(* Derivation trees *)
Inductive NodeTree (T:Type) :=
| N(n: T)(children: list (NodeTree T)): NodeTree T.
Arguments N {T}.

Definition root {T} nt : T :=
  match nt with
  | N n _ => n
  end.
Definition children {T} nt : (list (NodeTree T)) :=
  match nt with
  | N _ c => c
  end.


Lemma TJ_term1_root : forall n Θ Γ t T c, J_term1 (root (N (TJ n Θ Γ t T) c)) = t. Proof. steps. Qed.
Lemma EJ_term1_root : forall n Θ Γ t T c, J_term1 (root (N (EJ n Θ Γ t T) c)) = t. Proof. steps. Qed.
Lemma StJ_term1_root : forall n Θ Γ t T c, J_term1 (root (N (StJ n Θ Γ t T) c)) = t. Proof. steps. Qed.

Lemma TJ_term2_root : forall n Θ Γ t T c, J_term2 (root (N (TJ n Θ Γ t T) c)) = T. Proof. steps. Qed.
Lemma EJ_term2_root : forall n Θ Γ t T c, J_term2 (root (N (EJ n Θ Γ t T) c)) = T. Proof. steps. Qed.
Lemma StJ_term2_root : forall n Θ Γ t T c, J_term2 (root (N (StJ n Θ Γ t T) c)) = T. Proof. steps. Qed.

(*
Lemma TJ_context_root : forall n Θ Γ t T c, J_context (root (N (TJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Lemma EJ_context_root : forall n Θ Γ t T c, J_context (root (N (EJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Lemma StJ_context_root : forall n Θ Γ t T c, J_context (root (N (StJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
 *)

Hint Rewrite TJ_term1_root EJ_term1_root StJ_term1_root
     TJ_term2_root EJ_term2_root StJ_term2_root : deriv.
                                                    (*
     TJ_context_root EJ_context_root StJ_context_root : deriv. *)

Definition derivation := NodeTree Judgment.

(* Induction on derivations *)

Fixpoint derivation_size (dv: derivation) : nat :=
  match dv with
  | N n c => S (max ( List.map derivation_size c))
  end.

Definition forallP {T} P (l: list T) := forall (k: T), k ∈ l -> P k.
Hint Unfold forallP: deriv.

Definition derivation_ind_aux :
  forall n dv P,
    derivation_size dv < n ->
    (forall J c, forallP P c -> P (@N Judgment J c)) ->
    P dv.
Proof.
  induction n; steps; destruct dv; steps.
  apply PeanoNat.Nat.nle_succ_0 in H. inversion H.
  apply le_S_n in H.
  apply X.
  intros k Hk.
  pose proof (List.in_map derivation_size children0 k Hk) as H_k_sizes.
  pose proof (in_list_smaller (List.map derivation_size children0) (derivation_size k) H_k_sizes) as H_max.
  apply IHn; steps. lia.
Qed.

Definition derivation_ind :
  forall dv P,
    (forall J c, forallP P c -> P (@N Judgment J c)) ->
    P dv.
Proof.
  intros.
  apply (derivation_ind_aux (S (derivation_size dv))); eauto.
Qed.


(* Decidable equality for Judgments *)
Lemma TJ_name_eq_dec: forall (x y: TJ_name), {x = y} + {x <> y}.
Proof.
  decide equality; apply tree_eq_dec.
Defined.
Lemma StJ_name_eq_dec: forall (x y: StJ_name), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y.
  decide equality.
Defined.
Lemma EJ_name_eq_dec: forall (x y: EJ_name), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y;
  decide equality; try apply tree_eq_dec.
Defined.

Lemma compactContext_eq_dec :
  forall (x y: compactContext), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as [ | c | c] , y as [ | c0 | c0].
  all: try pose proof (context_eq_dec c c0) as [Hb | Hb]; subst.
  all: try solve [steps].
  all: try solve [apply Coq.Init.Specif.right ; discriminate].
  all: apply Coq.Init.Specif.right; intros H; invert_constructor_equalities; apply (Hb H1).
Defined.

Definition Judgment_eq_dec : forall (x y : Judgment), {x = y} + {x <> y}.
Proof.
  intros.
  induction x; destruct y;
  decide equality;
    try apply tree_eq_dec ||
        apply compactContext_eq_dec ||
        apply TJ_name_eq_dec ||
        apply StJ_name_eq_dec ||
        apply EJ_name_eq_dec ||
        apply (list_eqdec (nat_eqdec)) ||
        (apply Coq.Init.Specif.right; discriminate) ||
        (apply Coq.Init.Specif.left; reflexivity).
Defined.

Definition Judgment_eq j1 j2 : bool := if (Judgment_eq_dec j1 j2) then true else false.
Notation "j1 ?= j2" := (Judgment_eq j1 j2) (at level 70, j2 at next level).

Lemma Judgment_eq_prop : forall j1 j2, (j1 ?= j2 = true) <-> j1 = j2.
Proof.
  unfold Judgment_eq.
  steps.
Qed.
Hint Rewrite Judgment_eq_prop: deriv.
