Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.AnnotatedBool.
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
Require Export SystemFR.DerivationHelpers.

Require Import Psatz.

(* Judgments *)
Inductive TJ_name :=
| J_Nat
| J_Match
| J_Bool
| J_If
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
| J_refine.

Inductive StJ_name :=
| StJ_sub.

Inductive EJ_name :=
| E_trans
| E_sym
| E_refl
| E_context : tree -> EJ_name
| E_lambdas
| E_pair_ext
.

Inductive Judgment:=
| TJ(name: TJ_name)(Θ: (list nat))(Γ: context)(t: tree)(T: tree): Judgment
| StJ(name: StJ_name)(Θ: (list nat))(Γ: context)(t: tree)(T: tree): Judgment
| EJ(name: EJ_name)(Θ: (list nat))(Γ: context)(t: tree)(T: tree): Judgment
.


Definition is_true (j: Judgment) : Prop :=
  match j with
  | TJ _ Θ Γ t T => [[ Θ; Γ ⊨ t : T ]]
  | StJ _ Θ Γ t T => [[ Θ; Γ ⊨ t <: T ]]
  | EJ _ Θ Γ t t' => [[ Θ; Γ ⊨ t ≡ t' ]]
  end.


Definition J_term1 dv :=
  match dv with
   | TJ _ _ _ t _ | StJ _ _ _ t _ | EJ _ _ _ t _ => t
  end.
Definition J_term2 dv :=
  match dv with
   | TJ _ _ _ _ t | StJ _ _ _ _ t | EJ _ _ _ _ t => t
  end.
Definition J_context dv :=
  match dv with
  | TJ _ _ Γ _ _ | StJ _ _ Γ _ _ | EJ _ _ Γ _ _ => Γ
  end.

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

Lemma TJ_context_root : forall n Θ Γ t T c, J_context (root (N (TJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Lemma EJ_context_root : forall n Θ Γ t T c, J_context (root (N (EJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Lemma StJ_context_root : forall n Θ Γ t T c, J_context (root (N (StJ n Θ Γ t T) c)) = Γ. Proof. steps. Qed.

Hint Rewrite TJ_term1_root EJ_term1_root StJ_term1_root
     TJ_term2_root EJ_term2_root StJ_term2_root
     TJ_context_root EJ_context_root StJ_context_root : deriv.

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
Definition TJ_name_eq_dec: forall (x y: TJ_name), {x = y} + {x <> y}.
Proof.
  decide equality; apply tree_eq_dec.
Defined.
Definition StJ_name_eq_dec: forall (x y: StJ_name), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y.
  decide equality.
Defined.
Definition EJ_name_eq_dec: forall (x y: EJ_name), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y;
  decide equality; try apply tree_eq_dec.
Defined.

Definition Judgment_eq_dec : forall (x y : Judgment), {x = y} + {x <> y}.
Proof.
  intros.
  induction x; destruct y;
  decide equality;
    try apply tree_eq_dec ||
        apply context_eq_dec ||
        apply TJ_name_eq_dec ||
        apply StJ_name_eq_dec ||
        apply EJ_name_eq_dec ||
        apply (list_eqdec (nat_eqdec)) ||
        (right; discriminate) ||
        (left; reflexivity).
Defined.

Definition Judgment_eq j1 j2 : bool := if (Judgment_eq_dec j1 j2) then true else false.
Notation "j1 ?= j2" := (Judgment_eq j1 j2) (at level 70, j2 at next level).

Lemma Judgment_eq_prop : forall j1 j2, (j1 ?= j2 = true) <-> j1 = j2.
Proof.
  unfold Judgment_eq.
  steps.
Qed.
Hint Rewrite Judgment_eq_prop: deriv.
