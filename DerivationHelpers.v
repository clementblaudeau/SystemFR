Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.AnnotatedBool.
Require Export SystemFR.AnnotatedNat.
Require Export SystemFR.AnnotatedIte.
Require Export SystemFR.AnnotatedArrow.

Import Coq.Strings.String.
Import Coq.Lists.List.
Import Coq.Bool.Bool.
Require Import Psatz.


Create HintDb deriv.
Hint Resolve annotated_reducible_true : deriv.
Hint Resolve annotated_reducible_false: deriv.
Hint Resolve annotated_reducible_zero: deriv.
Hint Resolve annotated_reducible_succ: deriv.
Hint Resolve annotated_reducible_T_ite: deriv.
Hint Resolve annotated_reducible_app: deriv.

Hint Rewrite tree_eq_prop: deriv.
Hint Rewrite annotated_term_bool: deriv.
Hint Rewrite annotated_type_bool: deriv.
(* Judgments *)
Inductive Judgment_name :=
| InferNat
| InferBool
| CheckBool
| InferIf.

Inductive Judgment:=
| J(name: Judgment_name)(Θ: (list nat))(Γ: context)(t: tree)(T: tree): Judgment.

Definition J_tree dv :=
  match dv with | J _ _ _ t _ => t end.
Definition J_type dv :=
  match dv with | J _ _ _ _ T => T end.
Definition J_context dv :=
  match dv with | J _ _ Γ _ _ => Γ end.

Definition is_true (j: Judgment) : Prop := match j with | J _ Θ Γ t T => [[ Θ; Γ ⊨ t : T ]] end.

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

Definition derivation := NodeTree Judgment.

(* Induction on derivations *)

Fixpoint derivation_size (dv: derivation) : nat :=
  match dv with
  | N n c => S (max ( map derivation_size c))
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
  pose proof (in_map derivation_size children0 k Hk) as H_k_sizes.
  pose proof (in_list_smaller (map derivation_size children0) (derivation_size k) H_k_sizes) as H_max.
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



(* Decidable equality for contexts *)
Definition context_eq_dec: forall (x y : context), {x = y} + {x <> y}.
Proof.
  repeat decide equality || apply tree_eq_dec.
Qed.
Definition context_eq c1 c2 : bool := if (context_eq_dec c1 c2) then true else false.
Definition list_nat_eq_dec : forall (x y : list nat), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

(* Decidable equality for Judgments *)
Definition Judgment_eq_dec : forall (x y : Judgment), {x = y} + {x <> y}.
Proof.
  repeat decide equality. Qed.
Definition Judgment_eq j1 j2 : bool := if (Judgment_eq_dec j1 j2) then true else false.
Notation "j1 ?= j2" := (Judgment_eq j1 j2) (at level 70, j2 at next level).

Lemma Judgment_eq_prop : forall j1 j2, (j1 ?= j2 = true) <-> j1 = j2.
Proof.
  unfold Judgment_eq.
  steps.
Qed.
(* apply_anywhere Judgment_eq_prop. *)
Hint Rewrite Judgment_eq_prop: deriv.

Definition Inb x l : bool := if (in_dec PeanoNat.Nat.eq_dec x l) then true else false.
Notation "x ?∈ l" := (Inb x l) (at level 70, l at next level).
Notation "x ?∉ l" := (negb (Inb x l)) (at level 70, l at next level).
Lemma Inb_prop : forall x A, (x ?∈ A = true) <-> (x ∈ A).
Proof.
  intros.
  unfold Inb, forallb.
  steps.
Qed.
Lemma Inb_prop2 : forall x A, (x ?∉ A = true) <-> not(x ∈ A).
Proof.
  intros.
  unfold Inb, forallb.
  steps.
Qed.
Lemma Inb_prop3 : forall x A, (x ?∈ A = false) <-> not(x ∈ A).
Proof.
  intros.
  unfold Inb, forallb.
  steps.
Qed.
Hint Rewrite Inb_prop: deriv.
Hint Rewrite Inb_prop2: deriv.
Hint Rewrite Inb_prop3: deriv.


Definition subsetb l1 l2 : bool := forallb (fun x => Inb x l2 ) l1.
Notation "a ?⊂ b" := (subsetb a b) (at level 70, b at next level).
Lemma subsetb_prop : forall l1 l2, (l1 ?⊂ l2 = true) <-> (subset l1 l2).
Proof.
  intros.
  unfold subsetb, Inb, subset, forallb.
  induction l1;  steps.
Qed.
Hint Rewrite subsetb_prop: deriv.
