Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.AnnotatedBool.
Require Export SystemFR.AnnotatedNat.

Import Coq.Strings.String.
Import Coq.Lists.List.
Require Import Psatz.



Create HintDb deriv.
Hint Resolve annotated_reducible_true : deriv.
Hint Resolve annotated_reducible_false: deriv.
Hint Resolve annotated_reducible_zero: deriv.
Hint Resolve annotated_reducible_succ: deriv.

(* Judgments *)
Inductive Judgment_name :=
| InferNat
| InferBool .

Inductive Judgment:=
| InferJudgment(name: Judgment_name)(Θ: (list nat))(Γ: context)(t: tree)(T: tree): Judgment.

Definition is_true (j: Judgment) : Prop := match j with | InferJudgment _ Θ Γ t T => [[ Θ; Γ ⊨ t : T ]] end.

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
  apply (derivation_ind_aux (S (derivation_size dv))); eauto. Qed.



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

Lemma Judgment_eq_prop : forall j1 j2, (j1 ?= j2 = true) -> j1 = j2.
Proof.
  unfold Judgment_eq.
  steps.
Qed.
Hint Resolve Judgment_eq_prop: deriv

Check @root.






Fixpoint is_valid(dv: derivation) : bool :=
  match dv with
  (* | N (InferJudgment "InferUnit" _ _ uu T_unit) nil => true *)
  | N (InferJudgment InferBool _ _ ttrue T_bool) nil => true
  | N (InferJudgment InferBool _ _ tfalse T_bool) nil => true
  | N (InferJudgment InferNat _ _ zero T_nat) nil => true
  | N (InferJudgment InferNat Θ Γ (succ t) T_nat) (dv'::nil) =>
    match dv' with
    | N j _ => andb (j ?= (InferJudgment InferNat Θ Γ t T_nat)) (is_valid dv')
    end
  | _ => false
  end.



Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  remember (fun dv => (is_valid dv) = true -> is_true (root dv)) as P.
  intros dv.
  assert (( is_valid dv = true -> is_true (root dv)) = P dv) as Hdv. steps.
  rewrite Hdv.
  apply (derivation_ind dv P).
  rewrite HeqP.
  intros.
  unfold forallP in X.
  unfold is_true. simpl.
  destruct J eqn:HJ.
  unfold is_valid in H. simpl in H.
  destruct_match.
  destruct_match; try solve [congruence].
  + (* zero *)
    steps; eauto with deriv.
  + (* succ *)
    repeat fold is_valid in H.
    repeat (destruct_match; try solve [congruence]).
    apply annotated_reducible_succ.
    pose proof (X (N (InferJudgment InferNat Θ Γ t0 T_nat) children0)) as H1. bools.
    destruct H as [H H'].
    assert (n0 = (InferJudgment InferNat Θ Γ t0 T_nat)) as Hn0. unfold Judgment_eq in H.
    destruct_match; eauto. inversion H.
    unfold root in H1. unfold is_true in H1.
    apply H1.
    steps.
    steps.
  + (* ite *)
    steps; eauto with deriv.


Qed.
