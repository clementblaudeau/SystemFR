Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.AnnotatedBool.
Require Export SystemFR.AnnotatedNat.
Require Export SystemFR.AnnotatedIte.

Import Coq.Strings.String.
Import Coq.Lists.List.
Import Coq.Bool.Bool.
Require Import Psatz.


Create HintDb deriv.
Hint Resolve annotated_reducible_true : deriv.
Hint Resolve annotated_reducible_false: deriv.
Hint Resolve annotated_reducible_zero: deriv.
Hint Resolve annotated_reducible_succ: deriv.
Hint Rewrite tree_eq_prop: deriv.

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

Fixpoint is_valid(dv: derivation) : bool :=
  match dv with
  (* | N (InferJudgment "InferUnit" _ _ uu T_unit) nil => true *)

  (* Bools *)
  | N (J (InferBool | CheckBool) _ _ ttrue T_bool) nil => true
  | N (J (InferBool | CheckBool) _ _ tfalse T_bool) nil => true

  (* Naturals *)
  | N (J InferNat _ _ zero T_nat) nil => true
  | N (J InferNat Θ Γ (succ t) T_nat) (N j nil as dv' ::nil) =>
    (j ?= (J InferNat Θ Γ t T_nat)) && (is_valid dv')

  (* If then else *)
  | N (J InferIf Θ Γ (ite b t1 t2) T)
      ((N jb nil as db)
         ::(N ((J I1 _ ((x,Te1)::_) _ T1) as j1) nil as d1)
         ::(N ((J I2 _ ((_,Te2)::_) _ T2) as j2) nil as d2)
         ::nil) =>
    (jb ?= (J CheckBool Θ Γ b T_bool)) && (is_valid db)
    && (j1 ?= (J I1 Θ ((x, T_equiv b ttrue)::Γ) t1 T1)) && (is_valid d1)
    && (j2 ?= (J I2 Θ ((x, T_equiv b tfalse)::Γ) t2 T2)) && (is_valid d2)
    && tree_eq T (T_ite b T1 T2)
    && (x ?∉ (fv t1))
    && (x ?∉ (fv t2))
    && (x ?∉ (fv T1))
    && (x ?∉ (fv T2))
    && (x ?∉ (fv_context Γ))
    && ( x ?∉ Θ )

  | _ => false
  end.

Lemma subset_context_support: forall Γ, subset (fv_context Γ) (fv_context Γ).
Proof.
  intros Γ x.
  eauto using fv_context_support.
Qed.
Hint Resolve subset_context_support: deriv.


Fixpoint check_fv_context (Θ:list nat) Γ : bool :=
  match Γ with
  | nil => true
  | (x,T)::Γ' => check_fv_context Θ Γ' &&
               ((fv T) ?⊂ (support Γ')) &&
               (x ?∈ (support Γ' )) &&
               ((pfv T type_var) ?⊂ Θ)
  end.


Ltac inst_list_prop:=
  match goal with
    | H: forall x, x ∈ ?a1::nil -> _ |- _ => unshelve epose proof (H a1 _); clear H
    | H: forall x, x ∈ ?a1::?a2::nil -> _ |- _ => unshelve epose proof (H a1 _); unshelve epose proof (H a2 _); clear H
    | H: forall x, x ∈ ?a1::?a2::?a3::nil -> _ |- _ => unshelve epose proof (H a1 _); unshelve epose proof (H a2 _); unshelve epose proof (H a3 _); clear H
  end.


Ltac lighter :=
  (intros) ||
  (congruence) ||
  (subst) ||
  (destruct_and) ||
  intuition auto ||
  (cbn in *)
   .

Lemma is_valid_wf_aux: forall dv, is_valid dv = true -> wf (J_tree (root dv)) 0 /\ wf (J_type (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros.
  unfold root, J_tree, J_type.
  unfold forallP in X.

  unfold is_valid in H.

  repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || (destruct_match; repeat fold is_valid in * ; try solve [congruence]) || eauto with cbn wf || intuition auto || simpl.
Qed.

Lemma is_valid_wf_t : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf t 0.
Proof.
  intros.
  pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ). steps.
Qed.

Lemma is_valid_wf_T : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf T 0.
Proof.
  intros.
  pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ). steps.
Qed.


Lemma is_valid_support_term_aux : forall dv, is_valid dv = true -> subset (fv (J_tree (root dv)) ) (support (J_context (root dv))) /\ subset (fv (J_type (root dv)) ) (support (J_context (root dv))).
Proof.
  unfold fv.
  induction dv using derivation_ind.
  intros.
  unfold root, J_tree, J_type.
  unfold forallP in X.
  unfold is_valid in H.
  repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || fold is_valid in * ||  (destruct_match; repeat fold is_valid in * ; try solve [congruence]) || intuition auto || simpl  || eauto with cbn sets.
Qed.
Lemma is_valid_support_t : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> subset (fv t) (support Γ).
Proof.
  intros.
  pose proof (is_valid_support_term_aux  (N (J n Θ Γ t T) c) H ). steps.
Qed.
Hint Resolve is_valid_support_t: deriv.
Lemma is_valid_support_T : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> subset (fv T) (support Γ).
Proof.
  intros.
  pose proof (is_valid_support_term_aux  (N (J n Θ Γ t T) c) H ). steps.
Qed.
Hint Resolve is_valid_support_T: deriv.


(* Lemma is_valid_wf_context : forall n Θ Γ t T,  is_valid (J n Θ Γ t T) = true ->
  *)
Hint Resolve is_valid_wf_t: deriv.
Hint Resolve is_valid_wf_T: deriv.
Hint Resolve annotated_reducible_T_ite: deriv.

Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros.
  unfold forallP in X.
  unfold is_true. simpl.
  destruct J0 eqn:HJ.
  unfold is_valid in H.
  repeat subst || bools || destruct_and || autorewrite with deriv in * || invert_constructor_equalities || (destruct_match; try solve [congruence] ; repeat fold is_valid in *) || inst_list_prop || intuition auto || eauto with deriv || cbn.
  apply (annotated_reducible_T_ite _ _ _ _ _ _ _ n); eauto 4 with deriv sets.
  (* 6 *)
  pose proof (subset_context_support Γ).
  pose proof (is_valid_support_t  CheckBool Θ Γ t0_1 T_bool nil H11).
  intros H2000.
  apply H1.
  apply (in_subset (fv t0_1) _ _).
  eauto with sets deriv cbn.
  intros x.
  pose proof (fv_context_support Γ x term_var). eauto with sets.
  eauto with sets.
  (* 4 *)
  pose proof (is_valid_support_t _ _ _ _ _ _ H9).
  simpl in H7.
  eauto with deriv sets cbn.
  (* 3 *)
  pose proof (is_valid_support_t _ _ _ _ _ _ H7).
  simpl in H7.
  eauto with deriv sets cbn.
  (* 2 *)
  pose proof (is_valid_support_T _ _ _ _ _ _ H9).
  simpl in H7.
  eauto with deriv sets cbn.
  (* 3 *)
  pose proof (is_valid_support_T _ _ _ _ _ _ H7).
  simpl in H7.
  eauto with deriv sets cbn.
Qed.
