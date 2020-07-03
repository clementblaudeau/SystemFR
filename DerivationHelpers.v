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


Import Coq.Strings.String.
Import Coq.Bool.Bool.
Require Import Psatz.


Create HintDb deriv.
Hint Resolve annotated_reducible_true : deriv.
Hint Resolve annotated_reducible_false: deriv.
Hint Resolve annotated_reducible_zero: deriv.
Hint Resolve annotated_reducible_succ: deriv.
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

Hint Rewrite tree_eq_prop: deriv.




(* Bool unequality *)
Notation "n ?<> m" := (negb (PeanoNat.Nat.eqb n m)) (at level 80).
Lemma neqb_prop: forall n m, (n ?<> m) = true <-> n <> m.
Proof.
  intros.
  split. intros. unfold negb in H.  destruct_match; try solve [congruence].
  eapply PeanoNat.Nat.eqb_neq; eauto.
  intros. unfold negb. destruct_match; try solve [reflexivity].
  eapply PeanoNat.Nat.eqb_neq in H. rewrite H in matched. congruence.
Qed.
Hint Rewrite neqb_prop: deriv.

(* Annotated - boolean version *)

Fixpoint is_annotated_termb t :=
  match t with
  | fvar y term_var => true
  | lvar _ term_var => true
  | err T => is_annotated_typeb T

  | uu => true

  | tsize t => is_annotated_termb t

  | lambda T t' => is_annotated_typeb T && is_annotated_termb t'
  | app t1 t2 => is_annotated_termb t1 && is_annotated_termb t2

  | forall_inst t1 t2 => is_annotated_termb t1 && is_annotated_termb t2

  | type_abs t => is_annotated_termb t
  | type_inst t T => is_annotated_termb t && is_annotated_typeb T

  | pp t1 t2 => is_annotated_termb t1 && is_annotated_termb t2
  | pi1 t' => is_annotated_termb t'
  | pi2 t' => is_annotated_termb t'

  | because t1 t2 => is_annotated_termb t1 && is_annotated_termb t2
  | get_refinement_witness t1 t2 => is_annotated_termb t1 && is_annotated_termb t2

  | ttrue => true
  | tfalse => true
  | ite t1 t2 t3 => is_annotated_termb t1 && is_annotated_termb t2 && is_annotated_termb t3
  | boolean_recognizer _ t => is_annotated_termb t

  | zero => true
  | succ t' => is_annotated_termb t'
  | tmatch t' t0 ts => is_annotated_termb t' && is_annotated_termb t0 && is_annotated_termb ts

  | tfix T t' => is_annotated_typeb T && is_annotated_termb t'

  | notype_tlet t1 t2 => is_annotated_termb t1 && is_annotated_termb t2
  | tlet t1 A t2 => is_annotated_termb t1 && is_annotated_typeb A && is_annotated_termb t2
  | trefl t1 t2 => is_annotated_termb t1 && is_annotated_termb t2

  | tfold T t => is_annotated_typeb T && is_annotated_termb t
  | tunfold t => is_annotated_termb t
  | tunfold_in t1 t2 => is_annotated_termb t1 && is_annotated_termb t2
  | tunfold_pos_in t1 t2 => is_annotated_termb t1 && is_annotated_termb t2

  | tleft t => is_annotated_termb t
  | tright t => is_annotated_termb t
  | sum_match t tl tr => is_annotated_termb t && is_annotated_termb tl && is_annotated_termb tr

  | typecheck t T => is_annotated_termb t && is_annotated_typeb T

  | _ => false
  end
with is_annotated_typeb T :=
       match T with
       | fvar y type_var => true
       | lvar y type_var => true
       | T_unit => true
       | T_bool => true
       | T_nat => true
       | T_refine A p => is_annotated_typeb A && is_annotated_termb p
       | T_type_refine A B => is_annotated_typeb A && is_annotated_typeb B
       | T_prod A B => is_annotated_typeb A && is_annotated_typeb B
       | T_arrow A B => is_annotated_typeb A && is_annotated_typeb B
       | T_sum A B => is_annotated_typeb A && is_annotated_typeb B
       | T_intersection A B => is_annotated_typeb A && is_annotated_typeb B
       | T_union A B => is_annotated_typeb A && is_annotated_typeb B
       | T_top => true
       | T_bot => true
       | T_equiv t1 t2 => is_annotated_termb t1 && is_annotated_termb t2
       | T_forall A B => is_annotated_typeb A && is_annotated_typeb B
       | T_exists A B => is_annotated_typeb A && is_annotated_typeb B
       | T_abs T => is_annotated_typeb T
       | T_rec n T0 Ts => is_annotated_termb n && is_annotated_typeb T0 && is_annotated_typeb Ts
       | _ => false
       end
.

Lemma annotated_term_type_bool_aux : forall t, (is_annotated_termb t = true <-> is_annotated_term t) /\ (is_annotated_typeb t = true <-> is_annotated_type t).
  induction t ; repeat bools || steps.
Qed.

Lemma annotated_term_bool : forall t, (is_annotated_termb t = true <-> is_annotated_term t).
  intros.
  apply (proj1 (annotated_term_type_bool_aux t)).
Qed.

Lemma annotated_type_bool : forall t, (is_annotated_typeb t = true <-> is_annotated_type t).
  intros.
  apply (proj2 (annotated_term_type_bool_aux t)).
Qed.

Hint Rewrite annotated_term_bool: deriv.
Hint Rewrite annotated_type_bool: deriv.


Fixpoint wfb t k :=
  match t with
  | fvar _ _ => true
  | lvar i term_var => PeanoNat.Nat.ltb i k
  | lvar i type_var => true

  | notype_err => true
  | err T => wfb T k

  | uu => true

  | tsize t => wfb t k

  | notype_lambda t' => wfb t' (S k)
  | lambda T t' => wfb T k && wfb t' (S k)
  | app t1 t2 => wfb t1 k && wfb t2 k

  | forall_inst t1 t2 => wfb t1 k && wfb t2 k

  | type_abs t => wfb t k
  | type_inst t T => wfb t k && wfb T k

  | pp t1 t2 => wfb t1 k && wfb t2 k
  | pi1 t => wfb t k
  | pi2 t => wfb t k

  | because t1 t2 => wfb t1 k && wfb t2 k
  | get_refinement_witness t1 t2 => wfb t1 k && wfb t2 (S k)

  | ttrue => true
  | tfalse => true
  | ite t1 t2 t3 => wfb t1 k && wfb t2 k && wfb t3 k
  | boolean_recognizer _ t => wfb t k

  | zero => true
  | succ t' => wfb t' k
  | tmatch t' t1 t2 =>
    wfb t' k &&
    wfb t1 k &&
    wfb t2 (S k)

  | tfix T t' => wfb T (S k) && wfb t' (S (S k))
  | notype_tfix t' => wfb t' (S (S k))

  | notype_tlet t1 t2 => wfb t1 k && wfb t2 (S k)
  | tlet t1 T t2 => wfb t1 k && wfb T k && wfb t2 (S k)

  | trefl t1 t2 => wfb t1 k && wfb t2 k

  | tfold T t' => wfb T k && wfb t' k
  | tunfold t' => wfb t' k
  | tunfold_in t1 t2 => wfb t1 k && wfb t2 (S k)
  | tunfold_pos_in t1 t2 => wfb t1 k && wfb t2 (S k)

  | tleft t' => wfb t' k
  | tright t' => wfb t' k
  | sum_match t' tl tr => wfb t' k && wfb tl (S k) && wfb tr (S k)

  | typecheck t T => wfb t k && wfb T k

  | T_unit => true
  | T_bool => true
  | T_nat => true
  | T_prod T1 T2 => wfb T1 k && wfb T2 (S k)
  | T_arrow T1 T2 => wfb T1 k && wfb T2 (S k)
  | T_sum T1 T2 => wfb T1 k && wfb T2 k
  | T_refine T p => wfb T k && wfb p (S k)
  | T_type_refine T1 T2 => wfb T1 k && wfb T2 (S k)
  | T_intersection T1 T2 => wfb T1 k && wfb T2 k
  | T_union T1 T2 => wfb T1 k && wfb T2 k
  | T_top => true
  | T_bot => true
  | T_equiv t1 t2 => wfb t1 k && wfb t2 k
  | T_forall T1 T2 => wfb T1 k && wfb T2 (S k)
  | T_exists T1 T2 => wfb T1 k && wfb T2 (S k)
  | T_abs T => wfb T k
  | T_rec n T0 Ts => wfb n k && wfb T0 k && wfb Ts k
  end.

Fixpoint wfsb (gamma: list (nat * tree)) k :=
  match gamma with
  | nil => true
  | (x,A) :: gamma' => wfb A k && wfsb gamma' k
  end.

Lemma wfb_prop : forall t k, (wfb t k = true) <-> (wf t k).
Proof.
  induction t;
    (repeat bools || steps || rewrite PeanoNat.Nat.ltb_lt in * || rewrite PeanoNat.Nat.leb_le in * || lia || eauto with eapply_any).
Qed.

Lemma wfsb_prop : forall Γ k, (wfsb Γ k = true) <-> (wfs Γ k).
Proof.
  induction Γ.
  steps.
  repeat bools || steps || rewrite  wfb_prop in * || eauto with eapply_any.
Qed.

Hint Rewrite wfb_prop wfsb_prop: deriv.

(* Judgments *)
Inductive Judgment_name :=
| InferNat | InferMatch | CheckNat
| InferBool | CheckBool | InferIf
| InferPP | InferPi1 | InferPi2
| InferApp | InferLambda
| InferLeft | InferRight
| InferSumMatch : tree -> Judgment_name
| InferLet : tree -> Judgment_name
| InferVar | InferVarWeaken
| InferFix.

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

Lemma J_tree_root : forall n Θ Γ t T c, J_tree (root (N (J n Θ Γ t T) c)) = t. Proof. steps. Qed.
Lemma J_type_root : forall n Θ Γ t T c, J_type (root (N (J n Θ Γ t T) c)) = T. Proof. steps. Qed.
Lemma J_context_root : forall n Θ Γ t T c, J_context (root (N (J n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Hint Rewrite J_tree_root J_type_root  J_context_root: deriv.

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
Hint Rewrite Judgment_eq_prop: deriv.

Definition option_dec: forall X (x y : option X), decidable X -> {x = y} + {x <> y}.
  intros.
  decide equality.
Qed.
Definition option_tree_dec_eq t1 t2 := if (option_dec tree t1 t2 tree_eq_dec) then true else false.
Definition option_tree_dec_eq_prop : forall t1 t2, (option_tree_dec_eq t1 t2 = true) <-> (t1 = t2).
Proof.
  unfold option_tree_dec_eq. steps.
Qed.

Hint Rewrite option_tree_dec_eq_prop: deriv.



(* Boolean set inclusion definitions and lemmas *)
Definition Inb x l : bool := if (List.in_dec PeanoNat.Nat.eq_dec x l) then true else false.
Notation "x ?∈ l" := (Inb x l) (at level 70, l at next level).
Notation "x ?∉ l" := (negb (Inb x l)) (at level 70, l at next level).
Lemma Inb_prop : forall x A, (x ?∈ A = true) <-> (x ∈ A).
Proof.
  intros.
  unfold Inb.
  steps.
Qed.
Lemma Inb_prop2 : forall x A, (x ?∉ A = true) <-> not(x ∈ A).
Proof.
  intros.
  unfold Inb.
  steps.
Qed.
Lemma Inb_prop3 : forall x A, (x ?∈ A = false) <-> not(x ∈ A).
Proof.
  intros.
  unfold Inb.
  steps.
Qed.
Hint Rewrite Inb_prop: deriv.
Hint Rewrite Inb_prop2: deriv.
Hint Rewrite Inb_prop3: deriv.

Definition subsetb l1 l2 : bool := List.forallb (fun x => Inb x l2 ) l1.
Notation "a ?⊂ b" := (subsetb a b) (at level 70, b at next level).
Lemma subsetb_prop : forall l1 l2, (l1 ?⊂ l2 = true) <-> (subset l1 l2).
Proof.
  intros.
  unfold subsetb, Inb, subset, List.forallb.
  induction l1;  steps.
Qed.
Hint Rewrite subsetb_prop: deriv.


(* Support helper lemmas *)
Lemma support_fvar : forall n U Γ, subset (pfv (fvar n term_var) term_var) (@support nat tree ((n,U)::Γ)).
Proof.
  intros.
  simpl.
  destruct_match; try solve [congruence]; eauto with sets.
Qed.
Hint Resolve support_fvar: sets.

Lemma pfv_fvar: forall n tag, pfv (fvar n tag) tag = singleton n.
Proof.
  intros.
  simpl.
  destruct_match; try solve [congruence]; eauto with sets.
Qed.

Lemma pfv_fvar2: forall n, ((if tag_eq_dec term_var term_var then @singleton nat n else nil) = singleton n).
Proof.
  intros.
  destruct_match; try solve [congruence]; eauto with sets.
  Qed.
Hint Rewrite pfv_fvar2: deriv.


Lemma support_open : forall t1 t2 tag k A, subset (pfv (open k t1 t2) tag) A ->
                                      subset (pfv t2 tag) A ->
                                      subset (pfv t1 tag) A.
Proof.
  induction t1; repeat steps || match goal with | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H end; eauto with sets ; apply subset_union2; eauto with eapply_any sets.
Qed.
Hint Resolve support_open: sets.


Lemma support_open2 : forall t1 t2 tag (k: nat) A, subset (pfv t2 tag) A ->
                                            subset (pfv t1 tag) A ->
                                            subset (pfv (open k t1 t2) tag) A.
Proof.
  induction t1; repeat steps || apply subset_union3 || match goal with | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H end.
Qed.
Hint Resolve support_open2: sets.

Require Import Coq.Lists.List.

Fixpoint NoDupb l : bool :=
  match l with
  | nil => true
  | x::l' => (x ?∉ l') && (NoDupb l')
  end.

Lemma NoDupb_prop : forall l, (NoDup l) <-> (NoDupb l = true).
Proof.
  induction l.
  steps.
  rewrite NoDup_cons_iff.
  simpl.
  rewrite IHl.
  bools.
  rewrite Inb_prop3.
  reflexivity.
Qed.
