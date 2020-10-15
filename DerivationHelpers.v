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
Require Export SystemFR.AnnotatedEquivalentRefine.
Require Export SystemFR.AnnotatedSub.
Require Export SystemFR.AnnotatedRefine.

Import Coq.Strings.String.
Import Coq.Bool.Bool.
Require Import Psatz.


Create HintDb deriv.


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
  | notype_tfix  t => is_annotated_termb t

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

(* Erase term *)
Fixpoint is_erased_termb (t : tree) : bool :=
  match t with
  | app t1 t2 | pp t1 t2 => is_erased_termb t1 && is_erased_termb t2
  | ite t1 t2 t3 => is_erased_termb t1 && is_erased_termb t2 && is_erased_termb t3
  | fvar _ term_var | lvar _ term_var | notype_err | uu | ttrue | tfalse | zero => true
  | tmatch t' t0 ts => is_erased_termb t' && is_erased_termb t0 && is_erased_termb ts
  | notype_lambda t' | pi1 t' | pi2 t' | succ t' | notype_tfix t' => is_erased_termb t'
  | tsize t0 | boolean_recognizer _ t0 | tright t0 | tleft t0 => is_erased_termb t0
  | sum_match t0 tl tr => is_erased_termb t0 && is_erased_termb tl && is_erased_termb tr
  | _ => false
  end.
Lemma is_erased_termb_prop : forall t, (is_erased_termb t = true) <-> (is_erased_term t).
Proof.
  induction t.
  all: repeat simpl || steps || bools.
Qed.
Hint Rewrite is_erased_termb_prop: deriv.



(* Decidable equality for contexts *)
Definition context_eq_dec: forall (x y : context), {x = y} + {x <> y}.
Proof.
  repeat decide equality || apply tree_eq_dec.
Defined.
Definition context_eq c1 c2 : bool := if (context_eq_dec c1 c2) then true else false.
Definition list_nat_eq_dec : forall (x y : list nat), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.
Definition list_nat_eq l1 l2 := if (list_nat_eq_dec l1 l2) then true else false.
Definition list_nat_eq_prop : forall l1 l2, list_nat_eq l1 l2 = true <-> l1 = l2.
Proof.
  unfold list_nat_eq.
  steps.
Qed.

Definition option_dec: forall X (x y : option X), decidable X -> {x = y} + {x <> y}.
  intros.
  unfold decidable in *.
  destruct x, y;
  decide equality.
Defined.

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
  sets.
  unfold List.In.
  eauto.
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


Lemma subset_nil : forall {T} A, @subset T nil A.
Proof.
  steps. eauto with sets.
Qed.

Lemma in_subset_not:
  forall {T} (l1 l2: list T) (x: T),
    subset l1 l2 -> not (x ∈ l2) -> not (x ∈ l1).
Proof.
  steps.
Qed.
Hint Resolve in_subset_not: sets.
Hint Unfold fv: deriv.


Hint Rewrite fv_context_append: deriv.





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



Lemma subset_context_support: forall Γ, subset (support Γ) (fv_context Γ).
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


Lemma ex_falso_quolibet : forall P, false = true  -> P.
Proof.
  intros.
  congruence.
Qed.
Lemma trueAndTrue : True /\ True.
Proof.
  steps.
Qed.

Lemma inList1 : forall {T} n (l: list T), n ∈ n::l.
Proof.
  steps.
Qed.

Lemma inList2 : forall {T} n n0 (l: list T), n ∈ n0::n::l.
Proof.
  steps.
Qed.

Lemma inList3 : forall {T} n n0 n1 (l: list T), n ∈ n1::n0::n::l.
Proof.
  steps.
Qed.

Ltac inst_list_prop:=
  match goal with
  | H: forall x, x ∈ nil -> _ |- _ => clear H
  | H: forall x, x ∈ ?a1::nil ->  _ |- _ =>
    pose proof (H a1 (inList1 a1 nil)); clear H
  | H: forall x, x ∈ ?a1::?a2::nil -> _ |- _ =>
    pose proof (H a1 (inList1 a1 _));
    pose proof (H a2 (inList2 a2 a1 _)); clear H
  | H: forall x, x ∈ ?a1::?a2::?a3::nil -> _ |- _ =>
    pose proof (H a1 (inList1 a1 _) );
    pose proof (H a2 (inList2 a2 a1 _) );
    pose proof (H a3 (inList3 a3 a2 a1 _) ); clear H
 end.

Ltac modus_ponens :=
  match goal with
  | H1: ?A , H2: ?A -> _ |- _ => pose proof (H2 H1) ; clear H2
  end.

Lemma subset_open_open: forall k1 k2 t n3 n2 n1 A,
    subset (fv (open k1 (open k2 t (fvar n3 term_var)) (fvar n2 term_var))) (n1::n2::n3::A) ->
    ~ n3 ∈ (fv t) ->
    ~ n2 ∈ (fv t) ->
    ~ n1 ∈ (fv t) ->
    subset (fv t) A.
  intros.
  apply (subset_add5 _ n1 n2 n3 _ _ H2 H1 H0).
  pose proof (proj2
                (iff_and (singleton_subset (n1::n2::n3::A) n2))
                (inList2 n2 n1 (n3::A))) as H_temp1.
  pose proof (proj2
                (iff_and (singleton_subset (n1::n2::n3::A) n3))
                (inList3 n3 n2 n1 (A))) as H_temp2.
  rewrite <- (pfv_fvar n2 term_var) in H_temp1.
  rewrite <- (pfv_fvar n3 term_var) in H_temp2.
  pose proof (support_open (open k2 t (fvar n3 term_var)) (fvar n2 term_var) term_var k1 _ H H_temp1) as H_temp3.
  apply (support_open t (fvar n3 term_var) term_var k2 (n1::n2::n3::A) H_temp3 H_temp2).
Qed.


Ltac light_bool :=
  match goal with
  | H: _ |- _ => rewrite_strat hints bools in H
  end || destruct_and.


(* Unfold refinement in context *)
Fixpoint refinementUnfoldInContext Γ1 Γ2 :=
  match Γ1, Γ2 with
  | ((x, T_refine ty P)::Γ1') , ((p, T_equiv Px ttrue)::(y, ty')::Γ2') =>
    if ((PeanoNat.Nat.eqb x y) && (tree_eq ty ty') && (tree_eq Px (open 0 P (fvar x term_var)))
        && (context_eq Γ1' Γ2'))
    then Some (x,p,ty,P)
    else None
  | (x1,t1)::Γ1',(x2,t2)::Γ2' =>
    if (PeanoNat.Nat.eqb x1 x2 && tree_eq t1 t2)
    then (refinementUnfoldInContext Γ1' Γ2')
    else None
  | _,_ => None
  end.

Lemma refinementUnfoldInContext_nil :
  forall Γ, refinementUnfoldInContext Γ nil = None.
Proof. destruct Γ; steps. Qed.

Lemma if_same_result :
  forall A (b:bool) (a:A), (if b then a else a) = a.
Proof. steps. Qed.


Lemma refinementUnfoldInContext_nil2 :
  forall Γ x, refinementUnfoldInContext Γ (x::nil) = None.
Proof. destruct Γ. steps.
       destruct p, x, t ; repeat
         try solve [simpl; rewrite refinementUnfoldInContext_nil, if_same_result; reflexivity] ||
       destruct t0 ||
       destruct t0_2.
Qed.


Lemma refinementUnfoldInContext_same_head :
  forall Γ Γ1 Γ2, refinementUnfoldInContext (Γ++Γ1) (Γ++Γ2) = refinementUnfoldInContext Γ1 Γ2.
Proof.
  induction Γ. steps.
  intros.
  destruct a.
  assert (PeanoNat.Nat.eqb n n = true). rewrite PeanoNat.Nat.eqb_eq; eauto.
  assert (tree_eq t t = true). rewrite tree_eq_prop; eauto.
  destruct t eqn: T; repeat rewrite_any || simpl || reflexivity.
Qed.

Lemma refinementUnfoldInContext_prop :
  forall Γ1 Γ2 x p ty P,
    refinementUnfoldInContext Γ1 Γ2 = Some (x,p,ty,P) <->
    exists Γ Γ', (Γ1 = Γ++(x,T_refine ty P)::Γ' /\ Γ2 = Γ++(p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x,ty)::Γ').
  split; intros.
  + (* -> *)
    generalize dependent Γ2; induction Γ1; intros.
    ++ unfold refinementUnfoldInContext; steps.
    ++ destruct Γ2; try solve [ rewrite refinementUnfoldInContext_nil in H; discriminate].
       destruct Γ2; try solve [ rewrite refinementUnfoldInContext_nil2 in H; discriminate].
       destruct a, p0, p1.
       destruct t eqn: T;
         try solve [
               simpl in *; destruct_match; try discriminate;
               pose proof (IHΓ1 ((n1,t1)::Γ2) H) as [Γ [Γ' [Hg1 Hg2] ] ];
               bools; destruct_and; rewrite tree_eq_prop, PeanoNat.Nat.eqb_eq in *;
               exists ((n0,t)::Γ),Γ';  subst; rewrite_any; steps ] ;
       destruct t0 eqn: T0;
         try solve [
               simpl in *; destruct_match; try discriminate;
               pose proof (IHΓ1 ((n1,t1)::Γ2) H) as [Γ [Γ' [Hg1 Hg2] ] ];
               bools; destruct_and; rewrite tree_eq_prop, PeanoNat.Nat.eqb_eq in *;
               exists ((n0,t)::Γ),Γ';  subst; rewrite_any; steps ] ;
       destruct t2_4 eqn: T2_4;
         try solve [
               simpl in *; destruct_match; try discriminate;
               pose proof (IHΓ1 ((n1,t1)::Γ2) H) as [Γ [Γ' [Hg1 Hg2] ] ];
               bools; destruct_and; rewrite tree_eq_prop, PeanoNat.Nat.eqb_eq in *;
               exists ((n0,t)::Γ),Γ';  subst; rewrite_any; steps ].
       subst; simpl in H.
       destruct_match; try discriminate. bools. steps.
       rewrite tree_eq_prop, PeanoNat.Nat.eqb_eq in *.
       subst; exists nil, Γ1.
       assert (Γ1 = Γ2); unfold context_eq in H1; steps.
  + (* <- *)
    steps; induction Γ;
      repeat rewrite refinementUnfoldInContext_same_head ||
             steps || bools || list_utils ||
             rewrite PeanoNat.Nat.eqb_neq in * || unfold tree_eq,context_eq in * .
Qed.


Lemma refinementUnfoldInContext_fv :
  forall Γ1 Γ2 x p ty P tag,
    refinementUnfoldInContext Γ1 Γ2 = Some (x,p,ty,P) ->
    forall x, x ∈ (pfv_context Γ2 tag) <-> (x = p \/ x ∈ (pfv_context Γ1 tag)).
Proof.
  intros.
  rewrite refinementUnfoldInContext_prop in *.
  repeat steps || list_utils || fv_open ; eauto with sets fv.
Qed.


Lemma refinementUnfoldInContext_support1 :
  forall Γ1 Γ2 x p ty P,
    refinementUnfoldInContext Γ1 Γ2 = Some (x,p,ty,P) ->
    forall y, y ∈ support Γ2 ->
         y <> p ->
         y ∈ support Γ1.
Proof.
  intros.
  rewrite refinementUnfoldInContext_prop in *.
  repeat steps || list_utils || fv_open ; eauto with sets fv.
Qed.

Lemma refinementUnfoldInContext_support2 :
  forall Γ1 Γ2 x p ty P,
    refinementUnfoldInContext Γ1 Γ2 = Some (x,p,ty,P) ->
    subset (support Γ1) (support Γ2).
Proof.
  intros.
  rewrite refinementUnfoldInContext_prop in *.
  repeat steps || list_utils || fv_open ; eauto with sets fv.
Qed.


Lemma refinementUnfoldInContext_support3 :
  forall A Γ1 Γ2 x p ty P,
    refinementUnfoldInContext Γ1 Γ2 = Some (x,p,ty,P) ->
    subset A (support Γ2) ->
    ~ p ∈ A ->
    subset A (support Γ1).
Proof.
  intros.
  rewrite refinementUnfoldInContext_prop in *.
  repeat steps || list_utils || fv_open ; eauto with sets fv.
Qed.



Definition closed_valueb t := (wfb t 0) && (is_erased_termb t) && (is_value t) && (list_nat_eq (fv t) nil).

Lemma closed_valueb_prop :
  forall t, closed_valueb t = true <-> closed_value t.
Proof.
  unfold closed_valueb, closed_value, closed_term.
  repeat steps || bools || rewrite is_value_correct in * || rewrite wfb_prop in * || rewrite is_erased_termb_prop in * || rewrite list_nat_eq_prop in *.
Qed.

Hint Rewrite closed_valueb_prop: deriv.
