Require Export SystemFR.DerivationHelpers.


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

  (* Pairs *)
  (* PP *)
  | N (J InferPP Θ Γ (pp t1 t2) (T_prod A B))
      ((N ((J I1 _ _ _ _) as j1) nil as d1)
         :: (N ((J I2 _ _ _ _) as j2) nil as d2)::nil) =>
    (j1 ?= (J I1 Θ Γ t1 A)) && (is_valid d1)
    && (j2 ?= (J I2 Θ Γ t2 (open 0 B t1))) && (is_valid d2)
    && (is_annotated_termb t1) && (is_annotated_typeb B)
  (* Pi1 *)
  | N (J InferPi1 Θ Γ (pi1 t) A) ((N ((J I1 _ _ _ (T_prod _ B)) as j) nil as d)::nil) =>
    (j ?= (J I1 Θ Γ t (T_prod A B))) && (is_valid d)
  (* Pi2 *)
  | N (J InferPi2 Θ Γ (pi2 t) T) ((N ((J I1 _ _ _ (T_prod A B)) as j) nil as d)::nil) =>
    (j ?= (J I1 Θ Γ t (T_prod A B))) && (is_valid d)
    && (is_annotated_typeb B)
    && (is_annotated_termb t)
    && ((fv B) ?⊂ (support Γ))
    && (tree_eq T (open 0 B (pi1 t)))

  (* App *)
  | N (J InferApp Θ Γ (app t1 t2) T)
      ((N ((J I1 _ _ _ (T_arrow U V)) as j1) nil as d1)
         :: (N ((J I2 _ _ _ _) as j2) nil as d2)::nil) =>
    (j1 ?= (J I1 Θ Γ t1 (T_arrow U V))) && (is_valid d1)
    && (j2 ?= (J I2 Θ Γ t2 U)) && (is_valid d2)
    && is_annotated_typeb V
    && is_annotated_termb t2
    && (tree_eq T (open 0 V t2))

  (* Lambda *)
  | N (J InferLambda Θ Γ (lambda U t) (T_arrow _ V as T))
      ((N ((J I1 _ ((x,_)::_) _ _) as j) nil as d)::nil) =>
    (j ?= (J I1 Θ ((x,U)::Γ) (open 0 t (fvar x term_var)) (open 0 V (fvar x term_var)))) && (is_valid d)
    && is_annotated_termb t
    && wfb U 0
    && (x ?∉ fv_context Γ)
    && (x ?∉ Θ)
    && (x ?∉ (fv V))
    && (x ?∉ (fv t))
    && ((fv U) ?⊂ (support Γ))
    && (fv_context Γ ?⊂ (support Γ))
    && is_annotated_typeb V
    && (tree_eq T (T_arrow U V))


  | _ => false
  end.



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


Ltac inst_list_prop:=
  match goal with
  | H: forall x, x ∈ ?a1::nil -> _ |- _ => unshelve epose proof (H a1 _); clear H
  | H: forall x, x ∈ ?a1::?a2::nil -> _ |- _ => unshelve epose proof (H a1 _); unshelve epose proof (H a2 _); clear H
  | H: forall x, x ∈ ?a1::?a2::?a3::nil -> _ |- _ => unshelve epose proof (H a1 _); unshelve epose proof (H a2 _); unshelve epose proof (H a3 _); clear H
  end.


(* Conservation lemmas *)
Lemma is_valid_wf_aux: forall dv, is_valid dv = true -> wf (J_tree (root dv)) 0 /\ wf (J_type (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_tree, J_type. unfold forallP in X.
  unfold is_valid in H.
  (repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || (destruct_match; try solve [congruence];  repeat fold is_valid in *) || intuition auto || simpl || match goal with |H: wf (_ _) _ |- _ => simpl in H end || eauto with cbn wf).
   Qed.


Lemma is_valid_wf_t : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf t 0.
Proof.
  intros; pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ); steps.
Qed.

Lemma is_valid_wf_T : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf T 0.
Proof.
  intros; pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ); steps.
Qed.



Lemma is_valid_support_term_aux : forall dv, is_valid dv = true -> subset (fv (J_tree (root dv)) ) (support (J_context (root dv))) /\ subset (fv (J_type (root dv)) ) (support (J_context (root dv))).
Proof.
  unfold fv.
  induction dv using derivation_ind.
  intros.
  unfold root, J_tree, J_type.
  unfold forallP in X.
  unfold is_valid in H ;
  repeat (subst || bools || destruct_and || (autorewrite with deriv in *) || inst_list_prop || invert_constructor_equalities || fold is_valid in * ||  (destruct_match; repeat fold is_valid in * ; try solve [congruence]) || intuition auto || simpl ||
         match goal with
         | H: subset (pfv (T_arrow _ _) _) _ |- _ => simpl in H
         | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
         | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2
         |H: subset (pfv (open ?k ?t1 ?t2) ?tag) ?A |- _ => ( try solve [eauto with cbn sets] ; (apply (support_open t1 t2 tag k) in H))
         end ) ;
  eauto using subset_transitive, subset_union2, fv_open with sets.
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


Hint Resolve is_valid_wf_t: deriv.
Hint Resolve is_valid_wf_T: deriv.

Ltac consume_is_valid :=
  match goal with
  | H: is_valid (N (J ?n ?Θ ?Γ ?t ?T) ?c) = true |- _ =>
    epose proof (is_valid_wf_t n Θ Γ t T c H) ;
    epose proof (is_valid_wf_T n Θ Γ t T c H) ;
    epose proof (is_valid_support_t n Θ Γ t T c H) ;
    epose proof (is_valid_support_T n Θ Γ t T c H) ; clear H
  end.

Lemma in_subset_not:
  forall {T} (l1 l2: list T) (x: T),
    subset l1 l2 -> not (x ∈ l2) -> not (x ∈ l1).
Proof.
  steps.
Qed.
Hint Resolve in_subset_not: sets.
Hint Unfold fv: deriv.

Lemma subset_any_type: forall n Γ,  subset (pfv (fvar n term_var) term_var) (n :: @support nat tree Γ).
Proof.
  intros. apply (support_fvar n zero Γ). Qed.
Hint Resolve subset_any_type: deriv.

Ltac subset_open :=
  match goal with
  | H: subset (fv (open ?k ?t (fvar ?n term_var))) (?n :: (support ?Γ)) |- _ =>
    pose proof (support_open t (fvar n term_var) term_var k (n::support Γ) H (subset_any_type n Γ)); clear H
  end.
Hint Extern 50 => eapply support_open: deriv.

(* Main soundess result *)
Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros.
  unfold forallP in X.
  unfold is_true. simpl.
  destruct J eqn:HJ.
  unfold is_valid in H.
  repeat (subst || bools || destruct_and || (autorewrite with deriv in *) || invert_constructor_equalities || (destruct_match; try solve [congruence] ; repeat fold is_valid in *) || inst_list_prop || intuition auto || consume_is_valid || simpl || cbn in * || subset_open) ;  eauto 4 using support_open, wf_open_rev, subset_add3, subset_any_type with deriv sets.
Qed.
