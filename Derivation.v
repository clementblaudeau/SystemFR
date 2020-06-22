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

  (* [Anotated] App *)
  | N (J InferApp Θ Γ (app t1 t2) T)
      ((N ((J I1 _ _ _ (T_arrow U V)) as j1) nil as d1)
         :: (N ((J I2 _ _ _ _) as j2) nil as d2)::nil) =>
    (j1 ?= (J I1 Θ Γ t1 (T_arrow U V))) && (is_valid d1)
    && (j2 ?= (J I2 Θ Γ t2 U)) && (is_valid d2)
    && is_annotated_typeb V
    && is_annotated_termb t2
    && (tree_eq T (open 0 V t2))


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


Ltac lighter :=
  (intros) ||
  (congruence) ||
  (subst) ||
  (destruct_and) ||
  intuition auto ||
  (cbn in *).

Ltac wf_root :=
  match goal with
  | H: wf (J_tree (root (N (J _ _ _ _ _) _))) _ |- _ => simpl in H
  | H: wf (J_type (root (N (J _ _ _ _ _) _))) _ |- _ => simpl in H
  | H: wf (J_context (root (N (J _ _ _ _ _) _))) _ |- _ => simpl in H
  end.


(* Conservation lemmas *)
Lemma is_valid_wf_aux: forall dv, is_valid dv = true -> wf (J_tree (root dv)) 0 /\ wf (J_type (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_tree, J_type. unfold forallP in X. unfold is_valid in H.
  (repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || (destruct_match; try solve [congruence];  repeat fold is_valid in *) || wf_root || intuition auto || simpl) ; eauto with cbn wf.
Qed.

Lemma is_valid_wf_t : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf t 0.
Proof.
  intros; pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ); steps.
Qed.

Lemma is_valid_wf_T : forall n Θ Γ t T c, is_valid (N (J n Θ Γ t T) c) = true -> wf T 0.
Proof.
  intros; pose proof (is_valid_wf_aux  (N (J n Θ Γ t T) c) H ); steps.
Qed.

Lemma J_tree_root : forall n Θ Γ t T c, J_tree (root (N (J n Θ Γ t T) c)) = t. Proof. steps. Qed.
Lemma J_type_root : forall n Θ Γ t T c, J_type (root (N (J n Θ Γ t T) c)) = T. Proof. steps. Qed.
Lemma J_context_root : forall n Θ Γ t T c, J_context (root (N (J n Θ Γ t T) c)) = Γ. Proof. steps. Qed.
Hint Rewrite J_tree_root J_type_root  J_context_root: deriv.


Lemma is_valid_support_term_aux : forall dv, is_valid dv = true -> subset (fv (J_tree (root dv)) ) (support (J_context (root dv))) /\ subset (fv (J_type (root dv)) ) (support (J_context (root dv))).
Proof.
  unfold fv.
  induction dv using derivation_ind.
  intros.
  unfold root, J_tree, J_type.
  unfold forallP in X.
  unfold is_valid in H.
  repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || fold is_valid in * ||  (destruct_match; repeat fold is_valid in * ; try solve [congruence]) || wf_root || intuition auto || simpl  ; eauto using subset_transitive, subset_union2, fv_open with cbn sets.
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


(* Main soundess result *)
Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros.
  unfold forallP in X.
  unfold is_true. simpl.
  destruct J eqn:HJ.
  unfold is_valid in H.
  repeat subst || bools || destruct_and || autorewrite with deriv in * || invert_constructor_equalities || (destruct_match; try solve [congruence] ; repeat fold is_valid in *) || inst_list_prop || intuition auto || consume_is_valid.
   simpl. eauto with deriv cbn sets.
   simpl. eauto with deriv cbn sets.
   simpl. eauto with deriv cbn sets.
   pose proof annotated_reducible_app.

   simpl. eauto with deriv cbn sets.
   simpl. eauto with deriv cbn sets.
   simpl. eauto with deriv cbn sets.
   simpl. eauto with deriv cbn sets.





    Qed.
