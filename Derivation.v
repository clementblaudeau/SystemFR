Require Export SystemFR.DerivationHelpers.
Require Export SystemFR.Syntax.


Fixpoint is_valid(dv: derivation) : bool :=
  match dv with
  (* | N (InferJudgment "InferUnit" _ _ uu T_unit) nil => true *)

  (* Bools *)
  | N (J (InferBool | CheckBool) _ _ ttrue T_bool) nil => true
  | N (J (InferBool | CheckBool) _ _ tfalse T_bool) nil => true

  (* Naturals *)
  | N (J (InferNat | CheckNat) _ _ zero T_nat) nil => true
  | N (J (InferNat | CheckNat) Θ Γ (succ t) T_nat) (N j _ as dv' ::nil) =>
    (j ?= (J CheckNat Θ Γ t T_nat)) && (is_valid dv')
  | N (J InferMatch Θ Γ (tmatch tn t0 ts) T)
      ((N jn nil as dn)
         ::(N ((J I0 _ ((p, _)::_) _ _) as j0) _ as d0)
         ::(N ((J Is _ ((_,_)::(n,_)::_) _ _) as js) _ as ds)
         ::nil) =>
    (jn ?= (J CheckNat Θ Γ tn T_nat)) && (is_valid dn)
    && (j0 ?= (J I0 Θ ((p, T_equiv tn zero)::Γ) t0 T)) && (is_valid d0)
    && (js ?= (J Is Θ ((p, T_equiv tn (succ (fvar n term_var)))::(n, T_nat)::Γ) (open 0 ts (fvar n term_var)) T))
    && (is_valid ds)
    && (p ?∉ (fv ts)) && (p ?∉ (fv t0)) && (p ?∉ (fv tn)) && (p ?∉ (fv T)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv tn)) && (n ?∉ (fv ts)) && (n ?∉ (fv T)) && (n ?∉ (fv_context Γ))
    && (n ?<> p) && (n ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_termb ts)

  (* If then else *)
  | N (J InferIf Θ Γ (ite b t1 t2) T)
      ((N jb _ as db)
         ::(N ((J I1 _ ((x,Te1)::_) _ T1) as j1) _ as d1)
         ::(N ((J I2 _ ((_,Te2)::_) _ T2) as j2) _ as d2)
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
    && (x ?∉ Θ )

  (* Pairs *)
  (* PP *)
  | N (J InferPP Θ Γ (pp t1 t2) (T_prod A B))
      ((N ((J I1 _ _ _ _) as j1) _ as d1)
         :: (N ((J I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (J I1 Θ Γ t1 A)) && (is_valid d1)
    && (j2 ?= (J I2 Θ Γ t2 (open 0 B t1))) && (is_valid d2)
    && (is_annotated_termb t1) && (is_annotated_typeb B)
  (* Pi1 *)
  | N (J InferPi1 Θ Γ (pi1 t) A) ((N ((J I1 _ _ _ (T_prod _ B)) as j) _ as d)::nil) =>
    (j ?= (J I1 Θ Γ t (T_prod A B))) && (is_valid d)
  (* Pi2 *)
  | N (J InferPi2 Θ Γ (pi2 t) T) ((N ((J I1 _ _ _ (T_prod A B)) as j) _ as d)::nil) =>
    (j ?= (J I1 Θ Γ t (T_prod A B))) && (is_valid d)
    && (is_annotated_typeb B)
    && (is_annotated_termb t)
    && ((fv B) ?⊂ (support Γ))
    && (tree_eq T (open 0 B (pi1 t)))

  (* Sums *)
  (* Left *)
  | N (J InferLeft Θ Γ (tleft t) (T_sum A B)) ((N ((J I1 _ _ _ _) as j) _ as d)::nil) =>
    (j ?= (J I1 Θ Γ t A)) && (is_valid d) && (wfb B 0) && ((fv B) ?⊂ (support Γ))
  (* Right *)
  | N (J InferRight Θ Γ (tright t) (T_sum A B)) ((N ((J I1 _ _ _ _) as j) _ as d)::nil) =>
    (j ?= (J I1 Θ Γ t B)) && (is_valid d) && (wfb A 0) && ((fv A) ?⊂ (support Γ))
  (* Sum_match *)
  | N (J (InferSumMatch T) Θ Γ (sum_match t tl tr) T')
      ((N ((J I1 _ _ _ (T_sum A B)) as j) _ as d)
         :: (N ((J Il _ ((p, _)::(y, _)::_) _ _) as jl) _ as dl)
         :: (N ((J Ir _ _ _ _) as jr) _ as dr) :: nil) =>
       (j ?= (J I1 Θ Γ t (T_sum A B))) && (is_valid d)
       && (jl ?= (J Il Θ ((p, T_equiv t (tleft (fvar y term_var)))::(y, A)::Γ) (open 0 tl (fvar y term_var)) (open 0 T (tleft (fvar y term_var)))))
       && (is_valid dl)
       && (jr ?= (J Ir Θ ((p, T_equiv t (tright (fvar y term_var)))::(y, B)::Γ) (open 0 tr (fvar y term_var)) (open 0 T (tright (fvar y term_var)))))
       && (is_valid dr)
       && (tree_eq T' (open 0 T t))
       && (p ?∉ (fv tl)) && (p ?∉ (fv tr)) && (p ?∉ (fv t)) && (p ?∉ (fv T)) && (p ?∉ (fv A)) && (p ?∉ (fv B)) && (p ?∉ (fv_context Γ))
       && (y ?∉ (fv tl)) && (y ?∉ (fv tr)) && (y ?∉ (fv t)) && (y ?∉ (fv T)) && (y ?∉ (fv A)) && (y ?∉ (fv B)) && (y ?∉ (fv_context Γ))
       && (y ?<> p) && (y ?∉ Θ) && (p ?∉ Θ)
       && (is_annotated_termb t) && (is_annotated_termb tl)
       && (is_annotated_termb tr)  && (is_annotated_typeb T)


  (* App *)
  | N (J InferApp Θ Γ (app t1 t2) T)
      ((N ((J I1 _ _ _ (T_arrow U V)) as j1) _ as d1)
         :: (N ((J I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (J I1 Θ Γ t1 (T_arrow U V))) && (is_valid d1)
    && (j2 ?= (J I2 Θ Γ t2 U)) && (is_valid d2)
    && is_annotated_typeb V
    && is_annotated_termb t2
    && (tree_eq T (open 0 V t2))

  (* Lambda *)
  | N (J InferLambda Θ Γ (lambda U t) (T_arrow _ V as T))
      ((N ((J I1 _ ((x,_)::_) _ _) as j) _ as d)::nil) =>
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
  unfold is_valid in H ;
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

Ltac basic_is_valid := repeat subst || bools || destruct_and || autorewrite with deriv in * || inst_list_prop || invert_constructor_equalities || fold is_valid in * ||  (destruct_match; repeat fold is_valid in * ; try solve [congruence]) || intuition auto || simpl.

Ltac is_valid_support_ltac :=
  match goal with
  | H: subset (pfv (T_arrow _ _) _) _ |- _ => simpl in H
  | H: subset (pfv (T_sum _ _) _) _ |- _ => simpl in H
  | H: subset _ (support (_::_)) |- _ => simpl in H
  | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
  | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2; eauto
  | _: ?x ∈ ?A -> False, H: subset ?A (?x::_) |- _ => apply subset_add3 in H; eauto
  | H1: ?m ∈ (fv ?t) -> False, H2: ?n ∈ (fv ?t) -> False, H3: subset (pfv (open 0 ?t (fvar ?n term_var)) term_var) (?m :: ?n :: (support ?Γ)) |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H2) ;
    apply (subset_add3 _ m _ _ H1) ;
    apply (support_open t (fvar n term_var) term_var 0 (m::n::(support Γ)) H3) ;
    rewrite pfv_fvar ; eauto with sets
  | H1: ?n ∈ (fv ?t) -> False, H2: subset (pfv (open 0 ?t (fvar ?n term_var)) term_var) (?n :: (support ?Γ)) |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H1) ;
    apply (support_open t (fvar n term_var) term_var 0 (n::(support Γ)) H2) ;
    rewrite pfv_fvar ; eauto with sets
  | H1: ?m ∈ (fv ?t) -> False, H2: ?n ∈ (fv ?t) -> False, H3: subset (pfv (open 0 ?t (?c (fvar ?n term_var))) term_var) (?m :: ?n :: (support ?Γ)) |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H2) ;
    apply (subset_add3 _ m _ _ H1) ;
    apply (support_open t (c (fvar n term_var)) term_var 0 (m::n::(support Γ)) H3)
  | H:_ |- subset (pfv (open 0 ?t ?rep) term_var) ?A => apply (subset_transitive _ _ _ (fv_open _ _ _ _))
  end.




Lemma is_valid_support_term_aux : forall dv, is_valid dv = true -> subset (fv (J_tree (root dv)) ) (support (J_context (root dv))) /\ subset (fv (J_type (root dv)) ) (support (J_context (root dv))).
Proof.
  unfold fv.
  induction dv using derivation_ind.
  intros.
  unfold root, J_tree, J_type.
  unfold forallP in X.
  unfold is_valid in H ; repeat basic_is_valid ; eauto 2 using fv_open, subset_transitive, subset_union2 with sets;   repeat is_valid_support_ltac || basic_is_valid ; eauto 4 using fv_open, subset_transitive, subset_union2  with sets.
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
Hint Rewrite PeanoNat.Nat.eqb_neq: deriv.

Ltac destruct_match_congruence := destruct_match ; try solve [bools; congruence].

(* Main soundess result *)
Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros.
  unfold forallP in X.
  unfold is_true. simpl.
  destruct J eqn:HJ.
  unfold is_valid in H ; repeat basic_is_valid; eauto 2 with deriv ;
    repeat invert_constructor_equalities || inst_list_prop || consume_is_valid || match goal with | H: is_true (root (N _ _)) |- _ => simpl in H end || subst || intuition auto || subset_open || is_valid_support_ltac ||
           match goal with
           | H: subset (fv (open 0 ?t (fvar ?n term_var))) (?m :: ?n :: ?A) |- _ =>
             apply (support_open _ (fvar n term_var) term_var 0 _) in H; eauto 2 with deriv sets
           | H: wf (open _ _ _) _ |- _ => apply wf_open_rev in H
           end ; eauto 3 with sets deriv.

  eauto 3 with sets deriv.
  apply (annotated_reducible_ite _ _ _ _ _ _ n); eauto 2 using support_open, wf_open_rev, subset_add3, subset_any_type with deriv sets cbn.
  unfold fv.
  unfold T_ite.
  simpl.
  unfold pfv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.
  eauto 3 with sets deriv.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  apply (support_open _ (fvar _ term_var) term_var 0 _) in H20; eauto 2 with sets deriv.

  admit.
  simpl; eauto with sets deriv.
  fold fv in H20.
  is_valid_support_ltac.
  admit.

  match goal with | H: subset (fv (open ?k ?t (fvar ?n term_var))) (?m :: ?n :: ?A) |- _ => apply (support_open t (fvar ?n term_var) term_var k ((m :: n :: A))) in H end.

match goal with | H: subset (fv (open ?k ?t (fvar ?n term_var))) (_ :: ?n :: ?A) |- _ => eapply support_open in H; eauto with sets end.





  repeat eapply support_open; eauto.
  repeat destruct_match_congruence ;
    repeat subst || bools || destruct_and || autorewrite with deriv in * || invert_constructor_equalities || inst_list_prop || intuition auto || consume_is_valid || simpl.
  ; eauto 2 using support_open, wf_open_rev, subset_add3, subset_any_type with deriv sets.
  repeat match goal with | H: is_true (root (N _ _)) |- _ => simpl in H end.



                                                                                                       || cbn in * || subset_open || is_valid_support_ltac  ;

  apply (annotated_reducible_match Θ Γ _ _ _ _ n2 n); eauto 2 with sets.
  apply PeanoNat.Nat.eqb_neq; eauto.
  eauto 3 using wf_open_rev with deriv.
  apply (subset_add3 _ n2 _ _ H6).
  apply (subset_add3 _ n _ _ H12).
  eapply support_open; eauto.
  rewrite pfv_fvar; eauto with sets.
  eauto 4 using support_open, wf_open_rev, subset_add3, subset_any_type with deriv sets.
Qed.
