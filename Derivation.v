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

  (* tlet *)
  | N (J (InferLet B) Θ Γ (tlet t1 A t2) T)
      ((N ((J I1 _ _ _ _) as j1) _ as d1)
         :: (N ((J I2 _ ((p, _)::(x,_)::_) _ _) as j2) _ as d2) :: nil) =>
    (j1 ?= (J I1 Θ Γ t1 A)) && (is_valid d1)
    && (j2 ?= (J I2 Θ ((p, T_equiv (fvar x term_var) t1)::(x,A)::Γ) (open 0 t2 (fvar x term_var)) (open 0 B (fvar x term_var)))) && (is_valid d2)
    && (x ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (x ?<> p)
    && (x ?∉ (fv t2)) && (p ?∉ (fv t2))
    && (x ?∉ (fv B)) && (p ?∉ (fv B))
    && (x ?∉ (fv A)) && (p ?∉ (fv A))
    && (x ?∉ (fv t1)) && (p ?∉ (fv t1))
    && (x ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_typeb B)
    && (is_annotated_termb t1) && (is_annotated_termb t2)
    && (tree_eq T (open 0 B t1))

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


Ltac light_bool :=
  match goal with
  | H: _ |- _ => rewrite_strat hints bools in H
  end || destruct_and.

Ltac rewrite_deriv :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints deriv in H
  end.

Ltac destruct_clear t H := destruct t; try apply (ex_falso_quolibet _ H).

(* Conservation lemmas *)
Lemma is_valid_wf_aux: forall dv, is_valid dv = true -> wf (J_tree (root dv)) 0 /\ wf (J_type (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_tree, J_type. unfold forallP in X.
  destruct J. destruct name; destruct_clear t H.
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || light_bool || match goal with | H: wf (_ _) _ |- _ => simpl in H end || rewrite_deriv || invert_constructor_equalities || inst_list_prop || modus_ponens ; simpl.
  all: repeat split; eauto with wf.
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
  | H: subset (pfv (_ _ _) _) _ |- _ => simpl in H
  | H: subset _ (support (_::_)) |- _ => simpl in H
  | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
  | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2; eauto
  | _: ?x ∈ ?A -> False, H: subset ?A (?x::_) |- _ => apply subset_add3 in H; eauto
  | H1: ?m ∈ (fv ?t) -> False,
        H2: ?n ∈ (fv ?t) -> False,
            H3: subset (pfv (open 0 ?t (fvar ?n term_var)) term_var) (?m :: ?n :: (support ?Γ))
    |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H2) ;
    apply (subset_add3 _ m _ _ H1) ;
    apply (support_open t (fvar n term_var) term_var 0 (m::n::(support Γ)) H3) ;
    rewrite pfv_fvar ; eauto with sets
  |H: subset (fv (open ?k ?t1 ?t2)) _ |- _ => apply (support_open t1 t2 _) in H; clear H
  | H1: ?n ∈ (fv ?t) -> False,
        H2: subset (pfv (open 0 ?t (fvar ?n term_var)) term_var) (?n :: (support ?Γ))
    |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H1) ;
    apply (support_open t (fvar n term_var) term_var 0 (n::(support Γ)) H2) ;
    rewrite pfv_fvar ; eauto with sets
  | H1: ?m ∈ (fv ?t) -> False,
        H2: ?n ∈ (fv ?t) -> False,
            H3: subset (pfv (open 0 ?t (?c (fvar ?n term_var))) term_var) (?m :: ?n :: (support ?Γ))
    |- subset (pfv ?t term_var) (support ?Γ) =>
    apply (subset_add3 _ n _ _ H2) ;
    apply (subset_add3 _ m _ _ H1) ;
    apply (support_open t (c (fvar n term_var)) term_var 0 (m::n::(support Γ)) H3)
  | H:_ |- subset (pfv (open 0 ?t ?rep) term_var) ?A => apply (subset_transitive _ _ _ (fv_open _ _ _ _))
  end.

Lemma subset_nil : forall {T} A, @subset T nil A.
Proof.
  steps.
  eauto with sets.
Qed.

Lemma in_subset_not:
  forall {T} (l1 l2: list T) (x: T),
    subset l1 l2 -> not (x ∈ l2) -> not (x ∈ l1).
Proof.
  steps.
Qed.
Hint Resolve in_subset_not: sets.
Hint Unfold fv: deriv.

Lemma is_valid_support_term_aux : forall dv, is_valid dv = true -> subset (fv (J_tree (root dv)) ) (support (J_context (root dv))) /\ subset (fv (J_type (root dv)) ) (support (J_context (root dv))).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_tree, J_type, fv. unfold forallP in X.
  destruct J.
  pose proof (subset_context_support Γ).
  destruct name; destruct_clear t H.
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: simpl; eauto 2 using subset_nil.
  all: repeat subst || light_bool || rewrite_deriv || rewrite pfv_fvar || rewrite pfv_fvar2 ||
              match goal with
              | H1: ~ ?x ∈ ?A, H2: subset ?A (?x::?B) |- _ => apply (subset_add3 _ x A B H1) in H2
              | H: subset (pfv (_ _ _) _) _ |- _ => simpl in H
              | H: subset _ (support (_::_)) |- _ => simpl in H
              | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
              | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2; eauto
              | H1: ~ ?n ∈ (fv_context ?Γ),
                    H2: subset (support ?Γ) (fv_context ?Γ)
                |- _ => apply (in_subset_not (support Γ) (fv_context Γ) n H2) in H1
              | H: subset (fv (open ?k ?t1 ?t2)) ?A
                |- subset (pfv ?t1 term_var) _ => apply (support_open t1 t2 term_var k A) in H
              | H: subset( fv (_ _ _)) _ |- _ => cbn in H end
       || invert_constructor_equalities || apply support_open2|| inst_list_prop || modus_ponens || simpl || split; eauto 2 using singleton_subset, inList1, inList2, inList3 with sets.
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
Require Import SystemFR.AnnotatedLet.

(* Main soundess result *)
Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_tree, J_type, fv. unfold forallP in X.
  destruct J.
  pose proof (subset_context_support Γ).
  destruct name; destruct_clear t H.
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || light_bool || rewrite_deriv || invert_constructor_equalities || inst_list_prop || modus_ponens || simpl || consume_is_valid .
  (* remove easy cases *)
  all: eauto 2 with deriv.
  all: repeat  match goal with | H: is_true (root _) |- _ => simpl in H end.
  all: try apply (annotated_reducible_match Θ Γ _ _ _ T n7 n3); eauto.
  all: try apply (annotated_reducible_T_ite Θ Γ t1 t2 t3 T0 T1 n3); eauto.
  all: try eapply annotated_reducible_pi1; eauto.
  all: try eapply annotated_reducible_pi2; eauto.
  all: try eapply (annotated_reducible_pp Θ Γ); eauto.
  all: try eapply (annotated_reducible_app); eauto.
  all: try eapply annotated_reducible_lambda; eauto.
  all: try apply (annotated_reducible_sum_match Θ Γ t1 t2 t3 t4_1 t4_2 t0 n4 n3).
  all: try apply (annotated_reducible_let Θ Γ _ _ n4 n3).
  all: repeat destruct_and || assumption ||  match goal with
              | H1: ~ ?x ∈ ?A, H2: subset ?A (?x::?B) |- _ => apply (subset_add3 _ x A B H1) in H2
              | H: subset _ (support (_::_)) |- _ => simpl in H
              | H1: subset ?A ?B,
                    H2: subset ?B ?C,
                        H3: ~?n ∈ ?C
                |- ~ ?n ∈ ?A => apply (in_subset_not _ _ n (subset_transitive _ _ _ H1 H2) H3)
              | H: subset (fv (open ?k ?t1 ?t2)) ?A
                |- subset (fv ?t1) _ => apply (support_open t1 t2 term_var k A) in H
              | H: wf (open _ _ _) _ |- _ => apply wf_open_rev in H
              | H: wf (_ _ _) _ |- _ => simpl in H
              | H: subset (fv (_ _ _)) _ |- _ => cbn in H; apply subset_union3 in H
              | H: _ |- subset (singleton ?n) (?n :: _) => apply singleton_subset, inList1
              | H: _ |- subset (singleton ?n) (_ :: ?n :: _) => apply singleton_subset, inList2
              | H: _ |- subset (singleton ?n) (_ :: _ :: ?n :: _) => apply singleton_subset, inList3
                                           end || rewrite pfv_fvar || rewrite pfv_fvar2 || simpl.

Qed.
