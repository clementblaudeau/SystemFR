Require Export SystemFR.DerivationTrees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Evaluator.
Require Export SystemFR.NatLessThanErase.


Reset Ltac Profile.
Set Ltac Profiling.

Fixpoint is_valid(dv: derivation) : bool :=
  match dv with
  (* | N (InferJudgment "InferUnit" _ _ uu T_unit) nil => true *)

  (* TYPING JUDGMENTS *)

  (* Bools *)
  | N (TJ J_Bool _ _ ttrue T_bool) nil => true
  | N (TJ J_Bool _ _ tfalse T_bool) nil => true

  (* Naturals *)
  | N (TJ J_Nat _ _ zero T_nat) nil => true
  | N (TJ J_Nat _ _ (succ t) T_nat) nil => (isNat t)
  | N (TJ J_Nat Θ Γ (succ t) T_nat) (N (TJ I0 _ _ _ T_nat as j) _ as dv' ::nil) =>
    (j ?= (TJ I0 Θ Γ t T_nat)) && (is_valid dv')
  | N (TJ J_Match Θ Γ (tmatch tn t0 ts) T)
      ((N jn nil as dn)
         ::(N ((TJ I0 _ ((p, _)::_) _ _) as j0) _ as d0)
         ::(N ((TJ Is _ ((_,_)::(n,_)::_) _ _) as js) _ as ds)
         ::nil) =>
    (jn ?= (TJ J_Nat Θ Γ tn T_nat)) && (is_valid dn)
    && (j0 ?= (TJ I0 Θ ((p, T_equiv tn zero)::Γ) t0 T)) && (is_valid d0)
    && (js ?= (TJ Is Θ ((p, T_equiv tn (succ (fvar n term_var)))::(n, T_nat)::Γ) (open 0 ts (fvar n term_var)) T))
    && (is_valid ds)
    && (p ?∉ (fv ts)) && (p ?∉ (fv t0)) && (p ?∉ (fv tn)) && (p ?∉ (fv T)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv tn)) && (n ?∉ (fv ts)) && (n ?∉ (fv T)) && (n ?∉ (fv_context Γ))
    && (n ?<> p) && (n ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_termb ts)

  (* If then else *)
  | N (TJ J_If Θ Γ (ite b t1 t2) T)
      ((N (TJ Ic _ _ _ _ as jb) _ as db)
         ::(N ((TJ I1 _ ((x1,(T_equiv _ ttrue))::_) _ T1) as j1) _ as d1)
         ::(N ((TJ I2 _ ((x2,(T_equiv _ tfalse))::_) _ T2) as j2) _ as d2)
         ::nil) =>
    (jb ?= (TJ Ic Θ Γ b T_bool)) && (is_valid db)
    && (x1 ?∉ (fv_context Γ))
    && (x1 ?∉ Θ )
    && (x1 ?∉ (fv t1))
    && (x2 ?∉ (fv t2))
    && ((PeanoNat.Nat.eqb x1 x2) || ((x2 ?∉ (fv_context Γ)) && (x2 ?∉ Θ ))) &&
    if (tree_eq T (T_ite b T1 T2)) then (
        (* Type unification *)
        (j1 ?= (TJ I1 Θ ((x1, T_equiv b ttrue)::Γ) t1 T1)) && (is_valid d1)
        && (j2 ?= (TJ I2 Θ ((x2, T_equiv b tfalse)::Γ) t2 T2)) && (is_valid d2)
        && (x1 ?∉ (fv T1))
        && (x2 ?∉ (fv T2))
      )
    else (
        (* Same type *)
        (j1 ?= (TJ I1 Θ ((x1, T_equiv b ttrue)::Γ) t1 T)) && (is_valid d1)
        && (j2 ?= (TJ I2 Θ ((x2, T_equiv b tfalse)::Γ) t2 T)) && (is_valid d2)
        && (x1 ?∉ (fv T)) && (x2 ?∉ (fv T))
      )



  (* Pairs *)
  (* PP *)
  | N (TJ J_PP Θ Γ (pp t1 t2) (T_prod A B))
      ((N ((TJ I1 _ _ _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Γ t1 A)) && (is_valid d1)
    && (j2 ?= (TJ I2 Θ Γ t2 (open 0 B t1))) && (is_valid d2)
    && (is_annotated_termb t1) && (is_annotated_typeb B)
  (* Pi1 *)
  | N (TJ J_Pi1 Θ Γ (pi1 t) A) ((N ((TJ I1 _ _ _ (T_prod _ B)) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Γ t (T_prod A B))) && (is_valid d)
  (* Pi2 *)
  | N (TJ J_Pi2 Θ Γ (pi2 t) T) ((N ((TJ I1 _ _ _ (T_prod A B)) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Γ t (T_prod A B))) && (is_valid d)
    && (is_annotated_typeb B)
    && (is_annotated_termb t)
    && ((fv B) ?⊂ (support Γ))
    && (tree_eq T (open 0 B (pi1 t)))

  (* Sums *)
  (* Left *)
  | N (TJ J_Left Θ Γ (tleft t) (T_sum A B)) ((N ((TJ I1 _ _ _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Γ t A)) && (is_valid d) && (wfb B 0) && ((fv B) ?⊂ (support Γ))
  (* Right *)
  | N (TJ J_Right Θ Γ (tright t) (T_sum A B)) ((N ((TJ I1 _ _ _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Γ t B)) && (is_valid d) && (wfb A 0) && ((fv A) ?⊂ (support Γ))
  (* Sum_match *)
  | N (TJ (J_SumMatch T) Θ Γ (sum_match t tl tr) T')
      ((N ((TJ I1 _ _ _ (T_sum A B)) as j) _ as d)
         :: (N ((TJ Il _ ((p, _)::(y, _)::_) _ _) as jl) _ as dl)
         :: (N ((TJ Ir _ _ _ _) as jr) _ as dr) :: nil) =>
       (j ?= (TJ I1 Θ Γ t (T_sum A B))) && (is_valid d)
       && (jl ?= (TJ Il Θ ((p, T_equiv t (tleft (fvar y term_var)))::(y, A)::Γ) (open 0 tl (fvar y term_var)) (open 0 T (tleft (fvar y term_var)))))
       && (is_valid dl)
        && (jr ?= (TJ Ir Θ ((p, T_equiv t (tright (fvar y term_var)))::(y, B)::Γ) (open 0 tr (fvar y term_var)) (open 0 T (tright (fvar y term_var)))))
       && (is_valid dr)
       && (tree_eq T' (open 0 T t))
       && (p ?∉ (fv tl)) && (p ?∉ (fv tr)) && (p ?∉ (fv t)) && (p ?∉ (fv T)) && (p ?∉ (fv A)) && (p ?∉ (fv B)) && (p ?∉ (fv_context Γ))
       && (y ?∉ (fv tl)) && (y ?∉ (fv tr)) && (y ?∉ (fv t)) && (y ?∉ (fv T)) && (y ?∉ (fv A)) && (y ?∉ (fv B)) && (y ?∉ (fv_context Γ))
       && (y ?<> p) && (y ?∉ Θ) && (p ?∉ Θ)
       && (is_annotated_termb t) && (is_annotated_termb tl)
       && (is_annotated_termb tr)  && (is_annotated_typeb T)


  (* App *)
  | N (TJ J_App Θ Γ (app t1 t2) T)
      ((N ((TJ I1 _ _ _ (T_arrow U V)) as j1) _ as d1)
         :: (N ((TJ I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Γ t1 (T_arrow U V))) && (is_valid d1)
    && (j2 ?= (TJ I2 Θ Γ t2 U)) && (is_valid d2)
    && is_annotated_typeb V
    && is_annotated_termb t2
    && (tree_eq T (open 0 V t2))

  (* Lambda *)
  | N (TJ J_Lambda Θ Γ (lambda U t) (T_arrow _ V as T))
      ((N ((TJ I1 _ ((x,_)::_) _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ ((x,U)::Γ) (open 0 t (fvar x term_var)) (open 0 V (fvar x term_var)))) && (is_valid d)
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
  | N (TJ (J_Let B) Θ Γ (tlet t1 A t2) T)
      ((N ((TJ I1 _ _ _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ ((p, _)::(x,_)::_) _ _) as j2) _ as d2) :: nil) =>
    (j1 ?= (TJ I1 Θ Γ t1 A)) && (is_valid d1)
    && (j2 ?= (TJ I2 Θ ((p, T_equiv (fvar x term_var) t1)::(x,A)::Γ) (open 0 t2 (fvar x term_var)) (open 0 B (fvar x term_var)))) && (is_valid d2)
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

  (* Var *)
  | N (TJ J_Var _ Γ (fvar x term_var) T) nil =>
    (option_tree_dec_eq (lookup PeanoNat.Nat.eq_dec Γ x) (Some T))
    && (wfb T 0) && (subsetb (fv T) (support Γ))

  (* Drop refinement *)
  | N (TJ J_drop Θ Γ t T2)
      ((N ((TJ I1 _ _ _ T1) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Γ t T1)) && (is_valid d1) && (tree_eq T2 (drop_refinement T1))

  (* Unfold refinement - typing jugement version *)
  | N (TJ J_refine_unfold Θ Γ t T)
      (( N ((TJ I1 _ Γ' _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Γ' t T)) && (is_valid d1) &&
    match refinementUnfoldInContext Γ' Γ with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (is_annotated_termb P) && ((fv ty) ?⊂ (support Γ')) && ((fv P) ?⊂ (support Γ'))
        && (wfb P 1))
    | None => false
    end



  (* Add refinement *)
  | N (TJ J_refine Θ Γ t (T_refine A b))
      (( N ((TJ I1 _ _ _ _) as j1) _ as d1)
         :: ( N ((EJ I2 _ ((p, _)::(x, _)::_) B ttrue) as j2) _ as d2):: nil) =>
    (j1 ?= (TJ I1 Θ Γ t A)) && (is_valid d1)
    && (j2 ?= (EJ I2 Θ ((p, T_equiv (fvar x term_var) t) :: (x,A) :: Γ) (open 0 b (fvar x term_var)) ttrue)) && (is_valid d2)
    && (p ?∉ (fv_context Γ)) && (p ?∉ (fv b)) && (p ?∉ (fv t)) && (p ?∉ (fv A)) && (p ?∉ Θ)
    && (x ?∉ (fv_context Γ)) && (x ?∉ (fv b)) && (x ?∉ (fv t)) && (x ?∉ (fv A)) && (x ?∉ Θ)
    && (x ?<> p) && (is_annotated_termb b) && ((fv b) ?⊂ (fv_context Γ))


  (* Var - weaken *)
  | N (TJ J_VarWeaken Θ ((x,T)::Γ) u U)
      ((N ((TJ I1 _ _ _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Γ u U)) && (is_valid d1)
    && (x ?∉ (support Γ)) && (x ?∉ (fv u)) && (x ?∉ (fv U)) && (x ?∉ Θ)

  (* Fix *)
  | N (TJ J_Fix Θ Γ (tfix T ts) (T_forall T_nat T'))
      ((N ((TJ I1 _ ((p, _)::(y, _)::(n, _)::_) _ _) as j1) _ as d1) :: nil) =>
    (tree_eq T T')
    && (j1 ?= (TJ I1 Θ ((p, T_equiv (fvar y term_var) (tfix T ts))
                         ::(y, T_forall (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var))) T)
                         ::(n, T_nat)::Γ)
                 (open 0 (open 1 ts (fvar n term_var)) (fvar y term_var))
                 (open 0 T (fvar n term_var))))
    && (isValue (erase_term ts)) && (is_valid d1)
    && (n ?∉ (fv_context Γ)) && (y ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv T)) && (y ?∉ (fv T)) && (p ?∉ (fv T))
    && (n ?∉ (fv ts)) && (y ?∉ (fv ts)) && (p ?∉ (fv ts))
    && (n ?∉ Θ) && (y ?∉ Θ) && (p ?∉ Θ)
    && (NoDupb (n::y::p::nil)) && (wfb (erase_term ts) 1) && (wfb ts 1)
    && (is_annotated_termb ts) && (is_annotated_typeb T)

  (* Elimination *)
  | N (TJ J_equiv_elim Θ Γ t2 T)
      (( N ((EJ I1 _ _ t1 _) as j1) _  as d1)
         :: ( N ((TJ I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (EJ I1 Θ Γ t1 t2)) && (is_valid d1)
    && (j2 ?= (TJ I2 Θ Γ t1 T)) && (is_valid d2)

  (* Forall Instantiation *)
  | N (TJ J_forall_inst Θ Γ (forall_inst t1 t2) T2)
      (( N ((TJ I1 _ _ _ (T_forall U V)) as j1) _ as d1)
         :: ( N ((TJ I2 _ _ _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Γ t1 (T_forall U V))) && (is_valid d1)
    && (j2 ?= (TJ I2 Θ Γ t2 U)) && (is_valid d2)
    && (tree_eq T2 (open 0 V t2))
    && ((fv t1) ?⊂ (support Γ)) && ((fv t2) ?⊂ (support Γ)) && ((fv V) ?⊂ (support Γ))
    && (is_annotated_typeb V) && (is_annotated_termb t2)

  (* EQUIVALENCE JUDGMENTS *)
  (* Symetric *)
  | N (EJ E_sym Θ Γ t1 t2)
      ((N ((EJ I1 _ _ _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (EJ I1 Θ Γ t2 t1)) && (is_valid d1)

  (* Transitivity *)
  | N (EJ E_trans Θ Γ t1 t3)
      ((N ((EJ I1 _ _ _ t2) as j1) _ as d1)
         :: (N ((EJ I2 _ _ _ _) as j2) _ as d2) :: nil) =>
       (j1 ?= (EJ I1 Θ Γ t1 t2)) && (is_valid d1)
       && (j2 ?= (EJ I2 Θ Γ t2 t3)) && (is_valid d2)

  (* Reflexivity *)
  | N (EJ E_refl Θ Γ t t') nil =>
    (tree_eq t t') && (wfb t 0)
    && ((fv t) ?⊂ (support Γ))
    && (is_erased_termb t)

  (* Lambdas *)
  | N (EJ E_lambdas Θ Γ (lambda A t1) (lambda B t2))
      (( N ((EJ I1 _ _ _ _) as j1) _ as d1) :: nil) =>
    (j1 ?= (EJ I1 Θ Γ t1 t2)) && (is_valid d1)
    && (wfb A 0) && (wfb B 0) (* ADDED HYPOTHESIS *)
    && (is_annotated_termb t1)
    && (is_annotated_termb t2)
    && (is_annotated_typeb A)
    && (subsetb (fv A) (support Γ))
    && (subsetb (fv B) (support Γ)) (* ADDED HYPOTHESIS *)

  (* Context *)
  | N (EJ (E_context C) Θ Γ T1 T2)
      (( N ((EJ I1 _ _ t1 t2) as j1)   as d1) :: nil) =>
    (j1 ?= (EJ I1 Θ Γ t1 t2)) && (is_valid d1)
    && (is_annotated_termb t1) && (is_annotated_termb t2)
    && (subsetb (fv C) (support Γ)) && (is_annotated_termb C)
    && (tree_eq T1 (open 0 C t1))
    && (tree_eq T2 (open 0 C t2))
    && (wfb C 1)

  (* Unfold refinement - equivalence jugement version *)
  | N (EJ E_refine_unfold Θ Γ t T)
      (( N ((EJ I1 _ Γ' _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (EJ I1 Θ Γ' t T)) && (is_valid d1) &&
    match refinementUnfoldInContext Γ' Γ with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (is_annotated_termb P) && ((fv ty) ?⊂ (support Γ')) && ((fv P) ?⊂ (support Γ'))
        && (wfb P 1))
    | None => false
    end

  (* Pair ext *)
  | N (EJ E_pair_ext Θ Γ t T)
      (( N ((TJ I1 _ _ _ (T_prod A B)) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Γ t (T_prod A B))) && (is_valid d1)
    && (tree_eq T (pp (pi1 t) (pi2 t)))
    && (is_annotated_termb t)

  (* SMT solver (trusted) *)
  | N (EJ E_SMT Θ Γ t1 t2) c =>
    (List.forallb is_valid c) && (wfb t1 0) && (wfb t2 0)
    && ((fv t1) ?⊂ (support Γ)) && ((fv t2) ?⊂ (support Γ))

  | _ => false
  end.



Ltac rewrite_deriv :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints deriv in H
  end.

Ltac destruct_clear t H := destruct t; try apply (ex_falso_quolibet _ H).


Lemma is_valid_wf_aux: forall dv, is_valid dv = true -> wf (J_term1 (root dv)) 0 /\ wf (J_term2 (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2. unfold forallP in X.
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || light_bool || match goal with | H: wf (_ _) _ |- _ => simpl in H end || rewrite_deriv || invert_constructor_equalities || inst_list_prop || modus_ponens ; simpl.
  all: repeat split; eauto with wf.
Qed.

Lemma is_valid_wf_t : forall n Θ Γ t T c, is_valid (N (TJ n Θ Γ t T) c) = true -> wf t 0.
Proof. intros; pose proof (is_valid_wf_aux  (N (TJ n Θ Γ t T) c) H ); steps. Qed.

Lemma is_valid_wf_T : forall n Θ Γ t T c, is_valid (N (TJ n Θ Γ t T) c) = true -> wf T 0.
Proof. intros; pose proof (is_valid_wf_aux  (N (TJ n Θ Γ t T) c) H ); steps. Qed.

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

Hint Rewrite fv_context_append: deriv.

Lemma is_valid_support_term_aux :
  forall dv, is_valid dv = true ->
        subset (fv (J_term1 (root dv)) ) (support (J_context (root dv))) /\
        subset (fv (J_term2 (root dv)) ) (support (J_context (root dv))).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv. unfold forallP in X.
  destruct J.
  pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: simpl; eauto 2 using subset_nil.
  all: unfold fv_context in *.
  all: repeat subst || light_bool || rewrite_deriv || discriminate || rewrite pfv_fvar || rewrite pfv_fvar2 ||
              match goal with
              | H1: ~ ?x ∈ ?A, H2: subset ?A (?x::?B) |- _ => apply (subset_add3 _ x A B H1) in H2
              | H: subset (pfv (_ _ _) _) _ |- _ => simpl in H
              | H: subset _ (support (_::_)) |- _ => simpl in H
              | H : subset (support (_++_)) _ |- _ => rewrite support_append in H
              | H: is_nat_value ?t |- subset (pfv ?t ?tag) ?A => rewrite nat_value_fv
              | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
              | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2; eauto
              | H1: ~ ?n ∈ (fv_context ?Γ),
                    H2: subset (support ?Γ) (fv_context ?Γ)
                |- _ => apply (in_subset_not (support Γ) (fv_context Γ) n H2) in H1
              | H: subset (fv (open ?k ?t1 ?t2)) ?A
                |- subset (pfv ?t1 term_var) _ => apply (support_open t1 t2 term_var k A) in H
              | H: ?x ∈ ?A |- subset (singleton ?x) ?A => apply singleton_subset; assumption
              | H: lookup ?e ?A ?x = Some ?y |- _ => apply (@lookupSupport _ _ e A x y) in H
              | H: _ |- subset (singleton ?n) (?n :: _) => apply singleton_subset, inList1
              | H: _ |- subset (singleton ?n) (_ :: ?n :: _) => apply singleton_subset, inList2
              | H: _ |- subset (singleton ?n) (_ :: _ :: ?n :: _) => apply singleton_subset, inList3
              | H: subset (fv (open ?k1 (open ?k2 ?t (fvar ?n3 term_var)) (fvar ?n2 term_var))) (?n1::?n2::?n3::?A),
                   H1: ~ ?n3 ∈ (fv ?t),
                       H2: ~ ?n2 ∈ (fv ?t),
                           H3: ~ ?n1 ∈ (fv ?t)
                |- subset (pfv ?t term_var) ?A  => apply (subset_open_open k1 k2 t n3 n2 n1 A H H1 H2 H3)
              | H: subset( fv (_ _ _)) _ |- _ => cbn in H
              | H: refinementUnfoldInContext ?Γ ?Γ0 = Some (?x, ?p, ?ty, ?P) |- _ =>
                apply refinementUnfoldInContext_support2 in H
              end
       || invert_constructor_equalities || apply support_open2|| inst_list_prop || modus_ponens || simpl || split;
    eauto 3 using singleton_subset, inList1, inList2, inList3 with sets.
Qed.


Lemma is_valid_support_t : forall n Θ Γ t T c, is_valid (N (TJ n Θ Γ t T) c) = true -> subset (fv t) (support Γ).
Proof. intros. pose proof (is_valid_support_term_aux  (N (TJ n Θ Γ t T) c) H ). steps. Qed.
Hint Resolve is_valid_support_t: deriv.

Lemma is_valid_support_T : forall n Θ Γ t T c, is_valid (N (TJ n Θ Γ t T) c) = true -> subset (fv T) (support Γ).
Proof. intros. pose proof (is_valid_support_term_aux  (N (TJ n Θ Γ t T) c) H ). steps. Qed.
Hint Resolve is_valid_support_T: deriv.


Hint Resolve is_valid_wf_t: deriv.
Hint Resolve is_valid_wf_T: deriv.

(* Parameter SMT_Check (Θ Γ ... ) : Prop. *)

Lemma trustSMTSolver_ADMITTED : forall  Θ Γ t T c, is_valid (N (EJ E_SMT Θ Γ t T) c) = true -> [[Θ;Γ ⊨ t ≡ T]].
Admitted.


Ltac consume_is_valid :=
  match goal with
  | H: is_valid ?dv = true |- _ =>
    epose proof (is_valid_support_term_aux dv H) ;
    epose proof (is_valid_wf_aux dv H) ; clear H
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
Hint Rewrite PeanoNat.Nat.eqb_eq: deriv.

Ltac soundness_finish :=
  repeat destruct_and || assumption ||  match goal with
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
              | H: NoDupb ?L |- List.NoDup ?L => apply NoDupb_prop
              | H: subset (fv (_ _ _)) _ |- _ => cbn in H; apply subset_union3 in H
              | H: _ |- subset (singleton ?n) (?n :: _) => apply singleton_subset, inList1
              | H: ~ ?a ∈ ?L |- List.NoDup (?a::?L) => apply (List.NoDup_cons a H)
              | H:_ |- List.NoDup (?a::nil) => apply (List.NoDup_cons a (@List.in_nil _ a))
              | H:_ |- List.NoDup nil => apply List.NoDup_nil
              | H: _ |- subset (singleton ?n) (_ :: ?n :: _) => apply singleton_subset, inList2
              | H: _ |- subset (singleton ?n) (_ :: _ :: ?n :: _) => apply singleton_subset, inList3
              | H: subset (fv (open ?k1 (open ?k2 ?t (fvar ?n3 term_var)) (fvar ?n2 term_var))) (?n1::?n2::?n3::?A),
                   H1: ~ ?n3 ∈ (fv ?t),
                       H2: ~ ?n2 ∈ (fv ?t),
                           H3: ~ ?n1 ∈ (fv ?t)
                |- subset (pfv ?t term_var) ?A  => apply (subset_open_open k1 k2 t n3 n2 n1 A H H1 H2 H3)
                                      end || rewrite pfv_fvar || rewrite pfv_fvar2 || simpl || unfold fv || rewrite_deriv.

Hint Rewrite isValueCorrect: deriv.
(* Main soundess result *)
Lemma is_valid_soundess : forall dv, (is_valid dv) = true -> (is_true (root dv)).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv, is_true. unfold forallP in X.
  destruct J.
  pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match; try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || rewrite_deriv || light_bool || invert_constructor_equalities || inst_list_prop || modus_ponens || simpl || consume_is_valid || destruct_or || destruct_and.
  all: repeat match goal with | H: is_true (root _) |- _ => simpl in H end.
  (* remove easy cases *)
  all: eauto 2 with deriv.
  all: try discriminate.
  all: unfold fv_context in *.
  all:
    try
      match goal with
      | H: _ |- [[?Θ; ?Γ ⊨ ?t : drop_refinement ?T]] => eapply annotated_reducible_drop
      | H: [[ ?Θ ; ((?p, _)::(?x,_)::_) ⊨ (open _ ?b _) ≡ ttrue ]] |- [[ ?Θ ; ?Γ ⊨ ?t : T_refine _ _ ]] => eapply (annotated_reducible_refine Θ Γ _ _ _  x p); eauto
      | H: (is_nat_value ?t) |- [[?Θ; ?Γ ⊨ (succ ?t) : T_nat]] => apply (annotated_reducible_nat_value Θ Γ (succ t) (INVSucc t H)); cbv
      | H: _
        |- [[?Θ; ?Γ ⊨ (tmatch ?tn ?t0 ?ts) : ?T]] => apply (annotated_reducible_match Θ Γ _ _ _ T n7 n3)
      | H1: [[?Θ; (?x1, T_equiv _ ttrue)::?Γ ⊨ _ : _ ]],
        H2: [[?Θ; (?x2, T_equiv _ tfalse)::?Γ ⊨ _ : _ ]]
        |- [[?Θ; ?Γ ⊨ (ite ?t1 ?t2 ?t3) : (T_ite _ ?T1 ?T2)]] =>
        (apply (annotated_reducible_T_ite Θ Γ t1 t2 t3 T1 T2 x1 x2))
      | H1: [[?Θ; (?x1, T_equiv _ ttrue)::?Γ ⊨ _ : _ ]],
        H2: [[?Θ; (?x2, T_equiv _ tfalse)::?Γ ⊨ _ : _ ]]
        |- [[?Θ; ?Γ ⊨ (ite ?t1 ?t2 ?t3) : ?T ]] => apply (annotated_reducible_ite Θ Γ t1 t2 t3 T x1 x2)
      | H: [[?Θ; ?Γ ⊨ ?t : (T_prod ?A ?B)]]
        |- [[?Θ; ?Γ ⊨ (pi1 ?t) : ?A]] => apply (annotated_reducible_pi1 Θ Γ t A B)
      | H: [[?Θ; ?Γ ⊨ ?t : (T_prod ?A ?B)]]
        |- [[?Θ; ?Γ ⊨ (pi2 ?t) : _]] => apply (annotated_reducible_pi2 Θ Γ t A B)
      | H: _
        |- [[?Θ; ?Γ ⊨ (app ?t) : ?T]] => apply (annotated_reducible_app)
      | H: _
        |- [[?Θ; ?Γ ⊨ (pp ?t1 ?t2) : (T_prod ?A ?B)]] => eapply (annotated_reducible_pp Θ Γ A B t1 t2)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_arrow ?U ?V)]]
        |- [[?Θ; ?Γ ⊨ (app ?t1 ?t2) : ?T]] => apply (annotated_reducible_app Θ Γ t1 t2 U V)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_sum ?A ?B)]], H1: ?y <> ?p
        |- [[?Θ; ?Γ ⊨ (sum_match ?t1 ?t2 ?t3) : ?T]] => eapply (annotated_reducible_sum_match Θ Γ t1 t2 t3 A B _ y p)
      | H: _
        |- [[?Θ; ?Γ ⊨ (lambda ?T ?t) : _]] => eapply (annotated_reducible_lambda)
      | H: _
        |- [[?Θ; ?Γ ⊨ (tlet ?T ?t) : _]] => eapply (annotated_reducible_let Θ Γ)
      | H: ?x <> ?p
        |- [[?Θ; ?Γ ⊨ (tlet ?t1 ?A ?t2) : _]] => apply (annotated_reducible_let Θ Γ t1 t2 x p A)
      | H: [[ ?Θ; (?p,_)::(?y,_)::(?n,_)::?Γ ⊨ _ : _ ]] |-  [[?Θ; ?Γ ⊨ (tfix ?t1 ?t2) : (T_forall T_nat ?t1)]] => apply (annotated_reducible_fix_strong_induction Θ Γ t2 t1 n y p)
                                                                                                                    | H: [[ ?Θ; ?Γ ⊨ ?t1 : (T_forall ?U ?V)]], H2 : [[_; _ ⊨ ?t2 : ?U]] |- _ => apply (annotated_reducible_forall_inst Θ Γ t1 t2 U V)
      |H: [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2 ]], H2: [[?Θ; ?Γ ⊨ ?t2 ≡ ?t3]] |- [[?Θ; ?Γ ⊨ ?t1 ≡ ?t3 ]] => apply (annotated_equivalent_trans Θ Γ t1 t2 t3 H H2)
      |H: [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2 ]] |- [[?Θ; ?Γ ⊨ ?t2 ≡ ?t1 ]] => apply (annotated_equivalent_sym Θ Γ t1 t2 H)
      |H: _ |- [[?Θ; ?Γ ⊨ ?t ≡ ?t ]] => apply (annotated_equivalent_refl Θ Γ t)
      |H: _ |- [[?Θ; ?Γ ⊨ (lambda ?A ?t1) ≡ (lambda ?B ?t2) ]] => apply (annotated_equivalence_lambdas Θ Γ t1 t2 A B); eauto with wf
      | H:  [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2]] |- [[?Θ; ?Γ ⊨ open 0 ?C ?t1 ≡ open 0 ?C ?t2]] => apply (annotated_equivalence_context Θ Γ C t1 t2)
      |H1: [[ ?Θ ; ?Γ ⊨ ?t1 ≡ ?t2]], H2 : [[ ?Θ ; ?Γ ⊨ ?t1 : ?T]]
       |- [[ ?Θ ; ?Γ ⊨ ?t2 : ?T]] => apply (annotated_equivalent_elim Θ Γ t1 t2 T)
      |H: [[?Θ;?Γ ⊨ ?t : ?T_prod ?A ?B ]]
       |-  [[?Θ;?Γ ⊨ ?t ≡ (pp (pi1 ?t) (pi2 ?t))]] => apply (annotated_equivalent_pair_ext Θ Γ t A B)
      | H: refinementUnfoldInContext ?Γ0 ?Γ = Some (?x, ?p, ?ty, ?P) |- [[ ?Θ ; ?Γ ⊨ ?t : ?T]] =>
        let Γ := fresh Γ in
        let Γ' := fresh Γ' in
        let fH := fresh H in
        rewrite refinementUnfoldInContext_prop in H; destruct H as [Γ [Γ' [H fH] ] ]; subst;
          apply annotated_reducible_unfold_refine; eauto; rewrite support_append in *;
            rewrite fv_context_append in *;
            list_utils; steps
      | H: refinementUnfoldInContext ?Γ0 ?Γ = Some (?x, ?p, ?ty, ?P) |- [[ ?Θ ; ?Γ ⊨ ?t ≡ ?T]] =>
        let Γ := fresh Γ in
        let Γ' := fresh Γ' in
        let fH := fresh H in
        rewrite refinementUnfoldInContext_prop in H; destruct H as [Γ [Γ' [H fH] ] ]; subst;
          apply annotated_reducible_equivalent_unfold_refine; eauto; rewrite support_append in *;
            rewrite fv_context_append in *;
            list_utils; steps
      end; eauto; soundness_finish.

  assert (is_valid (N (EJ E_SMT Θ Γ t T) c) = true).
  cbn; repeat bools || steps || autorewrite with deriv; eauto.
  eauto using trustSMTSolver_ADMITTED.
  Qed.

Show Ltac Profile.
