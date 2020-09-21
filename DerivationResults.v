Require Export SystemFR.Derivation.
Require Export SystemFR.Syntax.
Require Export SystemFR.Evaluator.
Require Export SystemFR.NatLessThanErase.

Require Import List.
Import ListNotations.
From ReductionEffect Require Import PrintingEffect.



Ltac modus_ponens_is_valid :=
  match goal with
  | H: is_valid ?ds ?Γ = true,
       H1: forall Γ, is_valid ?ds Γ = true -> _ |- _ => pose proof (H1 Γ H); clear H1
  end.


Ltac rewrite_deriv :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints deriv in H
  end.

Ltac destruct_clear t H := destruct t; try apply (ex_falso_quolibet _ H).

Hint Unfold closed_value: deriv.

Lemma is_valid_wf_aux: forall dv Γ, is_valid dv Γ = true -> wf (J_term1 (root dv)) 0 /\ wf (J_term2 (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2. unfold forallP in X.
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || light_bool || match goal with | H: wf (_ _) _ |- _ => simpl in H end || rewrite_deriv || invert_constructor_equalities || inst_list_prop || modus_ponens_is_valid || unfold closed_value, closed_term in * ; simpl.
  all: repeat split; eauto with wf deriv.
Qed.


Lemma is_valid_support_term_aux :
  forall dv Γ, is_valid dv Γ = true ->
          subset (fv (J_term1 (root dv)) ) (support Γ) /\
          subset (fv (J_term2 (root dv)) ) (support Γ).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv. unfold forallP in X.
  destruct J.
  all: pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)); try discriminate.
  (* Apply induction hypothesis and do the rewrites *)
  all: simpl; eauto 2 using subset_nil.
  all: unfold fv_context in *.
  all: repeat light_bool || subst || inst_list_prop || modus_ponens_is_valid.
  all: repeat rewrite_deriv || invert_constructor_equalities || subst.
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
              end
       || invert_constructor_equalities || apply support_open2 || simpl || split || rewrite_any || unfold closed_value, closed_term in * ;
    eauto 3 using singleton_subset, inList1, inList2, inList3, refinementUnfoldInContext_support3 with sets.
Qed.


(* Parameter SMT_Check (Θ Γ ... ) : Prop. *)

Lemma trustSMTSolver_ADMITTED : forall Θ Γ cΓ t T c, is_valid (N (EJ E_SMT Θ cΓ t T) c) Γ = true -> [[Θ;Γ ⊨ t ≡ T]].
Admitted.


Ltac consume_is_valid :=
  match goal with
  | H: is_valid ?dv ?Γ = true |- _ =>
    epose proof (is_valid_support_term_aux dv Γ H) ;
    epose proof (is_valid_wf_aux dv Γ H) ; clear H
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
  repeat subst || destruct_and ||
         assumption ||
         match goal with
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


Ltac destruct_andb :=
  match goal with
  |H: ?b1 && ?b2 = true |- _ =>
   let H1 := fresh H in
   let H2 := fresh H in
   pose proof (andb_prop b1 b2 H) as [H1 H2] ; clear H
  end.



(* Main soundess result *)
Lemma is_valid_soundess : forall dv Γ, is_valid dv Γ = true -> is_true (root dv) Γ.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv, is_true. unfold forallP in X.
  destruct J.
  all: pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match; try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat destruct_andb.
  all: try (inst_list_prop ; repeat modus_ponens_is_valid) ; subst.
  all: repeat consume_is_valid.
  all: repeat subst || rewrite_deriv || invert_constructor_equalities.
  all: repeat destruct_and || destruct_or || match goal with | H: is_true _ _ |- _ => simpl in H end || subst || light_bool.

  (* remove easy cases *)
  all: eauto 1 with deriv.
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
        |- [[?Θ; ?Γ ⊨ (pp ?t1 ?t2) : (T_prod ?A ?B)]] => eapply (annotated_reducible_pp Θ Γ A B t1 t2)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_arrow ?U ?V)]]
        |- [[?Θ; ?Γ ⊨ (Trees.app ?t1 ?t2) : ?T]] => apply (annotated_reducible_app Θ Γ t1 t2 U V)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_sum ?A ?B)]], H1: ?y <> ?p
        |- [[?Θ; ?Γ ⊨ (sum_match ?t1 ?t2 ?t3) : ?T]] => eapply (annotated_reducible_sum_match Θ Γ t1 t2 t3 A B _ y p)
      | H: _
        |- [[?Θ; ?Γ ⊨ (lambda ?T ?t) : _]] => eapply (annotated_reducible_lambda)
      | H: ?x <> ?p
        |- [[?Θ; ?Γ ⊨ (tlet ?t1 ?A ?t2) : _]] => apply (annotated_reducible_let Θ Γ t1 t2 x p A)
      | H: ?x <> ?p, H1: [[?Θ; ?Γ ⊨ ?t1 : ?A]]
        |- [[?Θ; ?Γ ⊨ (notype_tlet ?t1 ?t2) : _]] => apply (annotated_reducible_notype_tlet Θ Γ t1 t2 x p A)
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
      | H: refinementUnfoldInContext ?Γ ?Γ0 = Some (?x, ?p, ?ty, ?P) |- [[ ?Θ ; ?Γ ⊨ ?t ≡ ?T]] =>
        let Γ := fresh Γ in
        let Γ' := fresh Γ' in
        let fH := fresh H in
        rewrite refinementUnfoldInContext_prop in H; destruct H as [Γ [Γ' [H fH] ] ]; subst;
          apply annotated_reducible_equivalent_unfold_refine; eauto; rewrite support_append in *;
            rewrite fv_context_append in *;
            list_utils; steps
      end; soundness_finish; eauto with deriv.


  rewrite refinementUnfoldInContext_prop in matched5.
  destruct matched5 as [Γ1 [Γ2 [matched5 fH] ] ]. subst.
  pose proof (annotated_reducible_refine).
  pose proof (annotated_reducible_unfold_refine Θ Γ1 Γ2 n1 n2 t2 t1 t T H2 H11 H10 H9).

  assert (is_valid (N (EJ E_SMT Θ Same t T) c) Γ = true).
  cbn; repeat bools || steps || autorewrite with deriv; eauto.
  eauto using trustSMTSolver_ADMITTED.
  Qed.
