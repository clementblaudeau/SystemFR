Require Import Coq.Lists.List.
Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.WFLemmasClose.
Require Export SystemFR.ReducibilityEquivalent.
Require Import Psatz.

Opaque reducible_values.

(* Technical lemmas, actual heart of the proofs*)

Lemma satisfies_expand_vars:
  forall (Γ1 Γ2 : map nat tree) (x y p : nat) (t T : tree),
    (x ∈ support Γ2 -> False) ->
    subset (pfv T term_var) (support Γ2) ->
    subset (pfv t term_var) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->
    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->
    forall (ρ : interpretation) (l : list (nat * tree)),
      valid_interpretation ρ ->
      satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2) l ->
      satisfies (reducible_values ρ) (Γ1 ++ (x, T) :: Γ2) l.
Proof.
  steps.
  apply satisfies_weaken with (open 0 (close 0 T y) t);
    repeat step || rewrite support_append; eauto.
  + erewrite <- (open_close2 T y 0); eauto using wf_subst with wf.
    unfold substitute in *.
    rewrite substitute_open; rewrite_anywhere substitute_open; eauto using satisfies_wfs.
    apply reducibility_open_equivalent with (psubstitute t l0 term_var);
      try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv.
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2.
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
  + eapply subset_transitive;
      eauto using fv_open, fv_close;
      repeat steps || list_utils || fv_close || unfold subset.
Qed.

Lemma satisfies_expand_vars2:
  forall (Γ1 Γ2 : map nat tree) (x y p : nat) (t T : tree),
    (x ∈ support Γ2 -> False) ->
    subset (pfv T term_var) (support Γ2) ->
    subset (pfv t term_var) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->
    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->
    forall (ρ : interpretation) (l : list (nat * tree)),
      valid_interpretation ρ ->
      satisfies (reducible_values ρ) (Γ1 ++ (x, T) :: Γ2) l ->
      satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2) l.
Proof.
  steps.
  eapply satisfies_weaken with T;
    repeat step || rewrite support_append; eauto;
      try solve [
            eapply subset_transitive;
            eauto using fv_open, fv_close;
            repeat steps || list_utils || fv_close || unfold subset].
  erewrite <- (open_close2 T y 0) in H9 ; eauto using wf_subst with wf.
    rewrite substitute_open; rewrite_anywhere substitute_open; eauto using satisfies_wfs.
    apply reducibility_open_equivalent with (psubstitute (fvar y term_var) l0 term_var);
      try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv.
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2.
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

(* Lemmas for expanding vars in the context *)

Lemma open_equivalent_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->
    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u ≡ v ] <->
     [ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u ≡ v ]).
Proof.
  unfold open_equivalent; split; intros; eapply_any; steps;
    eauto using satisfies_expand_vars, satisfies_expand_vars2.
Qed.

Lemma open_reducible_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u : v ] <->
     [ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u : v ]).
Proof.
  unfold open_reducible; split; intros; eapply_any; steps;
    eauto using satisfies_expand_vars, satisfies_expand_vars2.
Qed.

Lemma open_subtype_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u <: v ] <->
     [ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u <: v ]).
Proof.
  unfold open_subtype; split; intros; eapply_any; steps;
    eauto using satisfies_expand_vars, satisfies_expand_vars2.
Qed.

(* Lemmas for expanding vars in terms/types *)

Lemma open_equivalent_expand_vars_term:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    wf t1 0 ->
    is_erased_term t1 ->
    ([ Θ; Γ ⊨ t1 ≡ t2 ] <->
     [ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) ≡ t2 ]).
Proof.
  unfold open_equivalent, substitute; split; intros;
    eapply equivalent_trans; try eapply_any; eauto;
      [ erewrite <- (open_close2 t1 y 0) at 2 |
        erewrite <- (open_close2 t1 y 0) at 1] ;
      eauto using wf_subst with wf;
    repeat rewrite substitute_open; eauto using satisfies_wfs;
    eapply equivalent_context; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_reducible_expand_vars_term:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ t1 : t2 ] <->
     [ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) : t2 ]).
Proof.
  unfold open_reducible, substitute; split; intros;
  eapply reducibility_equivalent2; try eapply_any; eauto using wf_subst with wf erased fv;
      [ erewrite <- (open_close2 t1 y 0) at 1 |
        erewrite <- (open_close2 t1 y 0) at 2] ;
      eauto using wf_subst with wf;
    repeat rewrite substitute_open; eauto using satisfies_wfs;
    eapply equivalent_context; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_reducible_expand_vars_type:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_term t1 ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ t1 : t2 ] <->
     [ Θ; Γ ⊨ t1 : (open 0 (close 0 t2 y) t) ]).
Proof.
  unfold open_reducible, reduces_to, substitute; steps; t_closer;
  unshelve epose proof (H6 _ _ _ _ _); eauto; steps;
  eexists; steps; eauto;
    [ erewrite <- (open_close2 t2 y 0) in H11 |
      erewrite <- (open_close2 t2 y 0) ]; eauto ;
    rewrite substitute_open; rewrite_anywhere substitute_open ; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent ; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_subtype_expand_vars_left:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_type t1 ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ t1 <: t2 ] <->
     [ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) <: t2 ]).
Proof.
  unfold open_subtype, substitute; split; intros; eapply_any; eauto;
    [ erewrite <- (open_close2 t1 y 0) at 1 |
      erewrite <- (open_close2 t1 y 0) in H10 ]; eauto;
  rewrite substitute_open ; rewrite_anywhere  substitute_open; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent ; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
      repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_subtype_expand_vars_right:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_erased_type t1 ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ t1 <: t2 ] <->
     [ Θ; Γ ⊨ t1 <: (open 0 (close 0 t2 y) t) ]).
Proof.
  unfold open_subtype, substitute; split; intros;
  [ erewrite <- (open_close2 t2 y 0) in H6 ; eauto; eapply H6 in H10; eauto |
    eapply H6 in H10; eauto; erewrite <- (open_close2 t2 y 0) by eauto ];

  rewrite substitute_open ; rewrite_anywhere  substitute_open; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent ; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
      repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.

Qed.
