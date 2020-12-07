Require Import Coq.Lists.List.
Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.WFLemmasClose.
Require Import Psatz.

Opaque reducible_values.

Lemma open_reducible_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_erased_type T ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    [ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u ≡ v ] ->
    [ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u ≡ v ].

Proof.
  unfold open_equivalent; intros; eapply_any; steps; eauto.
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
