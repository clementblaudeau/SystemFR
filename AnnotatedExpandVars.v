Require Export SystemFR.AnnotatedEquivalentMisc.
Require Export SystemFR.ErasedExpandVars.
Require Import Psatz.
Require Import Coq.Lists.List.

Opaque reducible_values.

Lemma annotated_equivalent_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u ≡ v ]] ->
    [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u ≡ v ]].
Proof.
  intros.
  repeat step || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_equivalent_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_reducible_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u : v ]] ->
    [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u : v ]].
Proof.
  intros.
  repeat step || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_reducible_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_subtype_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u <: v ]] ->
    [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u <: v ]].
Proof.
  intros.
  repeat step || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_subtype_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
  erewrite in_erased_context; eauto; steps.
Qed.
