Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedEquivalentRefine.

(* x is of type { y: ty | P(y) }
  which is split into `x : ty` and `P(x)≡ttrue`
 *)
Lemma annotated_reducible_equivalent_unfold_refine:
    forall Θ Γ Γ' x p ty P t T,
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv P) ->
    ~(p ∈ fv ty) ->
    ~(p ∈ fv_context Γ') ->
    ~(p ∈ fv_context Γ) ->
    (wf P 1) ->
    subset (fv ty) (support Γ') ->
    subset (fv P) (support Γ') ->
    (is_annotated_term P) ->
    [[ Θ; Γ++((x, T_refine ty P)::Γ') ⊨ t ≡ T]] ->
    [[ Θ; Γ++((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t ≡ T]].
Proof.
  repeat rewrite erase_context_append || rewrite erase_context_append in * || erase_open || step.
  eapply open_reducible_equivalent_refine_unfold; eauto with fv wf sets.
  all: repeat rewrite erased_context_support;  eauto using pfv_erase_type_subst, pfv_erase_term_subst, erase_term_erased.
Qed.

Lemma annotated_reducible_equivalent_fold_refine:
    forall Θ Γ Γ' x p ty P t T,
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv P) ->
    ~(p ∈ fv ty) ->
    ~(p ∈ fv_context Γ') ->
    ~(p ∈ fv_context Γ) ->
    ~(x ∈ fv ty) ->
    ~(x ∈ fv P) ->
    ~(x = p) ->
    (wf P 1) ->
    (is_annotated_term P) ->
    [[ Θ; Γ++((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t ≡ T]] ->
    [[ Θ; Γ++((x, T_refine ty P)::Γ') ⊨ t ≡ T]].
Proof.
  repeat rewrite erase_context_append || rewrite erase_context_append in * || erase_open || step.
  eapply open_reducible_equivalent_refine_fold; eauto with fv wf sets.
  all: repeat rewrite erased_context_support;  eauto using pfv_erase_type_subst, pfv_erase_term_subst, erase_term_erased.
Qed.
