Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedRefine.

Lemma annotated_reducible_refine:
  forall tvars gamma t A b x p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv A) ->
    ~(x = p) ->
    ~(x ∈ tvars) ->
    ~(p ∈ tvars) ->
    wf t 0 ->
    wf b 1 ->
    is_annotated_term b ->
    subset (fv t) (support gamma) ->
    subset (fv b) (support gamma) ->
    [[ tvars; gamma ⊨ t : A ]] ->
    [[ tvars; (p, T_equiv (fvar x term_var) t) :: (x,A) :: gamma ⊨ open 0 b (fvar x term_var) ≡ ttrue ]] ->
    [[ tvars; gamma ⊨ t : T_refine A b ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, open_equivalent;
    repeat step.
  apply open_reducible_refine with x p;
    repeat step || t_instantiate_sat3 || erase_open;
    side_conditions.
Qed.

(* x is of type { y: ty | P(y) }
  which is split into `x : ty` and `P(x)≡ttrue`
 *)
Lemma annotated_reducible_unfold_refine:
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
    [[ Θ; Γ++((x, T_refine ty P)::Γ') ⊨ t : T]] ->
    [[ Θ; Γ++((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t : T]].
Proof.
  unfold annotated_reducible, annotated_equivalent, open_equivalent.
  repeat rewrite erase_context_append || rewrite erase_context_append in * || erase_open || step.
  eapply open_reducible_refine_unfold; eauto with fv wf sets.
  all: repeat rewrite erased_context_support;  eauto using pfv_erase_type_subst, pfv_erase_term_subst, erase_term_erased.
Qed.
