Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet2.
Require Export SystemFR.NatLessThan.

Opaque reducible_values.
Opaque makeFresh.


Lemma open_reducible_equivalent_refine_unfold:
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
    (is_erased_term P) ->
    [ Θ; Γ++((x, T_refine ty P)::Γ') ⊨ t ≡ T] ->
    [ Θ; Γ++((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t ≡ T].
Proof.
  intros.
  eapply satisfies_transform_equivalent ; eauto; repeat steps || satisfies_cut || step_inversion satisfies.
  exists (l1++(x,t1)::lterms0); steps; eauto; try solve [rewrite substitute_skip with (x := p); steps].
  apply satisfies_drop in H10; steps; eauto.
  eapply satisfies_modify; eauto; repeat steps || simp_red || sets ; t_closer.
  - eapply subset_transitive; eauto.
    unfold subset; eauto using fv_context_support.
  - eapply subset_transitive; eauto.
    unfold subset; eauto using fv_context_support.
  - t_substitutions.
     eapply equivalent_true; eauto.
Qed.
