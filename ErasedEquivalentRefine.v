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

Lemma open_reducible_equivalent_refine_fold_head:
    forall Θ Γ Γ' x p ty P t T,
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv P) ->
    ~(p ∈ fv ty) ->
    ~(p ∈ fv_context Γ') ->
    ~(p ∈ fv_context Γ) ->
    ~(x = p) ->
    (wf P 1) ->
    subset (fv ty) (support Γ') ->
    subset (fv P) (support Γ') ->
    (is_erased_term P) ->
    [ Θ; ((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t ≡ T] ->
    [ Θ; ((x, T_refine ty P)::Γ') ⊨ t ≡ T].
Proof.
  intros.
  eapply satisfies_transform_equivalent in H10 ; eauto;
    repeat steps || satisfies_cut || step_inversion satisfies || rewrite_anywhere reducible_values_equation_10.
  exists ((p,uu)::(x,t0)::lterms); steps; eauto; try solve [rewrite substitute_nothing2; steps].
  repeat steps || list_utils || simp_red || sets || fv_open || apply SatCons || rewrite substitute_open3 ;
    eauto using satisfies_wfs, equivalent_star with wf fv erased.
Qed.

Lemma open_reducible_equivalent_refine_fold:
    forall Θ Γ Γ' x p ty P t T,
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv P) ->
    ~(p ∈ fv ty) ->
    ~(p ∈ fv_context Γ') ->
    ~(p ∈ fv_context Γ) ->
    ~(x = p) ->
    ~(x ∈ fv ty) ->
    ~(x ∈ fv P) ->
    (wf P 1) ->
    subset (fv ty) (support Γ') ->
    subset (fv P) (support Γ') ->
    (is_erased_term P) ->
    [ Θ; Γ++((p, T_equiv (open 0 P (fvar x term_var)) ttrue)::(x, ty)::Γ')  ⊨ t ≡ T] ->
    [ Θ; Γ++((x, T_refine ty P)::Γ') ⊨ t ≡ T].
Proof.
  intros.
  eapply_anywhere satisfies_transform_equivalent ; eauto;
    repeat steps || satisfies_cut || step_inversion satisfies || rewrite_anywhere reducible_values_equation_10.
  exists (l1++(p,uu)::(x,t0)::lterms); steps; eauto; try solve [rewrite substitute_skip; steps].
  eapply satisfies_insert;
    repeat steps || list_utils || sets || fv_open ; eauto with wf fv.
  + apply_anywhere satisfies_cut;
      repeat steps || step_inversion satisfies || rewrite reducible_values_equation_16 || rewrite substitute_open3 ;
      eauto using equivalent_star with wf fv erased.
  + repeat steps || list_utils || fv_open || eauto using x_not_in_support, NoDup_append || apply_anywhere satisfies_nodup || rewrite_anywhere support_append || apply NoDup_append with (x := z) in H13.
  + eapply satisfies_weaken with (T := (T_refine ty P)) ; eauto ;
      repeat steps || list_utils ||  rewrite reducible_values_equation_10 in * || sets || apply_anywhere satisfies_nodup.
Qed.
