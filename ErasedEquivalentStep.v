Require Export SystemFR.ReducibilityOpenEquivalent.
Opaque reducible_values.


Lemma reducible_sum_match_tright_step:
  forall ρ t tl tr T,
    is_erased_term t ->
    is_erased_term tr ->
    is_erased_term tl ->
    valid_interpretation ρ ->
    wf (sum_match (tright t) tl tr) 0 ->
    fv tl = nil ->
    fv tr = nil ->
    fv t = nil ->
    [ρ ⊨ t : T] ->
    [sum_match (tright t) tl tr ≡ open 0 tr t].
Proof.
  unfold reduces_to; steps.
  eapply equivalent_trans with (t2 := sum_match (tright v) tl tr); [equivalent_star |].
  eapply equivalent_trans with (t2 := open 0 tr v); [equivalent_star |].
  apply equivalent_context; eauto using equivalent_sym, equivalent_star.
Qed.

Lemma open_reducible_sum_match_tright_step:
  forall Θ Γ t tl tr T,
    is_erased_term t ->
    is_erased_term tr ->
    is_erased_term tl ->
    wf (sum_match (tright t) tl tr) 0 ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv t) (support Γ) ->
    [Θ; Γ ⊨ t : T] ->
    [Θ; Γ ⊨ sum_match (tright t) tl tr ≡ open 0 tr t].
Proof.
  unfold open_reducible, open_equivalent;
    repeat steps || t_substitutions.
  eapply reducible_sum_match_tright_step ;
    steps; eauto with erased fv wf.
Qed.


Lemma reducible_sum_match_tleft_step:
  forall ρ t tl tr T,
    is_erased_term t ->
    is_erased_term tr ->
    is_erased_term tl ->
    valid_interpretation ρ ->
    wf (sum_match (tright t) tl tr) 0 ->
    fv tl = nil ->
    fv tr = nil ->
    fv t = nil ->
    [ρ ⊨ t : T] ->
    [sum_match (tleft t) tl tr ≡ open 0 tl t].
Proof.
  unfold reduces_to; steps.
  eapply equivalent_trans with (t2 := sum_match (tleft v) tl tr); [equivalent_star |].
  eapply equivalent_trans with (t2 := open 0 tl v); [equivalent_star |].
  apply equivalent_context; eauto using equivalent_sym, equivalent_star.
Qed.

Lemma open_reducible_sum_match_tleft_step:
  forall Θ Γ t tl tr T,
    is_erased_term t ->
    is_erased_term tr ->
    is_erased_term tl ->
    wf (sum_match (tright t) tl tr) 0 ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv t) (support Γ) ->
    [Θ; Γ ⊨ t : T] ->
    [Θ; Γ ⊨ sum_match (tleft t) tl tr ≡ open 0 tl t].
Proof.
  unfold open_reducible, open_equivalent;
    repeat steps || t_substitutions.
  eapply reducible_sum_match_tleft_step ;
    steps; eauto with erased fv wf.
Qed.
