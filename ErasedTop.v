Require Export Equations.Equations.

Require Export SystemFR.RedTactics.

Opaque reducible_values.

Lemma reducible_values_top:
  forall ρ v T,
    valid_interpretation ρ ->
    [ ρ ⊨ v : T ]v ->
    [ ρ ⊨ v : T_top ]v.
Proof.
  repeat step || simp reducible_values;
    eauto using reducible_values_closed.
Qed.

Lemma reducible_top:
  forall ρ t T,
    valid_interpretation ρ ->
    [ ρ ⊨ t : T ] ->
    [ ρ ⊨ t : T_top ].
Proof.
  eauto using reducible_values_top, reducible_values_exprs.
Qed.

Lemma open_reducible_top:
  forall Θ Γ t T,
    [ Θ; Γ ⊨ t : T ] ->
    [ Θ; Γ ⊨ t : T_top ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3;
    eauto using reducible_top.
Qed.

Lemma open_reducible_top_value:
  forall tvars gamma t,
    (cbv_value t) ->
    subset (fv t) (support gamma) ->
    wf t 0 ->
    is_erased_term t ->
    [ tvars; gamma ⊨ t : T_top ].
Proof.
  unfold open_reducible, reduces_to.
  intros. split.
  + repeat steps || simp_red || t_closer.
  + exists (substitute t lterms). split; [|apply Operators_Properties.clos_rt_rt1n; steps].
    cbn. rewrite reducible_values_equation_14.
    steps. unfold closed_value, closed_term; steps; eauto with fv wf values erased.
    induction H; repeat steps || list_utils ; eauto with values sets.
Qed.
