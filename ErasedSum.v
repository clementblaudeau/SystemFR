Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ErasedLet2.
Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_left:
  forall ρ t A B,
    valid_interpretation ρ ->
    [ ρ ⊨ t : A ] ->
    [ ρ ⊨ tleft t : T_sum A B ].
Proof.
  unfold reduces_to; steps.
  eexists; steps; eauto with cbvlemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_left:
  forall Θ Γ t A B,
    [ Θ; Γ ⊨ t : A ] ->
    [ Θ; Γ ⊨ tleft t : T_sum A B ].
Proof.
  unfold open_reducible; steps; eauto using reducible_left.
Qed.

Lemma reducible_right:
  forall ρ t A B,
    valid_interpretation ρ ->
    [ ρ ⊨ t : B ] ->
    [ ρ ⊨ tright t : T_sum A B ].
Proof.
  unfold reduces_to; steps.
  eexists; steps; eauto with cbvlemmas;
    repeat step || simp_red || t_closing; eauto with values.
Qed.

Lemma open_reducible_right:
  forall Θ Γ t A B,
    [ Θ; Γ ⊨ t : B ] ->
    [ Θ; Γ ⊨ tright t : T_sum A B ].
Proof.
  unfold open_reducible; steps; eauto using reducible_right.
Qed.

Lemma open_reducible_sum_match:
  forall Θ Γ t tl tr T1 T2 T y1 y2 p1 p2,
    subset (fv t) (support Γ) ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv T1) (support Γ) ->
    subset (fv T2) (support Γ) ->
    subset (fv T) (support Γ) ->
    wf T 1 ->
    wf T1 0 ->
    wf T2 0 ->
    wf t 0 ->
    wf tr 1 ->
    wf tl 1 ->

    ~(y1 ∈ fv_context Γ) ->
    ~(y1 ∈ fv T) ->
    ~(y1 ∈ fv T1) ->

    ~(y2 ∈ fv_context Γ) ->
    ~(y2 ∈ fv T) ->
    ~(y2 ∈ fv T2) ->

    ~(p1 ∈ pfv_context Γ term_var) ->
    ~(p1 ∈ pfv t term_var) ->
    ~(p1 ∈ pfv T1 term_var) ->
    ~(p1 ∈ pfv T term_var) ->
    ~(p1 = y1) ->

    ~(p2 ∈ pfv_context Γ term_var) ->
    ~(p2 ∈ pfv t term_var) ->
    ~(p2 ∈ pfv T2 term_var) ->
    ~(p2 ∈ pfv T term_var) ->
    ~(p2 = y2) ->

    is_erased_term t ->
    is_erased_term tl ->
    is_erased_term tr ->
    is_erased_type T ->
    [ Θ; Γ ⊨ t : T_sum T1 T2 ] ->
    [ Θ; (p1, T_equiv t (tleft (fvar y1 term_var))) :: (y1, T1) :: Γ ⊨
        open 0 tl (fvar y1 term_var) : open 0 T (tleft (fvar y1 term_var)) ] ->
    [ Θ; (p2, T_equiv t (tright (fvar y2 term_var))) :: (y2, T2) :: Γ ⊨
        open 0 tr (fvar y2 term_var) : open 0 T (tright (fvar y2 term_var)) ] ->
    [ Θ; Γ ⊨ sum_match t tl tr : open 0 T t ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3 || top_level_unfold reduces_to || simp_red || t_substitutions.

  - eapply reducibility_rtl; eauto; t_closer.

    unshelve epose proof (H32 ρ ((p1, uu) :: (y1,v') :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || t_substitutions || simp_red ||
             t_values_info2 || t_deterministic_star;
      try solve [ equivalent_star ];
      t_closer;
      eauto with twf.

    eapply star_backstep_reducible; eauto with cbvlemmas;
      repeat step || list_utils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils; t_closer.

  - eapply reducibility_rtl; eauto; t_closer.

    unshelve epose proof (H33 ρ ((p2, uu) :: (y2,v') :: lterms) _ _ _);
      repeat step || apply SatCons || list_utils || t_substitutions || simp_red ||
             t_values_info2 || t_deterministic_star;
      try solve [ equivalent_star ];
      t_closer;
      eauto with twf.

    eapply star_backstep_reducible; eauto with cbvlemmas;
      repeat step || list_utils; t_closer.
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils; t_closer.
Qed.


Lemma reducible_T_sum:
  forall ρ t T1 T2,
    valid_interpretation ρ ->
    [ρ ⊨ sum_match t (tleft (lvar 0 term_var)) (tright (lvar 0 term_var)) : T_sum T1 T2] ->
    [ρ ⊨ t : T_sum T1 T2].
Proof.
  unfold reduces_to, closed_term; repeat steps || list_utils.
  eapply_anywhere star_smallstep_sum_match_inv; steps; eauto with values; simpl in *;
  exists v; steps; eauto using star_trans.
Qed.

Lemma open_reducible_T_sum:
  forall Θ Γ t T1 T2,
    [Θ; Γ ⊨ sum_match t (tleft (lvar 0 term_var)) (tright (lvar 0 term_var)) : T_sum T1 T2] ->
    [Θ; Γ ⊨ t : T_sum T1 T2].
Proof.
  unfold open_reducible; steps;
    eapply reducible_T_sum; steps.
Qed.
