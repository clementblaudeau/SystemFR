Require Export SystemFR.ErasedRefine.
Require Export SystemFR.ErasedTypeRefine.
Require Export SystemFR.ErasedSetOps.

Require Export SystemFR.TypeSugar.

Require Import Coq.Lists.List.

Opaque reducible_values.

Lemma open_reducible_T_ite:
  forall tvars gamma T1 T2 b t1 t2 x1 x2,
    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T1 ->
    is_erased_type T2 ->
    subset (fv b) (support gamma) ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->

    ~(x1 ∈ fv b) ->
    ~(x1 ∈ fv t1) ->
    ~(x1 ∈ fv T1) ->
    ~(x1 ∈ fv_context gamma) ->
    ~(x1 ∈ tvars) ->

    ~(x2 ∈ fv b) ->
    ~(x2 ∈ fv T2) ->
    ~(x2 ∈ fv t2) ->
    ~(x2 ∈ fv_context gamma) ->
    ~(x2 ∈ tvars) ->

    is_erased_term b ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    [ tvars; gamma ⊨ b : T_bool ] ->
    [ tvars; (x1, T_equiv b ttrue) :: gamma ⊨ t1 : T1 ] ->
    [ tvars; (x2, T_equiv b tfalse) :: gamma ⊨ t2 : T2 ] ->
    [ tvars; gamma ⊨ ite b t1 t2 : T_ite b T1 T2 ].
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  repeat apply reducible_union || step || top_level_unfold reducible || top_level_unfold reduces_to || simp_red.

  - left.
    apply reducible_refine; repeat step || (rewrite open_none by t_closer);
      try solve [ equivalent_star ];
      t_closer.

    eapply star_backstep_reducible; repeat step || list_utils; eauto with cbvlemmas;
      t_closer.

    eapply backstep_reducible; eauto with smallstep; repeat step || list_utils;
      eauto with fv wf erased.

    unshelve epose proof (H26 theta ((x1, uu) :: lterms) _ _);
      repeat step || list_utils || apply SatCons || simp_red || t_substitutions;
      equivalent_star.

  - right.
    apply reducible_refine; repeat step || (rewrite open_none by t_closer) || list_utils;
      t_closer;
      try solve [
        apply equivalent_star; repeat step || list_utils; t_closer;
        eapply star_trans; eauto using star_smallstep_ite_cond; eauto using star_one with smallstep
      ].

    eapply star_backstep_reducible; repeat step || list_utils; eauto with cbvlemmas;
      t_closer.

    eapply backstep_reducible; eauto with smallstep; repeat step || list_utils;
      eauto with fv wf erased.

    unshelve epose proof (H27 theta ((x2, uu) :: lterms) _ _);
      repeat step || list_utils || apply SatCons || simp_red || t_substitutions;
      equivalent_star.
Qed.
