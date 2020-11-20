Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedTop.

Lemma annotated_reducible_top:
  forall Θ Γ t T,
    [[ Θ; Γ ⊨ t : T ]] ->
    [[ Θ; Γ ⊨ t : T_top ]].
Proof.
  steps; eauto using open_reducible_top.
Qed.

Lemma annotated_reducible_top_value:
  forall Θ Γ t,
    (is_annotated_term t) ->
    (cbv_value (erase_term t)) ->
    subset (fv t) (support Γ) ->
    wf t 0 ->
    [[ Θ; Γ ⊨ t : T_top ]].
Proof.
  repeat steps || apply open_reducible_top_value ; steps; eauto with erased wf fv values.
  rewrite pfv_erase_context_subst2.
  eauto using subset_transitive, pfv_erase_term_subst.
Qed.
