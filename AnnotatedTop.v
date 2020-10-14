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
    (closed_value t) ->
    [[ Θ; Γ ⊨ t : T_top ]].
Proof.
  repeat steps ||
         (unfold annotated_reducible in *) ||
          (unfold closed_value in *) ||
           (unfold closed_term in * )
           || apply open_reducible_top_value
           || rewrite erase_erased_annotated_term;
           eauto with erased.
           Qed.
