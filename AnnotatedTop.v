Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedTop.

Lemma annotated_reducible_top:
  forall tvars gamma t T,
    [[ tvars; gamma ⊨ t : T ]] ->
    [[ tvars; gamma ⊨ t : T_top ]].
Proof.
  unfold annotated_reducible.
  steps; eauto using open_reducible_top.
Qed.

Lemma annotated_reducible_top_value:
  forall tvars gamma t,
    (is_annotated_term t) ->
    (closed_value t) ->
    [[ tvars; gamma ⊨ t : T_top ]].
Proof.
  repeat steps
  || (unfold annotated_reducible, closed_value, closed_term in * )
  || apply open_reducible_top_value
  || rewrite erase_erased_annotated_term;
    eauto.
Qed.
