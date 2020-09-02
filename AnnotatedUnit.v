Require Export SystemFR.Judgments.
Require Import SystemFR.ErasedUnit.

Lemma annotated_reducible_unit:
  forall theta gamma,
    [[ theta; gamma ⊨ uu : T_unit ]].
Proof.
  unfold annotated_reducible in *; repeat step;
    auto using open_reducible_unit.
Qed.
