Require Export SystemFR.Judgments.
Require Import SystemFR.ErasedUnit.

Lemma annotated_reducible_unit:
  forall Θ Γ,
    [[ Θ; Γ ⊨ uu : T_unit ]].
Proof.
   steps; auto using open_reducible_unit.
Qed.
