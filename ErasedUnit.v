Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque makeFresh.


Lemma reducible_unit:
  forall theta, reducible theta uu T_unit.
Proof.
  repeat step || simp_red || unfold reducible, reduces_to || eexists;
    eauto with smallstep step_tactic.
Qed.

Lemma open_reducible_unit:
  forall theta gamma,
    [ theta; gamma ⊨ uu : T_unit ].
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_unit.
Qed.
