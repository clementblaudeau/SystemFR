Require Import Coq.Lists.List.

Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedNat.
Require Export SystemFR.Evaluator.

Lemma annotated_reducible_zero:
  forall Θ Γ,
    [[ Θ; Γ ⊨ zero : T_nat ]].
Proof.
  eauto using open_reducible_zero.
Qed.


Lemma annotated_reducible_nat_value:
  forall tvars gamma t,
    (is_nat_value t) ->
    [[ tvars; gamma ⊨ t : T_nat ]].
Proof.
  assert (forall t lterms, is_nat_value t -> erase_term t = t /\ substitute t lterms = t /\ closed_term t). {
    intros.
    rewrite <- isNat_Correct in H.
    induction t; repeat steps || bools || cbv.
  }
  unfold annotated_reducible, open_reducible, reducible, reduces_to, erase_type.
  intros.
  pose proof (H t lterms H0) as [H_erased [H_subs H_closed ] ].
  split.
    + intuition.
    + exists t ; split.
      ++ unfold substitute, psubstitute.
         rewrite (reducible_values_equation_4 theta t); eauto.
      ++ rewrite H_erased, H_subs. apply Refl.
Qed.


Lemma annotated_reducible_succ:
  forall Θ Γ t,
    [[ Θ; Γ ⊨ t : T_nat ]] ->
    [[ Θ; Γ ⊨ succ t : T_nat ]].
Proof.
  eauto using open_reducible_succ.
Qed.

Lemma annotated_reducible_match:
  forall Θ Γ tn t0 ts T n p,
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context Γ) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context Γ) ->
    ~(n = p) ->
    ~(n ∈ Θ) ->
    ~(p ∈ Θ) ->
    wf ts 1 ->
    wf t0 0 ->
    subset (fv t0) (support Γ) ->
    subset (fv ts) (support Γ) ->
    is_annotated_term ts ->
    [[ Θ; Γ ⊨ tn : T_nat ]] ->
    [[ Θ; (p, T_equiv tn zero) :: Γ ⊨ t0 : T ]] ->
    [[ Θ; (
      (p, T_equiv tn (succ (fvar n term_var))) ::
      (n, T_nat) ::
      Γ
    ) ⊨
      open 0 ts (fvar n term_var) :
      T
    ]]
    ->
    [[ Θ; Γ ⊨ tmatch tn t0 ts : T ]].
Proof.
  repeat step || erase_open.
  apply open_reducible_match with n p; repeat step || erase_open; side_conditions.
Qed.
