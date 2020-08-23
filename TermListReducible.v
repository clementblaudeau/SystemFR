Require Import Coq.Lists.List.

Require Export SystemFR.TreeLists.
Require Export SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Lemma satisfies_erased_terms:
  forall theta l gamma,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    erased_terms l.
Proof.
  induction l; repeat step || step_inversion satisfies;
    eauto with erased.
Qed.

Hint Immediate satisfies_erased_terms: erased.

Lemma satisfies_weaken:
  forall theta gamma1 gamma2 x T T' l,
    satisfies (reducible_values theta) (gamma1 ++ (x, T) :: gamma2) l ->
    (forall t l,
      satisfies (reducible_values theta) gamma2 l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (substitute T' l)) ->
    subset (fv T) (support gamma2) ->
    subset (fv T') (support gamma2) ->
    NoDup (support (gamma1 ++ (x, T) :: gamma2)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T') :: gamma2) l.
Proof.
  induction gamma1;
    repeat step || list_utils || apply SatCons || step_inversion NoDup ||
           step_inversion satisfies.

  apply IHgamma1 with T; repeat step || list_utils; eauto.
Qed.

Lemma satisfies_transform:
  forall Γ Γ' Θ t T,
    [ Θ; Γ ⊨ t : T] ->
    (forall theta γ', satisfies (reducible_values theta) Γ' γ' ->
                 (support theta = Θ) ->
                 (valid_interpretation theta) ->
           exists γ, satisfies (reducible_values theta) Γ γ /\
                substitute t γ = substitute t γ' /\
                substitute T γ = substitute T γ') ->
    [ Θ; Γ' ⊨ t : T].
Proof.
  unfold open_reducible. steps.
  instantiate_any; steps.
  repeat rewrite_back_any.
  apply_any; steps.
Qed.

Lemma satisfies_transform_equivalent:
  forall Γ Γ' Θ t T,
    [ Θ; Γ ⊨ t ≡ T] ->
    (forall theta γ', satisfies (reducible_values theta) Γ' γ' ->
                 (support theta = Θ) ->
                 (valid_interpretation theta) ->
           exists γ, satisfies (reducible_values theta) Γ γ /\
                substitute t γ = substitute t γ' /\
                substitute T γ = substitute T γ') ->
    [ Θ; Γ' ⊨ t ≡ T].
Proof.
  unfold open_equivalent. steps.
  instantiate_any; steps.
  repeat rewrite_back_any.
  eapply_any; steps; eauto.
Qed.


Lemma satisfies_modify:
  forall (Γ Γ' : list (nat * tree)) (x : nat) (ty ty' : tree) (theta : interpretation) (l1 : list (nat * tree))
         (t1 : tree) (lterms0 : list (nat * tree)),
    satisfies (reducible_values theta) (Γ ++ (x, ty) :: Γ') (l1 ++ (x, t1) :: lterms0) ->
    support Γ = support l1 ->
    ~ x ∈ fv ty' ->
    subset (fv ty') (fv_context Γ') ->
    (x ∈ pfv_context Γ' term_var -> False) ->
    reducible_values theta t1 (psubstitute ty' lterms0 term_var) ->
    satisfies (reducible_values theta) (Γ ++ (x, ty') :: Γ') (l1 ++ (x, t1) :: lterms0).
Proof.
  induction Γ; repeat step || step_inversion satisfies || list_utils.
  + destruct l1; steps.
    apply SatCons; eauto.
  + destruct l1; steps.
    apply SatCons; eauto.
    unfold fv_context. repeat list_utils || steps.
Qed.
