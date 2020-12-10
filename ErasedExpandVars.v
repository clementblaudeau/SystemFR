Require Import Coq.Lists.List.
Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.WFLemmasClose.
Require Export SystemFR.ReducibilityEquivalent.
Require Import Psatz.

Opaque reducible_values.

(* Technical lemmas, actual heart of the proofs*)

Lemma satisfies_expand_vars_context:
  forall Γ1 Γ2 x y p t C ρ l,
    (x ∈ support Γ2 -> False) ->
    (y ∈ support Γ2) ->
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    is_erased_type C ->
    wf C 1 ->
    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 C t) :: Γ2) l <->
    satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 C (fvar y term_var)) :: Γ2) l.
Proof.
  split; intros;
    [ eapply satisfies_weaken with (open 0 C t) |
      eapply satisfies_weaken with (open 0 C (fvar y term_var)) ];
    repeat step || rewrite support_append; eauto;
      try solve [
            eapply subset_transitive;
            eauto using fv_open, fv_close with fv sets;
            repeat steps || list_utils || fv_close || unfold subset];
      rewrite substitute_open; rewrite_anywhere substitute_open; eauto using satisfies_wfs;
        eapply reducibility_open_equivalent;
        try eapply fv_open3;
        eauto using fv_close_subset, subset_transitive, wf_close, wf_subst, fv_open3 with wf erased fv cbn;
        eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
          repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Hint Extern 1 => apply <- satisfies_expand_vars_context: satisfies_expand_vars_context.
Hint Extern 1 => apply -> satisfies_expand_vars_context: satisfies_expand_vars_context.



Lemma open_equivalent_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t C u v,
    (x ∈ support Γ2 -> False) ->
    (y ∈ support Γ2) ->
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    is_erased_type C ->
    wf C 1 ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, open 0 C (fvar y term_var)) :: Γ2 ⊨ u ≡ v ] <->
     [ Θ; Γ1 ++ (x, open 0 C t) :: Γ2 ⊨ u ≡ v ]).
Proof.
  unfold open_equivalent; steps; eapply_any; eauto with satisfies_expand_vars_context.
Qed.

Lemma open_reducible_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t C u v,
    (x ∈ support Γ2 -> False) ->
    (y ∈ support Γ2) ->
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    is_erased_type C ->
    wf C 1 ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, open 0 C (fvar y term_var)) :: Γ2 ⊨ u : v ] <->
     [ Θ; Γ1 ++ (x, open 0 C t) :: Γ2 ⊨ u : v ]).
Proof.
  unfold open_reducible; steps; eapply_any; eauto with satisfies_expand_vars_context.
Qed.


Lemma open_subtype_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t C u v,
    (x ∈ support Γ2 -> False) ->
    (y ∈ support Γ2) ->
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    is_erased_type C ->
    wf C 1 ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ([ Θ; Γ1 ++ (x, open 0 C (fvar y term_var))  :: Γ2 ⊨ u <: v ] <->
     [ Θ; Γ1 ++ (x, open 0 C t) :: Γ2 ⊨ u <: v ]).
Proof.
  unfold open_subtype; steps; eapply_any; eauto with satisfies_expand_vars_context.
Qed.


(* Lemmas for expanding vars in terms/types *)

Lemma open_equivalent_expand_vars_term:
  forall Θ Γ y p C t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv C) (support Γ) ->
    (y ∈ support Γ) ->
    wf C 1 ->
    is_erased_term C ->
    ([ Θ; Γ ⊨ (open 0 C (fvar y term_var)) ≡ t2 ] <->
     [ Θ; Γ ⊨ (open 0 C t) ≡ t2 ]).
Proof.
  repeat unfold open_equivalent, substitute || steps;
    eapply equivalent_trans; try eapply_any; eauto;
    repeat rewrite substitute_open; eauto using satisfies_wfs;
    eapply equivalent_context; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_reducible_expand_vars_term:
  forall Θ Γ y p C t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv C) (support Γ) ->
    subset (fv t2) (support Γ) ->
    (y ∈ support Γ) ->
    wf C 1 ->
    wf t2 0 ->
    is_erased_term C ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ (open 0 C (fvar y term_var)) : t2 ] <->
     [ Θ; Γ ⊨ (open 0 C t) : t2 ]).
Proof.
  unfold open_reducible, substitute; split; intros;
  eapply reducibility_equivalent2; try eapply_any; eauto using wf_subst with wf erased fv;
    repeat rewrite substitute_open; eauto using satisfies_wfs;
    eapply equivalent_context; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_reducible_expand_vars_type:
  forall Θ Γ y p t1 C t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv C) (support Γ) ->
    subset (fv t1) (support Γ) ->
    (y ∈ support Γ) ->
    wf C 1 ->
    wf t1 0 ->
    is_erased_term t1 ->
    is_erased_type C ->
    ([ Θ; Γ ⊨ t1 : (open 0 C (fvar y term_var)) ] <->
     [ Θ; Γ ⊨ t1 : (open 0 C t) ]).
Proof.
  unfold open_reducible, reduces_to, substitute; steps; t_closer;
  unshelve epose proof (H7 _ _ _ _ _); eauto; steps;
  eexists; steps; eauto;
    rewrite substitute_open; rewrite_anywhere substitute_open ; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent ; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
    repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_subtype_expand_vars_left:
  forall Θ Γ y p C t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv C) (support Γ) ->
    y ∈ (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf C 1 ->
    wf t2 0 ->
    is_erased_type C ->
    is_erased_type t2 ->
    ([ Θ; Γ ⊨ (open 0 C (fvar y term_var)) <: t2 ] <->
     [ Θ; Γ ⊨ (open 0 C t) <: t2 ]).
Proof.
  unfold open_subtype, substitute; split; intros; eapply_any; eauto;
  rewrite substitute_open ; rewrite_anywhere  substitute_open; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent ; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
      repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.

Lemma open_subtype_expand_vars_right:
  forall Θ Γ y p t1 C t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv C) (support Γ) ->
    y ∈ (support Γ) ->
    wf t1 0 ->
    wf C 1 ->
    is_erased_type t1 ->
    is_erased_type C ->
    ([ Θ; Γ ⊨ t1 <: (open 0 C (fvar y term_var)) ] <->
     [ Θ; Γ ⊨ t1 <: (open 0 C t) ]).
Proof.
  unfold open_subtype, substitute; split; intros; unshelve epose proof (H7 _ _ _ _ _); eauto;
  rewrite substitute_open; rewrite_anywhere substitute_open; eauto using satisfies_wfs;
    eapply reducibility_open_equivalent; try eapply_any; try eapply fv_satisfies_nil;
      eauto using fv_close_subset, subset_transitive, wf_close, wf_subst with wf erased fv;
    eapply_anywhere satisfies_lookup3; eauto using satisfies_same_support, lookupSomeSupport2;
      repeat steps || rewrite_anywhere reducible_values_equation_16; eauto using equivalent_sym.
Qed.
