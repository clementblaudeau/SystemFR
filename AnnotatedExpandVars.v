Require Export SystemFR.AnnotatedEquivalentMisc.
Require Export SystemFR.ErasedExpandVars.
Require Import Psatz.
Require Import Coq.Lists.List.

Opaque reducible_values.

(* Lemmas for expanding vars in the context *)

Lemma annotated_equivalent_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ( [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u ≡ v ]] <->
      [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u ≡ v ]] ).
Proof.
  intros.
  repeat simpl || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_equivalent_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_reducible_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ( [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u : v ]] <->
      [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u : v ]]).
Proof.
  intros.
  repeat simpl || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_reducible_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_subtype_expand_vars_context:
  forall Θ Γ1 Γ2 x y p t T u v,
    ~(x ∈ support Γ2) ->
    subset (fv T) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf T 0 ->
    is_annotated_type T ->
    is_annotated_term t ->

    lookup PeanoNat.Nat.eq_dec Γ2 p = Some (T_equiv (fvar y term_var) t) ->

    ( [[ Θ; Γ1 ++ (x, T) :: Γ2 ⊨ u <: v ]] <->
      [[ Θ; Γ1 ++ (x, open 0 (close 0 T y) t) :: Γ2 ⊨ u <: v ]]).
Proof.
  intros.
  repeat simpl || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close ;
    eauto with erased annot.
  eapply open_subtype_expand_vars_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.


(* Lemmas for expanding vars in the terms/types *)


Lemma annotated_reducible_expand_vars_term:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_annotated_term t1 ->
    is_annotated_type t2 ->
    ([[ Θ; Γ ⊨ t1 : t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) : t2 ]]).
Proof.
  intros.
  repeat rewrite erase_term_open || rewrite erase_term_close;
    eauto with erased annot.
  eapply open_reducible_expand_vars_term;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_reducible_expand_vars_type:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_annotated_term t ->
    is_annotated_type t2 ->
    ([[ Θ; Γ ⊨ t1 : t2 ]] <->
     [[ Θ; Γ ⊨ t1 : (open 0 (close 0 t2 y) t) ]]).
Proof.
  intros.
  repeat rewrite erase_type_open || rewrite erase_type_close;
    eauto with erased annot.
  eapply open_reducible_expand_vars_type;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.


Lemma annotated_subtype_expand_vars_left:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_annotated_term t ->
    is_annotated_type t1 ->
    ([[ Θ; Γ ⊨ t1 <: t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) <: t2 ]]).
Proof.
  intros.
  repeat rewrite erase_type_open || rewrite erase_type_close;
    eauto with erased annot.
  eapply open_subtype_expand_vars_left;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.

Lemma annotated_subtype_expand_vars_right:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf t1 0 ->
    wf t2 0 ->
    is_annotated_term t ->
    is_annotated_type t2 ->
    ([[ Θ; Γ ⊨ t1 <: t2 ]] <->
     [[ Θ; Γ ⊨ t1 <: (open 0 (close 0 t2 y) t)]]).
Proof.
  intros.
  repeat rewrite erase_type_open || rewrite erase_type_close;
    eauto with erased annot.
  eapply open_subtype_expand_vars_right;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.


Lemma annotated_equivalent_expand_vars_term:
  forall Θ Γ y p t1 t2 t,
    lookup PeanoNat.Nat.eq_dec Γ p = Some (T_equiv (fvar y term_var) t) ->
    subset (fv t1) (support Γ) ->
    wf t1 0 ->
    is_annotated_term t1 ->
    ([[ Θ; Γ ⊨ t1 ≡ t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 (close 0 t1 y) t) ≡ t2 ]]).
Proof.
  intros.
  repeat rewrite erase_term_open || rewrite erase_term_close;
    eauto with erased annot.
  eapply open_equivalent_expand_vars_term;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets.
  erewrite in_erased_context; eauto; steps.
Qed.
