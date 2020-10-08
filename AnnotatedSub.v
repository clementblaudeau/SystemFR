Require Export SystemFR.Judgments.
Require Export SystemFR.ReducibilityLemmas.
Require Export SystemFR.AnnotatedSubtypeSetOps.
Require Export SystemFR.AnnotatedSubtypeOrder.
Require Export SystemFR.AnnotatedSubtypeRefine.

Opaque reducible_values.

Lemma annotated_reducible_sub:
  forall Θ Γ t T1 T2,
    [[ Θ; Γ ⊨ T1 <: T2 ]] ->
    [[ Θ; Γ ⊨ t : T1 ]] ->
    [[ Θ; Γ ⊨ t : T2 ]].
Proof.
  unfold open_reducible, open_subtype;
    repeat step; eauto using reducible_values_exprs.
Qed.

Fixpoint drop_refinement t :=
  match t with
  | T_refine t1 t2 => drop_refinement t1
  | _ => t
  end.
Lemma drop_refinement_wf :
  forall t k, wf t k -> wf (drop_refinement t) k.
Proof.
  intros.
  induction t; steps.
Qed.
Hint Resolve drop_refinement_wf: wf.

Lemma drop_refinement_pfv_subset :
  forall t tag, subset (pfv (drop_refinement t) tag) (pfv t tag).
  intros; induction t; steps; eauto using subset_left.
Qed.
Hint Resolve drop_refinement_pfv_subset: sets.

Lemma annotated_subtype_drop :
  forall tvars gamma T1,
    [[tvars; gamma ⊨ T1 <: drop_refinement T1]].
Proof.
  intros.
  induction T1; steps.
  eapply subtype_trans; eauto.
  eapply annotated_subtype_refine2.
  steps.
Qed.

Lemma annotated_reducible_drop:
  forall tvars gamma t T,
    [[ tvars; gamma ⊨ t : T ]] ->
    [[ tvars; gamma ⊨ t : (drop_refinement T) ]].
Proof.
  intros.
  eapply annotated_reducible_sub; eauto; steps; eauto using annotated_subtype_drop .
Qed.
