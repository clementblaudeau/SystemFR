Require Import Coq.Lists.List.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedInlineApplications.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.AnnotatedTactics.

Lemma annotated_reducible_inline_app_context:
  forall Θ Γ1 Γ2 x t T U C u v f,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_annotated_type C ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type U ->

    [[ Θ; Γ2 ⊨ t : T]] ->

    ([[ Θ; Γ1 ++ (x, open 0 C (app (lambda U f) t))  :: Γ2 ⊨ u : v ]] <->
     [[ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u : v ]]).
Proof.
  intros.
  repeat simpl || rewrite erase_context_append in * || rewrite erase_type_open || rewrite erase_type_close || rewrite erase_term_open ;
    eauto with erased annot;
  eapply open_reducible_inline_app_context;
    repeat rewrite erased_context_support;
    eauto using annotated_type_close, in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst
      with erased wf fv sets;
    erewrite in_erased_context; eauto; steps.
Qed.

Ltac annotated_rewrites :=
  repeat (rewrite erase_context_append in *) ||
          (rewrite erase_type_open in *) ||
           (rewrite erase_term_open in *) ;
            eauto with erased annot.


Lemma annotated_equivalent_inline_app_context:
  forall Θ Γ1 Γ2 x t T C f U u v ,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_annotated_type C ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type U ->

    [[ Θ; Γ2 ⊨ t : T]] ->

    ([[ Θ; Γ1 ++ (x, open 0 C (app (lambda U f) t))  :: Γ2 ⊨ u ≡ v ]] <->
     [[ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u ≡ v ]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ];
  eapply open_equivalent_inline_app_context;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.

Lemma annotated_subtype_inline_app_context:
  forall Θ Γ1 Γ2 x t T C u v U f,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_annotated_type C ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type U ->

    [[ Θ; Γ2 ⊨ t : T]] ->

    ([[ Θ; Γ1 ++ (x, open 0 C (app (lambda U f) t))  :: Γ2 ⊨ u <: v ]] <->
     [[ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u <: v ]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ];
  eapply open_subtype_inline_app_context;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.

(* Lemmas for inline inside the terms *)


Lemma annotated_equivalent_inline_app_term:
  forall Θ Γ C t2 U f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_term C ->
    is_annotated_type U ->
    [[ Θ; Γ ⊨ t : T]] ->
    ([[ Θ; Γ ⊨ (open 0 C (app (lambda U f) t)) ≡ t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 C (open 0 f t)) ≡ t2 ]]).
Proof.  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ].
  eapply open_equivalent_inline_app_term;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.


Lemma annotated_reducible_inline_app_term:
  forall Θ Γ C t2 U f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t2 0 ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_term C ->
    is_annotated_type t2 ->
    [[ Θ; Γ ⊨ t : T]] ->
    ([[ Θ; Γ ⊨ (open 0 C (app (lambda U f) t)) : t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 C (open 0 f t)) : t2 ]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ].
  eapply open_reducible_inline_app_term;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.

Lemma annotated_reducible_inline_app_type:
  forall Θ Γ t1 C U f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t1) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t1 0 ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type C ->
    is_annotated_type U ->
    is_annotated_term t1 ->
    [[ Θ; Γ ⊨ t : T]] ->
    ([[ Θ; Γ ⊨ t1 : (open 0 C (app (lambda U f) t))]] <->
     [[ Θ; Γ ⊨ t1 : (open 0 C (open 0 f t))]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ].
  eapply open_reducible_inline_app_type;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.

Lemma annotated_subtype_inline_app_left:
  forall Θ Γ  C t2 U f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t2 0 ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type C ->
    is_annotated_type t2 ->
    is_annotated_type U ->
    [[ Θ; Γ ⊨ t : T]] ->
    ([[ Θ; Γ ⊨ (open 0 C (app (lambda U f) t)) <: t2 ]] <->
     [[ Θ; Γ ⊨ (open 0 C (open 0 f t)) <: t2 ]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ].
  eapply open_subtype_inline_app_left;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.

Lemma annotated_subtype_inline_app_right:
  forall Θ Γ C t1 U f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t1) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t1 0 ->
    is_annotated_term t ->
    is_annotated_term f ->
    is_annotated_type C ->
    is_annotated_type t1 ->
    is_annotated_type U ->
    [[ Θ; Γ ⊨ t : T]] ->
    ([[ Θ; Γ ⊨ t1 <: (open 0 C (app (lambda U f) t))]] <->
     [[ Θ; Γ ⊨ t1 <: (open 0 C (open 0 f t))]]).
Proof.
  intros.
  repeat simpl || annotated_rewrites ; try solve [ steps ].
  eapply open_subtype_inline_app_right;
    repeat rewrite erased_context_support;
    eauto using in_erased_context, pfv_erase_type_subst, pfv_erase_term_subst  with erased wf fv.
Qed.
