Require Import Coq.Lists.List.
Require Export SystemFR.ReducibilityOpenEquivalent.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.FVLemmasClose.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.WFLemmasClose.
Require Export SystemFR.ReducibilityEquivalent.
Require Export SystemFR.RedTactics.
Require Import Psatz.

Opaque reducible_values.

Lemma satisfies_inline_app:
  forall Γ1 Γ2 x t T C f ρ lterms,
    subset (pfv C term_var) (support Γ2) ->
    subset (pfv t term_var) (support Γ2) ->
    subset (pfv f term_var) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->
    wf C 1 ->
    wf t 0 ->
    wf f 1 ->
    is_erased_type C ->
    is_erased_term t ->
    is_erased_term f ->
    [support ρ; Γ2 ⊨ t : T] ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2) lterms <->
    satisfies (reducible_values ρ) (Γ1 ++ (x, open 0 C (app (notype_lambda f) t)) :: Γ2) lterms.
Proof.
  steps;
    [ eapply satisfies_weaken with (open 0 C (open 0 f t)) |
      eapply satisfies_weaken with (open 0 C (app (notype_lambda f) t))] ;

    repeat step || rewrite support_append; eauto using subset_transitive, fv_open, subset_union2;
      unfold open_reducible, reduces_to in *;

      repeat steps || (eauto with wf erased fv cbn) ||
             rewrite substitute_open ||
             rewrite_anywhere substitute_open ||
             eapply reducibility_open_equivalent ||
             t_instantiate_sat3 ||
             eapply equivalent_beta ||
             (eapply equivalent_sym; eapply equivalent_beta);
      t_closer.
Qed.

Hint Extern 1 => apply <- satisfies_inline_app: satisfies_inline_app.
Hint Extern 1 => apply -> satisfies_inline_app: satisfies_inline_app.


(* Lemmas for inlining inside the context *)

Lemma open_reducible_inline_app_context:
  forall Θ Γ1 Γ2 x t T C u v f,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_erased_type C ->
    is_erased_term t ->
    is_erased_term f ->

    [ Θ; Γ2 ⊨ t : T] ->

    ([ Θ; Γ1 ++ (x, open 0 C (app (notype_lambda f) t))  :: Γ2 ⊨ u : v ] <->
     [ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u : v ]).
Proof.
  unfold open_reducible; steps; eapply_any; eauto with satisfies_inline_app.
Qed.

Lemma open_equivalent_inline_app_context:
  forall Θ Γ1 Γ2 x t T C u v f,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_erased_type C ->
    is_erased_term t ->
    is_erased_term f ->

    [ Θ; Γ2 ⊨ t : T] ->

    ([ Θ; Γ1 ++ (x, open 0 C (app (notype_lambda f) t))  :: Γ2 ⊨ u ≡ v ] <->
     [ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u ≡ v ]).
Proof.
  unfold open_equivalent; steps; eapply_any; eauto with satisfies_inline_app.
Qed.

Lemma open_subtype_inline_app_context:
  forall Θ Γ1 Γ2 x t T C u v f,
    subset (fv C) (support Γ2) ->
    subset (fv t) (support Γ2) ->
    subset (fv f) (support Γ2) ->
    NoDup (support Γ1 ++ x :: support Γ2) ->

    wf C 1 ->
    wf f 1 ->
    wf t 0 ->

    is_erased_type C ->
    is_erased_term t ->
    is_erased_term f ->

    [ Θ; Γ2 ⊨ t : T] ->

    ([ Θ; Γ1 ++ (x, open 0 C (app (notype_lambda f) t))  :: Γ2 ⊨ u <: v ] <->
     [ Θ; Γ1 ++ (x, open 0 C (open 0 f t)) :: Γ2 ⊨ u <: v ]).
Proof.
  unfold open_subtype; steps; eapply_any; eauto with satisfies_inline_app.
Qed.




(* Lemmas for inline inside the terms *)


Lemma open_equivalent_inline_app_term:
  forall Θ Γ  C t2 f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    is_erased_term t ->
    is_erased_term f ->
    [ Θ; Γ ⊨ t : T] ->
    ([ Θ; Γ ⊨ (open 0 C (app (notype_lambda f) t)) ≡ t2 ] <->
     [ Θ; Γ ⊨ (open 0 C (open 0 f t)) ≡ t2 ]).
Proof.
  repeat unfold open_equivalent, reduces_to, open_reducible, substitute || steps || t_instantiate_sat3;
    eapply equivalent_trans; try eapply_any; eauto;
      repeat steps || (eauto with wf erased fv cbn) ||
             rewrite substitute_open ||
             rewrite_anywhere substitute_open ||
             eapply equivalent_context ||
             eapply equivalent_beta ||
             (eapply equivalent_sym; eapply equivalent_beta);
      t_closer.
Qed.


Lemma open_reducible_inline_app_term:
  forall Θ Γ  C t2 f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t2 0 ->
    is_erased_term t ->
    is_erased_term f ->
    is_erased_term C ->
    is_erased_type t2 ->
    [ Θ; Γ ⊨ t : T] ->
    ([ Θ; Γ ⊨ (open 0 C (app (notype_lambda f) t)) : t2 ] <->
     [ Θ; Γ ⊨ (open 0 C (open 0 f t)) : t2 ]).
Proof.
  unfold open_equivalent, open_reducible, substitute; steps;
  unshelve epose proof (H11 _ _ _ _ eq_refl); eauto; top_level_unfold reduces_to; unfold closed_term in *;
  repeat steps ||
         ( rewrite substitute_open ||
           rewrite_anywhere substitute_open ||
           eapply reducibility_equivalent2 ||
           eapply equivalent_context ;
           eauto 6 using equivalent_beta, equivalent_sym with wf fv erased values).
Qed.

Lemma open_reducible_inline_app_type:
  forall Θ Γ t1 C f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t1) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t1 0 ->
    is_erased_term t ->
    is_erased_term f ->
    is_erased_type C ->
    is_erased_term t1 ->
    [ Θ; Γ ⊨ t : T] ->
    ([ Θ; Γ ⊨ t1 : (open 0 C (app (notype_lambda f) t))] <->
     [ Θ; Γ ⊨ t1 : (open 0 C (open 0 f t))]).
Proof.
  unfold open_equivalent, open_reducible, substitute; steps;
  repeat t_instantiate_sat3 ; steps;
   repeat steps ||
         ( rewrite substitute_open ||
           rewrite_anywhere substitute_open ;
           eauto 6 using equivalent_beta, equivalent_sym with wf fv erased values);
    eapply reducibility_open_equivalent2; eauto with fv erased wf values;
    unfold reduces_to, closed_term in * |-; steps;
    eauto 6 using equivalent_beta, equivalent_sym with erased wf fv values.
Qed.


Lemma open_subtype_inline_app_left:
  forall Θ Γ  C t2 f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t2) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t2 0 ->
    is_erased_term t ->
    is_erased_term f ->
    is_erased_type C ->
    is_erased_type t2 ->
    [ Θ; Γ ⊨ t : T] ->
    ([ Θ; Γ ⊨ (open 0 C (app (notype_lambda f) t)) <: t2 ] <->
     [ Θ; Γ ⊨ (open 0 C (open 0 f t)) <: t2 ]).
Proof.
  unfold open_equivalent, open_reducible, open_subtype, substitute; steps; eapply_any; eauto;
  t_instantiate_sat3; steps;
  repeat steps ||
         ( rewrite substitute_open ||
           rewrite_anywhere substitute_open  ||
           eapply reducibility_open_equivalent  ||
           eapply equivalent_context ||
           (unfold reduces_to, closed_value in * |-) ||
           eapply equivalent_beta ||
           eapply equivalent_sym, equivalent_beta ;
           eauto with wf fv erased values).
Qed.

Lemma open_subtype_inline_app_right:
  forall Θ Γ  C t1 f t T,
    subset (fv C) (support Γ) ->
    subset (fv t) (support Γ) ->
    subset (fv f) (support Γ) ->
    subset (fv t1) (support Γ) ->
    wf C 1 ->
    wf f 1 ->
    wf t 0 ->
    wf t1 0 ->
    is_erased_term t ->
    is_erased_term f ->
    is_erased_type C ->
    is_erased_type t1 ->
    [ Θ; Γ ⊨ t : T] ->
    ([ Θ; Γ ⊨ t1 <: (open 0 C (app (notype_lambda f) t))] <->
     [ Θ; Γ ⊨ t1 <: (open 0 C (open 0 f t))]).
Proof.
  unfold open_equivalent, open_reducible, open_subtype, substitute; steps;
    t_instantiate_sat3; steps;
  unshelve epose proof (H12 _ _ _ _ eq_refl _ _); eauto;
  repeat steps ||
         ( rewrite substitute_open ||
           rewrite_anywhere substitute_open  ||
           eapply reducibility_open_equivalent  ||
           eapply equivalent_context ||
           (unfold reduces_to, closed_value in * |-) ||
           eapply equivalent_beta ||
           eapply equivalent_sym, equivalent_beta ;
           eauto with wf fv erased values).
Qed.
