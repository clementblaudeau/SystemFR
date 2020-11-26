Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedSum.

Lemma annotated_reducible_left:
  forall Θ Γ t A B,
    [[ Θ; Γ ⊨ t : A ]] ->
    [[ Θ; Γ ⊨ tleft t : T_sum A B ]].
Proof.
  intros; eauto using open_reducible_left.
Qed.

Lemma annotated_reducible_right:
  forall Θ Γ t A B,
    [[ Θ; Γ ⊨ t : B ]] ->
    [[ Θ; Γ ⊨ tright t : T_sum A B ]].
Proof.
  intros; eauto using open_reducible_right.
Qed.

Lemma annotated_reducible_sum_match:
  forall Θ Γ t tl tr A B T y1 y2 p1 p2,
    ~(p1 ∈ fv tl) ->
    ~(p1 ∈ fv t) ->
    ~(p1 ∈ fv T) ->
    ~(p1 ∈ fv A) ->
    ~(p1 ∈ fv_context Γ) ->
    ~(p1 ∈ Θ) ->

    ~(p2 ∈ fv tr) ->
    ~(p2 ∈ fv t) ->
    ~(p2 ∈ fv T) ->
    ~(p2 ∈ fv B) ->
    ~(p2 ∈ fv_context Γ) ->
    ~(p2 ∈ Θ) ->

    ~(y1 ∈ fv tl) ->
    ~(y1 ∈ fv t) ->
    ~(y1 ∈ fv T) ->
    ~(y1 ∈ fv A) ->
    ~(y1 ∈ fv_context Γ) ->
    ~(y1 = p1) ->
    ~(y1 ∈ Θ) ->

    ~(y2 ∈ fv tr) ->
    ~(y2 ∈ fv B) ->
    ~(y2 ∈ fv t) ->
    ~(y2 ∈ fv T) ->
    ~(y2 ∈ fv_context Γ) ->
    ~(y2 = p2) ->
    ~(y2 ∈ Θ) ->

    wf T 1 ->
    wf t 0 ->
    wf A 0 ->
    wf B 0 ->
    wf tl 1 ->
    wf tr 1 ->
    is_annotated_type T ->
    is_annotated_term t ->
    is_annotated_term tl ->
    is_annotated_term tr ->
    subset (fv t) (support Γ) ->
    subset (fv tl) (support Γ) ->
    subset (fv tr) (support Γ) ->
    subset (fv A) (support Γ) ->
    subset (fv B) (support Γ) ->
    subset (fv T) (support Γ) ->
    [[ Θ; Γ ⊨ t : T_sum A B ]] ->
    [[
      Θ; (p1, T_equiv t (tleft (fvar y1 term_var))) :: (y1, A) :: Γ ⊨
        open 0 tl (fvar y1 term_var) :
        open 0 T (tleft (fvar y1 term_var)) ]]
    ->
    [[
      Θ; (p2, T_equiv t (tright (fvar y2 term_var))) :: (y2, B) :: Γ ⊨
        open 0 tr (fvar y2 term_var) :
        open 0 T (tright (fvar y2 term_var)) ]]
    ->
    [[ Θ; Γ ⊨ sum_match t tl tr : open 0 T t ]].
Proof.
  repeat step || erase_open.
  apply open_reducible_sum_match with (erase_type A) (erase_type B) y1 y2 p1 p2;
    repeat step;
    side_conditions.
Qed.

Lemma annotated_reducible_T_sum:
  forall Θ Γ t T1 T2,
    [[Θ; Γ ⊨ sum_match t (tleft (lvar 0 term_var)) (tright (lvar 0 term_var)) : T_sum T1 T2]] ->
    [[Θ; Γ ⊨ t : T_sum T1 T2]].
Proof.
  intros; eapply open_reducible_T_sum; steps.
Qed.
