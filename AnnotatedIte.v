Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedIte.

Lemma annotated_reducible_T_ite:
  forall tvars gamma b t1 t2 T1 T2 x1 x2,
    ~(x1 ∈ fv_context gamma) ->
    ~(x1 ∈ fv b) ->
    ~(x1 ∈ fv t1) ->
    ~(x1 ∈ fv T1) ->
    ~(x1 ∈ tvars) ->

    ~(x2 ∈ fv_context gamma) ->
    ~(x2 ∈ fv b) ->
    ~(x2 ∈ fv t2) ->
    ~(x2 ∈ fv T2) ->
    ~(x2 ∈ tvars) ->

    wf t1 0 ->
    wf t2 0 ->
    wf T1 0 ->
    wf T2 0 ->
    subset (fv b) (support gamma) ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    subset (fv T1) (support gamma) ->
    subset (fv T2) (support gamma) ->
    [[ tvars; gamma ⊨ b : T_bool ]] ->
    [[ tvars; (x1, T_equiv b ttrue) :: gamma ⊨ t1 : T1 ]] ->
    [[ tvars; (x2, T_equiv b tfalse) :: gamma ⊨ t2 : T2 ]] ->
    [[ tvars; gamma ⊨ ite b t1 t2 : T_ite b T1 T2 ]].
Proof.
  unfold annotated_reducible;
    repeat step.

  apply open_reducible_T_ite with (x1:=x1) (x2:=x2);
    repeat step;
    side_conditions.
Qed.
