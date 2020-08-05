Require Export SystemFR.Judgments.
Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.ErasedBool.

Lemma annotated_reducible_true:
  forall tvars gamma,
    [[ tvars; gamma ⊨ ttrue : T_bool ]].
Proof.
  unfold annotated_reducible;
    repeat step; eauto using open_reducible_true.
Qed.

Lemma annotated_reducible_false:
  forall tvars gamma,
    [[ tvars; gamma ⊨ tfalse : T_bool ]].
Proof.
  unfold annotated_reducible;
    repeat step; eauto using open_reducible_false.
Qed.

Lemma annotated_reducible_ite:
  forall tvars gamma b t1 t2 T x1 x2,

    ~(x1 ∈ fv_context gamma) ->
    ~(x1 ∈ fv b) ->
    ~(x1 ∈ fv t1) ->
    ~(x1 ∈ fv T) ->
    ~(x1 ∈ tvars) ->

    ~(x2 ∈ fv_context gamma) ->
    ~(x2 ∈ fv b) ->
    ~(x2 ∈ fv t2) ->
    ~(x2 ∈ fv T) ->
    ~(x2 ∈ tvars) ->

    wf t1 0 ->
    wf t2 0 ->
    subset (fv t1) (support gamma) ->
    subset (fv t2) (support gamma) ->
    [[ tvars; gamma ⊨ b : T_bool ]] ->
    [[ tvars; (x1, T_equiv b ttrue)  :: gamma ⊨ t1 : T ]] ->
    [[ tvars; (x2, T_equiv b tfalse) :: gamma ⊨ t2 : T ]] ->
    [[ tvars; gamma ⊨ ite b t1 t2 : T ]].
Proof.
  unfold annotated_reducible.
  repeat step.
    repeat step || apply open_reducible_ite with (x1 := x1) (x2 := x2);
    side_conditions.
Qed.
