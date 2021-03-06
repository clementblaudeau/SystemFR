Require Import String.
Require Import Relations.

Require Export SystemFR.PrimitiveSize.
Require Export SystemFR.PrimitiveRecognizers.

Inductive cbv_value: tree -> Prop :=
| IVUnit: cbv_value uu
| IVZero: cbv_value zero
| IVSucc: forall v, cbv_value v -> cbv_value (succ v)
| IVFalse: cbv_value tfalse
| IVTrue: cbv_value ttrue
| IVPair: forall v1 v2, cbv_value v1 -> cbv_value v2 -> cbv_value (pp v1 v2)
| IVLambda: forall t, cbv_value (notype_lambda t)
| IVLeft: forall v, cbv_value v -> cbv_value (tleft v)
| IVRight: forall v, cbv_value v -> cbv_value (tright v)
.

Hint Constructors cbv_value: values.

Inductive is_nat_value: tree -> Prop :=
| INVZero: is_nat_value zero
| INVSucc: forall v, is_nat_value v -> is_nat_value (succ v)
.

Hint Constructors is_nat_value: is_nat_value.

Ltac cbv_value t :=
  match goal with
  | H: cbv_value t |- _ => idtac
  | H: is_nat_value t |- _ => idtac
  | _ => match t with
        | zero => idtac
        | uu => idtac
        | tfalse => idtac
        | ttrue => idtac
        | succ ?v => cbv_value v
        | pp ?v1 ?v2 => cbv_value v1; cbv_value v2
        | notype_lambda _ => idtac
        | tleft ?v => cbv_value v
        | tright ?v => cbv_value v
        end
  end.

Ltac not_cbv_value t := tryif cbv_value t then fail else idtac.

Ltac t_invert_nat_value :=
  match goal with
  | H: is_nat_value _ |- _ => inversion H
  end.


Lemma is_nat_value_buildable:
  forall v, is_nat_value v ->
    exists n, v = build_nat n.
Proof.
  induction 1; steps.
  - exists 0; steps.
  - exists (S n); steps.
Qed.

Ltac is_nat_value_buildable :=
  match goal with
  | H: is_nat_value ?v |- _ =>
    poseNew (Mark v "is_nat_value_buildable");
    pose proof (is_nat_value_buildable v H)
  end.

Lemma tree_size_build_nat:
  forall n, tree_size (build_nat n) = n.
Proof.
  induction n; steps.
Qed.

Lemma is_nat_value_build_nat:
  forall n, is_nat_value (build_nat n).
Proof.
  induction n; steps; eauto with is_nat_value.
Qed.

Lemma cbv_value_build_nat:
  forall n, cbv_value (build_nat n).
Proof.
  induction n; steps; eauto with values.
Qed.

Lemma cbv_value_is_pair:
  forall v, cbv_value (is_pair v).
Proof.
  destruct v; steps.
Qed.

Lemma cbv_value_is_succ:
  forall v, cbv_value (is_succ v).
Proof.
  destruct v; steps.
Qed.

Lemma cbv_value_is_lambda:
  forall v, cbv_value (is_lambda v).
Proof.
  destruct v; steps.
Qed.

Hint Immediate is_nat_value_build_nat: values.
Hint Immediate cbv_value_build_nat: values.
Hint Immediate cbv_value_is_pair: values.
Hint Immediate cbv_value_is_succ: values.
Hint Immediate cbv_value_is_lambda: values.

Fixpoint top_level_var (t: tree): Prop :=
  match t with
  | fvar _ term_var => True
  | uu => False
  | zero => False
  | succ v => top_level_var v
  | tfalse => False
  | ttrue => False
  | pp v1 v2 => top_level_var v1 \/ top_level_var v2
  | notype_lambda t => False
  | tleft v => top_level_var v
  | tright v => top_level_var v
  | _ => False
  end.

Lemma fv_nil_top_level_var:
  forall t,
    pfv t term_var = nil ->
    ~ top_level_var t.
Proof.
  induction t;
    repeat step || list_utils || unfold singleton, add in *.
Qed.

Reserved Notation "t1 '~>' t2" (at level 20).

Inductive scbv_step: tree -> tree -> Prop :=
(* beta reduction *)
| SPBetaProj1: forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    pi1 (pp v1 v2) ~> v1
| SPBetaProj2: forall v1 v2,
    cbv_value v1 ->
    cbv_value v2 ->
    pi2 (pp v1 v2) ~> v2

| SPBetaApp: forall t v,
    cbv_value v ->
    scbv_step
      (app (notype_lambda t) v)
      (open 0 t v)

| SPBetaIte1: forall t1 t2,
    ite ttrue t1 t2 ~> t1
| SPBetaIte2: forall t1 t2,
    ite tfalse t1 t2 ~> t2

(* `notype_tfix` has a dummy hole which is used for type annotation in the `tfix` tree.
   During evaluation, we fill it with a zero *)
| SPBetaFix: forall ts,
    notype_tfix ts ~> open 0 (open 1 ts zero) (notype_tfix ts)

| SPBetaMatch0: forall t0 ts,
    tmatch zero t0 ts ~> t0
| SPBetaMatchS: forall v t0 ts,
    cbv_value v ->
    tmatch (succ v) t0 ts ~> open 0 ts v

| SPBetaMatchLeft: forall v tl tr,
    cbv_value v ->
    sum_match (tleft v) tl tr ~> open 0 tl v
| SPBetaMatchRight: forall v tl tr,
    cbv_value v ->
    sum_match (tright v) tl tr ~> open 0 tr v

| SPBetaSize:
    forall v,
      cbv_value v ->
      ~ top_level_var v ->
      tsize v ~> build_nat (tsize_semantics v)

| SPBetaIsPair:
    forall v,
      cbv_value v ->
      ~ top_level_var v ->
      boolean_recognizer 0 v ~> is_pair v
| SPBetaIsSucc:
    forall v,
      cbv_value v ->
      ~ top_level_var v ->
      boolean_recognizer 1 v ~> is_succ v
| SPBetaIsLambda:
    forall v,
      cbv_value v ->
      ~ top_level_var v ->
      boolean_recognizer 2 v ~> is_lambda v

(* reduction inside terms *)
| SPAppLeft: forall t1 t2 t,
    t1 ~> t2 ->
    app t1 t ~> app t2 t
| SPAppRight: forall t1 t2 v,
    cbv_value v ->
    t1 ~> t2 ->
    app v t1 ~> app v t2
| SPPairL: forall t1 t2 t,
    t1 ~> t2 ->
    pp t1 t ~> pp t2 t
| SPPairR: forall t1 t2 v,
    t1 ~> t2 ->
    cbv_value v ->
    pp v t1 ~> pp v t2
| SPProj1: forall t1 t2,
    t1 ~> t2 ->
    pi1 t1 ~> pi1 t2
| SPProj2: forall t1 t2,
    t1 ~> t2 ->
    pi2 t1 ~> pi2 t2

| SPSucc: forall t1 t2,
    t1 ~> t2 ->
    succ t1 ~> succ t2
| SPMatch: forall t1 t2 t0 ts,
    t1 ~> t2 ->
    tmatch t1 t0 ts ~> tmatch t2 t0 ts

| SPIte: forall t1 t1' t2 t3,
    t1 ~> t1' ->
    ite t1 t2 t3 ~> ite t1' t2 t3

| SPLeft: forall t1 t2,
    t1 ~> t2 ->
    tleft t1 ~> tleft t2
| SPRight: forall t1 t2,
    t1 ~> t2 ->
    tright t1 ~> tright t2
| SPSumMatch: forall t1 t2 tl tr,
    t1 ~> t2 ->
    sum_match t1 tl tr ~> sum_match t2 tl tr

| SPTSize: forall t1 t2,
    t1 ~> t2 ->
    tsize t1 ~> tsize t2

| SPRecognizer: forall r t1 t2,
    t1 ~> t2 ->
    boolean_recognizer r t1 ~> boolean_recognizer r t2
  where "t1 ~> t2" := (scbv_step t1 t2).

Notation "t1 ~>* t2" := (Relation_Operators.clos_refl_trans_1n _ scbv_step t1 t2) (at level 20).

Hint Constructors scbv_step: smallstep.

Lemma scbv_step_same:
  forall t1 t2 t3,
    t1 ~> t2 ->
    t2 = t3 ->
    t1 ~> t3.
Proof.
  steps.
Qed.

Ltac t_invert_step :=
  match goal with
  | _ => step_inversion scbv_step
  | H: boolean_recognizer _ _ ~> _ |- _ => inversion H; clear H
  | H: app _ _ ~> _ |- _ => inversion H; clear H
  | H: tunfold _ ~> _ |- _ => inversion H; clear H
  | H: tunfold_in _ _ ~> _ |- _ => inversion H; clear H
  | H: ite _ _ _ ~> _ |- _ => inversion H; clear H
  | H: tmatch _ _ _ ~> _ |- _ => inversion H; clear H
  | H: pp _ _ ~> _ |- _ => inversion H; clear H
  | H: pi1 _ ~> _ |- _ => inversion H; clear H
  | H: pi2 _ ~> _ |- _ => inversion H; clear H
  | H: sum_match _ _ _ ~> _ |- _ => inversion H; clear H
  | H: tsize _ ~> _ |- _ => inversion H; clear H
  end.

Lemma evaluate_step:
  forall v,
    cbv_value v ->
    forall t,
      v ~> t ->
      False.
Proof.
  induction 1;
    repeat
      step || step_inversion cbv_value || t_invert_step;
    eauto.
Qed.

Lemma evaluate_step2:
  forall t v,
    v ~> t ->
    cbv_value v ->
    False.
Proof.
  intros; eapply evaluate_step; eauto.
Qed.

Lemma evaluate_step3:
  forall t t',
    t ~> t' ->
    forall e,
      t = notype_lambda e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma evaluate_step4:
  forall t t',
    t ~> t' ->
    forall e,
      t = type_abs e ->
      False.
Proof.
  steps; t_invert_step.
Qed.

Lemma is_nat_value_value:
  forall v,
    is_nat_value v ->
    cbv_value v.
Proof.
  induction 1; steps; eauto with values.
Qed.

Hint Immediate is_nat_value_value: values.

Lemma is_nat_value_erased:
  forall v,
    is_nat_value v ->
    is_erased_term v.
Proof.
  induction 1; steps.
Qed.

Hint Immediate is_nat_value_erased: erased.

Ltac no_step :=
  match goal with
  | H: cbv_value err |- _ => inversion H
  | H1: cbv_value ?v,
    H2: ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; auto 2
  | H1: is_nat_value ?v,
    H2: ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with v t; eauto 2 with values
  | H1: cbv_value ?v1,
    H2: cbv_value ?v2,
    H3: pp ?v1 ?v2 ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with (pp v1 v2) t; auto with values
  | H1: cbv_value ?v,
    H3: succ ?v ~> ?t |- _ =>
    apply False_ind; apply evaluate_step with (succ v) t; auto with values
  | _ => t_invert_step; fail
  end.

Hint Immediate evaluate_step2: smallstep.
Hint Immediate evaluate_step3: smallstep.

Lemma deterministic_step:
  forall t1 t2,
    t1 ~> t2 ->
    forall t3,
      t1 ~> t3 ->
      t2 = t3.
Proof.
  induction 1; repeat step || t_equality;
    try solve [ repeat step || t_invert_step || no_step || t_equality ].
Qed.

Ltac deterministic_step :=
  match goal with
  | H1: ?t1 ~> ?t2,
    H2: ?t1 ~> ?t3 |- _ =>
    pose proof (deterministic_step _ _ H1 _ H2); clear H2
  end.

Hint Extern 1 => deterministic_step: smallstep.

Definition closed_term t :=
  pfv t term_var = nil /\
  wf t 0 /\
  is_erased_term t.

Definition closed_value v :=
  closed_term v /\
  cbv_value v.

Lemma cbv_value_open:
  forall v k rep,
    cbv_value v ->
    cbv_value (open k v rep).
Proof.
  induction 1;
    repeat step;
    eauto with values.
Qed.

Lemma cbv_value_subst:
  forall v l tag,
    cbv_value v ->
    cbv_value (psubstitute v l tag).
Proof.
  induction 1;
    repeat step;
    eauto with values.
Qed.
