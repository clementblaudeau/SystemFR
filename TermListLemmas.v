Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.WellFormed.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.


Lemma satisfies_insert:
  forall (P: tree -> tree -> Prop) gamma1 gamma2 l1 l2 t T x,
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma2) ->
    pfv t term_var = nil ->
    pfv t type_var = nil ->
    wf t 0 ->
    twf t 0 ->
    P t (substitute T l2) ->
    support gamma1 = support l1 ->
    ~(x ∈ support gamma1) ->
    ~(x ∈ fv_context gamma1) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv T -> False) ->
    satisfies P (gamma1 ++ gamma2) (l1 ++ l2) ->
    satisfies P (gamma1 ++ (x,T) :: gamma2) (l1 ++ (x,t) :: l2).
Proof.
  induction gamma1; destruct l1;
    repeat step || step_inversion satisfies || apply SatCons || t_listutils ||
           (rewrite substitute_skip by (steps; eauto with bfv b_cmap)); eauto.
Qed.


Lemma satisfies_drop:
  forall (P: tree -> tree -> Prop) gamma1 gamma2 l1 l2 t T x,
    support gamma1 = support l1 ->
    ~(x ∈ fv_context gamma1) ->
    satisfies P (gamma1 ++ (x,T) :: gamma2) (l1 ++ (x,t) :: l2) ->
    satisfies P (gamma1 ++ gamma2) (l1 ++ l2).
Proof.
  induction gamma1; destruct l1;
    repeat step || step_inversion satisfies || apply SatCons || t_listutils ||
           (rewrite substitute_skip in * by (steps; eauto with bfv b_cmap)); eauto.
Qed.
