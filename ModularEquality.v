From Ltac2 Require Ltac2.
Require Export SystemFR.Syntax.
Require Export SystemFR.WFLemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope bool_scope.
Require Import Psatz.

Module Ltac2Rewrite.
  Import Ltac2 Constr.

  Ltac2 reveal_fixpoint fn :=
    match Unsafe.kind fn with
    | Unsafe.Constant cst _ =>
      Std.eval_unfold [(Std.ConstRef cst, Std.AllOccurrences)] fn
    | _ => Control.throw Not_found
    end.

  Ltac2 unfold_fixpoint_once fn :=
    let fixpoint := reveal_fixpoint fn in
    match Unsafe.kind fixpoint with
    | Unsafe.Fix _ _ binders bodies =>
      let binder := Array.get binders 0 in
      let unbound_body := Array.get bodies 0 in
      let body := Unsafe.substnl [fn] 0 unbound_body in
      match Unsafe.check body with
      | Val b => b
      | Err error => Control.throw error
      end
    | _ => Control.throw Not_found
    end.

  Notation unfold_fixpoint_once fn :=
    ltac2:(let fn := Constr.pretype fn in
           let fn := unfold_fixpoint_once fn in exact $fn) (only parsing).
End Ltac2Rewrite.


Notation beta x :=
  ltac:(let x := (eval cbv beta in x) in exact x) (only parsing).


Definition mod_tree_eq t1 t2 a b :=
  exists C, t1 = open 0 C a /\ t2 = open 0 C b.

(* If t and t' are equal modulo substitutions of a for b, it returns true
 *)
Fixpoint mod_tree_eqb t1 t2 a b : bool :=
  if (tree_eq t1 t2) then true
  else
    if (tree_eq t1 a && tree_eq t2 b) then true
    else
      match (t1, t2) with
      | (ite t11 t12 t13, ite t21 t22 t23)
      | (tmatch t11 t12 t13, tmatch t21 t22 t23)
      | (tlet t11 t12 t13, tlet t21 t22 t23)
      | (sum_match t11 t12 t13, sum_match t21 t22 t23)
      | (T_rec t11 t12 t13, T_rec t21 t22 t23)
        => (mod_tree_eqb t11 t21 a b) && (mod_tree_eqb t12 t22 a b) && (mod_tree_eqb t13 t23 a b)

      | (Trees.app t11 t12, Trees.app t21 t22)
      | (forall_inst t11 t12, forall_inst t21 t22)
      | (type_inst t11 t12, type_inst t21 t22)
      | (pp t11 t12, pp t21 t22)
      | (because t11 t12, because t21 t22)
      | (notype_tlet t11 t12, notype_tlet t21 t22)
      | (trefl t11 t12, trefl t21 t22)
      | (tfold t11 t12, tfold t21 t22)
      | (tunfold_in t11 t12, tunfold_in t21 t22)
      | (tunfold_pos_in t11 t12, tunfold_pos_in t21 t22)
      | (typecheck t11 t12, typecheck t21 t22)
      | (T_refine t11 t12, T_refine t21 t22)
      | (T_type_refine t11 t12, T_type_refine t21 t22)
      | (T_prod t11 t12, T_prod t21 t22)
      | (T_arrow t11 t12, T_arrow t21 t22)
      | (T_sum t11 t12, T_sum t21 t22)
      | (T_intersection t11 t12, T_intersection t21 t22)
      | (T_union t11 t12, T_union t21 t22)
      | (T_equiv t11 t12, T_equiv t21 t22)
      | (T_forall t11 t12, T_forall t21 t22)
      | (T_exists t11 t12, T_exists t21 t22)
      | (lambda t11 t12, lambda t21 t22)
      | (get_refinement_witness t11 t12, get_refinement_witness t21 t22)
      | (tfix t11 t12, tfix t21 t22)
        => (mod_tree_eqb t11 t21 a b) && (mod_tree_eqb t12 t22 a b)

      | (err t11, err t21)
      | (tsize t11, tsize t21)
      | (notype_lambda t11, notype_lambda t21)
      | (type_abs t11, type_abs t21)
      | (pi1 t11, pi1 t21)
      | (pi2 t11, pi2 t21)
      | (succ t11, succ t21)
      | (notype_tfix t11, notype_tfix t21)
      | (tunfold t11, tunfold t21)
      | (tleft t11, tleft t21)
      | (tright t11, tright t21)
      | (T_abs t11, T_abs t21)
        => (mod_tree_eqb t11 t21 a b)

      | (boolean_recognizer n1 t11, boolean_recognizer n2 t21)
        => (PeanoNat.Nat.eqb n1 n2) && (mod_tree_eqb t11 t21 a b)
      | (unary_primitive o1 t11, unary_primitive o2 t21)
        => (if (un_op_eq_dec o1 o2) then true else false) && (mod_tree_eqb t11 t21 a b)
      | (binary_primitive o1 t11 t12, binary_primitive o2 t21 t22)
        => (if (bin_op_eq_dec o1 o2) then true else false) && (mod_tree_eqb t11 t21 a b) && (mod_tree_eqb t12 t22 a b)

      | _ => false

      end
.

Lemma mod_tree_eqb_eqn : forall t1 t2 a b,
    mod_tree_eqb t1 t2 a b =
    beta((Ltac2Rewrite.unfold_fixpoint_once mod_tree_eqb) t1 t2 a b).
Proof. intros. destruct t1, t2; reflexivity. Qed.

Lemma mod_tree_eqb_refl: forall t a b,
    mod_tree_eqb t t a b = true.
Proof.
  Opaque tree_eq.
  intros.
  pose proof (eq_refl t) as Heq. apply tree_eq_prop in Heq.
  destruct t; simpl; rewrite Heq; reflexivity.
Qed.

Lemma mod_tree_eqb_mod: forall a b,
    mod_tree_eqb a b a b = true.
Proof.
  Opaque tree_eq.
  intros.
  assert (tree_eq a a && tree_eq b b = true) as Heq by
        (apply andb_true_intro; repeat rewrite tree_eq_prop; steps).
  rewrite mod_tree_eqb_eqn.
  repeat (destruct_match; try reflexivity; try congruence).
Qed.

Hint Resolve mod_tree_eqb_refl: mod_eq.
Hint Resolve mod_tree_eqb_mod: mod_eq.


Lemma mod_tree_eqb_correct :
  forall a b t2 t1,
    wf t1 0 ->
    wf t2 0 ->
    mod_tree_eqb t1 t2 a b = true ->
    mod_tree_eq t1 t2 a b.
Proof.
  Opaque tree_eq.
  unfold mod_tree_eq; intros a b.
  assert (forall n t2 t1 k,
             tree_size t1 < n ->
             tree_size t2 < n ->
             wf t1 k -> wf t2 k ->
             mod_tree_eqb t1 t2 a b = true ->
             exists C : tree, t1 = open k C a /\ t2 = open k C b). {
    induction n; intros; try lia.
    rewrite_anywhere mod_tree_eqb_eqn.
    destruct (tree_eq t1 t2) eqn:Heq.
    + rewrite_anywhere tree_eq_prop.
      exists t1. repeat steps || open_none.
    + destruct (tree_eq t1 a && tree_eq t2 b) eqn:Hmod_eq.
      ++ repeat steps || bools || rewrite_anywhere tree_eq_prop.
         exists (lvar k term_var); steps.
      ++ clear Heq Hmod_eq.
         repeat (destruct_match; try discriminate H3);
           simpl in *; bools; light; try rewrite_anywhere PeanoNat.Nat.eqb_eq.
         all: repeat match goal with
                     | H1: wf ?t1 ?k,
                           H: mod_tree_eqb ?t1 ?t2 _ _ = true |- _ =>
                       let fresh_C := fresh "C" in
                       apply (IHn t2 t1 k) in H; eauto; try lia;
                         destruct H as [fresh_C [fresh_C1 fresh_C2]];
                         subst
                     end.
         all: try solve [
                    match goal with
                    | H:_ |- exists C, (?c (open _ ?C0 _) (open _ ?C1 _) (open _ ?C2 _)) = _ /\ _ = _ => exists (c C0 C1 C2)
                    | H:_ |- exists C, (?c (open _ ?C0 _) (open _ ?C1 _)) = _ /\ _ = _ => exists (c C0 C1)
                    | H:_ |- exists C, (?c (open _ ?C0 _)) = _ /\ _ = _ => exists (c C0)
                    end; steps ].
  }
  intros.
  eapply H with (n := S (PeanoNat.Nat.max (tree_size t1) (tree_size t2))); eauto;
    apply le_n_S, PeanoNat.Nat.max_le_iff; steps.
Qed.


Lemma mod_tree_eqb_equiv :
  forall a b t2 t1,
    wf t1 0 ->
    wf t2 0 ->
    mod_tree_eq t1 t2 a b ->
    mod_tree_eqb t1 t2 a b = true.
Proof.
  Opaque tree_eq.
  unfold mod_tree_eq; intros a b.
  assert (forall n C k,
             tree_size C < n ->
             mod_tree_eqb (open k C a) (open k C b) a b = true
            ). {
    induction n; intros; try lia.
    pose proof (eq_refl C).
    rewrite mod_tree_eqb_eqn.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    bools.
    repeat rewrite_anywhere tree_neq_prop.
    destruct C; simpl in *;
      solve [
          congruence |
          (eapply IHn; try lia) |
          (exfalso; steps) |
          (bools; intuition auto; try eapply_any; try lia; try (destruct_match);
           eauto using PeanoNat.Nat.eqb_refl)].
  }
  steps; eauto.
Qed.
