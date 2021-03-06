Require Export SystemFR.TypeErasure.
Require Export SystemFR.Freshness.
Require Export SystemFR.Notations.
Export Notations.UnTyped.

Require Export SystemFR.SmallStep.

Require Import Coq.Strings.String.
Open Scope bool_scope.

(* Helpers *)

Fixpoint is_nat (t : tree) : bool :=
  match t with
    | zero => true
    | succ t1 => (is_nat t1)
    | _ => false
end.

Fixpoint is_value (t: tree) : bool :=
  match t with
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (is_value e1) (is_value e2)
    | tleft e1 => (is_value e1)
    | tright e1 => (is_value e1)
    | zero => true
    | succ e1 => (is_value e1)
    | notype_lambda _ => true
    | _ => false end.

Definition get_pair t : {t': option (tree*tree) | forall t1 t2, t' = Some (t1, t2) <-> t = pp t1 t2}.
  Proof.
    exists ( match t with
    | pp e1 e2 => Some (e1,e2)
    | _ => None end).
    destruct t; steps.
  Defined.

  Definition get_app t : {t': option tree | forall t1, t' = Some t1 <-> t = notype_lambda t1}.
  Proof.
    exists (match t with
       | notype_lambda body => Some body
       | _ => None end).
    destruct t; steps.
  Defined.

  Definition get_LR t : {t': option tree | forall t1, t' = Some t1 <-> (t = tleft t1 \/ t = tright t1)}.
  Proof.
    exists (match t with
       | tleft t' => Some t'
       | tright t' => Some t'
       | _ => None end).
    destruct t; steps.
  Defined.


(* Evaluator (smallstep) *)
Fixpoint ss_eval (t: tree) {struct t}: (option tree) :=
  match t with
    | ite ttrue t1 t2 => Some t1
    | ite tfalse t1 t2 => Some t2
    | ite t t1 t2 => option_map (fun e => ite e t1 t2) (ss_eval t)

    | pp e1 e2 => match (is_value e1) with
                   | true => option_map (pp e1) (ss_eval e2)
                   | false => option_map (fun e => pp e e2) (ss_eval e1) end

    | pi1 t => match get_pair t with
              | exist _ None _  => option_map pi1 (ss_eval t)
              | exist _ (Some (e1, e2)) _ =>
                if (is_value e1) && (is_value e2)
                then Some e1
                else option_map pi1 (ss_eval t) end

    | pi2 t => match get_pair t with
              | exist _ None _ => option_map pi2 (ss_eval t)
              | exist _ (Some (e1, e2)) _ =>
                if (is_value e1) && (is_value e2)
                then Some e2
                else option_map pi2 (ss_eval t) end

    | app t1 t2 => match (is_value t1) with
                    | true => match get_app t1 with
                             | exist _ None _ => option_map (app t1) (ss_eval t2)
                             | exist _ (Some ts) _ =>
                               if (is_value t2)
                               then Some (open 0 ts t2)
                               else option_map (app t1) (ss_eval t2) end
                    | false => option_map (fun e => app e t2) (ss_eval t1) end

    | notype_tfix ts => Some (open 0 (open 1 ts zero) (notype_tfix ts))

    | succ t => option_map succ (ss_eval t)

    | tmatch t1 t0 ts => match t1 with
                       | zero => Some t0
                       | succ t2 =>
                         if (is_value t2)
                         then Some (open 0 ts t2)
                         else option_map (fun e => tmatch e t0 ts) (ss_eval t1)
                       | _ => option_map (fun e => tmatch e t0 ts) (ss_eval t1) end

    | sum_match t tl tr => if (is_value t) then match t with
                                   | tleft v => Some (open 0 tl v)
                                   | tright v => Some (open 0 tr v)
                                   | _ => None end
                          else option_map (fun e => sum_match e tl tr) (ss_eval t)

    | tleft t => option_map tleft (ss_eval t)
    | tright t => option_map tright (ss_eval t)

    | tsize t => if (is_value t) then Some (build_nat (tsize_semantics t)) else (option_map tsize (ss_eval t))
    | boolean_recognizer r t => if (is_value t) then match r with
                                                   | 0 => Some (is_pair t)
                                                   | 1 => Some (is_succ t)
                                                   | 2 => Some (is_lambda t)
                                                   | _ => None end
                               else option_map (boolean_recognizer r) (ss_eval t)
    | _ => None
  end.

(* Compute a certain number of small steps *)
Fixpoint ss_eval_n (t : tree) (k: nat) : (option tree) :=
  match k with
    | 0 => Some t
    | S k' => match ss_eval t with
               | Some t' => ss_eval_n t' k'
               | None => Some t end
  end.

(* Entry point for evaluation *)
Definition eval (t: tree) (k: nat): (option tree) :=
  ss_eval_n (erase_term t) k.


(* Tactics *)
Ltac destruct_sig :=
match goal with
  | H: _ |- context[let _ := get_pair ?t in _ ]  =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[get_pair ?t = _ ] |- _ =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[_ = get_pair ?t ] |- _ =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[get_app ?t = _ ] |- _ =>
    let fresh := fresh "get_app" in destruct (get_app t) (* eqn:fresh *)
  | H: context[_ = get_app ?t ] |- _ =>
    let fresh := fresh "get_app" in destruct (get_app t) (* eqn:fresh *)
end. (* match on type of t = sig *)

Ltac destruct_ss_eval :=
  match goal with
    | H: context[ss_eval ?t] |- _ => destruct (ss_eval t) end.


(* Results *)
Lemma is_value_correct : forall v, is_value v = true <-> cbv_value v.
Proof.
  split.
  - induction v; repeat step || bools; eauto with values.
  - induction 1; repeat step || bools.
Defined.

Lemma ss_eval_step : forall t t', ss_eval t = Some t' -> is_value t = true -> False.
Proof.
  induction t; repeat step || options.
Qed.

Ltac ss_eval_step :=
  match goal with
  |H: ss_eval ?t1 = Some ?t2 |- _ => poseNew (Mark (t1, t2) "ss_eval_step_h");
                                   pose proof  (ss_eval_step _ _ H) end.


Lemma ss_eval_correct2: forall t t',
  pfv t term_var = nil ->
  t ~> t' ->
  ss_eval t = Some t'.
Proof.
  intros. induction H0 ; repeat light || options || invert_constructor_equalities || ss_eval_step || destruct_sig || instantiate_eq_refl || list_utils || bools || rewrite <- is_value_correct in * ||  eauto using fv_nil_top_level_var with smallstep values || destruct_match.
Qed.

Lemma ss_eval_correct1: forall t t',
  ss_eval t = Some t' ->
  pfv t term_var = nil ->
  t ~> t'.
Proof.
  induction t; intros ; repeat light ; destruct_ss_eval ; repeat light || options || bools || list_utils || instantiate_eq_refl || invert_constructor_equalities || rewrite is_value_correct in * || destruct_sig || congruence ||  step_inversion cbv_value || destruct_match ; eauto using ss_eval_step, fv_nil_top_level_var with smallstep values.
Qed.

(* Main theorem : the evaluator corresponds to the small call-by-value steps *)
Theorem ss_eval_correct : forall t t',
  pfv t term_var = nil ->
    ss_eval t = Some t' <-> t ~> t'.
Proof.
  split; eauto using ss_eval_correct1, ss_eval_correct2.
Qed.

(* Extraction *)
(*
Require Extraction.

Extraction Language Ocaml.
Set Extraction AccessOpaque.

Extraction "evaluator.ml" eval.
*)
