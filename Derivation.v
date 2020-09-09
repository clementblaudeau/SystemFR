Require Export SystemFR.DerivationTrees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Evaluator.
Require Export SystemFR.NatLessThanErase.

Require Import List.
Import ListNotations.

Reset Ltac Profile.
Set Ltac Profiling.

Fixpoint is_valid(dv: derivation) (Γ: context) : bool :=
  match dv with

  (* TYPING JUDGMENTS *)

  (* Unit *)
  | N (TJ J_Unit _ _ uu T_unit ) nil => true

  (* Bools *)
  | N (TJ J_Bool _ _ ttrue T_bool) nil => true
  | N (TJ J_Bool _ _ tfalse T_bool) nil => true

  (* Naturals *)
  | N (TJ J_Nat _ _ zero T_nat) nil => true
  | N (TJ J_Nat _ _ (succ t) T_nat) nil => (isNat t)
  | N (TJ J_Nat Θ _ (succ t) T_nat) (N (TJ I0 _ Same _ T_nat as j) _ as dv' ::nil) =>
    (j ?= (TJ I0 Θ Same t T_nat)) && (is_valid dv' Γ)

  (* Nat match *)
  | N (TJ J_Match Θ _ (tmatch tn t0 ts) T)
      ((N jn nil as dn)
         ::(N ((TJ I0 _ (Append [(p, T_equiv _ zero)] ) _ _) as j0) _ as d0)
         ::(N ((TJ Is _ (Append [(_, T_equiv _ _ ); (n,_)] ) _ _) as js) _ as ds)
         ::nil) =>
    (jn ?= (TJ J_Nat Θ Same tn T_nat)) && (is_valid dn Γ)
    && (j0 ?= (TJ I0 Θ (Append [(p, T_equiv tn zero)]) t0 T)) && (is_valid d0 ((p, T_equiv tn zero)::Γ))
    && (js ?= (TJ Is Θ (Append [(p, T_equiv tn (succ (fvar n term_var))); (n, T_nat)]) (open 0 ts (fvar n term_var)) T))
    && (is_valid ds ((p, T_equiv tn (succ (fvar n term_var))):: (n, T_nat)::nil++Γ) )
    && (p ?∉ (fv ts)) && (p ?∉ (fv t0)) && (p ?∉ (fv tn)) && (p ?∉ (fv T)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv tn)) && (n ?∉ (fv ts)) && (n ?∉ (fv T)) && (n ?∉ (fv_context Γ))
    && (n ?<> p) && (n ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_termb ts)

  (* If then else *)
  | N (TJ J_If Θ _ (ite b t1 t2) T)
      ((N (TJ Ic _ Same _ T_bool as jb) _ as db)
         ::(N ((TJ I1 _ (Append [(x1,(T_equiv _ ttrue ))]) _ T1) as j1) _ as d1)
         ::(N ((TJ I2 _ (Append [(x2,(T_equiv _ tfalse))]) _ T2) as j2) _ as d2)
         ::nil) =>
    (jb ?= (TJ Ic Θ Same b T_bool)) && (is_valid db Γ)
    && (x1 ?∉ (fv_context Γ))
    && (x1 ?∉ Θ )
    && (x1 ?∉ (fv t1))
    && (x2 ?∉ (fv t2))
    && ((PeanoNat.Nat.eqb x1 x2) || ((x2 ?∉ (fv_context Γ)) && (x2 ?∉ Θ ))) &&
    if (tree_eq T (T_ite b T1 T2)) then (
        (* Type unification *)
        (j1 ?= (TJ I1 Θ (Append [(x1, T_equiv b ttrue)]) t1 T1)) && (is_valid d1 ((x1, T_equiv b ttrue)::Γ))
        && (j2 ?= (TJ I2 Θ (Append [(x2, T_equiv b tfalse)]) t2 T2)) && (is_valid d2 ((x2, T_equiv b tfalse)::Γ))
        && (x1 ?∉ (fv T1))
        && (x2 ?∉ (fv T2))
      )
    else (
        (* Same type *)
        (j1 ?= (TJ I1 Θ (Append [(x1, T_equiv b ttrue)]) t1 T)) && (is_valid d1 ((x1, T_equiv b ttrue)::Γ))
        && (j2 ?= (TJ I2 Θ (Append [(x2, T_equiv b tfalse)]) t2 T)) && (is_valid d2 ((x2, T_equiv b tfalse)::Γ))
        && (x1 ?∉ (fv T)) && (x2 ?∉ (fv T))
      )

  (* Pairs *)
  (* PP *)
  | N (TJ J_PP Θ _ (pp t1 t2) (T_prod A B))
      ((N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 A)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 (open 0 B t1))) && (is_valid d2 Γ)
    && (is_annotated_termb t1) && (is_annotated_typeb B)
  (* Pi1 *)
  | N (TJ J_Pi1 Θ _ (pi1 t) A)
      ((N ((TJ I1 _ Same _ (T_prod _ B)) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Same t (T_prod A B))) && (is_valid d Γ)
  (* Pi2 *)
  | N (TJ J_Pi2 Θ _ (pi2 t) T)
      ((N ((TJ I1 _ Same _ (T_prod A B)) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Same t (T_prod A B))) && (is_valid d Γ)
    && (is_annotated_typeb B)
    && (is_annotated_termb t)
    && ((fv B) ?⊂ (support Γ))
    && (tree_eq T (open 0 B (pi1 t)))

  (* Sums *)
  (* Left *)
  | N (TJ J_Left Θ _ (tleft t) (T_sum A B))
      ((N ((TJ I1 _ Same _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Same t A)) && (is_valid d Γ) && (wfb B 0) && ((fv B) ?⊂ (support Γ))
  (* Right *)
  | N (TJ J_Right Θ _ (tright t) (T_sum A B))
      ((N ((TJ I1 _ Same _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ Same t B)) && (is_valid d Γ) && (wfb A 0) && ((fv A) ?⊂ (support Γ))
  (* Sum_match *)
  | N (TJ (J_SumMatch T) Θ _ (sum_match t tl tr) T')
      ((N ((TJ I1 _ Same _ (T_sum A B)) as j) _ as d)
         :: (N ((TJ Il _ (Append [(p, _);(y, _)]) _ _) as jl) _ as dl)
         :: (N ((TJ Ir _ _ _ _) as jr) _ as dr) :: nil) =>
       (j ?= (TJ I1 Θ Same t (T_sum A B))) && (is_valid d Γ)
       && (jl ?= (TJ Il Θ (Append [(p, T_equiv t (tleft (fvar y term_var)));(y, A)]) (open 0 tl (fvar y term_var)) (open 0 T (tleft (fvar y term_var)))))
       && (is_valid dl ((p, T_equiv t (tleft (fvar y term_var)))::(y, A)::Γ))
       && (jr ?= (TJ Ir Θ (Append [(p, T_equiv t (tright (fvar y term_var)));(y, B)]) (open 0 tr (fvar y term_var)) (open 0 T (tright (fvar y term_var)))))
       && (is_valid dr ((p, T_equiv t (tright (fvar y term_var)))::(y, B)::Γ))
       && (tree_eq T' (open 0 T t))
       && (p ?∉ (fv tl)) && (p ?∉ (fv tr)) && (p ?∉ (fv t)) && (p ?∉ (fv T)) && (p ?∉ (fv A)) && (p ?∉ (fv B)) && (p ?∉ (fv_context Γ))
       && (y ?∉ (fv tl)) && (y ?∉ (fv tr)) && (y ?∉ (fv t)) && (y ?∉ (fv T)) && (y ?∉ (fv A)) && (y ?∉ (fv B)) && (y ?∉ (fv_context Γ))
       && (y ?<> p) && (y ?∉ Θ) && (p ?∉ Θ)
       && (is_annotated_termb t) && (is_annotated_termb tl)
       && (is_annotated_termb tr)  && (is_annotated_typeb T)


  (* App *)
  | N (TJ J_App Θ _ (Trees.app t1 t2) T)
      ((N ((TJ I1 _ Same _ (T_arrow U V)) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 (T_arrow U V))) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 U)) && (is_valid d2 Γ)
    && is_annotated_typeb V
    && is_annotated_termb t2
    && (tree_eq T (open 0 V t2))

  (* Lambda *)
  | N (TJ J_Lambda Θ _ (lambda U t) (T_arrow _ V as T))
      ((N ((TJ I1 _ (Append [(x,_)]) _ _) as j) _ as d)::nil) =>
    (j ?= (TJ I1 Θ (Append [(x,U)]) (open 0 t (fvar x term_var)) (open 0 V (fvar x term_var))))
    && (is_valid d ((x,U)::Γ))
    && is_annotated_termb t
    && wfb U 0
    && (x ?∉ fv_context Γ)
    && (x ?∉ Θ)
    && (x ?∉ (fv V))
    && (x ?∉ (fv t))
    && ((fv U) ?⊂ (support Γ))
    && (fv_context Γ ?⊂ (support Γ))
    && is_annotated_typeb V
    && (tree_eq T (T_arrow U V))

  (* tlet *)
  | N (TJ (J_Let B) Θ _ (tlet t1 A t2) T)
      ((N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ (Append [(p, _);(x,_)]) _ _) as j2) _ as d2) :: nil) =>
    (j1 ?= (TJ I1 Θ Same t1 A)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ (Append [(p, T_equiv (fvar x term_var) t1);(x,A)]) (open 0 t2 (fvar x term_var)) (open 0 B (fvar x term_var)))) && (is_valid d2 ((p, T_equiv (fvar x term_var) t1)::(x,A)::Γ) )
    && (x ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (x ?<> p)
    && (x ?∉ (fv t2)) && (p ?∉ (fv t2))
    && (x ?∉ (fv B)) && (p ?∉ (fv B))
    && (x ?∉ (fv A)) && (p ?∉ (fv A))
    && (x ?∉ (fv t1)) && (p ?∉ (fv t1))
    && (x ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_typeb B)
    && (is_annotated_termb t1) && (is_annotated_termb t2)
    && (tree_eq T (open 0 B t1))

  (* notype_tlet *)
  | N (TJ (J_Let B) Θ _ (notype_tlet t1 t2) T)
      ((N ((TJ I1 _ Same _ A) as j1) _ as d1)
         :: (N ((TJ I2 _ (Append [(p, _);(x,_)]) _ _) as j2) _ as d2) :: nil) =>
    (j1 ?= (TJ I1 Θ Same t1 A)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ (Append [(p, T_equiv (fvar x term_var) t1);(x,A)]) (open 0 t2 (fvar x term_var)) (open 0 B (fvar x term_var)))) && (is_valid d2 ((p, T_equiv (fvar x term_var) t1)::(x,A)::Γ) )
    && (x ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (x ?<> p)
    && (x ?∉ (fv t2)) && (p ?∉ (fv t2))
    && (x ?∉ (fv B)) && (p ?∉ (fv B))
    && (x ?∉ (fv A)) && (p ?∉ (fv A))
    && (x ?∉ (fv t1)) && (p ?∉ (fv t1))
    && (x ?∉ Θ) && (p ?∉ Θ)
    && (is_annotated_typeb B)
    && (is_annotated_termb t1) && (is_annotated_termb t2)
    && (tree_eq T (open 0 B t1))

  (* Var *)
  | N (TJ J_Var _ _ (fvar x term_var) T) nil =>
    (option_tree_dec_eq (lookup PeanoNat.Nat.eq_dec Γ x) (Some T))
    && (wfb T 0) && (subsetb (fv T) (support Γ))

  (* Drop refinement *)
  | N (TJ J_drop Θ _ t T2)
      ((N ((TJ I1 _ Same _ T1) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Same t T1)) && (is_valid d1 Γ) && (tree_eq T2 (drop_refinement T1))

  (* Unfold refinement - typing jugement version *)
  | N (TJ J_refine_unfold Θ _ t T)
      (( N ((TJ I1 _ (New Γ') _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ (New Γ') t T)) && (is_valid d1 Γ') &&
    match refinementUnfoldInContext Γ' Γ with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (is_annotated_termb P) && ((fv ty) ?⊂ (support Γ')) && ((fv P) ?⊂ (support Γ'))
        && (wfb P 1))
    | None => false
    end

  (* Add refinement *)
  | N (TJ J_refine Θ _ t (T_refine A b))
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: ( N ((EJ I2 _ (Append [(p, _);(x, _)]) B ttrue) as j2) _ as d2):: nil) =>
    (j1 ?= (TJ I1 Θ Same t A)) && (is_valid d1 Γ)
    && (j2 ?= (EJ I2 Θ (Append [(p, T_equiv (fvar x term_var) t);(x,A)]) (open 0 b (fvar x term_var)) ttrue))
    && (is_valid d2 ((p, T_equiv (fvar x term_var) t)::(x,A)::Γ))
    && (p ?∉ (fv_context Γ)) && (p ?∉ (fv b)) && (p ?∉ (fv t)) && (p ?∉ (fv A)) && (p ?∉ Θ)
    && (x ?∉ (fv_context Γ)) && (x ?∉ (fv b)) && (x ?∉ (fv t)) && (x ?∉ (fv A)) && (x ?∉ Θ)
    && (x ?<> p) && (is_annotated_termb b) && ((fv b) ?⊂ (fv_context Γ))

  (*
  (* Var - weaken *)
  | N (TJ J_VarWeaken Θ ((x,T)::Γ) u U)
      ((N ((TJ I1 _ _ _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Γ u U)) && (is_valid d1)
    && (x ?∉ (support Γ)) && (x ?∉ (fv u)) && (x ?∉ (fv U)) && (x ?∉ Θ)
  *)

  (* Fix *)
  | N (TJ J_Fix Θ _ (tfix T ts) (T_forall T_nat T'))
      ((N ((TJ I1 _ (Append [(p, _);(y, _);(n, _)]) _ _) as j1) _ as d1) :: nil) =>
    (tree_eq T T')
    && (j1 ?= (TJ I1 Θ (Append [(p, T_equiv (fvar y term_var) (tfix T ts))
                          ;(y, T_forall (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var))) T)
                          ;(n, T_nat)])
                  (open 0 (open 1 ts (fvar n term_var)) (fvar y term_var))
                  (open 0 T (fvar n term_var))))
    && (isValue (erase_term ts))
    && (is_valid d1 ((p, T_equiv (fvar y term_var) (tfix T ts))
                          ::(y, T_forall (T_refine T_nat (annotated_tlt (lvar 0 term_var) (fvar n term_var))) T)
                          ::(n, T_nat)::Γ))
    && (n ?∉ (fv_context Γ)) && (y ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv T)) && (y ?∉ (fv T)) && (p ?∉ (fv T))
    && (n ?∉ (fv ts)) && (y ?∉ (fv ts)) && (p ?∉ (fv ts))
    && (n ?∉ Θ) && (y ?∉ Θ) && (p ?∉ Θ)
    && (NoDupb (n::y::p::nil)) && (wfb (erase_term ts) 1) && (wfb ts 1)
    && (is_annotated_termb ts) && (is_annotated_typeb T)

  (* Elimination *)
  | N (TJ J_equiv_elim Θ _ t2 T)
      (( N ((EJ I1 _ Same t1 _) as j1) _  as d1)
         :: ( N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (EJ I1 Θ Same t1 t2)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t1 T)) && (is_valid d2 Γ)

  (* Forall Instantiation *)
  | N (TJ J_forall_inst Θ _ (forall_inst t1 t2) T2)
      (( N ((TJ I1 _ Same _ (T_forall U V)) as j1) _ as d1)
         :: ( N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 (T_forall U V))) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 U)) && (is_valid d2 Γ)
    && (tree_eq T2 (open 0 V t2))
    && ((fv t1) ?⊂ (support Γ)) && ((fv t2) ?⊂ (support Γ)) && ((fv V) ?⊂ (support Γ))
    && (is_annotated_typeb V) && (is_annotated_termb t2)

  (* Error *)
  | N (TJ J_error Θ _ (err t) T)
      (( N ((EJ I1 _ Same tfalse ttrue) as j1) _ as d1) :: nil) =>
    (j1 ?= (EJ I1 Θ Same tfalse ttrue)) && (is_valid d1 Γ)
    && (wfb T 0 )
    && (tree_eq t T)
    && ((fv T) ?⊂ (support Γ))

  (* Top *)
  | N (TJ J_Top Θ _ t T_top)
      (( N ((TJ I1 _ Same _ T) as j1) _ as d1) :: nil) =>
    (j1 ?= (TJ I1 Θ Same t T)) && (is_valid d1 Γ)

  | N (TJ J_Top_value Θ _ t T_top) nil =>
    (closed_valueb t) && (is_annotated_termb t)


  (* EQUIVALENCE JUDGMENTS *)
  (* Symetric *)
  | N (EJ E_sym Θ _ t1 t2)
      ((N ((EJ I1 _ Same _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (EJ I1 Θ Same t2 t1)) && (is_valid d1 Γ)

  (* Transitivity *)
  | N (EJ E_trans Θ _ t1 t3)
      ((N ((EJ I1 _ Same _ t2) as j1) _ as d1)
         :: (N ((EJ I2 _ Same _ _) as j2) _ as d2) :: nil) =>
    (j1 ?= (EJ I1 Θ Same t1 t2)) && (is_valid d1 Γ)
    && (j2 ?= (EJ I2 Θ Same t2 t3)) && (is_valid d2 Γ)

  (* Reflexivity *)
  | N (EJ E_refl Θ _ t t') nil =>
    (tree_eq t t') && (wfb t 0)
    && ((fv t) ?⊂ (support Γ))
    && (is_erased_termb t)

  (* Lambdas *)
  | N (EJ E_lambdas Θ _ (lambda A t1) (lambda B t2))
      (( N ((EJ I1 _ Same _ _) as j1) _ as d1) :: nil) =>
    (j1 ?= (EJ I1 Θ Same t1 t2)) && (is_valid d1 Γ)
    && (wfb A 0) && (wfb B 0) (* ADDED HYPOTHESIS *)
    && (is_annotated_termb t1)
    && (is_annotated_termb t2)
    && (is_annotated_typeb A)
    && (subsetb (fv A) (support Γ))
    && (subsetb (fv B) (support Γ)) (* ADDED HYPOTHESIS *)

  (* Context *)
  | N (EJ (E_context C) Θ _ T1 T2)
      (( N ((EJ I1 _ Same t1 t2) as j1)   as d1) :: nil) =>
    (j1 ?= (EJ I1 Θ Same t1 t2)) && (is_valid d1 Γ)
    && (is_annotated_termb t1) && (is_annotated_termb t2)
    && (subsetb (fv C) (support Γ)) && (is_annotated_termb C)
    && (tree_eq T1 (open 0 C t1))
    && (tree_eq T2 (open 0 C t2))
    && (wfb C 1)

  (* Unfold refinement - equivalence jugement version *)
  | N (EJ E_refine_unfold Θ _ t T)
      (( N ((EJ I1 _ (New Γ') _ _) as j1) _ as d1)::nil) =>
    (j1 ?= (EJ I1 Θ (New Γ') t T)) && (is_valid d1 Γ') &&
    match refinementUnfoldInContext Γ' Γ with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (is_annotated_termb P) && ((fv ty) ?⊂ (support Γ')) && ((fv P) ?⊂ (support Γ'))
        && (wfb P 1))
    | None => false
    end

  (* Pair ext *)
  | N (EJ E_pair_ext Θ _ t T)
      (( N ((TJ I1 _ Same _ (T_prod A B)) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Same t (T_prod A B))) && (is_valid d1 Γ)
    && (tree_eq T (pp (pi1 t) (pi2 t)))
    && (is_annotated_termb t)

  (* SMT solver (trusted) *)
  | N (EJ E_SMT Θ _ t1 t2) c =>
    (List.forallb (fun ds => is_valid ds Γ) c) && (wfb t1 0) && (wfb t2 0)
    && ((fv t1) ?⊂ (support Γ)) && ((fv t2) ?⊂ (support Γ))

  | _ => false
  end.



Ltac modus_ponens_is_valid :=
  match goal with
  | H: is_valid ?ds ?Γ = true,
       H1: forall Γ, is_valid ?ds Γ = true -> _ |- _ => pose proof (H1 Γ H); clear H1
  end.


Ltac rewrite_deriv :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints deriv in H
  end.

Ltac destruct_clear t H := destruct t; try apply (ex_falso_quolibet _ H).

Hint Unfold closed_value: deriv.

Lemma is_valid_wf_aux: forall dv Γ, is_valid dv Γ = true -> wf (J_term1 (root dv)) 0 /\ wf (J_term2 (root dv)) 0.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2. unfold forallP in X.
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat subst || light_bool || match goal with | H: wf (_ _) _ |- _ => simpl in H end || rewrite_deriv || invert_constructor_equalities || inst_list_prop || modus_ponens_is_valid || unfold closed_value, closed_term in * ; simpl.
  all: repeat split; eauto with wf deriv.
Qed.


Lemma is_valid_support_term_aux :
  forall dv Γ, is_valid dv Γ = true ->
          subset (fv (J_term1 (root dv)) ) (support Γ) /\
          subset (fv (J_term2 (root dv)) ) (support Γ).
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv. unfold forallP in X.
  destruct J.
  all: pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match;  try apply (ex_falso_quolibet _ H)); try discriminate.
  (* Apply induction hypothesis and do the rewrites *)
  all: simpl; eauto 2 using subset_nil.
  all: unfold fv_context in *.
  all: repeat light_bool || subst || inst_list_prop || modus_ponens_is_valid.
  all: repeat rewrite_deriv || invert_constructor_equalities || subst.
  all: repeat subst || light_bool || rewrite_deriv || discriminate || rewrite pfv_fvar || rewrite pfv_fvar2 ||
              match goal with
              | H1: ~ ?x ∈ ?A, H2: subset ?A (?x::?B) |- _ => apply (subset_add3 _ x A B H1) in H2
              | H: subset (pfv (_ _ _) _) _ |- _ => simpl in H
              | H: subset _ (support (_::_)) |- _ => simpl in H
              | H : subset (support (_++_)) _ |- _ => rewrite support_append in H
              | H: is_nat_value ?t |- subset (pfv ?t ?tag) ?A => rewrite nat_value_fv
              | H: subset (_ ++ _) _ |- _ => apply subset_union3 in H
              | H: _ |- subset ( _ ++ _ ) _ => apply subset_union2; eauto
              | H1: ~ ?n ∈ (fv_context ?Γ),
                    H2: subset (support ?Γ) (fv_context ?Γ)
                |- _ => apply (in_subset_not (support Γ) (fv_context Γ) n H2) in H1
              | H: subset (fv (open ?k ?t1 ?t2)) ?A
                |- subset (pfv ?t1 term_var) _ => apply (support_open t1 t2 term_var k A) in H
              | H: ?x ∈ ?A |- subset (singleton ?x) ?A => apply singleton_subset; assumption
              | H: lookup ?e ?A ?x = Some ?y |- _ => apply (@lookupSupport _ _ e A x y) in H
              | H: _ |- subset (singleton ?n) (?n :: _) => apply singleton_subset, inList1
              | H: _ |- subset (singleton ?n) (_ :: ?n :: _) => apply singleton_subset, inList2
              | H: _ |- subset (singleton ?n) (_ :: _ :: ?n :: _) => apply singleton_subset, inList3
              | H: subset (fv (open ?k1 (open ?k2 ?t (fvar ?n3 term_var)) (fvar ?n2 term_var))) (?n1::?n2::?n3::?A),
                   H1: ~ ?n3 ∈ (fv ?t),
                       H2: ~ ?n2 ∈ (fv ?t),
                           H3: ~ ?n1 ∈ (fv ?t)
                |- subset (pfv ?t term_var) ?A  => apply (subset_open_open k1 k2 t n3 n2 n1 A H H1 H2 H3)
              | H: subset( fv (_ _ _)) _ |- _ => cbn in H
              | H: refinementUnfoldInContext ?Γ ?Γ0 = Some (?x, ?p, ?ty, ?P) |- _ =>
                apply refinementUnfoldInContext_support2 in H
              end
       || invert_constructor_equalities || apply support_open2 || simpl || split || rewrite_any || unfold closed_value, closed_term in * ;
    eauto 3 using singleton_subset, inList1, inList2, inList3 with sets.
Qed.


(* Parameter SMT_Check (Θ Γ ... ) : Prop. *)

Lemma trustSMTSolver_ADMITTED : forall Θ Γ cΓ t T c, is_valid (N (EJ E_SMT Θ cΓ t T) c) Γ = true -> [[Θ;Γ ⊨ t ≡ T]].
Admitted.


Ltac consume_is_valid :=
  match goal with
  | H: is_valid ?dv ?Γ = true |- _ =>
    epose proof (is_valid_support_term_aux dv Γ H) ;
    epose proof (is_valid_wf_aux dv Γ H) ; clear H
  end.


Lemma subset_any_type: forall n Γ,  subset (pfv (fvar n term_var) term_var) (n :: @support nat tree Γ).
Proof.
  intros. apply (support_fvar n zero Γ). Qed.
Hint Resolve subset_any_type: deriv.

Ltac subset_open :=
  match goal with
  | H: subset (fv (open ?k ?t (fvar ?n term_var))) (?n :: (support ?Γ)) |- _ =>
    pose proof (support_open t (fvar n term_var) term_var k (n::support Γ) H (subset_any_type n Γ)); clear H
  end.
Hint Extern 50 => eapply support_open: deriv.
Hint Rewrite PeanoNat.Nat.eqb_neq: deriv.
Hint Rewrite PeanoNat.Nat.eqb_eq: deriv.

Ltac soundness_finish :=
  repeat subst || destruct_and ||
         assumption ||
         match goal with
         | H1: ~ ?x ∈ ?A, H2: subset ?A (?x::?B) |- _ => apply (subset_add3 _ x A B H1) in H2
         | H: subset _ (support (_::_)) |- _ => simpl in H
         | H1: subset ?A ?B,
               H2: subset ?B ?C,
                   H3: ~?n ∈ ?C
           |- ~ ?n ∈ ?A => apply (in_subset_not _ _ n (subset_transitive _ _ _ H1 H2) H3)
         | H: subset (fv (open ?k ?t1 ?t2)) ?A
           |- subset (fv ?t1) _ => apply (support_open t1 t2 term_var k A) in H
         | H: wf (open _ _ _) _ |- _ => apply wf_open_rev in H
         | H: wf (_ _ _) _ |- _ => simpl in H
         | H: NoDupb ?L |- List.NoDup ?L => apply NoDupb_prop
         | H: subset (fv (_ _ _)) _ |- _ => cbn in H; apply subset_union3 in H
         | H: _ |- subset (singleton ?n) (?n :: _) => apply singleton_subset, inList1
         | H: ~ ?a ∈ ?L |- List.NoDup (?a::?L) => apply (List.NoDup_cons a H)
         | H:_ |- List.NoDup (?a::nil) => apply (List.NoDup_cons a (@List.in_nil _ a))
         | H:_ |- List.NoDup nil => apply List.NoDup_nil
         | H: _ |- subset (singleton ?n) (_ :: ?n :: _) => apply singleton_subset, inList2
         | H: _ |- subset (singleton ?n) (_ :: _ :: ?n :: _) => apply singleton_subset, inList3
         | H: subset (fv (open ?k1 (open ?k2 ?t (fvar ?n3 term_var)) (fvar ?n2 term_var))) (?n1::?n2::?n3::?A),
              H1: ~ ?n3 ∈ (fv ?t),
                  H2: ~ ?n2 ∈ (fv ?t),
                      H3: ~ ?n1 ∈ (fv ?t)
           |- subset (pfv ?t term_var) ?A  => apply (subset_open_open k1 k2 t n3 n2 n1 A H H1 H2 H3)
         end || rewrite pfv_fvar || rewrite pfv_fvar2 || simpl || unfold fv || rewrite_deriv.

Hint Rewrite isValueCorrect: deriv.


Ltac destruct_andb :=
  match goal with
  |H: ?b1 && ?b2 = true |- _ =>
   let H1 := fresh H in
   let H2 := fresh H in
   pose proof (andb_prop b1 b2 H) as [H1 H2] ; clear H
  end.



(* Main soundess result *)
Lemma is_valid_soundess : forall dv Γ, is_valid dv Γ = true -> is_true (root dv) Γ.
Proof.
  induction dv using derivation_ind.
  intros. unfold root, J_term1, J_term2, fv, is_true. unfold forallP in X.
  destruct J.
  all: pose proof (subset_context_support Γ).
  (* Finish pattern matching deconstruction *)
  all: cbn in H; repeat (destruct_match; try apply (ex_falso_quolibet _ H)).
  (* Apply induction hypothesis and do the rewrites *)
  all: repeat destruct_andb.
  all: try (inst_list_prop ; repeat modus_ponens_is_valid) ; subst.
  all: repeat consume_is_valid.
  all: repeat subst || rewrite_deriv || invert_constructor_equalities.
  all: repeat destruct_and || destruct_or || match goal with | H: is_true _ _ |- _ => simpl in H end || subst || light_bool.

  (* remove easy cases *)
  all: eauto 1 with deriv.
  all: try discriminate.
  all: unfold fv_context in *.
  all:
    try
      match goal with
      | H: _ |- [[?Θ; ?Γ ⊨ ?t : drop_refinement ?T]] => eapply annotated_reducible_drop
      | H: [[ ?Θ ; ((?p, _)::(?x,_)::_) ⊨ (open _ ?b _) ≡ ttrue ]] |- [[ ?Θ ; ?Γ ⊨ ?t : T_refine _ _ ]] => eapply (annotated_reducible_refine Θ Γ _ _ _  x p); eauto
      | H: (is_nat_value ?t) |- [[?Θ; ?Γ ⊨ (succ ?t) : T_nat]] => apply (annotated_reducible_nat_value Θ Γ (succ t) (INVSucc t H)); cbv
      | H: _
        |- [[?Θ; ?Γ ⊨ (tmatch ?tn ?t0 ?ts) : ?T]] => apply (annotated_reducible_match Θ Γ _ _ _ T n7 n3)
      | H1: [[?Θ; (?x1, T_equiv _ ttrue)::?Γ ⊨ _ : _ ]],
            H2: [[?Θ; (?x2, T_equiv _ tfalse)::?Γ ⊨ _ : _ ]]
        |- [[?Θ; ?Γ ⊨ (ite ?t1 ?t2 ?t3) : (T_ite _ ?T1 ?T2)]] =>
        (apply (annotated_reducible_T_ite Θ Γ t1 t2 t3 T1 T2 x1 x2))
      | H1: [[?Θ; (?x1, T_equiv _ ttrue)::?Γ ⊨ _ : _ ]],
            H2: [[?Θ; (?x2, T_equiv _ tfalse)::?Γ ⊨ _ : _ ]]
        |- [[?Θ; ?Γ ⊨ (ite ?t1 ?t2 ?t3) : ?T ]] => apply (annotated_reducible_ite Θ Γ t1 t2 t3 T x1 x2)
      | H: [[?Θ; ?Γ ⊨ ?t : (T_prod ?A ?B)]]
        |- [[?Θ; ?Γ ⊨ (pi1 ?t) : ?A]] => apply (annotated_reducible_pi1 Θ Γ t A B)
      | H: [[?Θ; ?Γ ⊨ ?t : (T_prod ?A ?B)]]
        |- [[?Θ; ?Γ ⊨ (pi2 ?t) : _]] => apply (annotated_reducible_pi2 Θ Γ t A B)
      | H: _
        |- [[?Θ; ?Γ ⊨ (pp ?t1 ?t2) : (T_prod ?A ?B)]] => eapply (annotated_reducible_pp Θ Γ A B t1 t2)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_arrow ?U ?V)]]
        |- [[?Θ; ?Γ ⊨ (Trees.app ?t1 ?t2) : ?T]] => apply (annotated_reducible_app Θ Γ t1 t2 U V)
      | H: [[?Θ; ?Γ ⊨ ?t1 : (T_sum ?A ?B)]], H1: ?y <> ?p
        |- [[?Θ; ?Γ ⊨ (sum_match ?t1 ?t2 ?t3) : ?T]] => eapply (annotated_reducible_sum_match Θ Γ t1 t2 t3 A B _ y p)
      | H: _
        |- [[?Θ; ?Γ ⊨ (lambda ?T ?t) : _]] => eapply (annotated_reducible_lambda)
      | H: ?x <> ?p
        |- [[?Θ; ?Γ ⊨ (tlet ?t1 ?A ?t2) : _]] => apply (annotated_reducible_let Θ Γ t1 t2 x p A)
      | H: ?x <> ?p, H1: [[?Θ; ?Γ ⊨ ?t1 : ?A]]
        |- [[?Θ; ?Γ ⊨ (notype_tlet ?t1 ?t2) : _]] => apply (annotated_reducible_notype_tlet Θ Γ t1 t2 x p A)
      | H: [[ ?Θ; (?p,_)::(?y,_)::(?n,_)::?Γ ⊨ _ : _ ]] |-  [[?Θ; ?Γ ⊨ (tfix ?t1 ?t2) : (T_forall T_nat ?t1)]] => apply (annotated_reducible_fix_strong_induction Θ Γ t2 t1 n y p)
      | H: [[ ?Θ; ?Γ ⊨ ?t1 : (T_forall ?U ?V)]], H2 : [[_; _ ⊨ ?t2 : ?U]] |- _ => apply (annotated_reducible_forall_inst Θ Γ t1 t2 U V)
      |H: [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2 ]], H2: [[?Θ; ?Γ ⊨ ?t2 ≡ ?t3]] |- [[?Θ; ?Γ ⊨ ?t1 ≡ ?t3 ]] => apply (annotated_equivalent_trans Θ Γ t1 t2 t3 H H2)
      |H: [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2 ]] |- [[?Θ; ?Γ ⊨ ?t2 ≡ ?t1 ]] => apply (annotated_equivalent_sym Θ Γ t1 t2 H)
      |H: _ |- [[?Θ; ?Γ ⊨ ?t ≡ ?t ]] => apply (annotated_equivalent_refl Θ Γ t)
      |H: _ |- [[?Θ; ?Γ ⊨ (lambda ?A ?t1) ≡ (lambda ?B ?t2) ]] => apply (annotated_equivalence_lambdas Θ Γ t1 t2 A B); eauto with wf
      | H:  [[?Θ; ?Γ ⊨ ?t1 ≡ ?t2]] |- [[?Θ; ?Γ ⊨ open 0 ?C ?t1 ≡ open 0 ?C ?t2]] => apply (annotated_equivalence_context Θ Γ C t1 t2)
      |H1: [[ ?Θ ; ?Γ ⊨ ?t1 ≡ ?t2]], H2 : [[ ?Θ ; ?Γ ⊨ ?t1 : ?T]]
       |- [[ ?Θ ; ?Γ ⊨ ?t2 : ?T]] => apply (annotated_equivalent_elim Θ Γ t1 t2 T)
      |H: [[?Θ;?Γ ⊨ ?t : ?T_prod ?A ?B ]]
       |-  [[?Θ;?Γ ⊨ ?t ≡ (pp (pi1 ?t) (pi2 ?t))]] => apply (annotated_equivalent_pair_ext Θ Γ t A B)
      | H: refinementUnfoldInContext ?Γ0 ?Γ = Some (?x, ?p, ?ty, ?P) |- [[ ?Θ ; ?Γ ⊨ ?t : ?T]] =>
        let Γ := fresh Γ in
        let Γ' := fresh Γ' in
        let fH := fresh H in
        rewrite refinementUnfoldInContext_prop in H; destruct H as [Γ [Γ' [H fH] ] ]; subst;
          apply annotated_reducible_unfold_refine; eauto; rewrite support_append in *;
            rewrite fv_context_append in *;
            list_utils; steps
      | H: refinementUnfoldInContext ?Γ0 ?Γ = Some (?x, ?p, ?ty, ?P) |- [[ ?Θ ; ?Γ ⊨ ?t ≡ ?T]] =>
        let Γ := fresh Γ in
        let Γ' := fresh Γ' in
        let fH := fresh H in
        rewrite refinementUnfoldInContext_prop in H; destruct H as [Γ [Γ' [H fH] ] ]; subst;
          apply annotated_reducible_equivalent_unfold_refine; eauto; rewrite support_append in *;
            rewrite fv_context_append in *;
            list_utils; steps
      end; soundness_finish; eauto with deriv.

  assert (is_valid (N (EJ E_SMT Θ Same t T) c) Γ = true).
  cbn; repeat bools || steps || autorewrite with deriv; eauto.
  eauto using trustSMTSolver_ADMITTED.
  Qed.

Show Ltac Profile.
