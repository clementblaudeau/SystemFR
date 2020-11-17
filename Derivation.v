Require Export SystemFR.DerivationTrees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Evaluator.

Require Import List.
Import ListNotations.


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
  | N (TJ J_Nat _ _ (succ t) T_nat) nil => (is_nat t)
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

  (* Primitives *)
  | N (TJ J_UnPrimitive Θ _ (unary_primitive Not t1) T_bool)
      (( N ((TJ I1 _ Same _ T_bool) as j1) _ as d1)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_bool)) && (is_valid d1 Γ)

  | N (TJ J_BinPrimitive Θ _ (binary_primitive (Plus | Mul) t1 t2) T_nat)
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_nat)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 T_nat)) && (is_valid d2 Γ)

  | N (TJ J_BinPrimitive Θ _ (binary_primitive (And | Or) t1 t2) T_bool)
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_bool)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 T_bool)) && (is_valid d2 Γ)

  | N (TJ J_BinPrimitive Θ _ (binary_primitive (Lt | Leq | Gt | Geq | Eq | Neq) t1 t2) T_bool)
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_nat)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 T_nat)) && (is_valid d2 Γ)

  | N (TJ J_BinPrimitive Θ _ (binary_primitive Minus t1 t2) T_nat)
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)
         :: (N ((EJ I3 _ Same _ _) as j3) _ as d3)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_nat)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 T_nat)) && (is_valid d2 Γ)
    && (j3 ?= (EJ I3 Θ Same (binary_primitive Geq t1 t2) ttrue)) && (is_valid d3 Γ)

  | N (TJ J_BinPrimitive Θ _ (binary_primitive Div t1 t2) T_nat)
      (( N ((TJ I1 _ Same _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ Same _ _) as j2) _ as d2)
         :: (N ((EJ I3 _ Same _ _) as j3) _ as d3)::nil) =>
    (j1 ?= (TJ I1 Θ Same t1 T_nat)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t2 T_nat)) && (is_valid d2 Γ)
    && (j3 ?= (EJ I3 Θ Same (binary_primitive Gt t2 zero) ttrue)) && (is_valid d3 Γ)

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
    match refinementUnfoldInContext Γ Γ' with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (x ?<> p) && (x ?∉ fv ty) && (x ?∉ fv P)
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
    && (j1 ?= (TJ I1 Θ
                  (Append [(p, T_equiv (fvar y term_var) (tfix T ts))
                           ;(y, T_forall (T_refine T_nat (binary_primitive Lt (lvar 0 term_var) (fvar n term_var))) T)
                           ;(n, T_nat)])
                  (open 0 (open 1 ts (fvar n term_var)) (fvar y term_var))
                  (open 0 T (fvar n term_var))))
    && (is_value (erase_term ts))
    && (is_valid d1 ((p, T_equiv (fvar y term_var) (tfix T ts))
                       ::(y, T_forall (T_refine T_nat (binary_primitive Lt (lvar 0 term_var) (fvar n term_var))) T)
                       ::(n, T_nat)::Γ))
    && (n ?∉ (fv_context Γ)) && (y ?∉ (fv_context Γ)) && (p ?∉ (fv_context Γ))
    && (n ?∉ (fv T)) && (y ?∉ (fv T)) && (p ?∉ (fv T))
    && (n ?∉ (fv ts)) && (y ?∉ (fv ts)) && (p ?∉ (fv ts))
    && (n ?∉ Θ) && (y ?∉ Θ) && (p ?∉ Θ)
    && (NoDupb (n::y::p::nil)) && (wfb (erase_term ts) 1) && (wfb T 1)
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

  (* Fold rules *)
  | N (TJ J_Unfold_z Θ _ (tunfold t) T0)
      (( N ((EJ I1 _ Same n zero) as j1) _ as d1)
         ::(N ((TJ I2 _ Same _ (T_rec _ _ Ts)) as j2) _ as d2)::nil) =>
    (j1 ?= (EJ I1 Θ Same n zero)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t (T_rec n T0 Ts))) && (is_valid d2 Γ)
    && (wfb T0 0) && (wfb Ts 0) && (twfb T0 0) && (twfb Ts 1)

  | N (TJ J_Unfold_s Θ _ (tunfold t) T)
      (( N ((EJ I1 _ Same t' ttrue) as j1) _ as d1)
         ::(N ((TJ I2 _ Same _ (T_rec n T0 Ts)) as j2) _ as d2)::nil) =>
    (j1 ?= (EJ I1 Θ Same (spositive n) ttrue)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ Same t (T_rec n T0 Ts))) && (is_valid d2 Γ)
    && (wfb T0 0) && (wfb Ts 0) && (twfb T0 0) && (twfb Ts 1) && (wfb n 0)
    && (tree_eq T (topen 0 Ts (T_rec (tpred n) T0 Ts)))
    && ((fv n) ?⊂ (support Γ)) && ((fv T0) ?⊂ (support Γ)) && ((fv Ts) ?⊂ (support Γ))
    && (is_annotated_termb n) && (is_annotated_typeb T0) && (is_annotated_typeb Ts)

  | N (TJ J_Unfold_in Θ _ (tunfold_in t1 t2) T)
      (( N ((TJ I1 _ _ _ (T_rec n T0 Ts)) as j1) _ as d1)
         :: (N ((TJ I2 _ (Append ((p2,_)::(p1,_)::(y,_)::nil)) _ _ ) as j2) _ as d2)
         :: (N ((TJ I3 _ _ _ _) as j3) _ as d3) :: nil) =>
    let T1 := (T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) in
    let t2y := (open 0 t2 (fvar y term_var)) in
    let fv_t1 := (fv t1) in let fv_t2 := (fv t2) in
    let fv_n  := (fv n)  in let fv_T0 := (fv T0) in
    let fv_Ts := (fv Ts) in let fv_T  := (fv T)  in
    let fv_Γ  := (fv_context Γ) in
    let support_Γ := (support Γ) in
    (j1 ?= (TJ I1 Θ Same t1 (T_rec n T0 Ts))) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ (Append ((p2, T_equiv n zero)::(p1, T1)::(y, T0)::nil)) t2y T))
    && (is_valid d2 ((p2, T_equiv n zero)::(p1, T1)::(y, T0)::Γ))
    && (j3 ?= (TJ I3 Θ (Append ((p1, T1)::(y, (topen 0 Ts (T_rec (tpred n) T0 Ts)))::nil)) t2y T))
    && (is_valid d3 ((p1, T1)::(y, (topen 0 Ts (T_rec (tpred n) T0 Ts)))::Γ))
    && (fv_t1 ?⊂ support_Γ) && (fv_t2 ?⊂ support_Γ) && (fv_n ?⊂ support_Γ)
    && (fv_T0 ?⊂ support_Γ) && (fv_Ts ?⊂ support_Γ)
    && (wfb n 0) && (wfb T 0) && (wfb T0 0) && (wfb Ts 0)
    && (wfb t1 0) && (wfb (erase_term t2) 0) && (twfb T0 0) && (twfb Ts 1)
    && (is_annotated_termb n) && (is_annotated_termb t2) && (is_annotated_typeb T0) && (is_annotated_typeb Ts)
    && (p1 ?∉ Θ) && (p1 ?∉ fv_Γ) && (p1 ?∉ fv_t1) && (p1 ?∉ fv_t2)
    && (p1 ?∉ fv_n) && (p1 ?∉ fv_T0) && (p1 ?∉ fv_Ts) && (p1 ?∉ fv_T)
    && (p2 ?∉ Θ) && (p2 ?∉ fv_Γ) && (p2 ?∉ fv_t1) && (p2 ?∉ fv_t2)
    && (p2 ?∉ fv_n) && (p2 ?∉ fv_T0) && (p2 ?∉ fv_Ts) && (p2 ?∉ fv_T)
    && (y ?∉ Θ) && (y ?∉ fv_Γ) && (y ?∉ fv_t1) && (y ?∉ fv_t2)
    && (y ?∉ fv_n) && (y ?∉ fv_T0) && (y ?∉ fv_Ts) && (y ?∉ fv_T)
    && NoDupb (p1::p2::y::nil)

  | N (TJ J_Unfold_pos_in Θ _ (tunfold_pos_in t1 t2) T)
      (( N ((TJ I1 _ _ _ (T_rec n T0 Ts)) as j1 ) _ as d1)
         :: (N ((EJ I2 _ _ _ _) as j2) _ as d2)
         :: (N ((TJ I3 _ (Append ((p1, _)::(y,_)::nil)) _ _) as j3) _ as d3) :: nil) =>
    let T1 := (T_equiv t1 (tfold (T_rec n T0 Ts) (fvar y term_var))) in
    let Ty := (topen 0 Ts (T_rec (tpred n) T0 Ts)) in
    let fv_t1 := (fv t1) in let fv_t2 := (fv t2) in
    let fv_n  := (fv n)  in let fv_T0 := (fv T0) in
    let fv_Ts := (fv Ts) in let fv_T  := (fv T)  in
    let fv_Γ  := (fv_context Γ) in
    let support_Γ := (support Γ) in
    (j1 ?= (TJ I1 Θ Same t1 (T_rec n T0 Ts))) && (is_valid d1 Γ)
    && (j2 ?= (EJ I2 Θ Same (binary_primitive Lt zero n) ttrue)) && (is_valid d2 Γ)
    && (j3 ?= (TJ I3 Θ (Append ((p1, T1)::(y, Ty)::nil)) (open 0 t2 (fvar y term_var)) T))
    && (is_valid d3 ((p1,T1)::(y,Ty)::Γ))
    && (fv_t1 ?⊂ support_Γ) && (fv_t2 ?⊂ support_Γ) && (fv_n ?⊂ support_Γ)
    && (fv_T0 ?⊂ support_Γ) && (fv_Ts ?⊂ support_Γ)
    && (wfb n 0) && (wfb T 0) && (wfb T0 0) && (wfb Ts 0)
    && (wfb t1 0) && (wfb (erase_term t2) 0) && (twfb T0 0) && (twfb Ts 1)
    && (is_annotated_termb n) && (is_annotated_termb t2) && (is_annotated_typeb T0) && (is_annotated_typeb Ts)
    && (p1 ?∉ Θ) && (p1 ?∉ fv_Γ) && (p1 ?∉ fv_t1) && (p1 ?∉ fv_t2)
    && (p1 ?∉ fv_n) && (p1 ?∉ fv_T0) && (p1 ?∉ fv_Ts) && (p1 ?∉ fv_T)
    && (y ?∉ Θ) && (y ?∉ fv_Γ) && (y ?∉ fv_t1) && (y ?∉ fv_t2)
    && (y ?∉ fv_n) && (y ?∉ fv_T0) && (y ?∉ fv_Ts) && (y ?∉ fv_T)
    && NoDupb (p1::y::nil)

  | N (TJ J_Fold Θ _ (tfold (T_rec n T0 Ts) t) T)
      (( N ((TJ I1 _ _ _ _) as j1) _ as d1)
         :: (N ((TJ I2 _ (Append [(p, _)]) _ _) as j2) _ as d2)
         :: (N ((TJ I3 _ (Append [(_,_);(pn,_)]) _ _) as j3) _ as d3)::nil) =>
    let fv_n  := (fv n)  in let fv_T0 := (fv T0) in
    let fv_Ts := (fv Ts) in let fv_t  := (fv t) in
    let fv_Γ  := (fv_context Γ) in
    let support_Γ := (support Γ) in
    (j1 ?= (TJ I1 Θ Same n T_nat)) && (is_valid d1 Γ)
    && (j2 ?= (TJ I2 Θ (Append [(p, T_equiv n zero)]) t T0)) && (is_valid d2 ((p, T_equiv n zero)::Γ))
    && (j3 ?= (TJ I3 Θ (Append [(p, T_equiv n (succ (fvar pn term_var))); (pn, T_nat)]) t (topen 0 Ts (T_rec (fvar pn term_var) T0 Ts))))
    && (is_valid d3 ((p, T_equiv n (succ (fvar pn term_var)))::(pn, T_nat)::Γ))
    && (tree_eq T (T_rec n T0 Ts))
    && (is_annotated_termb n) && (is_annotated_typeb T0) && (is_annotated_typeb Ts)
    && (fv_n ?⊂ support_Γ) && (fv_T0 ?⊂ support_Γ) && (fv_Ts ?⊂ support_Γ)
    && (wfb n 0) && (twfb n 0) && (wfb T0 0) && (twfb T0 0)
    && (wfb Ts 0) && (twfb Ts 1) && (p ?<> pn)
    && (p ?∉ Θ) && (p ?∉ fv_Γ) && (p ?∉ fv_n) && (p ?∉ fv_T0) && (p ?∉ fv_Ts) && (p ?∉ fv_t)
    && (pn ?∉ Θ) && (pn ?∉ fv_Γ) && (pn ?∉ fv_n) && (pn ?∉ fv_T0) && (pn ?∉ fv_Ts) && (pn ?∉ fv_t)

  | N (TJ J_Fold2 Θ _ t (T_rec n1 T0 Ts))
      (( N ((TJ I1 _ _ _ T2) as j1) _ as d1)
         :: (N ((EJ I2 _ _ _ n2) as j2) _ as d2) :: nil) =>
    (j1 ?= (TJ I1 Θ Same t T2)) && (is_valid d1 Γ)
    && (j2 ?= (EJ I2 Θ Same n1 n2)) && (is_valid d2 Γ)
    && (tree_eq (drop_refinement T2) (T_rec n2 T0 Ts))

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
    match refinementUnfoldInContext Γ Γ' with
    | Some (x, p, ty, P) => (
        (p ?∉ fv t) && (p ?∉ fv T) && (p ?∉ fv P) && (p ?∉ fv ty) && (p ?∉ fv_context Γ)
        && (x ?<> p) && (x ?∉ fv ty) && (x ?∉ fv P)
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



(* Helpers to debug invalid derivations *)
Definition extract_name dv := match dv with
                              | N (TJ  n _ _ _ _) _ => (inl n)
                              | N (EJ  n _ _ _ _) _ => (inr (inl n))
                              | N (StJ n _ _ _ _) _=> (inr (inr n)) end.


Fixpoint split_goals (dv:derivation) Γ1 :=
  let Γ0 := match dv with
            | N (TJ  n _ Same _ _) _
            | N (EJ  n _ Same _ _) _
            | N (StJ n _ Same _ _) _ => Γ1
            | N (TJ  n _ (Append l) _ _) _
            | N (EJ  n _ (Append l) _ _) _
            | N (StJ n _ (Append l) _ _) _ => l++Γ1
            | N (TJ  n _ (New Γ2) _ _) _
            | N (EJ  n _ (New Γ2) _ _) _
            | N (StJ n _ (New Γ2) _ _) _ => Γ2 end in
  N ((is_valid dv Γ0), (extract_name dv), Γ0 ) (
      match dv with
      | N J nil => nil
      | N J (d1::nil) => (split_goals d1 Γ0)::nil
      | N J (d1::d2::nil) => (split_goals d1 Γ0)::(split_goals d2 Γ0)::nil
      | N J (d1::d2::d3::nil) => (split_goals d1 Γ0)::(split_goals d2 Γ0)::(split_goals d3 Γ0)::nil
      | _ => nil end
     ).
