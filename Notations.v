Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.

Open Scope list.


(* Untyped embedded language *)
Module UnTyped.
  Declare Custom Entry expr.

  (* Entry point *)
  Notation "'⤳' t" := (fun (fv_id:nat) => t) (at level 100).
  Notation "[| x |]" := (x 0) (x custom expr).
  Notation "( x )" := (fun (fv_id:nat) => (x fv_id)) (in custom expr, x custom expr).
  Notation "x" := (⤳ x) (in custom expr at level 0, x ident).

  (* Variables (nameless) - not used in practice *)
  Notation "'ft{' v '}'" := (⤳ (fvar v term_var)) (in custom expr, v constr).
  Notation "'lt{' v '}'" := (⤳ (lvar v term_var)) (in custom expr, v constr).
  Notation "'fT{' v '}'" := (⤳ (fvar v type_var)) (in custom expr, v constr).
  Notation "'lT{' v '}'" := (⤳ (lvar v type_var)) (in custom expr, v constr).

  (* Base terms *)
  Notation "'0'" := (⤳ zero) (in custom expr).
  Notation "'1'" := (⤳ (succ zero)) (in custom expr).
  Notation "'2'" := (⤳ (succ (succ zero))) (in custom expr).
  Notation "'3'" := (⤳ (succ (succ (succ zero)))) (in custom expr).
  Notation "'4'" := (⤳ (succ (succ (succ (succ zero))))) (in custom expr).
  Notation "'5'" := (⤳ (succ (succ (succ (succ (succ zero)))))) (in custom expr).
  Notation "'6'" := (⤳ (succ (succ (succ (succ (succ (succ zero))))))) (in custom expr).
  Notation "'7'" := (⤳ (succ (succ (succ (succ (succ (succ (succ zero)))))))) (in custom expr).
  Notation "'8'" := (⤳ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))) (in custom expr).
  Notation "'9'" := (⤳ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))) (in custom expr).

  Notation "'()'" := (⤳ uu) (in custom expr).
  Notation "'t_true'" := (⤳ttrue) (in custom expr).
  Notation "'t_false'" := (⤳tfalse) (in custom expr).
  Notation "'error'" := (notype_err) (in custom expr).
  Notation "'size' t " := (fun fv_id => (tsize (t fv_id))) (in custom expr at level 0,
                                                            t custom expr).
  (* Conditionnal *)
  Notation "'if' c 'then' t 'else' f" :=
    (fun fv_id => (ite (c fv_id) (t fv_id) (f fv_id)))
      (in custom expr at level 1, c custom expr, t custom expr, f custom expr).

  (* Pairs *)
  Notation "( t1 , t2 )" :=
    (fun (fv_id:nat) => (pp (t1 fv_id) (t2 fv_id)))
      (in custom expr, t1 custom expr, t2 custom expr).
  Notation "t '._1'" := (fun fv_id => (pi1 (t fv_id))) (in custom expr at level 80, t custom expr).
  Notation "t '._2'" := (fun fv_id => (pi2 (t fv_id))) (in custom expr at level 80, t custom expr).

  (* Needs Coq 8.11 to work
Definition pp_notation (p1 : nat -> tree) (p2 : nat -> tree) : (nat -> tree) :=
  fun (fv_id : nat) => pp (p1 fv_id) (p2 fv_id).
Notation "( t1 , .. , t2 , tn )" :=
  (pp_notation  t1 .. (pp_notation t2 tn) ..)
    (in custom expr, t1  custom expr, t2 custom expr, tn custom expr, left associativity). *)

  (* Functions *)
  Notation "'fun' x  => t" := (* non-recursive *)
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (notype_lambda (close 0 (t (S fv_id)) fv_id))))
      (in custom expr at level 100, x ident, t custom expr).
  Notation "'def_rec' f x => t":= (* recursive *)
    (fun fv_id => (
         let f := (fvar fv_id term_var) in
         let x := (fvar (S fv_id) term_var) in
         (notype_tfix (close 0 (notype_lambda (close 0 (t (S (S fv_id))) (S fv_id))) fv_id) )))
      (in custom expr at level 100, f ident, x ident, t custom expr).
  Notation "'def_rec' f x y => t":= (* for convinience, recursive with 2 arguments *)
    (fun fv_id => (
         let f := (fvar fv_id term_var) in
         let x := (fvar (S fv_id) term_var) in
         let y := (fvar (S (S fv_id)) term_var) in
         (notype_tfix (close 0 (
                               notype_lambda (close 0 (notype_lambda (
                                                           close 0 (t (S(S(S fv_id))))
                                                                 (S (S fv_id)))) (S fv_id))) fv_id))))
      (in custom expr at level 100, f ident, x ident, y ident, t custom expr).
  Notation " t1 t2 " :=
    (fun fv_id => (app (t1 fv_id) (t2 fv_id)))
      (in custom expr at level 50, left associativity,
          t1 custom expr,
          t2 custom expr).

  (* Naturals *)
  Notation "'s' t" := (fun fv_id => (succ (t fv_id))) (in custom expr at level 2, t custom expr).
  Notation "'match' t 'with' '|' '0' => t1 '|' 's' x => t2 'end'" :=
    (fun (fv_id:nat) => (
         tmatch (t fv_id)
                (t1 fv_id)
                (let x := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id))))
      (in custom expr at level 190, t custom expr, t1 custom expr, t2 custom expr, x ident).

  (* Let expression *)
  Notation "'let' x := t1 'in' t2" :=
    (fun (fv_id : nat) => (
         notype_tlet (t1 fv_id)
                     (let x := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id) )))
      (in custom expr at level 190, t1 custom expr, t2 custom expr, x ident).

  (* Sum *)
  Notation "'right' t " :=
    (fun fv_id => tright (t fv_id))
      (in custom expr at level 180, right associativity, t custom expr).
  Notation "'left' t " :=
    (fun fv_id => tleft (t fv_id))
      (in custom expr at level 180, right associativity, t custom expr).
  Notation "'match' t 'with' '|' 'left' l => t1 '|' 'right' r => t2 'end'" :=
    (fun (fv_id:nat) => (
         sum_match (t fv_id)
                (let l  := (fvar fv_id term_var) in (close 0 (t1 (S fv_id)) fv_id))
                (let r := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id))))
      (in custom expr at level 190, t custom expr, t1 custom expr, t2 custom expr, l ident, r ident).

End UnTyped.


Module Typed.
  Import UnTyped.
  Declare Custom Entry type.

  (* Additionnal entry points *)
  Notation "[|| x ||]" := (x 0) (x custom type).
  Notation "( x )" := (fun (fv_id:nat) => (x fv_id)) (in custom type, x custom type).
  Notation "x" := (⤳ x) (in custom type at level 0, x ident).

  (* Base Types *)
  Notation "'Nat'" := (⤳ T_nat) (in custom type).
  Notation "'Unit'" := (⤳ T_unit) (in custom type).
  Notation "'Bool'" := (⤳ T_bool) (in custom type).
  Notation "'⊤'" := (⤳ T_top) (in custom type).
  Notation "'⊥'" := (⤳ T_bot) (in custom type).

  (* Additionnal base terms *)
  Notation "'error' [ T ] " := (fun fv_id => err (T fv_id)) (in custom expr, T custom type).

  (* Equivalence *)
  Notation "[ t1 ≡ t2 ]" :=
    (fun fv_id => (T_equiv (t1 fv_id) (t2 fv_id)))
      (in custom type at level 200,
          t1 custom expr,
          t2 custom expr).

  (* Arrow type *)
  Notation "τ1 -> τ2" := (fun fv_id => (T_arrow (τ1 fv_id) (τ2 fv_id))) (in custom type at level 90, right associativity, τ1 custom type, τ2 custom type).
  Notation "x : τ1 -> τ2" :=
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (T_arrow (τ1 fv_id) (close 0 (τ2 (S fv_id)) fv_id ))))
      (in custom type, τ1 custom type at level 85, τ2 custom type at next level, x ident).

  (* Prod type *)
  Notation "τ1 * τ2" :=(fun fv_id => (T_prod (τ1 fv_id) (τ2 fv_id))) (in custom type at level 90, right associativity, τ1 custom type, τ2 custom type).
  Notation "x : τ1 * τ2" :=
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (T_prod (τ1 fv_id) (close 0 (τ2 (S fv_id)) fv_id ))))
      (in custom type, τ1 custom type at level 85, τ2 custom type at level 100, x ident).

  (* Sum type *)
  Notation "τ1 + τ2" :=
    (fun fv_id => (T_sum (τ1 fv_id) (τ2 fv_id))) (in custom type at level 95, τ1 custom type, τ2 custom type).
  Notation "x : τ1 + τ2" :=
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (T_sum (τ1 fv_id) (close 0 (τ2 (S fv_id)) fv_id ))))
      (in custom type, τ1 custom type at level 85, τ2 custom type at level 100, x ident).

  (* Refinement types *)
  Notation "{ x : τ1 | t }" :=
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (T_refine (τ1 fv_id) (close 0 (t (S fv_id)) fv_id))))
      (in custom type at level 200, τ1 custom type, t custom expr, x ident).
  Notation "{{ x : τ1 | τ2 }}" :=
    (fun fv_id => (
         let x := (fvar fv_id term_var) in
         (T_type_refine (τ1 fv_id) (close 0 (τ2 (S fv_id)) fv_id))))
      (in custom type at level 200, τ1 custom type, τ2 custom type, x ident).

  (* Union type *)
  Notation "τ1 ∪ τ2" :=
    (fun fv_id => (T_union (τ1 fv_id) (τ2 fv_id))) (in custom type at level 190, right associativity, τ1 custom type, τ2 custom type).

  (* Intersection type *)
  Notation "τ1 ∩ τ2" :=
    (fun fv_id => (T_intersection (τ1 fv_id) (τ2 fv_id))) (in custom type at level 170, right associativity, τ1 custom type, τ2 custom type).
(*
Notation "'forall' x : τ1 . τ2" :=
  (fun fv_id => (
       let x := (fvar fv_id term_var) in
       (T_intersection (τ1 fv_id) (close 0 (τ2 (S fv_id)) fv_id))))
    (in custom type at level 190, right associativity, τ1 custom type, τ2 custom type).
Notation "'forall' α : 'Type' . τ1 ":=
  (fun fv_id => (
       let α := (fvar fv_id type_var) in
       (T_abs (tclose 0 (τ1 (S fv_id)) fv_id))))
    (in custom type at level 190, right associativity, τ1 custom type, α ident). *)

End Typed.

Module Tests.
  Import UnTyped.
  Import Typed.

  Example base_types :
    ([|| Nat ||], [|| Unit ||], [|| Bool ||], [|| ⊤ ||], [|| ⊥ ||]) =
    (T_nat, T_unit, T_bool, T_top, T_bot).
  Proof. reflexivity. Qed.

  Example arrow_type1 :
    [|| (Nat -> Bool) -> Unit -> ⊤ ||] =
    T_arrow (T_arrow T_nat T_bool) (T_arrow T_unit T_top).
  Proof. reflexivity. Qed.

  Example arrow_type2 :
    [|| x : Nat -> y : Nat -> [x ≡ y] ||] =
    T_arrow T_nat (T_arrow T_nat (T_equiv (lvar 1 term_var) (lvar 0 term_var))).
  Proof. reflexivity. Qed.

  Example prod_type1 : [|| Nat * Bool ||] = T_prod T_nat T_bool.
  Proof. simpl. reflexivity. Qed.

  Example prod_type2 : [|| x : Nat * Bool * Unit ||] = T_prod T_nat (T_prod T_bool T_unit).
  Proof. reflexivity. Qed.

  Example sum_type1 : [|| Bool -> Nat + Unit ||] = T_sum (T_arrow T_bool T_nat) T_unit.
  Proof. reflexivity. Qed.

  Example sum_type2 :
    [|| Nat + x : Bool -> y : Nat * [x ≡ y] + Nat ||] =
    T_sum T_nat (T_arrow T_bool (T_prod T_nat
                                        (T_sum (T_equiv (lvar 1 term_var) (lvar 0 term_var)) T_nat))).
  Proof. reflexivity. Qed.

  Example refine_type1 : [|| { x : Bool | x } ||] = T_refine T_bool (lvar 0 term_var).
  Proof. reflexivity. Qed.

  Example refine_by_type1 : [|| {{ x : Bool | [x ≡ x] }} ||] = (T_type_refine T_bool (T_equiv (lvar 0 term_var) (lvar 0 term_var))).
  Proof. reflexivity. Qed.

  Example union_type1 : [|| Nat ∩ Bool ∪ Nat ||] = T_union (T_intersection T_nat T_bool) T_nat.
  Proof. reflexivity. Qed.

End Tests.
