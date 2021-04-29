From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

About reflect.
Print Bool.reflect.
Print erefl.
Print Logic.eq_refl.

Section CaseTacticForTypeFamilies.

(** * Exercise *)
(* CONSTRAINTS: do _not_ use `rewrite`, `->` or any lemmas to solve this exercise.
   Use _only_ the `case` tactic *)
  
Lemma sym T (a x y : T) :
  x = y -> y = x.
Proof.
  move => P.
  case E : y / P.
  Show Proof.
  exact erefl.
Qed.

(* Hint: use the `case: ... / ...` variant *)

(** * Exercise *)
(* Figure out what `alt_spec` means and prove the lemma *)

Locate "alt_spec".
Print alt_spec.

Lemma altP P b :
  reflect P b -> alt_spec P b b.
Proof.
  move => Q.
  case E : b / Q.
  - by constructor.
  - by constructor.
Qed.
  
(* Hint: use the `case: ... / ...` variant *)

End CaseTacticForTypeFamilies.

Section MultiRules.

(** * Exercise: A spec for boolean equality *)
  
Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Type :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.

(* Print eq_xor_neq.
Print altP.
Print eqP.
Search (?x = ?y -> ?y = ?x).
Search (?x == ? x). *)

Search (?x != ?y -> _).
Locate "!=".

Search (?x == ?y -> _).

Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof.
  case : (altP eqP).
  - move => xy.
    set h1 := (esym xy).
    case eqP : _ / h1.
    rewrite eq_refl.
    constructor.
    by exact erefl.
  - move => h1.
    set h2 := @ifN_eq T bool y x (x != y) (x == y) h1.
    rewrite eq_sym.
    move : h2.
    case : (y == x).
    - move => h2.
      by set h3 := Bool.no_fixpoint_negb (x == y) h2.
    constructor.
    move : h1.
    by rewrite eq_sym.
Qed.
 
(** Hint: Use `case: (altP eqP)` to get the right assumptions.
          Also, try using `case: eqP` instead to see the difference. *)


(** * Exercise: use `eqVneq` to prove this lemma *)

Print eqVneq.

Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof.
  move : (eqVneq x w).
  move : (eqVneq y z).
  case.
  - move => yz.
    case.
    - by done.
    - by done.
  - done.
Qed.

Reset eqVneq_example.
Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof.
  move => h1 h2.
  split.
  - by rewrite eq_sym.
  - split.
    - by rewrite eq_sym.
    - by done.
Qed.
      
(** * Exercise *)

Locate "*".

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof.
  rewrite /is_true.
  case : a.
  case : b.
  - apply : ReflectT.
      by exact (conj erefl erefl).
  - apply : ReflectF.
      by case.
  - apply : ReflectF.
      by case.
Qed.
  
Arguments andX {a b}.

(** * Exercise: prove the following lemma using `andX` lemma. *)
(* CONSTRAINTS: you may only use `move` and `rewrite` to solve this;
     no `case` or `[]` or any other form of case-splitting is allowed!
     and no lemmas other than `andX` *)
Lemma andX_example a b :
  a && b -> b && a && a && b.
Proof.
  move/andX.
  rewrite /is_true.
  move => h1.
  rewrite h1.
  rewrite h1.
  exact erefl.
Qed.

(** Hint: `reflect`-lemmas may act like functions (implications) *)

End MultiRules.
