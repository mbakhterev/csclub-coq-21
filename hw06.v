
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.


(*
Use your solution of Homework 2 and prove correctness of your implementations.
I'm repeating some (partial) definitions here just to make sure
the lemma statements make sense.
*)

(* A language of arithmetic expression *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus n m => addn (eval n) (eval m)
  | Minus n m => subn (eval n) (eval m)
  | Mult n m => muln (eval n) (eval m)
  end.

(* Stack language *)
Inductive instr := Push (n : nat) | Add | Sub | Mul.

Definition prog := seq instr.
Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  match p, s  with
  | [::], t => s
  | Push n :: r, t => run r (n :: t)
  | Add :: r, n :: m :: t => run r ((addn m n) :: t)
  | Sub :: r, n :: m :: t => run r ((subn m n) :: t)
  | Mul :: r, n :: m :: t => run r ((muln m n) :: t)
  | _, _ => [::]                               
  end.

(* Compiler from the expression language to the stack language *)
                                                         
Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus m n => compile m ++ compile n ++ [:: Add]
  | Minus m n => compile m ++ compile n ++ [:: Sub]
  | Mult m n => compile m ++ compile n ++ [:: Mul]
  end.

Arguments compile e : simpl nomatch.

Definition E := (Plus (Const 10) (Mult (Const 11) (Const 3))).
                  
Check erefl : run (compile E) [::] = [:: eval E].
Compute (compile E).

(** Here is a correctness theorem for the compiler: it preserves the
meaning of programs. By "meaning", in this case, we just mean the final
answer computed by the program. For a high-level expression, the answer
is the result of calling [eval]. For stack programs, the answer
is whatever [run] leaves on the top of the stack. The correctness
theorem states that these answers are the same for an expression and
the corresponding compiled program. *)

Lemma run_order (e : expr) (p : prog) (s : stack) :
  run (compile e ++ p) s = run p (eval e :: s).
Proof.
  move : e p s.
  elim.
  - move => //.
  - move => ex hx ey hy p s.
    rewrite /= -!catA.
    rewrite (hx (compile ey ++ [:: Add] ++ p) s).
    rewrite (hy ([:: Add] ++ p) (eval ex :: s)).
    by rewrite /=.
  - move => ex hx ey hy p s.
    rewrite /= -!catA.
    rewrite (hx (compile ey ++ [:: Sub] ++ p) s).
    rewrite (hy ([:: Sub] ++ p) (eval ex :: s)).
    by rewrite /=.
  - move => ex hx ey hy p s.
    rewrite /= -!catA.
    rewrite (hx (compile ey ++ [:: Mul] ++ p) s).
    rewrite (hy ([:: Mul] ++ p) (eval ex :: s)).
    by rewrite /=.
Qed.

Theorem compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
  move : (run_order e [::] [::]).
  rewrite cats0.
  exact.
Qed.

(* ==== OPTIONAL part: decompiler ==== *)

Definition decompile (p : prog) : option expr :=
  replace_with_your_solution_here.

(** Prove [decompile] cancels [compile]. *)

Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof.
Admitted.

(* Prove the [compile] function is injective *)

Lemma compile_inj :
  injective compile.
Proof.
Admitted.

