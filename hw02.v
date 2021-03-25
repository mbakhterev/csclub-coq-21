From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrnat.
From mathcomp Require Import ssrbool eqtype ssrfun seq.

Unset Printing Notations.
Set Printing Notations.

(** * Arithmetic expression language *)


(** NOTE: If you don't need this homework graded for you university,
          please, do _not_ submit it through the CS club website. *)

(** NOTE: In a later homework we are going to prove some properties of the
functions this homework asks you to implement. Please keep your code so you can
reuse it later. *)


(** Define is a simple language of arithmetic expressions consisting of
constants (natural numbers) and arbitrarily nested additions, subtractions and
multiplications *)

Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

(** Let us define a special notation for our language.
    We reuse the standard arithmetic notations here, but only inside
    double square brackets (see examples below) *)

(* This means we declare `expr` as an identifier referring to a 'notation
entry' *)

Declare Custom Entry expr.

(* And we let the parser know `expr` is associated with double brackets, so
inside double brackets the parser will use notations associated with custom
`expr` entries *)

Notation "'[[' e ']]'" := e (e custom expr at level 0).

(* Numerals can be used without wrapping those in the `Const` constructor *)

Notation "x" :=
  (Const x)
    (in custom expr at level 0, x bigint).

Notation "( x )" := x (in custom expr, x at level 2).

Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).

(* Define notations for subtraction and multiplication.
   Hint: lower level means higher priority.
   Your notations should start with `in custom expr` as above. *)

Notation "x - y" := (Minus x y) (in custom expr at level 2, left associativity).

Notation "x * y" := (Mult x y) (in custom expr at level 1, left associativity).

(** Here is how we write Plus (Const 0) (Plus (Const 1) (Const 2)) *)

Check [[
          0 + (1 + 2)
      ]].

Check [[ 0 + 1 - 2 * 3 ]].

(** And this is Plus (Plus (Const 0) (Const 1)) (Const 2) *)

Check [[
          (0 + 1) + 2
      ]].

(* Make sure the following are parsed as expected.
   What query can you use to do that? *)

Check erefl: 2 = 2.

Check erefl: [[ ((0 + 1) + 2) + 3 ]] = Plus (Plus (Plus (Const 0) (Const 1)) (Const 2)) (Const 3).

Check erefl: [[ 0 + (1 + (2 + 3)) ]] = Plus (Const 0) (Plus (Const 1) (Plus (Const 2) (Const 3))).

Check erefl: [[ 0 * 1 + 2 ]] = Plus (Mult (Const 0) (Const 1)) (Const 2).

Check erefl: [[ 0 + 1 * 2 ]] = Plus (Const 0) (Mult (Const 1) (Const 2)).

Check erefl: [[ (0 + 1) * 2 ]] = Mult (Plus (Const 0) (Const 1)) (Const 2).

(** Write an evaluator for the expression language which fixes its semantics.
Basically, the semantics of the expression language should be the same as
the corresponding Coq functions `addn`, `subn`, `muln`. *)

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus n m => addn (eval n) (eval m)
  | Minus n m => subn (eval n) (eval m)
  | Mult n m => muln (eval n) (eval m)
  end.

(** Some unit tests *)

(** We haven't discussed in depth what `erefl` means yet.
    But for now, let's just assume if the following lines
    typecheck then the equalities below hold *)

Check erefl : eval [[ 0 - 4 ]] = 0.
Check erefl : eval [[ 0 + (2 - 1) ]] = 1.
Check erefl : eval [[ (0 + 1) + 2 ]] = 3.
Check erefl : eval [[ 2 + 2 * 2 ]] = 6.
Check erefl : eval [[ (2 + 2) * 2 ]] = 8.
Check erefl : eval [[ 10 * 10 * 10 * 10 - 1 ]] = 9999.
Check erefl : eval [[ 10 * 10 * 10 - 1 ]] = 999.

(** * Compiling arithmetic expressions to a stack language *)

(** Here is a "low-level" stack language which can serve as the target language
for a compiler from the arithmetic expression language above.
See, for instance, this page for more detail:
https://en.wikipedia.org/wiki/Stack-oriented_programming.

A program in this language is a list of instructions, each of which manipulates
a stack of natural numbers. There are instructions for pushing constants onto
the stack and for adding/subtracting/muliplying the top two elements of the
stack, popping them off the stack, and pushing the result onto the stack. *)

Inductive instr := Push (n : nat) | Add | Sub | Mul.

(*
Feel free to define your own notations for the stack operations
to make it easier writing unit tests
For example, this is one possible way to start:

Notation " << n >> " := (Push n) (at level 0, n constr).
*)


(* Feel free to either define your own datatype to represent lists or reuse the
`seq` datatype provided by Mathcomp (this is why this file imports the `seq`
module at the beginning). Btw, `seq` is just a notation for the standard `list`
datatype.

    Inductive list (A : Type) : Type :=
      | nil
      | cons of A & list A.

You can construct new lists (sequences) like so:
  - [::]           --  notation for the `nil` constructor;
  - x :: xs        --  notation for the `cons` constructor;
  - [:: 1; 2; 3]   --  notation for a sequence of three elements 1, 2 and 3.

Using `seq`, we can define the type of programs as follows:

    Definition prog := seq instr.

And the type of stacks like so:

    Definition stack := seq nat.
*)

Definition prog := seq instr.
Definition stack := seq nat.

(** The [run] function is an interpreter for the stack language. It takes a
 program (list of instructions) and the current stack, and processes the program
 instruction-by-instruction, returning the final stack. *)

Reset run.

Fixpoint run (p : prog) (s : stack) : stack :=
  match p, s with
  | [::], _ => s
  | (Push n) :: r, _ => run r (n :: s)
  | Add :: r, n :: m :: ns => run r ((addn m n) :: ns)
  | Sub :: r, n :: m :: ns => run r ((subn m n) :: ns)
  | Mul :: r, n :: m :: ns => run r ((muln m n) :: ns)
  | _, _ => [::]
  end.

(** Unit tests: *)

Check erefl :
  run [:: Push 0; Push 1; Push 2; Add; Push 3; Push 4; Mul; Push 10; Push 6; Sub] [::]
    = rev [:: 0; 3; 12; 4].

Check erefl : run [:: Push 1; Push 2; Push 3; Push 4; Push 5; Push 6; Mul; Mul; Mul; Mul; Mul] [::] = [:: 720].

(** Now, implement a compiler from "high-level" expressions to "low-level" stack
programs and do some unit tests. *)

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus n m => (compile n) ++ (compile m) ++ [:: Add]
  | Minus n m => (compile n) ++ (compile m) ++ [:: Sub]
  | Mult n m => (compile n) ++ (compile m) ++ [:: Mul]
  end.

(** Do some unit tests *)

Compute compile [[ 10 - 20 ]].

Check erefl : compile [[ 20 - 10 ]] = [:: Push 20; Push 10; Sub ].

Compute eval [[ 10 + 20 * 30 - 50 ]].

Check erefl : run (compile [[ 10 + 20 * 30 - 50 ]]) [::] = [:: eval [[ 10 + 20 * 30 - 50 ]]].

(* Some ideas for unit tests:
  - check that `run (compile e) [::] = [:: eval e]`, where `e` is an arbitrary expression;
  - check that `compile` is an injective function
*)

(** Optional exercise: decompiler *)

(** Implement a decompiler turning a stack program into the corresponding
expression *)
(* Hint: you might want to introduce a recursive helper function `decompile'` to
 reuse it for `decompile`. *)

Reset decomp.

Fixpoint decomp (s : seq expr) (p : prog) : option expr :=
  match p, s with
  | (Push n) :: r, _ => decomp (Const n :: s) r
  | Add :: r, m :: n :: t => decomp (Plus n m :: t) r
  | Add :: _, _ => None
  | Mul :: r, m :: n :: t => decomp (Mult n m :: t) r
  | Mul :: _, _ => None
  | Sub :: r, m :: n :: t => decomp (Minus n m :: t) r
  | Sub :: _, _ => None
  | [::], [:: r] => Some r
  | [::], _ => None
  end.

Definition decompile (p : prog) : option expr := decomp [::] p.

(** Unit tests *)

Compute decompile [:: Push 10; Push 1; Push 0; Sub; Mul].

Check erefl: decompile [:: Push 10; Push 1; Push 0; Sub; Mul ] = Some [[ 10 * (1 - 0) ]].
Check erefl: decompile [:: Push 10; Push 20; Push 30; Mul; Add; Push 50; Sub] = Some [[ 10 + 20 * 30 - 50 ]].
Check erefl: decompile [:: Push 10; Push 20; Push 30; Mul] = None.

(* Some ideas for unit tests:
  - check that `decompile (compile e) = Some e`, where `e` is an arbitrary expression
*)

Check erefl: decompile (compile [[ 10 + 20 * 30 - 50 ]]) = Some [[ 10 + 20 * 30 - 50 ]].

Check erefl: decompile (compile [[ 10 * 20 * (40 - 1) * 50 + 40 * 30 - 7 ]])
  = Some [[ 10 * 20 * (40 - 1) * 50 + 40 * 30 - 7 ]].
