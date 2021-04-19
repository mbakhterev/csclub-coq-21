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

Print option.

Fixpoint decompile_rec (p : prog) (s : seq expr) {struct p} : option expr :=
  match p, s with
  | Push n :: r, t => decompile_rec r (Const n :: s)
  | Mul :: r, n :: m :: t => decompile_rec r (Mult m n :: t)
  | Sub :: r, n :: m :: t => decompile_rec r (Minus m n :: t)
  | Add :: r, n :: m :: t => decompile_rec r (Plus m n :: t)
  | [::], [:: e] => Some e
  | _, _ => None
  end.

Arguments decompile_rec p s : simpl nomatch.
  
Definition decompile (p : prog) : option expr := decompile_rec p [::].

(** Prove [decompile] cancels [compile]. *)

Lemma decompile_rec_compile (e : expr) (p : prog) (s : seq expr) :
  decompile_rec (compile e ++ p) s = decompile_rec p (e :: s).
Proof.
  move : e p s.
  elim.
  - by move => //.
  - move => em hm en hn p s.
    move => /=.
    rewrite -!catA.
    rewrite hm hn.
      by exact.
  - move => em hm en hn p s.
    move => /=.
    rewrite -!catA.
    rewrite hm hn.
      by exact.
  - move => em hm en hn p s.
    move => /=.
    rewrite -!catA.
    rewrite hm hn.
      by exact.
Qed.
  

Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof.
  move : (decompile_rec_compile e [::] [::]).
  rewrite /= cats0.
  done.
Qed.

(* Prove the [compile] function is injective *)

Definition decrec (p : prog) := decompile_rec p [::].

Lemma compile_inj :
  injective compile.
Proof.
  rewrite /injective.
  case => /=.
  - move => n e.
    move => h1.
    move : (congr1 decompile h1).
    rewrite decompile_compile /decompile /decompile_rec.
    by case.      
  - move => ex ey e.
    case : e.
    - move => n h1.
      move : (congr1 decrec h1).
      by rewrite /decrec !decompile_rec_compile /(compile (Const n)) //.
    - move => em en.
      rewrite /=.
      move => h1.
      move : (congr1 decrec h1).
      rewrite /decrec !decompile_rec_compile /=.
      case.
      move => exm eyn.
      set h2 := (proj2 (pair_equal_spec ex em ey en)) (conj exm eyn).
        by exact (congr1 (fun '(x, y) => Plus x y) h2).
    - move => em en.
      rewrite /=.
      move => h1.
      move : (congr1 decrec h1).
      rewrite /decrec !decompile_rec_compile /=.
      case.
        by exact.
    - move => em en.
      rewrite /=.
      move => h1.
      move : (congr1 decrec h1).
      rewrite /decrec !decompile_rec_compile /=.
      case.
        by exact.  
  - move => em en.
    rewrite /=.
    case.
    - move => n.
      rewrite /(compile (Const n)).
      move => h1.
      move : (congr1 decrec h1).
        by rewrite !/decrec !decompile_rec_compile //.
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
        by rewrite !/decrec !decompile_rec_compile //.
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
      rewrite !/decrec !decompile_rec_compile //.
      case.
      move => emn ene.
      set h2 := (proj2 (pair_equal_spec em n en e)) (conj emn ene).
        by exact (congr1 (fun '(x, y) => Minus x y) h2).
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
        by rewrite !/decrec !decompile_rec_compile //.

  - move => em en.
    rewrite /=.
    case.
    - move => n.
      rewrite /(compile (Const n)).
      move => h1.
      move : (congr1 decrec h1).
        by rewrite !/decrec !decompile_rec_compile //.
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
        by rewrite !/decrec !decompile_rec_compile //.
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
      by rewrite !/decrec !decompile_rec_compile //.
    - move => n.
      rewrite /=.
      move => e h1.
      move : (congr1 decrec h1).
      rewrite !/decrec !decompile_rec_compile //.
      case.
      move => emn ene.
      set h2 := (proj2 (pair_equal_spec em n en e)) (conj emn ene).
      by exact (congr1 (fun '(x, y) => Mult x y) h2).
Qed.
