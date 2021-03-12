From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool :=
  match b with
  | true => true
  | false => c
  end.

Compute orb true false.
Compute orb true true.
Compute orb false true.

Compute orb false false.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool :=
  match b with
  | false => c
  | true => negb c
  end.

Compute addb true false.
Compute addb false true.

Compute addb false false.
Compute addb true true.

(** Just for fun *)

Definition idb (b : bool) : bool := b.

Definition addbf (b : bool) : bool -> bool :=
  match b with
  | false => idb
  | true => negb
  end.

Compute addbf true false.
Compute addbf false true.

Compute addbf false false.
Compute addbf true true.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool := negb (addb b c).

Compute eqb true false.
Compute eqb false true.

Compute eqb false false.
Compute eqb true true.

(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.

(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

(* Проще всего определить dec2(n) = pred(pred(n)) для рекомендованной на лекции
реализации pred. Это автоматически снимет вопрос и о значениях для dec2(0)
и dec2(1). Определение pred понадобится ещё и для subn  *)

Definition predn (n : nat) : nat :=
  match n with
  | O => O
  | S k => k
  end.

Definition dec2 (n : nat) : nat := predn (predn n).

Definition one   : nat := (S zero).
Definition two   : nat := (S one).
Definition three : nat := (S two).
Definition four  : nat := (S three).
Definition five  : nat := (S four).
Definition six   : nat := (S five).
Definition seven : nat := (S six).
Definition eight : nat := (S seven).
Definition nine  : nat := (S eight).
Definition ten   : nat := (S nine).

Compute dec2 O.
Compute dec2 (S (S (S (S O)))).
Compute dec2 (S (S (S (S (S (S (S (S O)))))))).
Compute dec2 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))).

(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) {struct n} : nat :=
  match n with
  | O => m
  | S k => subn (predn m) k
  end.

Compute subn (S (S (S (S O)))) O.
Compute subn (S (S (S (S O)))) (S (S (S (S (S (S (S (S O)))))))).
Compute subn (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))) (S (S (S (S (S (S (S (S O)))))))).

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (m n : nat) { struct m } : nat :=
  match m with
  | O => n
  | S k => S (addn k n)
  end.

Fixpoint muln (m n : nat) { struct n } : nat :=
  match n with
  | O => O
  | S k => addn m (muln m k)
  end.

Compute muln three two.
Compute muln ten zero.
Compute muln five one.
Compute muln three six.

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) { struct n } : bool :=
  match m, n with
  | O, O => true
  | S k, S l => eqn k l
  | _, _ => false
  end.

Compute eqn one two.
Compute eqn (muln ten two) (muln four five).
Compute eqn (muln nine nine) (subn (muln ten nine) nine).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` return `true` if and only if `m` is less
to `n`. Your solution must not use recursion but you may reuse any of the
functions you defined in this module so far. *)

Definition leq (m n : nat) : bool := eqn O (subn m n).

Compute leq two three.
Compute leq (muln ten ten) (muln (muln five two) ten).

Compute leq three two.
Compute leq (muln ten ten) (muln nine nine).

Compute leq zero zero.
Compute leq zero ten.


(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

Fixpoint less (m n : nat) {struct m} : bool :=
  match m, n with
  | O, S k => true
  | S k, O => false
  | O, O => false
  | S k, S l => less k l
  end.

Compute less two three.
Compute less three three.
Compute less four three.

Fixpoint divn_loop (c m n : nat) {struct c} : nat :=
  match c with
  | O => O
  | S k => 
    match leq (muln c n) m with
    | true => c
    | false => divn_loop k m n
    end
  end.

Definition divn (m n : nat) : nat :=
  match n with
  | O => O
  | S k => divn_loop m m n
  end.

Compute eqn (divn (muln ten ten) ten) ten.
Compute eqn O (divn O O).
Compute eqn (divn (muln nine nine) seven) (addn one ten).
Compute eqn (divn (muln six seven) six) seven.
Compute eqn O (divn ten zero).
Compute eqn O (divn (muln nine nine) (muln ten ten)).

End My.
