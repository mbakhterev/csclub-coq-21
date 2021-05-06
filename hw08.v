From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.

(** * Exercise: finish the development we started at the last seminar *)

(** * Odd and even numbers *)

(** ** Part 1: Definitions *)

Section OddAndEven.

  
(** The goal of this exercise is to build a system of canonical structures
    so that the following statement about some properties of
    odd natural numbers can be proved with a couple of simple rewrites:

    Example test_odd (n : odd_nat) :
      ~~ (odd 6) && odd (n * 3).
    Proof. by rewrite oddP evenP. Qed.

    See the definitions of [odd_nat], [oddP], and [evenP] below.
    If you do everything the right way the example at the end of the section will work.
    In other words, the goal of this exercise is not to prove a statement,
    but rather make the given proof work.
    Please, DO NOT CHANGE the proof (I can assure you it works if the right canonical structures are given)
 *)


(** Let us define a structure defining the notion of odd numbers *)
Structure odd_nat := Odd {
  oval : nat;            (** [oval] is a natural number *)
  oprop : odd oval       (** [oprop] is the proof it is odd *)
}.

(** Example: [42 - 1] is an odd number *)

Definition o41 : odd_nat := @Odd 41 isT.

(** One issue here is that we cannot, for instance, add two odd naturals: *)
Fail Check o41 + o41.

(** Let's declare [oval] a coercion to work with terms of type [odd_nat]
    as if those were just regular naturals.
 *)
Coercion oval : odd_nat >-> nat.

Check o41 + o41.    (** Notice the result type is [nat] here: to use [odd_nat] as [nat] we forget the
                        extra information about oddity *)

(** Prove the main property of [odd_nat] *)
Lemma oddP {n : odd_nat} : odd n.
Proof.
  move : (oprop n).
  done.
Qed.

(** Let us do the analogous thing for the even numbers *)
Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP {n : even_nat} : ~~ (odd n).
Proof.
  move : (eprop n).
  done.
Qed.

(** Now we have all the definitions we referred to in the problem definition.  *)

(** The objective is to make it work: knowing that
    [n] is [odd] Coq should infer that [n * 3]
    is also [odd], and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof.
  Fail by rewrite oddP evenP.
Abort.

(** But Coq cannot infer it without any hints.
    The goal to provide the necessary hints in the form of canonical structure instances *)

(** Let's start by telling Coq that 0 is even *)

Print isT.
Canonical even_0 : even_nat := @Even 0 isT.

(** helper lemma *)
Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
  Show.
  case : n; rewrite //=.
Qed.
  
(** helper lemma *)
Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
  case : n; rewrite //=.
  move => n.
  case : (odd n); rewrite //=.
Qed.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)
Canonical odd_even (m : even_nat) : odd_nat :=
  @Odd m.+1 (oddS (eprop m)).

(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)
Canonical even_odd (m : odd_nat) : even_nat :=
  @Even m.+1 (evenS (oprop m)).

Unset Printing Notations.
Set Printing Notations.

(** Now let's deal with multiplication:
    DO NOT USE [case] tactic or the square brackets to
    destruct [n] or [m] *)
Lemma odd_mulP {n m : odd_nat} : odd (n * m).
Proof.
(** (!) do not break up [n] or [m] *)
  rewrite oddM.
  set h1 := oprop n.
  set h2 := oprop m.
  rewrite h1 h2.
  done.
Qed.
  
  (** teach Coq that [*] preserves being [odd] *)
  
Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  @Odd (muln n m) (@odd_mulP n m).

(** If the following proof works it means you did everything right: *)

Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof.
  rewrite //=.
  apply : odd_mulP.
Qed.

End OddAndEven.

(** ** Part 2: Equality for [odd_nat] *)

(** We cannot use [==] on [odd] natural numbers because
   [odd_nat] is not an [eqType] *)
Fail Check forall n : odd_nat, n == n.

(** * Optional exercise: define [eqType] instance for [odd_nat] *directly* *)

Definition eq_odd_nat (m n : odd_nat) : bool :=
 (oval m) == (oval n).
(* Hint: since you are comparing two structures you might think
   you need to check that both components of the structures are equal:
   this is not a problem for the first component of type [nat],
   but then you'll need to compare two *proofs* and this is
   tricky in general.
   However, here you actually don't need to compare the proofs at all:
   simply compare the first components and then you'll still be able
   to prove [Equality.axiom].
 *)

About Bool.reflect.

About eqP.

About eq_irrelevance.


Unset Printing All.
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Notations.

About eq_irrelevance.

Lemma odK (x : odd_nat) : x = @Odd (oval x) (oprop x).
Proof.
  by case : x.
Qed.

Lemma eq_odd_axiom : Equality.axiom eq_odd_nat.
Proof.
  rewrite /Equality.axiom /eq_odd_nat.
  move => x y.
  case : x.
  case : y.
  move => n nodd m modd.
  case : eqP; rewrite //= => h1; constructor; move : nodd modd.
  - rewrite h1 => nodd modd.
      by rewrite (eq_irrelevance modd nodd).
  - rewrite /not.
    move => nodd modd.
    case.
    apply h1.
Qed.
  
(*
 Hint 1: use [case: eqP] to case analyse on equality between natural numbers
         (you might need to do some definition unfolding before you can use it).

 Hint 2: use [eq_irrelevance] lemma (you might need to specify the exact
         occurence you want to rewrite like so rewrite [proof_name]eq_irrelevance).
*)

(** * Exercise: define [eqType] instance for [odd_nat] using [subType] *)

(* Since [odd_nat] is a subtype of natural numbers, i.e.
   a structure with a number and an additional (computable) constraint on it,
   we can use the [subType] machinery to derive equality (and not only equality)
   on it. *)
(* First, you derive [subType] instance by specifying the projection like: *)

Canonical oddnat_subType := Eval hnf in [subType for oval].

Print oddnat_subType.

(* Then you derive the equality mixin be specifying the type: *)

Definition oddnat_eqMixin := Eval hnf in [eqMixin of odd_nat by <:].

(* Comment out the the line with [Canonical oddnat_subType] above and
   make sure deriving of [oddnat_eqMixin] fails. *)

(* Now finish the definition of [eqType] for [oddnat]: *)

(* ADD YOUR CODE HERE *)

Print Equality.Pack.

Canonical oddnat_eqType := Equality.Pack oddnat_eqMixin.

(* This should work now *)

Check forall n : odd_nat, n == n.

Lemma odd_nat_eq_refl (n : odd_nat) :
  n == n.
Proof. by rewrite eq_refl. Qed.

(** * Exercise: Now deal with [even_nat] *)
Fail Check forall (m : even_nat), m == m.

(* ADD CODE HERE *)

Canonical evennat_subType := Eval hnf in [subType for eval].
Definition evennat_eqMixin := Eval hnf in [eqMixin of even_nat by <:].
Canonical evennat_eqType := Equality.Pack evennat_eqMixin.

Check forall (m : even_nat), m == m.

Lemma even_nat_eq_refl (n : even_nat) :
  n == n.
Proof. by rewrite eq_refl. Qed.

(*

==== OPTIONAL EXERCISES ====

Exercises in this section are not related to canonical structures
*)


(** An optional exercise with a short and a bit tricky one-line solution (less than 70 characters): *)

Set Printing Notations.

Lemma triple_compb_long (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
  have h y : f y = true \/ f y = false. by case : (f y); intuition.
  by case : (h true) (h false); case => p; case => q; case; rewrite /comp ?p ?q ?p ?q.
Qed.

Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
  by rewrite /comp; case; case E : (f true); case D : (f false); rewrite ?E ?D. 
Qed.
    
  
    
(** Hint: use [case <identifier>: <term>] tactic
          to pattern match on [<term>] and keep the result
          as an equation <identifier> in the context.
          E.g. [case E: b] where [b : bool] creates two subgoals with two equations
          in the context: [E = true] and [E = false] corresponingly.
 *)



(** Optional exercises: provide one-line proofs *)
Section EckmannHilton.
(** Here is an explanation for this section:
    https://en.wikipedia.org/wiki/Eckmann–Hilton_argument
    Hint: you can find informal proofs in that wiki page,
          use it as a source of inspiration if you get stuck.
 *)

Context {X : Type}.
Variables f1 f2 : X -> X -> X.

Variable e1 : X.
Hypothesis U1 : left_id e1 f1 * right_id e1 f1.

Variables e2 : X.
Hypothesis U2 : left_id e2 f2 * right_id e2 f2.

Hypothesis I : interchange f1 f2.

Compute interchange f1 f2.

Compute left_id e1 f1.

Compute right_id e1 f1.

Lemma units_same :
  e1 = e2.
Proof.
  rewrite -[e1] U1 -{1}[e1] U2 -{2}[e1] (snd U2) I !U1 U2. done.
Qed.

Locate "=2".

Lemma operations_equal :
  f1 =2 f2.
Proof.
  move => x y; rewrite - {1}[x] (snd U2) -{1}[y] U2 I -units_same !U1.
  done.
Qed.

Lemma I1 : interchange f1 f1.
Proof.
  move => x y z w; rewrite operations_equal -I -![f2 _ _]operations_equal.
  done.
Qed.

Lemma operations_comm :
  commutative f1.
Proof.
  move => x y.
  rewrite operations_equal -{1}[y](snd U1) -{1}[x]U1 -I units_same !U2.
  done.
Qed.
  
Lemma operations_assoc :
  associative f1.
Proof.
  move => x y z. rewrite -{2}[z]U1 I1 U1. done.
Qed.

End EckmannHilton.
