From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Axiom replace_with_your_solution_here : forall {A : Type}, A.

Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then e :: s
    else x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then insert x (sort s')
  else [::].

Hypothesis leT_total : total leT.
Hypothesis leT_tr : transitive leT.

(** * Exercise *)

Set Printing Notations.

Lemma let_aa (a : T) : leT a a.
Proof.
  move : (leT_total a a).
  case/orP; done.
Qed.

Lemma insert_inserts (e : T) (s : seq T) : insert e s = nil -> False.
  case : s; rewrite /insert.
  - by done.
  - move => a; case (leT e a); by done.
Qed.

Lemma insert_less (e : T) (l : seq T) :
  forall (a : T) (s : seq T), insert e l = a :: s -> leT a e.
Proof.
  case : l.
  - rewrite /insert => a s; case => h1 h2; rewrite h1.
      by exact (let_aa a).
  - move => x xs y ys; rewrite /insert.
    case h : (leT e x); case => h1 h2; rewrite -h1.
  - by exact (let_aa e).
  - move : (leT_total e x); by rewrite h //.
Qed.

Lemma sort_nil (s : seq T) : sort s = nil -> s = nil.
  case : s.
  - by done.
  - by move => a l; rewrite /sort => h; move : (insert_inserts h).
Qed.

About head.
Compute head 4 (cons 2 (cons 5 nil)).
Search (seq ?T -> ?T).
Print head.

Lemma sort_commute (l : seq T) :
  if (sort l) is s :: ss then sort (s :: ss) = s :: sort ss else sort [::] = [::].
Proof.
  elim : l.
  - by rewrite //.
    - move => a l IH.!

Lemma sort_some (s : seq T) :
  forall (e : T) (l : seq T), sort s = e :: l -> all (leT e) l.
Proof.
  elim : s.
  - move => e l; rewrite /sort. by case.
  - move => e l IH.
    move => x xs.
    rewrite /sort.
    case l.
Abort.
Admitted.

(*Lemma sort_some (s : seq T) :
  forall (e : T) (l : seq T), sort s = e :: l -> all (leT e) l.
Proof.
  case : s.
  by rewrite /sort.
  move => a l.
  case l.
  rewrite /sort /insert.
  move => e s.
  case.
  move => h1 h2.
  by rewrite -h2.
  move => x.
  elim.
  move => e xs.
  rewrite /sort /insert.
  case h1 : (leT a x); case; move => h2 h3; rewrite -h3 -h2 /all.
  by rewrite h1 //.
  move : (leT_total a x); case/orP.
  by rewrite h1.
  move => h4.
  by rewrite h4.
  move => y xs IH e es.
  rewrite /sort. *)
    
Lemma filter_sort p s :
  filter p (sort s) = sort (filter p s).
Proof.
  Show.
  elim : s.
  - by done.
  move => t l IH.
  rewrite /=.
    

(** Hint: you will probably need to introduce a number of helper lemmas *)

Set Printing Notations.

End InsertionSort.



Section AccPredicate.

(* To help you understand the meaning of the `Acc` predicate, here is how
 it can be used to write recursive functions without explicitly using recursion: *)


(** * Exercise:  understand how `addn_f` works *)
Section AdditionViaFix_F.

(* First, let's redefine the addition on natural numbers
   using the `Fix_F` combinator: *)
About Fix_F.
Print Fix_F.
(* notice we do recursion on the `a : Acc R x` argument *)

(* To define addition, we first need to choose the relation `R`
   which "connects" successive value.
   In the case of addition `R x y` can simply mean `y = x.+1` *)

Definition R m n := n = m.+1.

(* This definition has to be transparent, otherwise
   evaluation will get stuck *)
Definition esucc_inj : injective succn. by move=> n m []. Defined.

(* Every natural number is accessible w.r.t. R defined above *)
Fixpoint acc (n : nat) : Acc R n :=
  if n is n'.+1 then
      Acc_intro n'.+1 (fun y (pf : n'.+1 = y.+1) =>
                         eq_ind n' _ (acc n') y (esucc_inj pf))
  else Acc_intro 0 (fun y contra => False_ind _ (O_S y contra)).

Check acc.
(*
By the way, `forall n : nat, Acc R n` means that `R` is a well-founded
relation: https://en.wikipedia.org/wiki/Well-founded_relation.
*)
Print well_founded.

(* Addition via `Fix_F` *)
Definition addn_f : nat -> nat -> nat :=
  fun m =>
    @Fix_F nat
           R
           (fun=> nat -> nat)
           (fun m rec =>
              match m return (_ = m -> nat -> nat) with
              | m'.+1 => fun (eq : m = m'.+1) => succn \o rec m' eq
              | 0 => fun=> id
              end erefl)
           m
           (acc m).

(* This would get stuck if esucc *)
Check erefl : addn_f 2 4 = 6.

Lemma addn_equiv_addn_f :
  addn =2 addn_f.
Proof. by elim=> // m IHm n; rewrite addSn IHm. Qed.

End AdditionViaFix_F.



(** Exercise: implement multiplication on natural numbers using `Fix_F`:
    no explicit recursion, Program Fixpoint or things like that! *)
Section MultiplicationViaFix_F.

Definition muln_f : nat -> nat -> nat :=
  replace_with_your_solution_here.

(* this should not fail *)
Fail Check erefl : muln_f 21 2 = 42.

Lemma muln_equiv_muln_f :
  muln =2 muln_f.
Proof.
Admitted.

End MultiplicationViaFix_F.



End AccPredicate.
