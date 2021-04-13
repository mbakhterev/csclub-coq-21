From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Printing Notations.

(** Use SSReflect tactics.
    DO NOT use automation like [tauto], [intuition], [firstorder], etc.,
    except for [by], [done], [exact] tactic(al)s. *)


(** * Exercise *)

Lemma demorgan (A B : Prop) : ~ (A \/ B) -> (~ A /\ ~ B).
Restart.
move => nab.
move : conj.
apply.
- move => a.
  apply : nab.
  apply : or_introl.
  exact a.
move => b.
apply : nab.
apply : or_intror.
exact b.
Qed.

Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Restart.
move => noana.
move : (demorgan noana).
case.
move => na nna.
apply : False_ind.
exact (nna na).
Qed.

(** Hint: you might want to use a separate lemma here to make progress.
Or, use the `have` tactic: `have: statement` creates a new subgoal and asks
you to prove the statement. This is like a local lemma. *)


(** * Exercise *)

Lemma weak_Peirce (A B : Prop) :
  ((((A -> B) -> A) -> A) -> B) -> B.
Restart.
move => f.
apply : (f).
move => g.
apply : (g).
move => a.
apply : (f).
move => h.
exact a.
Qed.

(** * Exercise *)

(* Prove that having a general fixed-point combinator in Coq would be incosistent *)

Definition FIX := forall A : Type, (A -> A) -> A.

Lemma fix_inconsistent :
  FIX -> False.
Restart.
move => f.
move : (@f False).
apply.
exact id.
Qed.


Section Boolean.
(** * Exercise *)


Lemma negbNE b : ~~ ~~ b -> b.
Restart.
rewrite /negb.
move : b.
case.
- exact id.
- exact id.
Qed.

(** * Exercise *)

Lemma negbK : involutive negb.
Restart.
rewrite /involutive /negb /cancel.
case.
-  by [].
by [].
Qed.


(** * Exercise *)

Lemma negb_inj : injective negb.
Restart.
rewrite /injective /negb.
case.
- case.
  - by [].
  - by [].
case.
  - by [].
  - by [].
Qed.

End Boolean.


(** * Exercise *)

Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Restart.
elim : n.
- exact erefl.
move => n ih /=.
rewrite mulnS /=.
rewrite /addn /addn_rec /Nat.add.
exact (congr1 (fun x => S (S (S x))) ih).
Qed.

(** Hints:
- use the /= action to simplify your goal: e.g. move=> /=.
- use `Search (<pattern>)` to find a useful lemma about multiplication
*)

(** * Exercise
Prove by it induction: you may re-use the addnS and addSn lemmas only *)

Lemma plus_two_inj (n m : nat) : S (S n) = S (S m) -> eq n m.
Restart.
case.
exact.
Qed.

Lemma zz_plus (n : nat) : O = addn n n -> eq O n.
Restart.
case : n.
- exact.
exact.
Qed.

Lemma plus_zz (n : nat) : addn n n = O -> eq n O.
Restart.
case : n.
- exact.
exact.
Qed.

Lemma two_is_double_one (n : nat) : S (S O) = addn n n -> eq (S O) n.
Restart.
elim : n.
- exact.
move => n ih.
rewrite (addSn n (S n)).
rewrite (addnS n n).
move => h.
move : (plus_two_inj h).
move => h2.
move : (zz_plus h2).
move => h3.
exact (congr1 S h3).
Qed.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Restart.
move : n m.
elim.
- apply : plus_zz.
move => n h1.
case.
- apply : zz_plus.
move => k.
rewrite (addSn k (S k)).
rewrite (addnS k k).
rewrite (addSn n (S n)).
rewrite (addnS n n).
move => h2.
move : (plus_two_inj h2).
move => h3.
move : (h1 k h3).
apply : (congr1 S).
Qed.

(* This is a harder exercise than the previous ones but
   the tactics you already know are sufficient *)

(** * Optional exercise
    [negb \o odd] means "even".
    The expression here says, informally,
    the sum of two numbers is even if the summands have the same "evenness",
    or, equivalently, "even" is a morphism from [nat] to [bool] with respect
    to addition and equivalence correspondingly.
    Hint: [Unset Printing Notations.] and [rewrite /definition] are your friends :)
 *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
Admitted.


(** * Optional exercise *)
Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Proof.
Admitted.


(** * Optional exercise *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
Search (_ <= _ + _).
Admitted.
(** Hint: this lemmas does not require induction, just look for a couple lemmas *)





(* ================================================ *)

(*
More fun with functions, OPTIONAL
*)

Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

(** * Optional exercise *)
Lemma surj_epic f : surjective f -> epic f.
Proof.
Admitted.

(** * Optional exercise *)
Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Admitted.

(** * Optional exercise *)
Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Admitted.

(** * Optional exercise *)
Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

(** * Optional exercise *)
Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.


(** * Optional exercise *)
Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

(** * Optional exercise *)
Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

(** * Optional exercise *)
Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.
