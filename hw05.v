From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Unset Printing Notations. *)

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

Lemma s_flips_odd (n : nat) : odd (S n) = negb (odd n).
Restart.
elim : n.
- exact.
exact.
Qed.

Lemma rneutral_z (n : nat) : addn n O = n.
elim : n.
- exact.
move => n ih.
rewrite (addSn n O).
exact (congr1 S ih).
Qed.

Lemma rneutral_true (b : bool) : (Equality.op (Equality.class bool_eqType) b true) = b.
Restart.
case : b.
- exact.
exact.
Qed.
   
Check s_flips_odd.
Check rneutral_z.
Check rneutral_true.

Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Restart.
rewrite /morphism_2 /eq_op /(comp negb odd).
elim.
- exact.
move => n ih.
case.
- rewrite (addSn n O).
  rewrite (rneutral_z n).
  rewrite (s_flips_odd n).
  rewrite /(negb (odd O)).
  rewrite /(odd O).
  rewrite (rneutral_true (negb (negb (odd n)))).
  exact.
have h1 : forall (a b : bool), (Equality.op (Equality.class bool_eqType) (negb a) b) = negb (Equality.op (Equality.class bool_eqType) a b).
case.
- exact.
case.
- exact.
exact.
move => k.
rewrite (s_flips_odd n).
rewrite (h1 (negb (odd n)) (negb (odd (S k)))).
rewrite /(addSn n (S k)).
exact (congr1 negb (ih (S k))).
Qed.

(** * Optional exercise *)

Definition LEM (Q : Prop) := or Q (not Q).
Definition DNE (Q : Prop) := not (not Q) -> Q.

Lemma LEM_implies_DNE : forall Q : Prop, (LEM Q) -> (DNE Q).
Restart.
rewrite /LEM /DNE.
move => q.
case.
- exact.
move => nq nnq.
apply : (False_ind q (nnq nq)).
Qed.

Lemma nn_LEM : forall Q, not (not (LEM Q)).

Restart.
rewrite /LEM.
move => q.
move => h1.
move : (nlem h1).
move => vq.
move : (h1 (or_introl vq)).
exact.
Qed.

Lemma DNE_implies_LEM : (forall Q, DNE Q) -> (forall P, LEM P).
Restart.
move => dne.
move => p.
apply : (dne).
move => h1.
move : (nn_LEM h1).
exact.
Qed.

Reset DNE_iff_nppp.

Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Restart.
split.
- move => h1.
  move => p.
  move : (DNE_implies_LEM h1).
  move => h2.
  move : (h2 p).
  case.
  - exact.
  move => np.
  move => h3.
  exact (h3 np).
move => h1 p.
apply : LEM_implies_DNE.
apply : (h1).
move => h2.
move : (nn_LEM h2).
exact.
Qed.

(** * Optional exercise *)

Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Restart.
move : (leq0n p).
apply : leq_add.
Qed.

(** Hint: this lemmas does not require induction, just look for a couple lemmas *)


(* ================================================ *)

(*
More fun with functions, OPTIONAL
*)

Section PropertiesOfFunctions.

Lemma comp_assoc (a b c d: Type) (f : c -> d) (g : b -> c) (h : a -> b) : (f \o g) \o h =1 f \o (g \o h).
Restart.
done.
Qed.

Lemma comp_sym (a b : Type) (f g : a -> b) : f =1 g -> g =1 f.
Restart.
rewrite /eqfun.
move => fg.
move => x.
move : (fg x).
exact.
Qed.

Lemma comp_assoc_both
      (a b c d : Type)
      (g1 g2 : c -> d) (f : b -> c) (h1 h2 : a -> b)
  : (g1 \o f) \o h1 =1 (g2 \o f) \o h2
    -> g1 \o (f \o h1) =1 g2 \o (f \o h2).
Proof.
  move => k1.
  move : (comp_assoc g1 f h1) (comp_assoc g2 f h2).
  move => //.
Qed.

Lemma comp_assoc_both_r
      (a b c d : Type)
      (g1 g2 : c -> d) (f : b -> c) (h1 h2 : a ->b) :
  g1 \o (f \o h1) =1 g2 \o (f \o h2) -> (g1 \o f) \o h1 =1 (g2 \o f) \o h2.
Proof.
  done.
Qed.

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
Restart.
rewrite /surjective /epic.
case.
move => x.
move => h1.
move => c.
move => g1 g2.
move => eg12f.
have xx : (x =1 x).
exact.
move : (eq_comp eg12f xx).
move : (comp_assoc g1 f x).
move => h2 h3.
move : (comp_assoc g2 f x).
move => h4.
move : (comp_sym h2).
move => h5.
move : (ftrans h5 h3).
move => h6.
move : (ftrans h6 h4).
have gg1 : g1 =1 g1.
exact.
have gg2 : g2 =1 g2.
exact.
move : (eq_comp gg1 h1) (eq_comp gg2 h1).
move => s1 s2.
move => s3.
move : (ftrans (comp_sym s1) s3).
move => s4.
move : (ftrans s4 s2).
exact.
Qed.

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
Restart.
rewrite /epic.
move => epic_f epic_g D g1 g2.
set ef := epic_f D.
set eg := epic_g D.
move => h1.
set h2 := ftrans (comp_assoc g1 f g) h1.
set h3 := (ftrans h2 (comp_sym (comp_assoc g2 f g))).
set h4 := (eg (g1 \o f) (g2 \o f) h3).
exact (ef g1 g2 h4).
Qed.

(** * Optional exercise *)

Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Restart.
rewrite /epic.
move => epic_fg.
move => D g1 g2.
move => h1.
have gg : g =1 g.
exact.
set efg := epic_fg D g1 g2.
set h2 := (comp_assoc_both (eq_comp h1 gg)).
exact (efg h2).
Qed.

(** * Optional exercise *)

Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Restart.
rewrite /epic.
move => h1 D g1 g2 h2.
have gg : g =1 g.
exact.
set h3 := comp_assoc_both (eq_comp h2 gg).
have g1g1 : g1 =1 g1.
exact.
have g2g2 : g2 =1 g2.
exact.
have g1fg : g1 \o (f \o g) =1 g1.
move : (eq_comp g1g1 h1).
exact.
have g2fg : g2 \o (f \o g) =1 g2.
move : (eq_comp g2g2 h1).
exact.
exact (ftrans (comp_sym g1fg) (ftrans h3 g2fg)).
Qed.

End EpicProperties.

(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {A B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)

Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

(** * Optional exercise *)

Lemma inj_monic f : injective f -> monic f.
Restart.
rewrite /injective /monic /comp /eqfun.
move => h1 D.
move => g1 g2.
move => h2.
move => x.
exact (h1 (g1 x) (g2 x) (h2 x)).
Qed.

(** * Optional exercise *)

Lemma monic_inj f : monic f -> injective f.
Restart.
rewrite /injective /monic /comp /eqfun.
move => h1.
move => x1 x2.
set lx1 : unit -> B := fun _ => x1.
set lx2 : unit -> B := fun _ => x2.
set h2 := h1 unit lx1 lx2.
move => h3.
have h4 : forall x : unit, f (lx1 x) = f (lx2 x).
case.
rewrite /lx1 /lx2.
exact h3.
move : (h2 h4).
apply.
exact tt.
Qed.

End InjectiveMonic.

Section MonicProperties.

Context {A B C : Type}.

(** * Optional exercise *)

Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Restart.
rewrite /monic.
move => h1 h2.
move => D.
move => g1 g2.
move => h3.
set h4 := ftrans (comp_sym (comp_assoc f g g1)) h3.
set h5 := ftrans h4 (comp_assoc f g g2).
exact (h2 D g1 g2 (h1 D (g \o g1) (g \o g2) h5)).
Qed.


(** * Optional exercise *)
Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
  rewrite /monic.
  have ff : f =1 f.
  by exact.
  move => h1 D g1 g2 h2.
  set h3 := (eq_comp ff h2).
  set h4 := (@comp_assoc_both_r _ _ _ _ f f g g1 g2 h3).
  exact (h1 D g1 g2 h4).
Qed.
          
(** * Optional exercise *)
Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
  rewrite /monic.
  move => h1.
  move => D.
  move => g1 g2.
  have gg : g =1 g.
    by done.
  move => h2.
  move : (comp_assoc_both_r (eq_comp gg h2)).
  have gfg1 : (g \o f) \o g1 =1 g1.
    - have ig1 :id \o g1 =1 g1.
        by done.
        have g1g1 : g1 =1 g1.
        by done.
        have p1 : (g \o f) \o g1 =1 id \o g1.
        exact (eq_comp h1 g1g1).
        by done.
   have gfg2 : (g \o f) \o g2 =1 g2.
    - have ig2 :id \o g2 =1 g2.
        by done.
        have g2g2 : g2 =1 g2.
        by done.
        have p1 : (g \o f) \o g2 =1 id \o g2.
        exact (eq_comp h1 g2g2).
          by done.
move => h3.
move : (ftrans (comp_sym gfg1) (ftrans h3 gfg2)).
done.
Qed.
       
End MonicProperties.

End PropertiesOfFunctions.
