From mathcomp Require Import ssreflect ssrfun ssrbool.

(** Prove the following lemmas by providing explicit proof terms.
A bunch of exercises from the previous seminar we didn't have time
to cover have made it to this homework :) *)


(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.


Section Logic.

Variables A B C : Prop.

(** * Exercise *)

Print True.

Definition notTrue_iff_False : (~ True) <-> False
:= conj (fun nt => nt I)
        (fun f t => f).

(* Hint 1: use [Locate "<->".] and [Print iff.] commands to understand better
the type above. *)

(* Hint 2: If you are experiencing an error like the following one
"Found a matching with no clauses on a term unknown to have an empty inductive type." try adding explicit type annotations to functional parameters or
use `match <term> in <type> with ... end` instead of `match <term> with ... end` *)


(** * Exercise: double negation elimination works for `False` *)

(* Какой тип функции (~ (~ False)) -> False = [definition] = ((False -> False) -> False) -> False *)

Definition dne_False : ~ ~ False -> False
:= fun nnf => nnf id.


(** * Exercise: double negation elimination works for `True` too. *)

Definition dne_True : ~ ~ True -> True
:= fun nnt => I.


(** * Exercise: Weak Peirce's law
Peirce's law (https://en.wikipedia.org/wiki/Peirce%27s_law) is equivalent to
Double Negation Elimination (and the Law of Excluded Middle too),
so it does not hold in general, but we can prove its weak form. *)

Definition weak_Peirce : ((((A -> B) -> A) -> A) -> B) -> B
:= fun abaab => abaab (fun aba => aba (fun a => abaab (fun aba2 => a))).

(* Hint 1: use let-in expression to break the proof into pieces and solve them independently *)
(* Hint 2: annotate the identifiers of let-expressions with types: [let x : <type> := ... in ...] *)


Variable T : Type.
Variable P Q : T -> Prop.

(** * Exercise: existential introduction rule *)

Locate "exists".
Print ex.
Print ex_intro.

Definition exists_introduction :
  forall (x : T), P x -> (exists (x : T), P x)
:= fun x px => ex_intro _ x px.

(** * Exercise: Frobenius rule: existential quantifiers and conjunctions commute *)

Definition frobenius_rule :
  (exists x, A /\ P x) <-> A /\ (exists x, P x)
:= conj (fun '(ex_intro x (conj a px)) => conj a (ex_intro _ x px))
        (fun '(conj a (ex_intro x px)) => ex_intro _ x (conj a px)).


End Logic.

Section Equality.

Variables A B C D : Type.

Locate "&&".
Print erefl.

(** * Exercise *)

Definition eq1 : true = (true && true)
:= erefl.

(** * Exercise *)

Definition eq2 : 42 = (if true then 21 + 21 else 239)
:= erefl. 

(** * Exercise *)

Compute ~~ false.

Definition LEM_decidable :
  forall (b : bool), b || ~~ b = true
:= fun b => match b with
            | true => erefl
            | false => erefl
            end.

(** * Exercise *)

Definition if_neg :
  forall (A : Type) (b : bool) (vT vF: A),
    (if ~~ b then vT else vF) = if b then vF else vT
:= fun a b vt vf => match b with
                    | true => erefl
                    | false => erefl
                    end.

(** * Exercise : associativity of function composition *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Locate "\o".

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= erefl.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


Locate "=1".
Print eqfun.

(** * Exercise: Reflexivity *)

Unset Printing Notations.

Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f => fun x => erefl.

(** * Exercise: Symmetry *)

Reset eqext_sym.

Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
  := fun f g feqg => fun x => match feqg x
                              in (_ = gx)
                              return (gx = (f x))
                              with erefl => erefl end.

Print eqext_sym.

(** * Exercise: Transitivity *)

Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
  := fun f g h efg egh => fun x =>
    match egh x in (_ = hx) return (f x = hx) with
    | erefl => match efg x with erefl => erefl end
    end.

(** * Exercise: left congruence *)

Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
    := fun f g h efg => fun x => match efg x in (_ = gx) return (h (f x) = h gx) with erefl => erefl end.

(** * Exercise: right congruence *)

Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
    := fun f g h efg => fun x => match efg (h x) with erefl => erefl end.

End Equality.


(** * Extra exercises (feel free to skip) *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= fun a b =>
   match a, b with
   | true, true => erefl
   | true, false => erefl
   | false, true => erefl
   | false, false => erefl
   end.
   

Reset negnegid.

Definition negnegid : forall b : bool, b = ~~ ~~ b
:= fun b => match b with
            | true => erefl
            | false => erefl
            end.

Definition booltrans : forall (a b c : bool), (a = b) -> (b = c) -> (a = c)
:= fun a b c eab ebc =>
  match ebc in (_ = c') return (a = c') with
  | erefl => match eab with erefl => erefl end
  end.

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
  := fun b ennbt => booltrans b (negb (negb b)) true (negnegid b) ennbt.
