From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Import Specif.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Printing Notations.

(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` 
Axiom replace_with_your_solution_here : forall {A : Type}, A. *)


(* WARNING!
 Since we import `eqtype` module which redefines `eq_refl` to mean something else
 other than the equality type constructor, beware of using `eq_refl` in
 pattern-matching.
 For instance, in a `match`-expression like this one
    match foo in ... return ... with
    | eq_refl => ...
    end
 eq_refl is a new identifier which just shadows the `eq_refl` lemma,
 hence no index rewriting is happening. If you see weird type errors,
 just make sure you spelled the equality type constructor correctly
 in this context:
    match foo in ... return ... with
    | erefl => ...
    end
*)


(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= conj (fun '(ex_intro a b) => conj a b)
        (fun '(conj a b) => ex_intro (fun _ => B) a b).


(** * Exercise *)
Section Symmetric_Transitive_Relation.

Variables (D : Type)
          (R : D -> D -> Prop).

(* R's type D -> D -> Prop means R is a binary relation *)

(* The lemma refl_if read informally, means
"if R is a symmetric and transitive relation
then each element x which is related to some
element y is also related to itself" *)

Definition refl_if :
  (forall x y, R x y -> R y x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall x : D, (exists y, R x y) -> R x x
:= fun r_symm r_trans x '(ex_intro y r_xy) =>
   let r_yx := r_symm x y r_xy in r_trans x y x r_xy r_yx.

End Symmetric_Transitive_Relation.

Section Exercises_Natural.

(** * Exercise *)

Reset pair_inj.
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun eq_pairs =>
   match eq_pairs in (_ = ab2) return ((a1 = fst ab2) /\ (b1 = snd ab2)) with
   | erefl => conj erefl erefl
   end.


(** * Exercise *)

Inductive trilean : Type :=
  | Yes
  | No
  | Maybe.

Reset yes_no_disj.
Definition yes_no_disj :
  Yes <> No
:= fun eqen =>
   match eqen in (_ = n) return (if n is Yes then True else False) with
   | erefl => I
   end. 

(** * Exercise *)

(* (S m) + n = S (n + m) *)

Definition addnSl : forall (m n : nat), eq (addn (S m) n) (S (addn m n)) :=
fix ih m n :=
match m with
| O => erefl
| S m' => let ih' := ih m' n in
          let sm_n_ss_mn := congr1 S ih' in
          let ss_mn_ssmn : eq (addn (S (S m')) n) (S (S (addn m' n))) := erefl
          in eq_trans_r ss_mn_ssmn sm_n_ss_mn
end.

(* m + 0 = m *)

Definition addnOl : forall n : nat, eq (addn n O) n :=
fix ih n :=
match n with
| O => erefl
| S n' => let sno_s_no : eq (addn (S n') O) (S (addn n' O)) := erefl in
          let ih' := ih n' in
          let sno_sn := congr1 S ih'
          in eq_trans sno_s_no sno_sn
end.

Definition addA : associative addn
:= fix ih x y z :=
   match z with
   | 0 => match x with
          | 0 => erefl
          | S x' => let sx_yo_sxy := congr1 (addn (S x')) (addnOl y) in
                    let sxy_o_sxy := addnOl (addn (S x') y) in
                    eq_trans_r sx_yo_sxy sxy_o_sxy
          end
   | S z' => let ih' := ih x y z' in
             let Sxyz := addnS (addn x y) z' in
             let iSxyz := congr1 S ih' in
             let xSyz := addnS x (addn y z') in
             let xySz := congr1 (addn x) (addnS y z') in
             let xySz_Syxz := eq_trans xySz xSyz in
             let xy_Sz_Syxz := eq_trans_r Sxyz iSxyz in
             eq_trans_r xySz_Syxz xy_Sz_Syxz
   end.

(** * Exercise: *)

Definition addnCA : left_commutative addn :=
fix ih x y z :=
match x with
| O => erefl
| S x' => let ih' := ih x' y z in
          let sx_yz_sxyz := addnSl x' (addn y z) in
          let y_sxz_syxz := eq_trans (congr1 (addn y) (addnSl x' z)) (addnS y (addn x' z)) in 
          let iscongr := congr1 S ih' in
          let H := eq_trans sx_yz_sxyz iscongr in
          eq_trans_r H y_sxz_syxz
end.

(* Hint: re-use addnS lemma and some general lemmas about equality *)

End Exercises_Natural.

Section Exercises_Optional.

(** * ====== Optional exercises (feel free to skip) ====== *)

(** * Exercise (optional) *)

(* Я сам написал это решение, но, чёрт побери, я не понимаю, что всё это означает!
   Я понимаю даже, как это работает. Но что означает моё доказательство??? *)

Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= fun A P Q x y p => 
match p in (eq _ z) return (P x z p) with
| erefl => Q x
end.

(** * Exercise (optional): *)

Definition addnC : commutative addn :=
fix ih x y :=
match x with
| O => let oy_y : eq (addn O y) y := erefl in
       let yo_y := addnOl y in
       eq_trans_r oy_y yo_y
| S x' => let ih' := congr1 S (ih x' y) in
          let sx_y_s_xy := addnSl x' y in
          let y_sx_syx := addnS y x' in
          let sx_y_syx := eq_trans sx_y_s_xy ih' in
          eq_trans_r sx_y_syx y_sx_syx
end.

End Exercises_Optional.

Section Isomorphisms.

(** * Exercise (optional):

Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)

Reset iso.
Definition iso (A B : Type) (f : A -> B) (g : B -> A) :=
and (forall x : B, f (g x) = x)
    (forall y : A, g (f y) = y).
Print iso.

(* Пара примеров для тренировки *)
Reset nat_nat_iso.
Definition nat_nat_iso : iso (fun x : nat => x) (fun x : nat => x) :=
conj (fun x => erefl)
     (fun x => erefl).

Reset a_a_iso.
Definition a_a_iso : forall (A : Type), iso (fun x : A => x) (fun x : A => x) :=
fun A => conj (fun x => erefl) (fun x => erefl).

Reset isomorphic.
Definition isomorphic (A B : Type) := exists (f : A -> B) (g : B -> A), iso f g.
Print isomorphic.

(* Для тренировки *)
Definition a_a_isomorphic : forall A : Type, isomorphic A A :=
fun A => ex_intro _ id (ex_intro _ id (a_a_iso A)).

(* Изоморфизмы bool -> unit + unit ... *)
Definition buu : bool -> (sum unit unit) :=
fun b => match b with true => inl tt | false => inr tt end.

(* ... и unit + unit -> bool *)
Definition uub : (sum unit unit) -> bool :=
fun uu => match uu with inl tt => true | inr tt => false end.

(* Доказательство изоморфности *)
Reset b_uu_iso.
Definition b_uu_iso : iso buu uub :=
  conj (fun uu => match uu as y return (comp buu uub y = y) with inl tt => erefl | inr tt => erefl end)
       (fun b => if b as y return (comp uub buu y = y) then erefl else erefl).

(* Основное утверждение bool ≡ unit + unit *)
Reset b_uu_isomorphic.
Definition b_uu_isomorphic : isomorphic bool (sum unit unit) := ex_intro _ buu (ex_intro _ uub b_uu_iso).

(* Доказательство A + B ≡ {b : bool & if b then A else B} *)

About sigT.
Check forall (A B : Type) {b : bool & if b then A else B}.

(* Изоморфизмы A + B -> {b : bool & if b then A else B} ... *)


(* Доказательство A * B ≡ forall b : bool, if b then A else B *)

(* Изоморфизм -> ... *)
Reset abf.
Definition abf : forall (A B : Type), (prod A B) -> (forall (b : bool), if b then A else B) :=
fun A B ab => fun b => match b as c return (if c then A else B) with
                       | true => fst ab
                       | false => snd ab
                       end.

(* Изоморфизм <- *)
Reset fab.
Definition fab : forall (A B : Type), (forall b : bool, if b then A else B) -> (prod A B) :=
fun A B f => pair (f true) (f false).

(* Доказательство изоморфности *)

Reset tentt.
Definition tentt := (fun b => if b as c return (if c then nat else unit) then 10 else tt).
Print tentt.

Check abf.
Print abf.
Check abf (fab (fun b => if b as c return (if c then nat else unit) then 10 else tt)).
Compute (abf (10, tt)).
Compute (fab tentt).
Compute (comp abf fab).

Print nat.
Print bool.
Print unit.

(* Definition fab_iso : forall (A B : Type), iso (prod A B ) (forall b : bool, if b then A else B) (abf A B) (fab A B) :=
conj (fun x => _)
     _. *)

(* Definition fab_iso : forall (A B : Type), @iso A B (@abf A B) (@fab A B) :=
conj (fun ab => _)
     (fun f => _).

Definition fab_iso : forall (A B : Type), and (forall x : (prod A B), fab (abf x) = x) (forall y : (forall b : bool, if b then A else B), abf (fab y) = y) :=
  fun A B =>
    conj (fun ab => match ab as ab0 return (fab (abf ab0) = ab0) with (k, l) => erefl end)
         (fun f => _). *)

End Isomorphisms.

(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.
