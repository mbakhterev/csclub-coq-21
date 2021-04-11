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

(* Доказательство bool ≡ unit + unit *)

Definition uub : (sum unit unit) -> bool :=
  fun uu => if uu is inl tt then true else false.

Definition buu : bool -> (sum unit unit) :=
  fun b => if b then inl tt else inr tt.

Compute cancel uub buu.

Definition b_iso_uu : and (cancel uub buu) (cancel buu uub) :=
conj
  (fun uu => match uu as x return (buu (uub x) = x) with inl tt => erefl | inr tt => erefl end)
  (fun b => match b as x return (uub (buu x) = x) with true => erefl | false => erefl end).

Variables (A B : Type).

Axiom f_ext_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Unset Printing Notations.

(* Доказательство A * B ≡ forall b : bool, if b then A else B *)

Reset abf.
Definition abf : (prod A B) -> (forall b : bool, if b then A else B) :=
fun ab => let (k, l) := ab
          in fun b => if b as c return (if c return Type then A else B)
                      then k
                      else l.

Reset fab.
Definition fab : (forall b : bool, if b return Type then A else B) -> (prod A B) :=
fun f => pair (f true) (f false).

Definition ab_cancel_f : cancel abf fab :=
fun ab => match ab as x return (fab (abf x) = x) with (k, l) => erefl end.

Reset f_cancel_ab.
Definition f_cancel_ab : cancel fab abf :=
fun f => let abf_fab_congr_f : forall b : bool, (abf (fab f)) b = f b :=
                    fun b => if b as c return ((abf (fab f)) c = f c) then erefl else erefl 
              in f_ext_dep (abf (fab f)) f abf_fab_congr_f.

Definition ab_iso_f: and (cancel abf fab) (cancel fab abf) := conj ab_cancel_f f_cancel_ab.

(* Доказательство A + B ≡ {b : bool & if b then A else B} *)

Compute {b : bool & if b then A else B}.
Print sigT.

Reset sab_sig.
Definition sab_sig : (sum A B) -> sigT (fun b : bool => if b return Type then A else B) :=
fun s => match s with 
         | inl a => existT _ true a
         | inr b => existT _ false b
         end.

Reset sig_sab.
Definition sig_sab : sigT (fun b : bool => if b return Type then A else B) -> (sum A B) :=
fun s => match s with
         | existT true a => inl a
         | existT false b => inr b
         end.

Print sab_sig.

Compute fun e => sab_sig (sig_sab e).

Print existT.

Reset sig_cancel_sab.
Definition sig_cancel_sab : cancel sig_sab sab_sig :=
fun s => match s as x return (sab_sig (sig_sab x) = x) with
         | existT true a => erefl (sab_sig (sig_sab (existT _ true a)))
         | existT false b => erefl (sab_sig (sig_sab (existT _ false b)))
         end.

Reset sig_sab_K.
Definition sig_sab_K : cancel sig_sab sab_sig :=
fun s => let (b, v) as x return (eq (sab_sig (sig_sab x)) x) := s in
(if b as b' return (forall v' : if b' then A else B, sab_sig (sig_sab (existT _ b' v')) = existT _ b' v')
      then (fun a : A => erefl)
      else (fun b : B => erefl)) v.

Print sig_cancel_sab.

Definition sab_cancel_sig : cancel sab_sig sig_sab :=
fun s => match s as x return (sig_sab (sab_sig x) = x) with
         | inl a => erefl (sig_sab (sab_sig (inl a)))
         | inr b => erefl (sig_sab (sab_sig (inr b)))
         end.

End Isomorphisms.

(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.
