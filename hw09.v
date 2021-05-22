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

Lemma insert_path z e s :
  leT z e ->
  path leT z s ->
  path leT z (insert e s).
Proof.
move: z.
elim: s=> [/=| x1 s IHs] z.
- by move => ->.
move=> z_le_e.
move=> /=.
case/andP=> z_le_x1 path_x1_s.
case: ifP.
- by rewrite /= z_le_e path_x1_s => ->.
move=> /= e_gt_x1.
rewrite z_le_x1.
have:= leT_total e x1.
rewrite {}e_gt_x1 /= => x1_le_e.
exact: IHs.
Qed.

Lemma insert_sorted e s :        
  sorted leT s ->
  sorted leT (insert e s).
Proof.
rewrite /sorted.
case: s=> // x s.
move=> /=.
case: ifP; first by move=> /= ->->.
move=> e_gt_x.
apply: insert_path.
have:= leT_total e x.
by rewrite e_gt_x /= => ->.
Qed.

Lemma sort_sorted s : sorted leT (sort s).
Proof.
  rewrite /sorted.
  elim : s.
  - by rewrite //.
  - move => a l IH.
    move => //=.
    move : (@insert_sorted a (sort l) IH).
    rewrite /sorted.
    done.
Qed.

(** * Exercise *)

Lemma path_let e x l : leT e x -> path leT x l -> path leT e l.
Proof.
  elim : l.
  - by move => /=.
  - move => a l ih /= le_e_x.
    case/andP.
    move => le_x_a.
    move : (leT_tr le_e_x le_x_a).
    move => h1 h2.
    rewrite h1 h2.
    done.
Qed.
    

Lemma filter_keeps_sorted : forall l p x,
    sorted leT (x :: l) ->
    sorted leT (x :: filter p l).
Proof.
  elim.
  - by rewrite /=.
  - move => e l IH p x /=.
    case : ifP.
    set ih := (IH p e).
    move => h1.
    case/andP.
    move => le_x_e h2.
    have h3 : sorted leT (e :: l).
      by rewrite /sorted.
      move : (ih h3).
      rewrite /sorted /= le_x_e.
        by done.
  - move => h1.
    case/andP.
    move => le_x_e h2.
    set ih := IH p x.
    have h3 : sorted leT (x :: l).
    rewrite /=.
      by exact (path_let le_x_e h2).
      move : (ih h3) => /=.
      done.
Qed.

Lemma path_sorted a l : path leT a l -> sorted leT l.
Proof.
  elim : l.
  - by rewrite /=.
  - move => e l ih /=; case/andP; by done.
Qed.

Lemma insert_in_sorted e l :
  sorted leT (e :: l) -> insert e l = e :: l.
Proof.
  case : l.
  - by rewrite /=.
  - move => a l.
    rewrite /sorted /=.
    case/andP => h1 h2.
    rewrite h1.
    by done.
Qed.    

Lemma sort_of_sorted l : sorted leT l -> (sort l) = l.
Proof.
  elim : l.
  - by rewrite /=.
  - move => a l ih.
    rewrite /=.
    move => h1.
    set h2 := path_sorted h1.
    rewrite (ih h2).
    have h3 : sorted leT (a :: l).
    by rewrite /sorted.
    by exact (insert_in_sorted h3).
Qed.

Lemma path_le a e l : leT e a -> path leT a l -> path leT e l.
Proof.
  case l.
  - by rewrite /=.
  - move => x xs /= le_e_a.
    case/andP => le_a_x.
    move : (leT_tr le_e_a le_a_x) => le_e_x p_a_x.
    by rewrite le_e_x p_a_x.
Qed.

Lemma insert_filtered_path (p : T -> bool) e l :
  p e ->
  path leT e l ->
  insert e (filter p l) = e :: (filter p l).
Proof.
  move : e.
  elim : l.
  - by rewrite /=.
  - move => a l ih e pe /=.
    case/andP => le_e_a p_a_l.
  - case : ifP => pa.
    by rewrite /= le_e_a.
  - set p_e_l := path_le le_e_a p_a_l.
    by rewrite (ih e pe p_e_l).
Qed.

Lemma filter_path p e l:
  path leT e l -> path leT e (filter p l).
Proof.
  move : e.
  elim : l.
  - by rewrite /=.
  - move => a l ih e.
    rewrite /=.
    case/andP => le_e_a p_a_l.
    set p_e_l := path_le le_e_a p_a_l.
    case : ifP => pa.
  - rewrite /=.
    set h1 := (ih a p_a_l).
    by rewrite le_e_a h1.
  - by exact (ih e (path_le le_e_a p_a_l)).
Qed.
    
Lemma insert_filtered (p : T -> bool) a l :      
  p a
  -> (sorted leT l)
  -> insert a (filter p l) = filter p (insert a l).
Proof.
  move : a.
  elim : l => a.
  - move => pa /=. by rewrite pa.
  - move => l ih e pe.
    rewrite /=.
    move => path_al.
    case : ifP => pa /=.
  - case : ifP => le_e_a.
  - by rewrite /= pe pa.
  - rewrite {2}/filter pa.
    by rewrite (ih e pe (path_sorted path_al)).
  - case : ifP => le_e_a.
  - set h1 := (path_le le_e_a path_al).
    set h2 := (@filter_path p e l h1).
    set h3 := (@insert_filtered_path p e l pe h1).
    by rewrite h3 /= pe pa.
  - rewrite /= pa.
    set h1 := (@path_sorted a l path_al).
    by rewrite (ih e pe h1).
Qed.

Lemma mis_insert_filtered (p : T -> bool) a l:
  p a = false
  -> sorted leT l
  -> filter p (insert a l) = filter p l.
Proof.
  move : a.
  elim : l => e.
  - move => npe.
      by rewrite /= npe.
  - move => l ih a npa.
    rewrite /sorted /= => p_e_l.
    case : ifP => le_a_e.
  - by rewrite /= npa.
  - rewrite /=.
    case : ifP => pe.
    by rewrite (ih a npa (path_sorted p_e_l)).
  - by rewrite (ih a npa (path_sorted p_e_l)).
Qed.
    
Lemma filter_sort p l :
  filter p (sort l) = sort (filter p l).
Proof.
  Show.
  elim : l.
  - by done.
  - move => a l ih /=.
    case : ifP.
    rewrite /= => pa.
    set h0 := sort_sorted l.
    set h1 := @insert_filtered p a (sort l) pa h0.
    by rewrite -h1 ih.
  - move => npa.
    set h1 := @mis_insert_filtered p a (sort l) npa (sort_sorted l).
    by rewrite h1 ih.
Qed.
    
(** Hint: you will probably need to introduce a number of helper lemmas *)

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

About Fix_F.

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

Compute addn_f 4.

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
  fun m n =>
    @Fix_F nat
           R
           (fun => nat)
           (fun k rec =>
              match k return (_ = k -> nat) with
              | (S k') =>
                fun (eq : k = (S k')) => addn n (rec k' eq)
              | O => fun => 0
              end erefl)
           m
           (acc m).

Compute muln_f 11.

(* this should not fail *)
Check erefl : muln_f 21 2 = 42.

Lemma muln_equiv_muln_f :
  muln =2 muln_f.
Proof.
  elim => // m ih n.
  rewrite mulSn (ih n) /muln_f /=.
  done.
Qed.

End MultiplicationViaFix_F.



End AccPredicate.
