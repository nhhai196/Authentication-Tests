(* This module contains all basic lemma for lists *)

Require Import List Omega Ring Peano.
Import ListNotations.

Section List_Library.
Variable A B : Type.
Variable default : A.

Lemma list_nth_app : 
  forall (p : list A) (a:A) (n:nat), n < length p -> 
  nth_default default (a::p) (S n) = nth_default default p n.
Proof.
intros p a n lt. eauto.
Qed.

Lemma list_nth_app_left : 
  forall (p q : list A) (n:nat), n < length p -> 
  nth_default default (p++q) n = nth_default default p n.
Proof.
intros p q n lt. generalize dependent n.
induction p. intros. simpl in lt. omega.
intros. destruct n. eauto. 
simpl in lt.
assert ((a::p)++q = a::p++q). eauto. rewrite H.
repeat rewrite list_nth_app. apply IHp. omega. omega.
rewrite app_length. omega.
Qed.


Lemma list_nth_app_left2 : 
  forall (p : list A) (a:A) (n:nat), n < length p -> 
  nth_default default (p++[a]) n = nth_default default p n.
Proof.
intros p a n lt.
apply list_nth_app_left. auto.
Qed.

Lemma list_nth_app_right : 
  forall (p q : list A) (n:nat), 
    n >= length p -> n < length (p++q) -> 
    nth_default default (p++q) n = nth_default default q (n - length p).
Proof.
induction p. intros q n lgt llt. simpl. rewrite <-(minus_n_O n). auto.
intros q n lgt llt.
destruct n. inversion lgt. simpl. apply IHp. 
inversion lgt; auto. subst. simpl in H0. omega.
inversion llt. auto. omega.
Qed.

Lemma list_split_fst :
   forall (p : list (A*B)) (a:A) (b:B), fst (split (p++[(a,b)])) = (fst (split p))++[a].
Proof.
intros p a b.
induction p. simpl. auto.
Admitted.

Lemma list_split_snd :
   forall (p : list (A*B)) (a:A) (b:B), snd (split (p++[(a,b)])) = (snd (split p))++[b].
Admitted.

Lemma list_tl_extend: 
  forall (p : list (A*B)) (x:A) , tl (fst (split p) ++ [x]) = tl (fst (split p)) ++ [x].
Admitted.

Lemma paradox : 1 - 2 = 0.
Proof.
auto.
Qed.

Lemma p2 : 1-2+2 = 2.
Proof.
rewrite paradox.
auto.
Qed.

Lemma a : forall n m, S n = S m -> n=m.
Proof.
intros. auto.
Qed. 

End List_Library.

