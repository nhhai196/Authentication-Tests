
(* This file contains all basic results for Coq which will be used when proving *)

Require Import Lists.List Omega.

Lemma nth_error_len : 
  forall (A:Type) (l:list A) (n:nat), nth_error l n = None -> (length l) <= n.
Proof.
intros A l n. generalize dependent l.
induction n.
intros l H.
unfold nth_error in H.
unfold error in H. destruct l. auto. inversion H.

intros l1 H. destruct l1. simpl; omega.
inversion H. apply IHn in H. simpl. omega.
Qed.

 