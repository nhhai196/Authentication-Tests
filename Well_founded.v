Require Import Omega.
Require Import List.

Open Scope nat.

Axiom lt_wf: well_founded lt.

(*Lemma lem : forall (m n:nat), m*m = 2*n*n -> m=0 /\ n=0.
Proof.
apply well_founded_ind with (A:=nat) (R:=lt).
exact lt_wf.
intros.
apply H.
*)

Lemma IH : forall p:nat, (exists q, q<>0 /\ p*p = 2*q*q) -> 
                         (exists p', p' < p /\ exists q', q' <> 0 /\ p'*p' = 2*q'*q').
Proof.
Admitted.
Definition P : nat -> Prop := fun p => (exists (q:nat),q <> 0 /\ p*p=2*q*q)->False.
Lemma irrational : forall (p:nat), P p.
Proof.
apply well_founded_induction with (A:=nat) (R:=lt).
exact lt_wf.
intros.
unfold P in H.
unfold P.
intros.
assert (exists p', p' < x /\ exists q', q'<>0 /\ p'*p' = 2*q'*q').
apply IH with (p:=x).
exact H0.
destruct H1 as (p0, (H2, H3)).
apply H with (y:=p0).
exact H2.
exact H3.
Qed.

