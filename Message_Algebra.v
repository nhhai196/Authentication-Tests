(* Some standard library imports *)

(* Require Import Logic List ListSet Arith Peano_dec Omega. *)
(* Require Import ProofIrrelevance. *)
(* Require Import Ensembles.  *)
(* Require Import LibTactics. *)
(* Require Import CoLoRRelDec CoLoRRelSub. *)
(* Require Import strictorder set_rep_equiv util. *)
(* Require Import String. *)

Require Import Relation_Definitions Relation_Operators Omega Arith.

(* ******************************************************* *)
(* VERSION 3 *)

(** * Discusson *)

(**

   We follow Joshua Guttman's Establishing and Preserving Protocol
   Security Goals.  Except where we don't...

   Start with sorts: names, nonces, data, symmetric keys, asymmetric
   keys. Let messages be the disjoint union of all these.

   Basic values include names, nonces, data, and keys.  "These keys
   include parameters and also the range of a key constructor" Latter
   presumably refers to pk and privk.  Not clear what "parameter"
   means there.

   About "variables", or "indeterminates": if names, etc are viewed as
   subsorts of message, then one should have variables at each sort.
   But if---as in JG's EPPSG paper---one allows variables to be
   replaced by any message, then names, nonce, etc should be viewed as
   predicates.

   EPPSG makes a distinction between parameters and variables...not
   clear on the difference.

   Note.  When we want to have functions like that that operate on
   certain "messages" only, like keys or names, then we do view keys
   and names as types.  When you want to treat these as messages then
   you must explcitly wrap them in their constructors.  As in

   [ (Enc (Data d) (pk n) ) ]  not just
   [ (Enc       d  (pk n) ) ]

   Too bad, though, since the only way the latter could be well-typed
   is via the former verbose version so you'd hope it could be
   "inferred".  But no, that's an accident: could certainly have two
   constructors with the same input and output types...
   Moral: subsort inclusion has to be made explicit.

*)


(** * Abstract types *)

Variable var   : Type.
Variable name  : Type.
Variable nonce : Type. 
Variable data  : Type.


Variable eq_var_dec : forall (x y:var), {x = y} + {x <> y}.
Hint Resolve eq_var_dec.
Variable eq_name_dec : forall (x y:name), {x = y} + {x <> y}.
Hint Resolve eq_name_dec.
Variable eq_nonce_dec : forall (x y:nonce), {x = y} + {x <> y}.
Hint Resolve eq_nonce_dec.
Variable eq_data_dec : forall (x y:data), {x = y} + {x <> y}.
Hint Resolve eq_data_dec.


(** * Keys *)


(** Interesting design choices about keys. Here we do not model
   symmetric and asymmetric keys as separate types; the distinction is
   just different constructor/injections into the key type.
   Sometimes simpler.  Possible issue is with key inverses...?
*)

(* Require Import ListSet. *)

Variable rawkey : Type.

Inductive key :=
| Sk : rawkey -> key
| Pubk : name -> key
| Privk : name -> key .

Variable eq_rawkey_dec : forall (x y:rawkey), {x=y} + {x<>y}.
Hint Resolve eq_rawkey_dec.

Definition eq_key_dec : forall (x y:key), {x=y} + {x<>y}.
Proof.
decide equality.
Qed.
Hint Resolve eq_key_dec.

Definition invk : key -> key  :=
  fun (k:key) =>
    match k with 
      | Sk x => Sk x
      | Pubk n => Privk n
      | Privk n => Pubk n
    end.


(** * Main message definitions *)

Inductive msg :=
| D : data -> msg
| K : key -> msg
| P : msg -> msg -> msg
| E : msg -> key -> msg.
Hint Constructors msg.

Definition eq_msg_dec : forall x y : msg,  
  {x = y} + {x <> y}.
Proof.
intros.
decide equality.
Qed.

Hint Resolve eq_msg_dec.

(** Atomic values *)
Inductive is_atomic : msg -> Prop := 
  |a_data : forall x, is_atomic (D x)
  |a_key : forall k, is_atomic (K k).
Hint Constructors is_atomic.

(** Concatenated terms or messages *)
Inductive concat : (msg -> Prop) := 
  | conc : forall m1 m2, concat (P m1 m2).
Hint Constructors concat.

(** Encryption *)
Inductive is_enc : msg -> Prop :=
  | encr : forall m k, is_enc (E m k).
Hint Constructors is_enc.


(** Treat basic as a predicate, not a subtype *)
Inductive is_basic : msg -> Prop :=
| bdata : forall x, is_basic (D x)
| bkey : forall x, is_basic (K x)  .
Hint Constructors is_basic.

(* Some basic results about atomic and concat *)
Lemma concat_not_atomic :
  forall m, concat m -> ~ is_atomic m.
Proof.
intros.
unfold not.
intros. inversion H. inversion H0.
symmetry in H1. rewrite H1 in H2. discriminate.
symmetry in H1. rewrite H1 in H2. discriminate.
Qed.

Lemma atomic_not_concat:
  forall m, is_atomic m -> ~concat m.
Proof.
intros.
unfold not. intros.
inversion H0. inversion H. 
symmetry in H1. rewrite H1 in H2.
discriminate.
symmetry in H1. rewrite H1 in H2.
discriminate.
Qed.

Lemma enc_not_basic : forall m1 m2, ~ is_basic (P m1 m2).
Proof.
intros.
unfold not. intros. inversion H.
Qed.

(**  * Three notions of subterm *)

(** ** Ingredient.   Called "carried by" in some CPSA pubs. *) 

(** *** Basis *)
Inductive ingred_1 :  msg -> msg -> Prop :=
| inpair1 : forall x y, ingred_1  x (P x y)
| inpair2 : forall x y, ingred_1  y (P x y)
| inenc1  : forall x k, ingred_1 x (E x k)  .
Hint Constructors ingred_1.

(** *** Transitive closure *)
Inductive ingred_p (x:msg) : msg -> Prop :=
| ingred_p_step y : ingred_1 x y -> ingred_p x y
| ingred_p_trans y y' : ingred_1 x y' -> ingred_p y' y -> ingred_p x y.
Hint Constructors ingred_p.

(** ***  Reflexive-Transitive closure *)
Inductive ingred (x: msg) : msg -> Prop :=
| ingred_refl : ingred x x
| ingred_step y  : ingred_p x y -> ingred x y.
Hint Constructors ingred.
Print ingred_ind.

Lemma ingred_p_transitive : 
  forall (x y z:msg), ingred_p x y -> ingred_p y z -> ingred_p x z.
Proof.
intros.
induction H.
apply ingred_p_trans with (y':=y); assumption.
apply ingred_p_trans with (y':= y'). auto.
apply IHingred_p. auto.
Qed.

Lemma ingred_trans : 
  forall (x y z:msg), ingred x y -> ingred y z -> ingred x z.
Proof.
intros.
induction H. auto.
inversion H0. subst. 
apply ingred_step; assumption.
apply ingred_step.
apply ingred_p_transitive with (y:=y); assumption.
Qed.

Lemma ingred_dec : forall x y, {ingred x y} + {~ingred x y}.
Proof.
Admitted.
Hint Resolve ingred_dec.
Print ingred_ind.

(** *** Some basic results about ingred *)
Lemma ingred_1_pair : forall x y z, ingred_1 x (P y z) -> 
                    ingred x y \/ ingred x z.
Proof.
intros.
inversion H.
left. apply ingred_refl.
right. apply ingred_refl.
Qed.

(* Induction on ingred_p x P(P y z) doesn't keep the information 
 about (P y z), so we have to use "REMEMBER" here *)
Lemma ingred_p_pair : forall y z x, ingred_p x (P y z) -> 
                    ingred x y \/ ingred x z.
Proof.
intros.
remember (P y z) as e in H.
induction H.
apply ingred_1_pair. rewrite Heqe in H. assumption.
assert (ingred y' y \/ ingred y' z). apply IHingred_p. auto.
assert (ingred x y'). apply ingred_step. apply ingred_p_step. assumption.
case H1.
intros. left. apply ingred_trans with (y:=y'); assumption.
intros. right. apply ingred_trans with (y:=y'); assumption.
Qed.

Lemma ingred_pair : forall x y z, ingred x (P y z) /\ x <> (P y z) -> 
                    ingred x y \/ ingred x z.
Proof.
intros.
destruct H as (H1, H2).
inversion H1. elim H2. auto.
apply ingred_p_pair. assumption.
Qed.

(** Similarly for encryption *)
Lemma ingred_1_enc : forall x y k, ingred_1 x (E y k) -> ingred x y.
Proof.
intros.
inversion H. auto.
Qed.

Lemma ingred_p_enc : forall x y k, ingred_p x (E y k) -> ingred x y.
Proof.
intros.
remember (E y k) as e in H.
induction H.
apply ingred_1_enc with (k:=k).  rewrite Heqe in H. assumption.
assert (ingred y' y). apply IHingred_p. assumption.
assert (ingred x y'). apply ingred_step. apply ingred_p_step. assumption.
apply ingred_trans with (y:=y'); assumption.
Qed.

Lemma ingred_enc : forall x y k, ingred x (E y k) /\ x <> (E y k) -> ingred x y. 
Proof. 
intros.
destruct H.
inversion H.
elim H0; auto.
apply ingred_p_enc with (k:=k). assumption.
Qed.

(** ** "Strong ingredient", written as [<<] in EPPSG *)
(** *** Basis *)

Inductive strong_ingred_1 :  msg -> msg -> Prop :=
| strpair1 : forall x y, strong_ingred_1  x (P x y)
| strpair2 : forall x y, strong_ingred_1  y (P x y)
| strenc1  : forall x k, strong_ingred_1 x (E x k)
| strkeysk :  forall x, strong_ingred_1 (K (Sk x)) (K (Sk x))
(*| strkeypubk :  forall n, strong_ingred_1 (N n) (K (Pubk n))
| strkeyprivk :  forall n, strong_ingred_1 (N n) (K (Privk n))*).

(** ** Transitive  closures *)
Inductive strong_ingred_p (x: msg) : msg -> Prop :=
| strong_ingred_p_step y : strong_ingred_1 x y -> strong_ingred_p x y
| strong_ingred_p_trans (y y':msg) : strong_ingred_1 x y' -> strong_ingred_p y' y -> strong_ingred_p x y.


(** ***  Reflexive-Transitive closure *)
Inductive strong_ingred (x: msg) : msg -> Prop :=
| strong_ingred_refl : strong_ingred x x 
| strong_ingred_step y  : strong_ingred_p x y -> strong_ingred x y.


(** ** The most liberal, the traditional notion of subterm *)

(** *** Basis *)
Inductive occurs_in_1 :  msg -> msg -> Prop :=
| opair1 : forall x y, occurs_in_1  x (P x y)
| opair2 : forall x y, occurs_in_1  y (P x y)
| oenc1  : forall x k, occurs_in_1 x (E x k)
| okeysk :  forall x, occurs_in_1 (K (Sk x)) (K (Sk x))
(*| okeypubk :  forall n, occurs_in_1 (N n) (K (Pubk n))
| okeyprivk :  forall n, occurs_in_1 (N n) (K (Privk n))*)
| oenc2  : forall x k, occurs_in_1 (K k) (E x k)  .

(** ***  Transitive closure *)
Inductive occurs_in_p (x: msg) : msg -> Prop :=
| occurs_in_p_step y : occurs_in_1 x y -> occurs_in_p x y
| occurs_in_p_trans y y' : occurs_in_1 x y' -> occurs_in_p y' y -> occurs_in_p x y.

(** ***  Reflexive-Transitive closure *)
Inductive occurs_in (x: msg) : msg -> Prop :=
| occurs_in_refl : occurs_in x x
| occurs_in_step y : occurs_in_p x y -> occurs_in x y.


(* existence of maximal encryption

Inductive maximal_enc : msg -> msg -> Prop :=
  | max_enc1 : forall m1 m2, (ingred m1 m2 /\ is_enc m1 /\ 
               (forall m, ingred m m2 /\ is_enc m -> ingred m m1)) ->
               maximal_enc m1 m2.

Lemma exists_1_max_enc : forall m, (exists e, ingred_1 e m /\ is_enc e) -> 
                          (exists e', maximal_enc e' m).
Proof.
intros.
destruct H as (e, (H1, H2)).
induction H1.
exists x. apply max_enc1.

Lemma exists_p_max_enc : forall m, (exists e, ingred_p e m /\ is_enc e) -> 
                          (exists e', maximal_enc e' m).
Proof.
intros.
destruct H as (e, (H1, H2)).
induction H1.

Lemma exists_max_enc : forall m, (exists e, ingred e m /\ is_enc e) -> 
                          (exists e', maximal_enc e' m).
Proof.
intros. destruct H as (e, (H1, H2)).
induction H1. exists e. apply max_enc1.
repeat split. apply ingred_refl. auto. 
intros. apply H.
*)
(* ** Size of messages *) 
(* A tool for reasoning about ingredients *)

Fixpoint size (m:msg) :=
  match m with 
   | D x => 1
   | K k => 1 
   | P m1 m2 => (size m1) + (size m2)
   | E x k => (size x) + 1
   end.

Check size.

(* Size of every message is always positive *)
Lemma zero_lt_size : forall x, 0 < size x.
Proof.
intro x.
induction x.
auto. auto.
simpl; omega. 
simpl; omega.
Qed.

Lemma size_lt_plus_l : forall x y, size x < size x + size y.
Proof.
intros x y. 
assert (size x + 0 < size x  + size y).
apply plus_lt_compat_l. apply zero_lt_size.
rewrite (plus_comm (size x) 0) in H.
rewrite (plus_O_n (size x)) in H. auto. 
Qed.

(* ** Relation between ingredient and size *)
(* Given a message, then size of an ingredient is always
less than or equal size of message itself *)

Lemma ingred_1_lt :
  forall x y, ingred_1 x y -> size(x) < size(y).
Proof.
intros x y H.
inversion H.
simpl. apply size_lt_plus_l.
simpl. rewrite plus_comm.
apply size_lt_plus_l.
simpl; omega.
Qed.

Lemma ingred_p_lt : 
  forall x y, ingred_p x y -> size(x) < size(y).
Proof.
intros x y H.
induction H.
apply ingred_1_lt; assumption.
assert (size x < size y'). apply ingred_1_lt; assumption.
apply lt_trans with (m:=size y'); assumption.
Qed.

Lemma ingred_lt : 
  forall x y, ingred x y -> size(x) <= size(y).
Proof. 
intros x y H.
inversion H.
auto.
assert (size x < size y).
apply ingred_p_lt; assumption.
omega.
Qed.
 
(* *) 
Lemma ingred_same_size_eq : 
  forall x y, ingred x y /\ size(x) >= size(y) -> x=y.
Proof.
intros x y H.
destruct H as (H0, H1).
inversion H0; auto.
assert (size x < size y). apply ingred_p_lt; assumption.
assert False. omega. elim H4.
Qed.

(* If each message ia an ingredient of the other, 
then they are the same *)
Lemma ingred_eq : forall x y, ingred x y -> ingred y x -> x=y.
Proof.
intros.
assert (size x <= size y). apply ingred_lt; assumption.
assert (size y <= size x). apply ingred_lt; assumption.
assert (size x = size y). omega. 
apply ingred_same_size_eq. split; assumption.
Qed.
