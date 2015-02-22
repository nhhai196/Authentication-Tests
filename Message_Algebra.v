
Require Import Relation_Definitions Relation_Operators 
               Omega Arith ListSet FSetInterface.

(* ******************************************************* *)
(* VERSION 4 *)

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


(** * Texts *)
(** ** Definition *)
Variable Text : Set.

(** ** Decidable equality for texts *)
Variable eq_text_dec : forall (x y:Text), {x = y} + {x <> y}.
Hint Resolve eq_text_dec.

(*********************************************************************)

(** * Keys *)

(** Interesting design choices about keys. Here we do not model
   symmetric and asymmetric keys as separate types; the distinction is
   just different constructor/injections into the key type.
   Sometimes simpler.  Possible issue is with key inverses...?
*)

(** ** Definition *)
Variable Key : Set.

Parameter K_p : set Key.

(** ** Inverse relation for keys *)
Variable inv : relation Key.

(** ** Inv is commutative *)
Axiom inv_comm : forall k k', inv k k' -> inv k' k.

(** ** Decidable equality for keys *)
Variable eq_key_dec : forall (x y:Key), {x=y} + {x<>y}.
Hint Resolve eq_key_dec.

(*********************************************************************)

(** * Messages *)
(** ** Inductive  definition for messages *)
Inductive msg : Set :=
  | T : Text -> msg
  | K : Key -> msg
  | P : msg -> msg -> msg
  | E : msg -> Key -> msg.
Hint Constructors msg.

(** ** Decidable equality for messages *)
Definition eq_msg_dec : forall x y : msg,  
  {x = y} + {x <> y}.
Proof.
intros.
decide equality.
Qed.
Hint Resolve eq_msg_dec.

(** ** Sign messages *)
Inductive smsg := 
  | xmit_msg : msg -> smsg 
  | recv_msg : msg -> smsg.

Notation "+ m" := (xmit_msg m) (at level 30) : ma_scope.
Notation "- m" := (recv_msg m) : ma_scope.


(* Convert sign messages to messages *)
Definition smsg_2_msg (m : smsg) : msg :=
   match m with
   | (xmit_msg x) => x
   | (recv_msg  x) => x
   end.
Hint Resolve smsg_2_msg.

Definition eq_smsg_dec : forall (x y : smsg), {x=y} + {x<>y}.
Proof.
intros.
decide equality.
Qed.
Hint Resolve eq_smsg_dec.

(** ** Atomic messages *)
Inductive atomic : msg -> Prop := 
  |atomic_text : forall t, atomic (T t)
  |atomic_key : forall k, atomic (K k).
Hint Constructors atomic.

(** ** Concatenated messages *)
Inductive pair : (msg -> Prop) := 
  | pair_step : forall m1 m2, pair (P m1 m2).
Hint Constructors pair.

(** ** Encrypted messages *)
Inductive enc : msg -> Prop :=
  | enc_step : forall m k, enc (E m k).
Hint Constructors enc.

(** ** Basic messages *)
(** Treat basic as a predicate, not a subtype *)
Inductive basic : msg -> Prop :=
  | b_text : forall t, basic (T t)
  | b_key : forall k, basic (K k)  .
Hint Constructors basic.

(** ** Simple message *)
(** A message is simple if it is not a concatenated (paired) message *)
Inductive simple : msg -> Prop :=
  | simple_step : forall m, ~ pair m -> simple m.

Lemma enc_imp_simple : forall x k, simple (E x k).
Proof.
intros x k.
apply simple_step.
unfold not. intro Hpair.
inversion Hpair.
Qed.

(** ** Some basic results about atomic, paired, simple, and basic messages *)
Lemma pair_not_atomic :
  forall m, pair m -> ~ atomic m.
Proof.
unfold not.
intros m HConc HAtom.
inversion HConc; inversion HAtom; subst; discriminate.
Qed.

Lemma atom_not_pair:
  forall m, atomic m -> ~ pair m.
Proof.
unfold not.
intros m HAtom Hpair.
inversion Hpair; inversion HAtom; subst; discriminate.
Qed.

Lemma enc_not_basic : forall m1 m2, ~ basic (P m1 m2).
Proof.
unfold not.
intros m1 m2 HBasic.
inversion HBasic.
Qed.

Lemma atomic_imp_simple : forall a, atomic a -> simple a.
Proof.
intros a Hatom.
apply simple_step.
apply atom_not_pair; assumption.
Qed.

(*********************************************************************)

(** * Freeness assumptions about pair and encryption *)
(* Both of them are provable in this context *)

(** ** For pair *)
(** If two concatenated (or encrypted) messages are equal then each
component of the first is equal the corresponding componet of the second *)
Lemma pair_free : forall m1 m2 m1' m2', 
                 P m1 m2 = P m1' m2' -> m1 = m1' /\ m2 = m2'.
Proof.
intros m1 m2 m1' m2' HPeq.
injection HPeq. auto.
Qed.

(** ** For Encryption *)
Lemma enc_free : forall m k m' k',
                 E m k = E m' k' -> m = m' /\ k = k'.
Proof.
intros m k m' k' HEeq.
injection HEeq.
auto.
Qed.

(** * Ingredient.   Called "carried by" in some CPSA pubs. *)
(** ** Definition *)
Inductive ingred : msg -> msg -> Prop :=
| ingred_refl : forall m, ingred m m
| ingred_pair_l : forall m l r, 
    ingred m l -> ingred m (P l r)
| ingred_pair_r : forall m l r, 
    ingred m r -> ingred m (P l r)
| ingred_encr : forall m x k, 
    ingred m x -> ingred m (E x k).

Notation "a <st b" := (ingred a b) (at level 30) : ss_scope.

Open Scope ss_scope.

(** ** Properties *)
(** *** Transitive *)
Lemma ingred_trans : 
  forall x y z,  x <st y -> y <st z -> x <st z.
Proof.
intros x y z Sxy Syz.
induction Syz.
  subst; auto.
  subst; apply ingred_pair_l; apply IHSyz; assumption.
  subst; apply ingred_pair_r; apply IHSyz; assumption.
  apply ingred_encr; apply IHSyz; assumption.
Qed.
Hint Resolve ingred_trans.

(** *** Some other basic results about ingredients *)
Lemma ingred_pair : forall (x y z:msg), x <> (P y z) ->
                                  x <st (P y z) -> 
                                  x <st y \/ x <st z.
Proof.
intros x y z Hneq Hst.
inversion Hst; subst.
  elim Hneq; trivial.
  auto.
  auto.
Qed.
Hint Resolve ingred_pair.

Lemma ingred_enc : forall (x y :msg) (k:Key), x <> (E y k) ->
                                 x <st (E y k) ->
                                 x <st y.
Proof.
intros x y k Hneq Hst.
inversion Hst; subst.
  elim Hneq; trivial.
  auto.
Qed.
Hint Resolve ingred_enc.

(*********************************************************************)

(** * Size of messages *)
(** ** Definition *)
Fixpoint size (m:msg) :=
  match m with 
   | T t => 1
   | K k => 1 
   | P m1 m2 => (size m1) + (size m2)
   | E x k => (size x) + 1
   end.

(** Size of every message is always positive *)
Lemma zero_lt_size : forall x, 0 < size x.
Proof.
intro x.
induction x; simpl; omega.
Qed.
Hint Resolve zero_lt_size.

Lemma size_lt_plus_l : forall x y, size x < size x + size y.
Proof.
intros x y.
assert (size x + 0 < size x  + size y).
apply plus_lt_compat_l. apply zero_lt_size.
rewrite (plus_comm (size x) 0) in H.
rewrite (plus_O_n (size x)) in H. auto. 
Qed.

(** ** Realtionship between ingredient and size *)

(** Size of an ingredient x is always less than or equal
 size of message y if x is an ingredient of y. *)
Lemma ingred_lt : 
  forall x y, x <st y -> size(x) <= size(y).
Proof. 
intros x y Hst.
induction Hst; subst; simpl; omega.
Qed.

Lemma ingred_ge_size_eq : 
  forall x y, x <st y -> size(x) >= size(y) -> x=y.
Proof.
intros x y Hst Hsize_gt.
inversion Hst; subst.
  auto.

  assert (Hx_lt_l : size x <= size l). apply ingred_lt; auto.
   assert (Hl_lt_Plr : size l < size (P l r)).
     simpl. apply size_lt_plus_l.
   assert (Hx_lt_Plr : size x < size (P l r)). omega.
   contradict Hsize_gt. omega.

  assert (Hx_lt_r : size x <= size r). apply ingred_lt; auto.
   assert (Hl_lt_Plr : size r < size (P l r)).
     simpl. rewrite <- (plus_comm). apply size_lt_plus_l.
   assert (Hx_lt_Plr : size x < size (P l r)). omega.
   contradict Hsize_gt. omega.

  assert (Hx_lt_l : size x <= size x0). apply ingred_lt; auto.
   assert (Hx0_lt_E : size x0 < size (E x0 k)).
     simpl. omega.
   assert (Hx_lt_E : size x < size (E x0 k)). omega.
   contradict Hsize_gt. omega.
Qed.
Hint Resolve ingred_ge_size_eq.

(** If each message is an ingredient of each other,
then they are equal *)
Lemma ingred_eq : forall (x y :msg), x <st y -> y <st x -> x = y.
Proof.
intros x y Hxy Hyx.
apply ingred_ge_size_eq. 
auto.
apply ingred_lt; auto.
Qed.
Hint Resolve ingred_eq.

Lemma atomic_ingred_eq : 
   forall x a, atomic a -> ingred x a -> x=a.
Proof.
intros x a Hat Hin.
inversion Hat; subst; inversion Hin; auto.
Qed.
Hint Resolve atomic_ingred_eq.

(*********************************************************************)

(** * Component *)
(** Intuitively, a message x is a component of a message m 
if we can get x just by seperation out all the pairs in m, 
without using decryption *)

(** ** Component of a message *)
(** A message t0 is an e-ingredients of message t
if t is in the smallest set containing t0 and closed 
under concatenation with arbitrary term t1, i.e,
if t0 is an atomic value of t *)
Inductive e_ingred : relation msg := 
  | e_ingred_refl : forall (t0:msg), e_ingred t0 t0
  | e_ingred_pair_l : forall t0 t1 t2, 
      e_ingred t0 t1 -> e_ingred t0 (P t1 t2)
  | e_ingred_pair_r : forall t0 t1 t2,
     e_ingred t0 t2 -> e_ingred t0 (P t1 t2).
Hint Constructors e_ingred.

Inductive comp : relation msg :=
  | comp_step : forall m1 m2, 
                simple m1 -> e_ingred m1 m2 -> comp m1 m2.
Notation "a <com b" := (comp a b) (at level 30) : ss_scope.
Hint Constructors comp.

(** ** Component implies ingredient *)
Lemma e_ingred_imp_ingred : forall m1 m2, e_ingred m1 m2 -> ingred m1 m2.
Proof.
intros m1 m2 Hein.
induction Hein; subst.
  apply ingred_refl.
  apply ingred_pair_l; assumption.
  apply ingred_pair_r; assumption.
Qed.

Lemma comp_imp_ingred : forall (m1 m2:msg), m1 <com m2 -> m1 <st m2.
Proof.
intros m1 m2 Hcom.
apply e_ingred_imp_ingred.
inversion Hcom; subst; assumption.
Qed.

(** ** Concatenation or pairing preserves components *)
(** If a message x is a component an other message m1,
it also is a component of every message which is concatenated from
m1 and an abitrary message m2 *)
Lemma preserve_comp_l : forall x m1 m2, comp x m1 -> comp x (P m1 m2).
Proof. 
intros x m1 m2 Hcom.
inversion Hcom; subst.
apply comp_step.
 auto.
 apply e_ingred_pair_l; assumption.
Qed.

Lemma preserve_comp_r : forall x m1 m2, comp x m2 -> comp x (P m1 m2).
Proof. 
intros x m1 m2 Hcom.
inversion Hcom; subst.
apply comp_step.
 auto.
 apply e_ingred_pair_r; assumption.
Qed.

(** ** An atomic message is a component of itself *)
Lemma comp_atomic_cyclic : forall a, atomic a -> comp a a.
Proof.
intros a Hatom.
constructor. 
  apply atomic_imp_simple; assumption.
  apply e_ingred_refl.
Qed.

(** ** A simple message is a component of itself *)
Lemma comp_simple_cyclic : forall a, simple a -> comp a a. 
Proof.
intros a Hsim.
constructor; [assumption |constructor].
Qed. 

(*********************************************************************)
  
(** * K-ingredients *)
Section K_relation.
(** A message t0 is an k-ingredients of message t
if t is in the smallest set containing t0 and closed 
under encryption and concatenation with arbitrary term t1, i.e,
if t0 is an atomic value of t *)
Variable F : Set.
Parameter inj_F_K : F -> Key.
Axiom inj_F_K_inj : forall x y : F, inj_F_K x = inj_F_K y -> x = y.
Coercion inj_F_K : F >-> Key.
Inductive k_ingred : relation msg := 
  | k_ingred_refl : forall (t0:msg), k_ingred t0 t0
  | k_ingred_pair_l : forall (t0 t1 t2 : msg), 
      k_ingred t0 t1 -> k_ingred t0 (P t1 t2)
  | k_ingred_pair_r : forall (t0 t1 t2 : msg),
     k_ingred t0 t2 -> k_ingred t0 (P t1 t2)
  | k_ingred_enc : forall (t0 t1 : msg) (k : F),
     k_ingred t0 t1 -> k_ingred t0 (E t1 k).
Hint Constructors k_ingred.
End K_relation.
Variable A : Set.
Variable B : A -> Key.
Variable m1 m2 : msg.
