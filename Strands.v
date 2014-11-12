(* Time-stamp: <Fri 10/17/14 10:52 Dan Dougherty Strands.v> *)

(* TO FIX:

 - better name for "path", "is_path", ...

 - can we avoid the default-value trick in the "ith" function?

*)
(* Things to learn how to do:

 1) once you prove "exists x, blah(x)"
    how to introduce, in a Section, a named Variable
    satifying blah, to use>

 2) How to extract minimum elements for a predicate?  Ie. would like a
    function from inhabited predicates to nodes, rturning minimal
    nodes.
*)

(* Add LoadPath "./". *)
(* Add LoadPath "./Classical_Wf". *)
Require Import Classical.
Require Import Message_Algebra.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Omega.

(** * The signature (vocabulary) for the models *)
(*  *************************************** *)

Variable node : Set. 
Variable strand : Set.
Variable role : Set.
Variable xmit : node -> Prop.
Variable recv : node -> Prop.
Variable msg_of : node -> msg.  
Variable msg_deliver : node -> node -> Prop.
Variable ssucc : node ->  node -> Prop.
Variable regular_strand : set strand.
Variable penetrable_strand : set strand.
Variable strand_of: node -> strand. 

(* not needed here...do it in protocol specs *)
(* Variable role_of: strand -> role.   (** maybe should be a relation *) *)
(* Variable strand_of: node -> strand. *)



(** * Some defined notions *)
(*  ************************ *)

(** *** Predecessor along a strand *)
Definition spred : node -> node -> Prop := fun x y => ssucc y x.

(** *** Strand-predecessor or message-deliver *)
Definition prec_generator : node -> node -> Prop  := 
  fun n m => ssucc n m \/ msg_deliver n m.


(** *** Transitive closures *)
(*  ------------------- *)

(* Transitive closure of strand-successor *)
Inductive ssuccs (x z: node) : Prop :=
  | ssuccs_step : ssucc x z -> ssuccs x z
  | ssuccs_trans (y': node) : ssucc x y'-> ssuccs y' z  -> ssuccs x z.


(* Transitive closure of strand-predecessor *)
Inductive spreds (x z: node) : Prop :=
  | spreds_step : spred x z -> spreds x z
  | spreds_trans (y': node) : spred x y'-> spreds y' z  -> spreds x z.

(* Transitive closure of (ssucc \/ msg_deliver) *)
Inductive prec (x z: node) : Prop :=
  | prec_ssucc_step : ssucc x z -> prec x z
  | prec_msg_step :  msg_deliver x z -> prec x z
  | prec_ssucc_trans (y': node) : ssucc x y'-> prec y' z  -> prec x z
  | prec_msg_trans (y': node) : msg_deliver x y'-> prec y' z  -> prec x z.


(** *** Reflexive-Transitive closures *)
(*  ---------------------------- *)

(* Reflexive_Transitive closure of strand-successor *)
Inductive ssuccseq (x z: node) : Prop :=
  | ssuccseq_refl : x = z -> ssuccseq x z
  | ssuccseq_trans : ssuccs x z -> ssuccseq x z.

(* Reflexive_Transitive closure of strand-predecessor *)
Inductive spredseq  (x z: node) : Prop :=
  | spredseq_refl : x = z -> spredseq x z
  | spredseq_trans : spreds x z -> spredseq x z.

(* Reflexive_Transitive closure of (ssucc \/ msg_deliver) *)
Inductive preceq  (x z: node) : Prop :=
  | preceq_refl : x = z -> preceq x z
  | preceq_trans : prec x z -> preceq x z.


(** Minimal nodes *)

Definition is_minimal: (node -> Prop) -> node -> Prop :=
  fun P x => (P x) /\ forall y, (prec y x) -> ~( P y).

Definition has_min_elt: (node -> Prop) -> Prop :=
  fun P  =>   exists x:node, is_minimal P x.


(** *** Origination *)

Definition orig_at : node -> msg -> Prop :=
  fun (n:node) (m:msg) =>
    xmit(n) /\  (ingred m (msg_of n)) /\
    (forall (n':node), ( (ssuccs n' n) -> 
      (ingred m (msg_of n')) ->
        False)).

Definition non_orig : msg -> Prop :=
  fun (m:msg) =>
    forall (n:node), ~orig_at n m.

Definition unique : msg -> Prop :=
  fun (m:msg) =>
    (exists (n:node), orig_at n m) /\
    (forall  (n n':node),
      (orig_at n m) /\ (orig_at n' m) ->
      n=n').



(* (*  Need this? *) *)

(* Definition sent_by : node -> msg -> Prop :=  *)
(*   fun (n: node) (m: msg) => *)
(*     exists (n' :node) , (preceq n' n) /\ (msg_of n') = m. *)


(** ** Decidable equality *)
(*  ---------------------------  *)

(** Q: what's the difference between Variable and Axiom here? %\\%
*)
Variable eq_msg_dec : forall x y : msg, {x = y} + {x <> y}.
Hint Resolve eq_msg_dec.
Variable eq_node_dec : forall x y : node, {x = y} + {x <> y}.
Hint Resolve eq_node_dec.
Variable eq_strand_dec : forall x y : strand, {x = y} + {x <> y}.
Hint Resolve eq_strand_dec.



(** * Axioms *)
(*  ******** *)

(** ** xmit and recv *)

(** no node is both transmit and receive %\\% *)
Axiom xmit_vs_recv: forall (n:node),  xmit(n) /\ recv(n) -> False.

(** every  node is either transmit or receive %\\% *)
Axiom xmit_or_recv: forall (n: node), xmit n \/ recv n.

(** strand-successor is irreflexive %\\% *)
Axiom ssucc_not_ref: forall (n:node),  ssucc n n -> False.

(** strand-successors are unique %\\% *)
Axiom ssucc_partial_fun: 
  forall (n n1 n2: node),  ssucc n n1 /\ ssucc n n2  -> n1 = n2.

(** Freeness for pairing and encryption *)
Axiom pair_freeness : 
  forall m1 m2 m1' m2', P m1 m2 = P m1' m2' ->
                        m1 = m1' /\ m2 = m2'.

Axiom enc_freeness : 
  forall h1 h2 k1 k2, E h1 k1 = E h2 k2 -> h1 = h2 /\ k1 = k2.


(** ** Message-delivery relation *)
(*  ---------------------------  *)

(** *** Messages match *)
Axiom msg_deliver_ax :
    forall x y : node, (msg_deliver x y) -> 
    (xmit x /\ recv y /\ msg_of x = msg_of y).

(** *** The bundle axiom: every received  message was sent  *)
Axiom was_sent : forall x : node, (recv x) -> 
                (exists y : node,  msg_deliver y x).

(** ** Well-foundedness *)

(* Better would be to just postulate well_founded for (ssucc \/ msg-deliver)
*)
Axiom wf_prec: well_founded prec.


(** * Theorems *)
(*  ********** *)

(** ** Baby results about xmit and recv *)

Lemma xmit_not_recv: forall n, xmit n -> ~(recv n).
Proof.
intros.
unfold not.
intros.
apply xmit_vs_recv with (n:=n).
tauto.
Qed.

Lemma recv_not_xmit: forall n, recv n -> ~(xmit n).
Proof.
intros n0 H0 H.
apply xmit_vs_recv with (n:=n0).
tauto.
Qed.

Lemma not_xmit_recv: forall n,  ~(xmit n) -> (recv n).
Proof.
unfold not.
intro.
assert (a1: (xmit n \/ recv n)).
exact (xmit_or_recv n).
tauto.
Qed.

Lemma not_recv_xmit: forall n,  ~(recv n) -> (xmit n).
Proof.
unfold not.
intro.
assert (a1: (xmit n \/ recv n)).
exact (xmit_or_recv n).
tauto.
Qed.

(** ** Baby results about prec *)

Theorem prec_transitive:
  forall x y z, (prec x y) -> (prec y z) -> (prec x z).
Proof.
intros.
induction H.
eapply (prec_ssucc_trans). apply H.
auto.

eapply (prec_msg_trans). apply H.
auto.

eapply (prec_ssucc_trans). 
apply H.
auto.
eapply (prec_msg_trans).
apply H.
auto.
Qed.

Lemma deliver_prec:
  forall n0 n1, (msg_deliver n0 n1) -> (prec n0 n1).
Proof.
intros.
apply prec_msg_step; auto.
Qed.

Lemma ssucc_prec:
  forall n0 n1, (ssucc n0 n1) -> (prec n0 n1).
Proof.
intros.
apply prec_ssucc_step; auto.
Qed.


Lemma ssuccs_prec:
  forall n0 n1, (ssuccs n0 n1) -> (prec n0 n1).
Proof.
intros.
induction H.
apply ssucc_prec; auto.
assert (prec x y').
apply ssucc_prec; auto.
apply prec_transitive with (y:=y'); auto.
Qed.


(** ** Baby results about origination
   Some of these would be axioms, in a first-order axiomatization 
*)

(* (these are ugly proofs, I'm just flailing around) :*) 

Lemma
  orig_is_sent :
  forall (n : node) (m : msg), orig_at n m ->  (ingred m (msg_of n)).

Proof.
unfold orig_at.
tauto.
Qed.

Lemma
  non_not_originate :
    forall (n : node) (m : msg), non_orig m -> orig_at n m -> False.
Proof.
intros n0 m0 H0.
unfold non_orig in H0.
intros H1.
unfold orig_at in H1.
destruct H1.
destruct H1.
assert (a0: orig_at n0 m0).
unfold orig_at.
auto.
assert (na0: ~ (orig_at n0 m0)).
apply H0.
tauto.
Qed.


Lemma
  unique_only_once :
    forall (m : msg) (n n' : node),
    unique m -> orig_at n m -> orig_at n' m -> n = n'.
Proof.
intros.
unfold unique in  H.
destruct H.
apply H2.
tauto.
Qed.

Lemma
  orig_not_sent_earlier :
    forall (n n' : node) (m : msg),
    (orig_at n m) ->  (ssucc n' n) ->  (ingred m (msg_of n')) -> False.
Proof.
intros n0 n'0 m0 H0.
intros H1.
intros H2.
unfold orig_at in H0.
destruct H0.
destruct H0.
apply (H3 n'0).
apply (ssuccs_step); auto.
auto.
Qed.

Lemma
  unique_does_originate :
    forall m : msg, unique m -> exists n : node, orig_at n m.
Proof.
intros.
unfold unique in H.
destruct H.
destruct H.
exists x. auto.
Qed.

Lemma msg_deliver_prec:
  forall n0 n1, (msg_deliver n0 n1) -> (prec n0 n1).
Proof.
intros.
apply prec_msg_step; auto.
Qed.

(** ** Every inhabited predicate has a prec-minimal element *)
Theorem always_min_elt :  forall P: node-> Prop, 
    (exists (x:node), (P x)) -> has_min_elt P.
Proof.
intros.
destruct H.
revert x H.
unfold has_min_elt.
unfold is_minimal.
apply (@well_founded_ind node prec (wf_prec)
 (fun x:node =>
  P x -> exists y:node, P y /\ (forall z:node, prec z y  ->   ~ (P z) ))).
intros.
case (classic (forall y:node, P y -> ~ prec y x)).
intros.
exists x.
split.
auto.
intros.
assert (a2: P z -> ~ prec z x).
apply H1.
tauto.
intros.
apply not_all_ex_not in H1.
destruct H1.
apply imply_to_and in H1.
destruct H1.
apply NNPP in H2.
apply H with (y:=x0).
assumption.
assumption.
Qed.


(** ** prec is acyclic *)

Theorem prec_is_acyclic: forall (x:node), (prec x x) -> False.
Proof.
intros x H.
assert (has_min_elt (fun x => prec x x )).
apply always_min_elt.
exists x;  auto.
unfold has_min_elt in H0.
destruct H0.
destruct H0.
assert (prec x0 x0 -> ~ prec x0 x0 ).
apply H1.
tauto.
Qed.


(** * Ingredients must originate *)

Section IngredientsOriginate.

Variable the_m: msg.
Definition m_ingred (n: node): Prop := ingred the_m (msg_of n).

(** If m is an ingredient somewhere then there is a minimal such place *)

Lemma 
  ingred_min:
  (exists n:node,  (m_ingred n)) ->
  (exists n:node, (is_minimal m_ingred n)).
Proof.  
intros H.
apply always_min_elt; auto.
Qed.


(** A minimal node can't be a reception *)

Lemma
  minimal_not_recv:
  forall (n:node), (is_minimal m_ingred n) ->
    ~ (recv n).
Proof.
unfold not.
intros.
unfold is_minimal in H.
destruct H.
assert (a1: exists n1, msg_deliver n1 n).
apply was_sent; auto.

destruct a1.
assert (a2: prec x n).
apply deliver_prec; auto.

assert (a3: ~(m_ingred x)).
apply H1; auto.
assert (a4: m_ingred x).

assert (a5: msg_of x = msg_of n).
apply msg_deliver_ax; auto.
unfold m_ingred.
unfold m_ingred in H.
rewrite a5; auto.
tauto.
Qed.

(** So, a minimal node must be a transmission *)

Lemma minimal_is_xmit:   forall (n:node), (is_minimal m_ingred n) ->
  (xmit n).
Proof.
intros.
apply not_recv_xmit.
apply minimal_not_recv; auto.
Qed.



(** Main result of this section: an ingredient must originate *)

Theorem
  ingred_originates_2:
    (exists n:node, (ingred the_m (msg_of n))) ->
    (exists n:node, (orig_at n the_m)).
Proof.
intros.
assert (a1: has_min_elt m_ingred).
apply always_min_elt.
unfold m_ingred; auto.
unfold orig_at.
unfold has_min_elt in a1.
destruct a1.
assert (a0: xmit x).
apply minimal_is_xmit; auto.

unfold m_ingred in H0.
unfold is_minimal in H0.
destruct H0.
exists x.
split.
auto.
split.
auto.
intros.
assert (a1: prec n' x).
apply ssuccs_prec; auto.
revert H3.
unfold not in H1.
apply H1; auto.
Qed.

End IngredientsOriginate.

(** * New Component *)
(** ** Component of a node *)
(** A message is a component of a node if it is a component 
of the message at that node *)
Definition comp_of_node : msg -> node -> Prop :=
  fun (m:msg) (n:node) => comp m (msg_of n). 
Notation "x <[node] y" := (comp_of_node x y) (at level 50) : ss_scope.

Lemma msg_deliver_comp : 
  forall (n1 n2:node) (m:msg),
  msg_deliver n1 n2 /\ 
  comp_of_node m n2 -> comp_of_node m n1.
Proof.
intros.
destruct H as (H1,H2).
unfold comp_of_node.
assert (msg_of n1 = msg_of n2).
apply msg_deliver_ax. auto.
rewrite H.
unfold comp_of_node in H2. auto.
Qed.
Hint Resolve msg_deliver_comp.

Lemma comp_of_node_imp_ingred : 
  forall (m:msg) (n:node), m <[node] n -> m <st (msg_of n).
Proof.
intros.
unfold comp_of_node in H.
apply comp_imp_ingred.
assumption.
Qed.

(** ** New at *)
(** A message is new at a node if it is a component of that node
and the message is not a component of any ealier node in the same 
strand with the node *)
Definition new_at : msg -> node -> Prop :=
  fun (m : msg) (n : node) => 
  m <[node] n /\ 
  forall (n' : node) , ssuccs n' n -> m <[node] n'-> False.

Lemma new_at_imp_comp : forall m n, new_at m n -> m <[node] n.
Proof.
intros m n H.
unfold new_at in H.
apply H.
Qed.

Lemma not_new_exists : 
  forall n L, L <[node] n -> ~ new_at L n ->
  exists n', ssuccs n' n /\ L <[node] n'.
Proof.
unfold not.
intros n L Hcom Hnnew.
apply Peirce. intros.
apply False_ind. apply Hnnew.
unfold new_at. split.
  assumption.
  intros n' Hssucc Hcomn'.
    apply H. exists n'.
      split; auto.
Qed.

(** * Path *)
(** ** Path condition *)
Inductive path_cond (m n : node) : Prop :=
  | path_cond_single :  msg_deliver m n -> path_cond m n
  | path_cond_double : ssuccs m n /\ 
                            recv(m) /\ 
                            xmit(n) -> 
                            path_cond m n.
Hint Constructors path_cond.
Notation "m |--> n" := (path_cond m n) (at level 30) : ss_scope.

(** ** Path condition implies prec *)
Lemma path_imp_prec : 
  forall (m n:node), m |--> n -> prec m n.
Proof.
intros.
apply path_cond_ind with (m:=m) (n:=n).
apply deliver_prec.
intros.
apply ssuccs_prec. apply H0.
auto.
Qed.

(** MAYBE WE CAN AVOID THIS?? *)
Variable default_n : node. 

(** ** ith node of a path *)
Definition nth_node : nat -> list node -> node :=
  fun (n:nat) (p:list node) => nth n p default_n.
Hint Resolve nth_node.

(** ** Axioms for paths *)
Definition is_path : list node -> Prop :=
  fun  (p: list node) => forall (n : nat), 
    n < length(p) - 1 -> 
    path_cond (nth_node n p ) (nth_node (n+1) p ).

(** ** Axiom for paths *)
(** All paths begin on a positive node and end on a negative node *)
Axiom path_begin_pos_end_neg : forall (p : list node),
  is_path p -> xmit(nth_node 0 p) /\ recv(nth_node (length p - 1)  p).

(** * Transformation path *)
Variable default_msg : msg.
Definition nth_msg : nat -> list msg -> msg :=
  fun (n:nat) (p:list msg) => nth n p default_msg.
Hint Resolve nth_msg.

Definition is_trans_path : list (prod node msg)->Prop := 
  fun (p:list (prod node msg)) => 
    let ln := fst (split p) in 
    let lm  := snd (split p) in
      (is_path ln \/ (ssucc (nth_node 0 ln) (nth_node 1 ln) /\ 
                     xmit (nth_node 0 ln) /\ 
                     xmit (nth_node 1 ln) /\
                     is_path (tl ln))) /\
      forall (n:nat),   
      (n < length p -> (nth_msg n lm) <[node] (nth_node n ln)) /\
      (n < length p - 1 ->
        let L1 := nth_msg n lm in 
        let L2 := nth_msg (n+1) lm in 
        let n1 := nth_node n ln in 
        let n2 := nth_node (n+1) ln in
          (L1 = L2 \/ (ssuccs n1 n2 /\ new_at L2 n2))).
Print is_trans_path.

(* Baby result : a single pair (n, L) is a trans-foramtion path *)
Lemma anode_trans_path : 
  forall (n:node) (t:msg), 
  comp_of_node t n -> is_trans_path (cons (n,t) nil).
Proof.
intros n t Hcom.
unfold is_trans_path.
simpl. split.
  left. constructor. simpl in H.
    apply False_ind; omega.
   intros n1; split.
     intro Hn1_lt. assert (n1=0). omega. subst. apply Hcom.
     intros Hn1_lt. apply False_ind. omega.
Qed.      

(** * Proposition 11 *)
(** For every atomic ingredient of a message, there exists 
a component of the message such that the atomic value is 
an ingredient of that component *)
Lemma ingred_exists_comp: 
  forall m a, atomic a -> a <st m -> exists L, a <st L /\ comp L m.
Proof.
intros m a Hatom Hingred.
induction m.
exists a; split.
  constructor.
  assert (a = T t). apply atomic_ingred_eq; auto. 
    subst. apply comp_atomic_cyclic; assumption.

exists a; split.
  constructor.
  assert (a = K k). apply atomic_ingred_eq; auto.
    subst. apply comp_atomic_cyclic; assumption.

assert (Hor : ingred a m1 \/ ingred a m2).
  apply ingred_pair. inversion Hatom; discriminate.
  assumption.
  case Hor.
    intro Hst.
    assert (Hex : exists L : msg, ingred a L /\ comp L m1).
    exact (IHm1 Hst). destruct Hex as (L, (HaL, Hcom)).
    exists L; split.
      assumption.
      apply preserve_comp_l; assumption.

    intros Hst.
        assert (Hex : exists L : msg, ingred a L /\ comp L m2).
    exact (IHm2 Hst). destruct Hex as (L, (HaL, Hcom)).
    exists L; split.
      assumption.
      apply preserve_comp_r; assumption.

assert (Hex : exists L : msg, a <st L /\ L <com m).
  apply IHm. apply ingred_enc with (k:=k).
    inversion Hatom; discriminate.
    assumption.
    destruct Hex as (L, (HaL, Hcom)).
  exists (E m k); split.
    assumption.
    apply comp_simple_cyclic.
      apply simple_step. unfold not. intros Hpair.
        inversion Hpair.
Qed.


Lemma ingred_exists_comp_of_node: 
  forall (n:node) (a:msg), atomic a -> a <st (msg_of n) 
                        -> exists L, a <st L /\ L <[node] n.
Proof.
intros.
apply ingred_exists_comp; assumption.
Qed.

Lemma ingred_of_earlier : 
  forall (n:node) (a:msg), 
   (~ orig_at n a) /\ xmit n /\ ingred a (msg_of n) -> 
   exists n', ssuccs n' n /\ ingred a (msg_of n').
Proof.
intros.
apply Peirce.
intros.
apply False_ind.
unfold not in H.
destruct H as (H1, (H2, H3)).
apply H1. unfold orig_at.
split. auto. split. auto.
intros. apply H0.
exists n'.
split; auto.
Qed.

(** Backward construction *)
Lemma backward_construction : 
  forall (n:node) (a L:msg), 
    atomic a -> L <[node] n -> ~ orig_at n a -> a <st L ->
    exists (n':node) (L':msg), 
      (msg_deliver n' n \/ ssuccs n' n) /\ a <st L' /\ L' <[node] n' /\ 
      (L' = L \/ (ssuccs n' n /\ new_at L n)).
Proof.
intros n a L Hatom Hcom Hnorig Hst.
assert (Hx_r : xmit n \/ recv n). apply xmit_or_recv.
case Hx_r.
  Focus 2. intros Hrecv.
    assert (Hex : exists (n':node), msg_deliver n' n). 
    apply was_sent. auto.
    destruct Hex as (n', Hmsg_deli).
    exists n'; exists L.
      split. left; auto.
      split. exact Hst.
      split. apply msg_deliver_comp with (n1:=n') (n2:=n).
      split; assumption.
      left. trivial.  

  intros Hxmit.
  assert (Hdec : new_at L n \/ ~(new_at L n)). tauto.
  case Hdec.
    intros Hnew. 
    assert (Hex2 :exists n1, ssuccs n1 n /\ ingred a (msg_of n1)).
    apply ingred_of_earlier. repeat split; auto.
    apply ingred_trans with (y:=L). 
      assumption.
      apply comp_of_node_imp_ingred; assumption.
    destruct Hex2 as (n1, (Hssucc, Hastn1)).
    assert (HexL1 : exists L1, ingred a L1 /\ comp_of_node L1 n1).
      apply ingred_exists_comp_of_node; assumption.
      destruct HexL1 as (L1, (H1, H2)).
    exists n1; exists L1.
      split. right. assumption.
      split. assumption.
      split. assumption.
      right. split; auto.

  intros Hnnew.
  assert (Hex : exists n', ssuccs n' n /\ L <[node] n').
    apply not_new_exists; auto.
  destruct Hex as (n', (Hssucc, Hn)).
  exists n'; exists L.
    split. right. auto.
    split. auto.
    split. assumption.
    left; trivial.
Qed.

Definition Prop11 : node -> Prop := 
  fun (n':node) => 
  forall (a t:msg), 
  atomic a -> a <st t /\ t <[node] n' -> 
  exists p, let ln := fst (split p) in 
            let lm := snd (split p) in 
            is_trans_path p /\ 
            orig_at (nth_node 0 ln) a /\
            nth_node (length p - 1) ln = n' /\ 
            nth_msg (length p -1) lm = t /\
            forall (i:nat), i < length p -> a <st (nth_msg i lm).
              
(* The main result *)
Lemma proposition11 : 
  forall (n':node), Prop11 n'.
Proof.
apply well_founded_ind with (R:=prec).
exact wf_prec.
intros.
unfold Prop11.
unfold Prop11 in H.
intros.
destruct H1 as (H1, H2).
assert (orig_at x a \/ ~ orig_at x a). tauto.
case H3.
  intros.
  exists (cons (x, t) nil).
  simpl. split.
    apply anode_trans_path with (n:=x) (t:=t). exact H2.
    split; auto; split; auto; split; auto.
  intros.
    assert (i=0). omega.
    rewrite H6;auto.

  intros.
  assert (Hex : exists (n':node) (L':msg), 
      (msg_deliver n' x \/ ssuccs n' x) /\ a <st L' /\ L' <[node] n' /\ 
      (L' = t \/ (ssuccs n' x /\ new_at t x))).
  apply backward_construction; assumption.
  destruct Hex as (n', (L', (Hor, (Hst, (Hcom, Hlast))))).
  assert (IH : forall a t : msg,
    atomic a ->
    a <st t /\ t<[node]n' ->
    exists p : list (node * msg),
      is_trans_path p /\
      orig_at (nth_node 0 (fst (split p))) a /\
      nth_node (length p - 1) (fst (split p)) = n' /\
      nth_msg (length p - 1) (snd (split p)) = t /\
      (forall i : nat, i < length p -> a <st nth_msg i (snd (split p)))).
  apply H with (y:= n'). case Hor.
    apply msg_deliver_prec.
    apply ssuccs_prec.
  assert (Hex2 : exists p : list (node * msg),
      is_trans_path p /\
      orig_at (nth_node 0 (fst (split p))) a /\
      nth_node (length p - 1) (fst (split p)) = n' /\
      nth_msg (length p - 1) (snd (split p)) = L' /\
      (forall i : nat, i < length p -> a <st nth_msg i (snd (split p)))).
    apply IH. assumption. split; assumption.
  destruct Hex2 as (p0, (Hex2, (Hex3, (Hex4, (Hex5, Hex6))))).
  assert (orig_at n' a \/ ~orig_at n' a). tauto.
  case H5.
    intro Horign'.
      exists ((n', L')::(x,t)::nil). simpl.
        split. admit.
        split. auto.
        split. auto.
        split. auto.
        intros. assert (i=0 \/ i=1). omega.
          case H7. 
            intro. subst; auto.
            intro; subst; auto.
    intro Hnorig.
      exists (p0++(n',L')::nil).
Admitted.

