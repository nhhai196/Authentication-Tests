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



(** * Working: extracting a minimal elelment *)


(* Section ExtractingMins. *)

(* Require Import IndefiniteDescription. *)

(* Variable P : node -> Prop. *)

(* Variable assm: exists (x:node) ( P:node->Prop),  P x. *)

(* (* Check assm. *) *)

(* (* Check functional_choice. *) *)

(* (* Check constructive_indefinite_description. *) *)

(* Definition prec_description :=  *)
(*  fun (P: node -> Prop) =>  *)
(*  constructive_indefinite_description  P. *)

(* (* Check prec_description. *) *)


(* Definition get_min (P : node -> Prop) := *)
(*    constructive_indefinite_description  P. *)


(* End ExtractingMins. *)


(* 
Notation " x [= y " := (ingred x y) (at level 50).
(** printing [= $\sqsubseteq$ *) 

Notation "x ~> y" := (msg_deliver x y) (at level 50).
(** printing ~> $\leadsto$ *) 

Notation " x ==> y " := (ssucc x y) (at level 50).
(** printing ==> $\Rightarrow$ *) 

Notation " x << y " := (prec x y) (at level 50).
(** printing << $\prec$ *) 

Notation " x ==>> y " := (ssuccseq x y) (at level 50).
(** printing ==>> $\Rightarrow^*$ *) 

Notation " x <<= y " := (preceq x y) (at level 50).
(** printing <<= $\preceq$ *) 

*)

(** * Induction *) 
Theorem induct_ok : 
  forall (P:node -> Prop), 
    (forall (x:node), (forall (y:node), prec y x -> P y) -> P x) -> 
                      forall (x:node), P x.
Proof.
(* Check well_founded_ind. *)
apply well_founded_ind.
exact wf_prec.
Qed.

(** ***Penetrable keys and safe keys *)

(** Notion of component *)

Definition comp : msg -> msg -> Prop :=
  fun (m0 : msg ) (m :msg) => 
    ingred m0 m /\ 
    ~(concat m0)  /\
    (forall (m1 : msg), (m0 <> m1) /\ 
   (ingred  m0 m1) /\ (ingred m1 m) -> (concat m1)).

(* Basic result about component *)
(* QUESTION : is key atomic?*)
Lemma comp_atom_or_enc : 
  forall m1, (exists m2, comp m1 m2) -> is_atomic m1 \/ is_enc m1.
Proof.
Admitted.


(* *** Component of a node : say t is a component 
of a node n if t is a component of msg_of (n) *)
Definition comp_of_node : msg -> node -> Prop :=
  fun (m : msg) (n : node) => comp m (msg_of n).

(* Basic results *)
Lemma comp_imp_ingred : forall (m1 m2:msg), comp m1 m2 -> ingred m1 m2.
Proof.
intros.
unfold comp in H.
apply H.
Qed.

Lemma comp_of_node_imp_ingred : 
  forall (m:msg) (n:node), comp_of_node m n -> ingred m (msg_of n).
Proof.
intros.
unfold comp_of_node in H.
apply comp_imp_ingred.
assumption.
Qed.

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

(* *** New at : A message msg is new at a node n = <s,i> 
if t is a component of msg_of(n) and
t is not a component of any node <s,j> for every j < i *)
Definition new_at : msg -> node -> Prop :=
  fun (m : msg) (n : node) => 
  comp_of_node m n /\ 
  forall (n' : node) , ssuccs n' n -> (comp_of_node m n')-> False.

Lemma new_at_imp_comp : forall m n, new_at m n -> comp_of_node m n.
Proof.
intros.
unfold new_at in H.
apply H.
Qed.

Variable LL : msg.
Definition m_comp (n:node):Prop := comp_of_node LL n.

(* Every component has to be new at some where *)
Theorem comp_new_at :
  forall (n:node), comp_of_node LL n ->
                           exists (n:node), new_at LL n.
Proof.
intros.
assert (a1: has_min_elt m_comp).
apply always_min_elt.
exists n; unfold m_comp; auto.
unfold new_at.
unfold has_min_elt in a1.
destruct a1.
unfold m_comp in H0.
unfold is_minimal in H0.
destruct H0.
exists x.
split.
auto.
intros.
unfold not in H1.
apply H1 with (y:=n').
apply ssuccs_prec; auto.
assumption.
Qed.

(** Transfroming edge *) 
(* Should we define edge first, 
then transforming edge : msg -> edge -> Prop *)
Definition transforming_edge : msg -> node -> node -> Prop :=
  fun (m: msg) (n1 n2 : node) =>  
  ssuccs n1 n2 /\ 
  recv (n1) /\ 
  xmit(n2) /\
  (ingred m (msg_of n1)) /\
  (exists t2, new_at t2 n2 /\ ingred m t2).
(* Similarly for transformed edge *)
Definition transformed_edge : msg -> node -> node -> Prop :=
  fun (m: msg) (n1 n2 : node) => 
  ssuccs n1 n2 /\ 
  xmit (n1) /\ 
  recv(n2) /\
  ingred m (msg_of n1) /\
  exists t2, new_at t2 n2 /\ ingred m t2.
Check (list node).

(** Regular node *)
Definition regular_node : node -> Prop :=
  fun (n : node) => exists s, set_In s regular_strand /\ s = strand_of n.

(** Penetrator node *)
Definition penetrator_node : node -> Prop :=
  fun (n:node) => exists s, set_In s penetrable_strand /\ s = strand_of n.
                                  
(** Test component *)
(* Here we need the notions of regular nodes *)
Definition test_component : msg -> msg -> node -> Prop :=
  fun (a t : msg) (n : node) => 
  exists h k, t = (E h k) /\
  ingred a t /\ 
  comp_of_node t n /\
  forall (n' : node), regular_node n' /\
  (forall c, comp_of_node c n' -> ~(ingred t c /\ t <> c)).

Variable PK : set key.
Definition test_for : msg -> node -> node -> Prop :=
  fun (a : msg) (n0 n1 : node) => orig_at n0 a /\ 
                                  unique a /\
                                  transformed_edge a n0 n1. 
 
(** Incoming test *)
Definition  incoming_test : msg -> msg -> node -> node -> Prop := 
  fun (a t : msg) (n0 n1 : node) => exists h K, t = (E h K) /\
                                    set_In K PK /\ 
                                    test_for a n0 n1 /\
                                    test_component a t n1. 

(** Anthentication test *)
(* Lemma Authentication_test_2 : 
  forall (n n' : node) (a t : msg),
   ssuccseq n n' /\ incoming_test a t n n' -> 
   exists (m m' : node), regular_node m /\
                         regular_node m' /\ 
                         comp_of_node t m' /\ 
                         transforming_edge a m m'.
*)
(** * Penetrator paths and normal bundles *)
(* The noation m |--> n means 
+ either m =>+ n with msg_of(m) negative and msg_of(n) positive, or else 
+ m --> n *)
Inductive path_condition (m n : node) : Prop :=
  | path_condition_single :  msg_deliver m n -> path_condition m n
  | path_condition_double : ssuccs m n /\ 
                            recv(m) /\ 
                            xmit(n) -> 
                            path_condition m n.

Hint Constructors path_condition.

(* path_condition implies prec *)
Lemma path_imp_prec : 
  forall (m n:node), path_condition m n -> prec m n.
Proof.
intros.
apply path_condition_ind with (m:=m) (n:=n).
apply deliver_prec.
intros.
apply ssuccs_prec. apply H0.
auto.
Qed.

(** * Path *)

(** MAYBE WE CAN AVOID THIS?? *)
Variable default : node. 

(** *** ith node of a path *)
Definition ith : nat -> list node -> node :=
  fun (n:nat) (p:list node) => nth n p default.

(** ** Axioms for paths *)
Definition is_path : list node -> Prop :=
  fun  (p: list node) => forall (n : nat), 
    (lt n ((length p)-1)) -> 
    path_condition (ith n p ) (ith (n+1) p ).
  
(* All paths begin on a positive node and end on a negative node *)
Axiom path_begin_pos_end_neg : forall (p : list node),
  (is_path p) -> xmit(ith 0 p) /\ recv(ith ((length p)-1)  p).

(** ** Penetrator paths *)
Definition p_path : list node -> Prop := 
  fun (p:list node) => 
is_path p /\ forall (n:nat), lt 0 n /\ lt n (length p - 1) -> 
                       penetrator_node (ith n p).

(** ** Falling and raising paths *)
Definition rasing : list node -> Prop := 
  fun (p:list node) => is_path p /\ forall n, lt n (length p - 1) -> 
                       ingred (msg_of (ith n p)) (msg_of (ith (n+1) p)).

Definition falling : list node -> Prop := 
  fun (p:list node) => is_path p /\ forall n, lt n (length p - 1) -> 
                       ingred (msg_of (ith (n+1) p)) (msg_of (ith n p)).

(* Transformation path *)
Variable default_pair :prod node msg.

(*Definition is_trans_path : list (prod node msg)->Prop := 
  fun (p:list (prod node msg)) => 
  forall (n:nat), lt n (length p) -> 
    comp_of_node (snd (nth n p default_pair)) 
                 (fst (nth n p default_pair)) /\
  forall (n:nat),
   (lt n (length p - 1) ->
   snd (nth n p default_pair) = snd (nth (n+1) p default_pair) \/
   (snd (nth n p default_pair) <> snd (nth (n+1) p default_pair)) ->
   (ssuccs (fst (nth n p default_pair)) (fst (nth (n+1) p default_pair))) /\
   new_at (snd (nth (n+1) p default_pair)) (fst (nth (n+1) p default_pair))).
*)

Definition is_trans_path : list (prod node msg)->Prop := 
  fun (p:list (prod node msg)) => 
    forall (n:nat), 
    let n1:= fst (nth n p default_pair) in
    let L1:= snd (nth n p default_pair) in
      let n2:= fst (nth (n+1) p default_pair) in 
      let L2:= snd (nth (n+1) p default_pair) in
      (lt n (length p) -> 
      comp_of_node L1 n1) /\
      ((lt n (length p - 1) ->
      L1 = L2 \/
      (L1 <> L2 ->
      (ssuccs n1 n2) /\
      new_at L2 n2))).

Check is_trans_path.
Print is_trans_path.
(* Baby result : a single pair (n, L) is a trans-foramtion path *)
Lemma anode_trans_path : 
  forall (n:node) (t:msg), 
  comp_of_node t n -> is_trans_path (cons (n,t) nil).
Proof.
intros.
unfold is_trans_path.
assert (length ((n,t)::nil) = 1).
auto.
rewrite H0.
intros. 
split.
intros.
assert (n0 = 0).
omega.
rewrite H2.
assert (nth 0 ((n,t)::nil) default_pair = (n,t)).
auto.
rewrite H3.
simpl.
exact H.
assert (1-1 =0); auto.
rewrite H1.
intros.
assert False. omega.
elim H3.
Qed.             

Lemma concat_trans_path : 
  forall p n L,
    is_trans_path p /\
    comp_of_node L n /\
    (snd (nth (length p -1) p default_pair) = L \/
    (snd (nth (length p -1) p default_pair) <> L ->
    (ssuccs (fst(nth (length p -1) p default_pair)) n /\
    new_at L n)) ->
    is_trans_path (p ++ (cons (n,L) nil))).
Proof. 
Admitted.


(* Some basic results for lists *)
Lemma fst_eq : forall (l1 l2:list (prod node msg)), 
               nth 0 (l1++l2) default_pair = nth 0 l1 default_pair.
Proof. 
Admitted.

(* TODO : l1 has to be non-empty *)
Lemma ignore_lasts : 
  forall l1 l2, forall (i:nat),
  lt i (length l1) -> nth i (l1++l2) default_pair = nth i l1 default_pair.
Proof.
Admitted.

Lemma last_elem : 
  forall (l1 : list (prod node msg)) x t, 
  nth (length (l1++(x,t)::nil) - 1) (l1++(x,t)::nil) default_pair = (x,t).
Proof.
Admitted.


Lemma ingred_earlier : 
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
(*Restart.
intros.
assert (exists n:node, (orig_at n a)).
apply ingred_originates_2.
exists n; apply H.
destruct H0.
exists x.
split. Focus 2. unfold orig_at in H0. tauto.
destruct H as (H1, (H2, H3)).
unfold orig_at in H0.
unfold orig_at in H1.
unfold not in H1.*)
Qed.

(* For every ingredient of *)
Lemma occur_1 : forall x y, ~ (x = P x y).
Proof.
unfold not; intros; induction x.
discriminate. discriminate. Focus 2. discriminate.
apply IHx1. assert (x1 = P x1 x2  /\ x2 = y).
apply pair_freeness. assumption.
destruct H0. rewrite H1 in H0. assumption.
Qed.

Lemma occur_2 : forall x y, ~ (x = P y x).
Proof.
unfold not; intros; induction x.
discriminate. discriminate. Focus 2. discriminate.
apply IHx2. assert (x1 = y  /\ x2 = P x1 x2).
apply pair_freeness. assumption.
destruct H0. rewrite H0 in H1. assumption.
Qed.

Lemma occur_3 : forall x y, ~ (x = E x y).
Proof.
unfold not; intros; induction x.
discriminate. discriminate. discriminate.
apply IHx. assert (x = E x k  /\ k = y).
apply enc_freeness. assumption.
destruct H0. rewrite H1 in H0. assumption.
Qed.

Lemma occur_4 : forall x y z, ~ (x = P (P x y) z).
Proof.
unfold not. intro x. induction x.
intros. discriminate.
intros. discriminate.
intros. Focus 2. discriminate.
apply IHx1 with (y:=z) (z:=y). assert (x1 = P (P x1 x2) y  /\ x2=z).
apply pair_freeness. assumption.
destruct H0. rewrite H1 in H0. assumption.
Qed.

Lemma occur_5 : forall x y z, ~ (x = P (P y x) z) /\
                              ~ (x = P y (P x z)) /\ 
                              ~ (x = P y (P z x)).
Proof.
unfold not. intro x. induction x.
intros. repeat split; discriminate.
intros. repeat split; discriminate.
intros.
Focus 2. intros. repeat split; discriminate.
repeat split.
intros. assert (x1 =  (P y (P x1 x2)) /\ x2 =z).
apply pair_freeness. auto.
destruct H0. elim IHx1 with (y:=y) (z:=x2). 
intros. destruct H3. apply H3. auto. 
intros. assert (x1=y /\ x2=P (P x1 x2) z).
apply pair_freeness. assumption. 
elim IHx2 with (y:=x1) (z:=z).
intros. apply H1. apply H0.
intros. assert (x1=y /\ x2=P z (P x1 x2)). 
apply pair_freeness. assumption.
elim IHx2 with (y:=z) (z:=x1).
intros. destruct H2. apply H3. apply H0.
Qed.

Lemma occur_6 : forall x y k, ~(x = E (P x y) k) /\ 
                              ~(x = P (E x k) y).
Proof.
unfold not; intro x.
induction x. intros.
repeat split; discriminate.
repeat split; discriminate.
repeat split. discriminate.
intros. assert (x1 = E (P x1 x2) k /\ x2 = y).
apply pair_freeness. auto.
elim IHx1 with (y:=x2) (k:=k).
intros. apply H1. apply H0.
split. intro. assert (x = P (E x k) y /\ k = k0).
apply enc_freeness. assumption.
apply IHx with (y:=y) (k:=k). apply H0.
discriminate.
Qed.

Lemma occur_7 : forall x y k, ~(x = E (P y x) k) /\ 
                              ~(x = P y (E x k)).
Proof.
unfold not; intro x.
induction x. intros.
repeat split; discriminate.
repeat split; discriminate.
repeat split. discriminate.
intros. assert (x1 = y /\ x2 = E (P x1 x2) k).
apply pair_freeness. auto.
elim IHx2 with (y:=x1) (k:=k).
intros. apply H1. apply H0.
split. intro. assert (x = P y (E x k) /\ k = k0).
apply enc_freeness. assumption.
apply IHx with (y:=y) (k:=k). apply H0.
discriminate.
Qed.

Lemma occur_8: forall x k k', ~ x = E (E x k) k'.
Admitted.

Lemma ingred_1_eq : forall x y, ingred_1 x y -> ingred_1 y x -> x = y.
Proof.
intros.
inversion H. subst. 
inversion H0. assert  (~ x = P (P x y0) y).
apply occur_4. elim H3. auto. 
assert (~ x =  P x0 (P x y0)). apply occur_5. elim H3. auto.
assert (~ x = E (P x y0) k ). apply occur_6. elim H3. auto.
subst. inversion H0.
assert (~ x = P (P x0 x) y). apply occur_5. elim H3. auto.
assert (~ x = P x1 (P x0 x)). apply occur_5. elim H3. auto.
assert (~ x = E (P x0 x) k). apply occur_7. elim H3. auto.
subst. inversion H0. 
assert (~ x = P (E x k) y). apply occur_6. elim H3. auto.
assert (~ x = P x0 (E x k)). apply occur_7. elim H3. auto.
assert (~ x = E (E x k) k0). apply occur_8. elim H3. auto.
Qed.

Lemma ingred_1_neq : forall x y, ingred_1 x y -> ~ingred_1 y x.
Proof.
unfold not.
intros.
inversion H. subst. 
inversion H0. assert  (~ x = P (P x y0) y).
apply occur_4. elim H3. auto. 
assert (~ x =  P x0 (P x y0)). apply occur_5. elim H3. auto.
assert (~ x = E (P x y0) k ). apply occur_6. elim H3. auto.
subst. inversion H0.
assert (~ x = P (P x0 x) y). apply occur_5. elim H3. auto.
assert (~ x = P x1 (P x0 x)). apply occur_5. elim H3. auto.
assert (~ x = E (P x0 x) k). apply occur_7. elim H3. auto.
subst. inversion H0. 
assert (~ x = P (E x k) y). apply occur_6. elim H3. auto.
assert (~ x = P x0 (E x k)). apply occur_7. elim H3. auto.
assert (~ x = E (E x k) k0). apply occur_8. elim H3. auto.
Qed.

Lemma ingred_p_neq : forall x y, ingred_p x y -> ~ingred_p y x.
Proof.
unfold not.
intros x y L R.
induction L.
inversion R. assert (~ ingred_1 y x).
apply ingred_1_neq; assumption.
elim H2; assumption.
Admitted.

Lemma ingred_1_not_eq : forall x y, ingred_1 x y -> x <> y.
Proof.
intros.
inversion H.
apply occur_1.
apply occur_2.
apply occur_3.
Qed.

Lemma ingred_1_nrefl : forall x, ~ ingred_1 x x.
Proof.
unfold not.
intros. inversion H.
assert (~ x = P x y). apply occur_1; assumption.
elim H2; auto.
assert (~ x = P x0 x). apply occur_2; assumption.
elim H2; auto.
assert (~ x = E x k). apply occur_3; assumption.
elim H2; auto.
Qed.


Lemma ingred_p_nrefl : forall x, ~ ingred_p x x.
Proof.
unfold not.
intros. inversion H. 
assert (~ ingred_1 x x). apply ingred_1_nrefl. elim H2; auto.
Admitted. 

Lemma ingred_p_not_eq : forall x y, ingred_p x y -> x<>y.
Proof.
Admitted.

Lemma ingred_eq : forall x y, ingred x y -> ingred y x -> x=y.
Proof.
intros; inversion H; auto.
inversion H0. auto.
assert (~ ingred_p y x).
apply ingred_p_neq. auto. elim H5; auto.
Qed.

Lemma ingred_reflex : forall m, ingred m m.
Proof.
Admitted.

Lemma comp_1 : forall a b, is_atomic a -> comp a (P a b).
Admitted.

Lemma comp_2 : forall a b, is_atomic a -> comp a (P b a).
Admitted.

Lemma comp_3 : forall a k, comp (E a k) (E a k).
Admitted.

Lemma ingred_1_exists_comp : 
  forall a m,is_atomic a -> ingred_1 a m -> exists L, ingred a L /\ comp L m.
Proof.
intros.
inversion H0.
exists a. split; [apply ingred_refl | apply comp_1]; auto.
exists a. split; [apply ingred_refl | apply comp_2]; auto.
exists (E a k). split.
apply ingred_step. apply ingred_p_step. apply inenc1.
apply comp_3.
Qed.

Lemma ingred_p_exists_comp : 
  forall a m,is_atomic a -> ingred_p a m -> exists L, ingred a L /\ comp L m.
Proof.
intros.
induction H0. apply ingred_1_exists_comp; auto.
assert (exists L1 : msg, ingred x L1 /\ comp L1 y').
apply ingred_1_exists_comp; auto.
assert (is_atomic y' \/ ~ is_atomic y'). tauto.
case H3.
intros.
assert (exists L : msg, ingred y' L /\ comp L y).
apply IHingred_p; auto. destruct H5 as (L, H5). exists L.
split. apply ingred_trans with (y:=y').
apply ingred_step. apply ingred_p_step. auto. 
apply H5. apply H5.

Lemma ingred_exists_comp2: 
  forall a m,is_atomic a /\ ingred a m -> exists L, ingred a L /\ comp L m.
Proof.
intros.
destruct H.
inversion H0. symmetry in H1. rewrite H1. exists a. 
unfold comp. repeat split.
apply ingred_refl. apply ingred_refl.
apply atomic_not_concat. assumption.
intros.
assert (a=m1). apply ingred_eq; apply H2.
destruct H2. assert False. rewrite H3 in H2; auto.
apply False_ind. assumption.
intros. inversion H1. inversion H3.
exists a. split. apply ingred_reflex. unfold comp. 
split. rewrite H6. auto. split. apply atomic_not_concat. auto.
intros. assert (m1 = P a y1).  destruct H7 as (H7, (H8, H9)).
inversion H8. inversion H9. apply False_ind. rewrite H10 in H11. 
intros. case y0.
Admitted.

Lemma ingred_exists_comp: 
  forall (n:node) (a:msg),
    ingred a (msg_of n) -> exists L, ingred a L /\ comp_of_node L n.
Proof.
Admitted.

Lemma not_new_exists : 
  forall n L, ~ new_at L n ->
  exists n', ssuccs n' n /\ new_at L n'.
Proof.
Admitted.
 
Lemma backward_construction : 
  forall (n:node) (a L:msg), 
    comp_of_node L n /\ ~ orig_at n a /\ ingred a L ->
    exists (n':node) (L':msg), 
      prec n' n /\
      ingred a L' /\ 
      comp_of_node L' n' /\ 
      (L' = L \/ (L' <> L -> ssuccs n' n /\ new_at L n)).
Proof.
intros.
assert (xmit n \/ recv n).
apply xmit_or_recv.
case H0.
Focus 2.
intros.
assert (exists (n':node), msg_deliver n' n). 
apply was_sent. auto.
destruct H2 as (n', H2).
exists n'.
exists L.
split. apply deliver_prec. auto.
split. apply H.
split. apply msg_deliver_comp with (n1:=n') (n2:=n).
split. auto. apply H.
left. auto.  
intros.
assert (new_at L n \/ ~(new_at L n)). tauto.
case H2.
intros. assert (exists n', ssuccs n' n /\ ingred a (msg_of n')).
apply ingred_earlier. repeat split; auto. apply H.
apply ingred_trans with (y:=L). 
apply H. apply comp_of_node_imp_ingred. apply H.
destruct H4 as (n', (H4, H5)).
assert (exists L', ingred a L' /\ comp_of_node L' n').
apply ingred_exists_comp; assumption.
destruct H6 as (L', (H6, H7)).
exists n'.
exists L'.
split. apply ssuccs_prec. apply H4.
split. assumption.
split. assumption.
right. intros. split; auto.
intros.
assert (exists n', ssuccs n' n /\ new_at L n').
apply not_new_exists. auto.
destruct H4 as (n', H4).
exists n'. 
exists L.
split. apply ssuccs_prec. apply H4.
split. apply H.
split. apply new_at_imp_comp. apply H4.
auto.
Qed.

Definition P11 : node -> Prop := 
  fun (n':node) => 
  forall (a t:msg), 
  ingred a t /\ comp_of_node t n' -> 
  exists p, is_trans_path p /\ 
  orig_at (fst (nth 0 p default_pair)) a /\
  fst (nth (length p - 1) p default_pair) = n' /\ 
  snd (nth (length p -1) p default_pair) = t /\
  forall (i:nat), lt i (length p) -> ingred a (snd (nth i p default_pair)).
              
(*Proposition 11 *)
Lemma proposition11 : 
  forall (n':node), P11 n'.
Proof.
apply induct_ok.
intros.
unfold P11.
unfold P11 in H.
intros.
destruct H0 as (H1, H2).
assert (orig_at x a \/ ~ orig_at x a).
tauto.
case H0.
intros.
exists (cons (x, t) nil).
simpl.
split.
apply anode_trans_path with (n:=x) (t:=t).
exact H2.
split; auto; split; auto; split; auto.
intros.
assert (i=0). omega.
rewrite H5;auto.
intros.
assert (exists (n':node) (L':msg), prec n' x /\
                               ingred a L' /\ 
                               comp_of_node L' n' /\ 
                               (L' = t \/
                               (L' <> t -> 
                               ssuccs n' x /\ 
                               new_at t x))).
apply backward_construction. auto.
destruct H4 as (n', (L', (H4, (H5, H6)))).
assert (forall a t : msg,
        ingred a t /\ comp_of_node t n' ->
        exists p : list (node * msg),
        is_trans_path p /\
        orig_at (fst (nth 0 p default_pair)) a /\
        fst (nth (length p - 1) p default_pair) = n' /\
        snd (nth (length p - 1) p default_pair) = t /\
        (forall i : nat, i < length p -> 
                         ingred a (snd (nth i p default_pair)))).
apply H with (y:=n'). auto.
assert (exists p : list (node * msg),
       is_trans_path p /\
       orig_at (fst (nth 0 p default_pair)) a /\
       fst (nth (length p - 1) p default_pair) = n' /\
       snd (nth (length p - 1) p default_pair) = L' /\
       (forall i : nat, i < length p -> 
                        ingred a (snd (nth i p default_pair)))).
apply H7.  
split. auto. apply H6.
destruct H8 as (p0,IH).
destruct IH as (IH1, (IH2, (IH3, (IH4, IH5)))).
exists (p0 ++ (cons (x,t) nil)).
split.
apply concat_trans_path.
rewrite IH4. rewrite IH3. apply H6.
split. 
assert ((nth 0 (p0 ++ (x, t) :: nil) default_pair)=
        (nth 0 p0 default_pair)).
apply fst_eq.
rewrite H8. auto.
assert (nth (length (p0 ++ (x, t) :: nil) - 1) 
       (p0 ++ (x, t) :: nil) default_pair = (x,t)).
apply last_elem.
rewrite H8.
split. auto. split. auto.
intros.
assert (length (p0 ++ (x, t) :: nil) = length p0 + 1).
apply app_length.
rewrite H10 in H9.
assert (i < length p0 \/ i = length (p0 ++ (x, t) :: nil) -1).
omega.
case H11.
intros.
assert (nth i (p0 ++ (x, t) :: nil) default_pair = nth i p0 default_pair).
apply ignore_lasts. auto.
rewrite H13. apply IH5. auto.
intros.
rewrite H12.
rewrite last_elem. simpl. auto.
Qed.

(* *** New definition for ingredients *)
Inductive Subterm : msg -> msg -> Prop :=
| st_refl : forall m, Subterm m m
| st_join_l : forall st l r, 
    Subterm st l -> Subterm st (P l r)
| st_join_r : forall st l r, 
    Subterm st r -> Subterm st (P l r)
| st_encr : forall st t k, 
    Subterm st t -> Subterm st (E t k).

Lemma subterm_tot : forall x y, Subterm x y /\ Subterm y x -> x=y.
Admitted.