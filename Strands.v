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
(* Variable strand : Set. *)
Definition strand : Type := list smsg.
Variable role : Set.
(* Predicate for positive and negative nodes *)
Variable xmit : node -> Prop.
Variable recv : node -> Prop.
Variable msg_of : node -> msg.  
Variable msg_deliver : node -> node -> Prop.
Variable ssucc : node ->  node -> Prop.
Definition path : Type := list (prod node msg).
(* Variable regular_strand : set strand. *)
(* Variable penetrable_strand : set strand.*)
Variable strand_of: node -> strand.
(* Predicates for regular nodes and penetrable nodes *)
Variable p_node : node -> Prop.
Variable r_node : node -> Prop.

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
(* Variable eq_strand_dec : forall x y : strand, {x = y} + {x <> y}.
Hint Resolve eq_strand_dec.
*)


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

(*********************************************************************)

(** * Penetrator Strands *)
Parameter K_p : set Key. 
Open Scope list_scope.
Import ListNotations.
Open Scope ma_scope.

Inductive MStrand (s : strand) : Prop := 
  | P_M : forall t : Text, s = [+ (T t)] -> MStrand s.
Hint Constructors MStrand.

Inductive KStrand (s : strand) : Prop := 
  | P_K : forall k : Key, set_In k K_p -> s = [+ (K k)] -> KStrand s.
Hint Constructors KStrand.

Inductive CStrand (s : strand) : Prop := 
  | P_C : forall (g h : msg), s = [- g; - h; + (P g h)] -> CStrand s.
Hint Constructors CStrand.

Inductive SStrand (s : strand) : Prop := 
  | P_S : forall (g h : msg), s = [- (P g h); + g ; + h] -> SStrand s.
Hint Constructors SStrand.

Inductive EStrand (s : strand) : Prop := 
  | P_E : forall (k : Key) (h :msg), s = [- (K k); - h; + (E h k)] -> EStrand s.
Hint Constructors EStrand.

Inductive DStrand (s : strand) : Prop := 
  | P_D : forall (k k' : Key) (h :msg), 
          inv k k' -> s = [- ( K k'); - (E h k); + h] -> DStrand s.
Hint Constructors DStrand.

Definition PenetratorStrand (s : strand) : Prop := 
  MStrand s \/ KStrand s \/ CStrand s \/ SStrand s \/ EStrand s \/ DStrand s.

(* Inductive PenetratorStrand (s : strand) : Prop :=
  | P_M : forall t : Text, s = [+ (T t)] -> PenetratorStrand s
  | P_K : forall k : Key, set_In k K_p -> s = [+ (K k)] -> PenetratorStrand s
  | P_C : forall (g h : msg), s = [- g; - h; + (P g h)] -> PenetratorStrand s
  | P_S : forall (g h : msg), s = [- (P g h); + g ; + h] -> PenetratorStrand s
  | P_E : forall (k : Key) (h :msg), s = [- (K k); - h; + (E h k)] -> PenetratorStrand s
  | P_D : forall (k k' : Key) (h :msg), 
          inv k k' -> s = [- ( K k'); - (E h k); + h] -> PenetratorStrand s.
Hint Constructors PenetratorStrand.
*)

(** ** Axiom about penetrator strands and penetrator nodes *)
Axiom P_node_strand : 
  forall (n:node), p_node n -> PenetratorStrand (strand_of n).


(** Axiom for strand_of *)
(* TODO : move to right place *)
Axiom ssuccs_same_strand :
  forall (n1 n2 : node), ssuccs n1 n2 -> strand_of n1 = strand_of n2.

(** ** Basic Results for Penetrator Strands *)
(* If n is a node of a MStrand or KStrand, then n is a positive node *)
Axiom MStrand_xmit_node : 
  forall (n:node), MStrand (strand_of n) -> xmit n.

Axiom KStrand_xmit_node :
  forall (n:node), KStrand (strand_of n) -> xmit n.

Axiom CStrand_not_falling : 
  forall (s:strand), CStrand s -> 
    ~ exists (n1 n2 : node), n1 <> n2 /\ 
        strand_of n1 = s /\ strand_of n2 = s /\ 
        ingred (msg_of n2) (msg_of n1).
Axiom EStrand_not_falling : 
  forall (s:strand), EStrand s -> 
    ~ exists (n1 n2 : node), n1 <> n2 /\ 
        strand_of n1 = s /\ strand_of n2 = s /\ 
        ingred (msg_of n2) (msg_of n1).

                   
(*********************************************************************)

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

(** ** Basic results about penetrator strands related to components *)
(* A MStrand or KStrand cannot have an edge *)
Axiom MStrand_not_edge :
  forall (s:strand), MStrand s -> ~ exists (n1 n2 : node),
                     strand_of n1 = s /\ strand_of n2 = s /\ ssuccs n1 n2.
 
Axiom KStrand_not_edge :
  forall (s:strand), KStrand s -> ~ exists (n1 n2 : node),
                     strand_of n1 = s /\ strand_of n2 = s /\ ssuccs n1 n2.  

Axiom CStrand_not : 
  forall (s:strand), CStrand s -> ~ exists (n1 n2 : node), 
                     strand_of n1 = s /\ strand_of n2 = s /\
                     recv n1 /\ xmit n2 /\ ssuccs n1 n2 /\
                     exists L1 L2, L1 <[node] n1 /\ L2 <[node] n2 /\ L1 <> L2.

Axiom SStrand_not : 
  forall (s:strand), SStrand s -> ~ exists (n1 n2 : node), 
                     strand_of n1 = s /\ strand_of n2 = s /\
                     recv n1 /\ xmit n2 /\ ssuccs n1 n2 /\
                     exists L1 L2, L1 <[node] n1 /\ L2 <[node] n2 /\ L1 <> L2.

(*********************************************************************)

(** * Penetrable Keys and Safe Keys *)
(* Penetrable key is already penetrated (K_p) or some regular strand
puts it in a form that could allow it to be penetrated, because for each key
protecting it, the matching key decryption key is already pentrable *)
Section Penetrable_Keys.
Parameter Kp : Set.
Parameter PK : nat -> Key -> Prop.
Axiom init_pkeys : sig (PK 0) = Kp.
Axiom next_pkeys : forall (i:nat) (k:Key), (exists (n:node) (t:msg),
                      r_node n /\ xmit n /\ new_at t n /\ 
                      k_ingred (sig (PK i)) (K k) t) -> PK (i+1) k.  

Inductive PKeys (k:Key) : Prop :=
  | pkey_step : (exists (i:nat), PK i k) -> PKeys k.

End Penetrable_Keys.
Check PKeys.

(*********************************************************************)

(** * Paths *)
Section Path.
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

(** ** Definitions for paths *)
Definition is_path : list node -> Prop :=
  fun  (p: list node) => forall (n : nat), 
    n < length(p) - 1 -> 
    path_cond (nth_node n p ) (nth_node (n+1) p).

(** ** Axiom for paths *)
(** All paths begin on a positive node and end on a negative node *)
Axiom path_begin_pos_end_neg : forall (p : list node),
  is_path p -> xmit(nth_node 0 p) /\ recv(nth_node (length p - 1)  p).

(** ** Penetrator Paths *)
Definition p_path : list node -> Prop := 
  fun (p:list node) => is_path p -> 
    forall (i:nat), (i > 0 /\ i < length p - 1) ->
    p_node (nth i p default_n).

(** ** Falling paths *)
Definition falling_path := 
  fun (p:list node) => p_path p -> forall (i:nat), i < length p -1 ->
    ingred (msg_of (nth (i+1) p default_n)) (msg_of (nth i p default_n)).

(** ** Rising paths *)
Definition rising_path := 
  fun (p:list node) => p_path p -> forall (i:nat), i < length p -1 ->
    ingred (msg_of (nth i p default_n)) (msg_of (nth (i+1) p default_n)).

(** ** Basic results for falling and rising paths *)
Lemma falling_imp_D_or_S : 
  forall (p:list node), falling_path p -> 
      forall (i:nat), 0 < i /\ i < length p - 1 /\ recv (nth i p default_n) -> 
          DStrand (strand_of (nth i p default_n)) \/
          SStrand (strand_of (nth i p default_n)).
Admitted.

Lemma rising_imp_E_or_C :
  forall (p:list node), rising_path p -> 
      forall (i:nat), 0 < i /\ i < length p - 1 /\ recv (nth i p default_n) -> 
          EStrand (strand_of (nth i p default_n)) \/
          CStrand (strand_of (nth i p default_n)).
Admitted.

(*********************************************************************)

(** * Edges *)
(** ** Transformed edges *)
(** ** Transforming edges *)

(*********************************************************************)

(* I want to define some constant of type msg here but we don't know any constant 
of this type, so I just say it is some variable *)
Variable default_msg : msg.

(** * Transformation paths *)
Section Trans_path.
Variable p : path.
Definition ln := fst (split p).
Hint Resolve ln.
Definition lm := snd (split p).
Hint Resolve lm.

Definition nth_msg : nat -> list msg -> msg :=
  fun (n:nat) (p:list msg) => nth n p default_msg.
Hint Resolve nth_msg.

Definition L (n:nat) := nth_msg n lm.
Hint Resolve L.
Definition nd (n:nat) := nth_node n ln.
Hint Resolve nd.

Definition is_trans_path : Prop := 
  (is_path ln /\
   (True \/ 
   (ssuccs (nd 0) (nd 1) /\  xmit (nd 0) /\ xmit (nd 1)))) /\
   forall (n:nat), (n < length p -> (L n) <[node] (nd n)) /\
     (n < length p - 1 -> (L n = L (n+1) \/ (L n <> L (n+1) -> 
                          recv (nd n) /\ xmit (nd (n+1)) /\ ssuccs (nd n) (nd (n+1)) /\
                          (exists m, xmit m /\ new_at (L (n+1)) m  /\ 
                           ssuccs (nd n) m /\ ssuccseq m (nd (n+1)))))).

End Trans_path.

(* Baby result : a single pair (n, L) is a trans-foramtion path *)
Lemma anode_trans_path : 
  forall (n:node) (t:msg), 
    t <[node] n -> is_trans_path [(n,t)].
Proof.
intros n t Hcom.
unfold is_trans_path.
simpl. split.
  split. constructor. simpl in H.
    apply False_ind; omega.
  left; auto.
  intros n1; split.
     intro Hn1_lt. assert (n1=0). omega. subst. apply Hcom.
     intros Hn1_lt. apply False_ind. omega.
Qed.      

(*********************************************************************)
(** * Proposition 7 *)
Section P7_1.
Variable pl : path.
Variable i : nat.
Let p := fst (split pl).
Let l := snd (split pl).
Let p_i := nth_node i p.
Let p_i1 := nth_node (i+1) p.
Hypothesis Hc : 0 < i /\ i < length pl - 1.
Hypothesis Hfp : falling_path p.
Hypothesis Hrec : recv p_i.
Hypothesis Hpn : p_node p_i.
Let s := strand_of p_i.

Lemma P7_1 : 
  enc (msg_of p_i) \/ pair (msg_of p_i).
Admitted.
Section P7_1_a.
Variable h : msg.
Variable k : Key.
Hypothesis Heq : msg_of p_i = E h k.
Lemma P7_1a : 
  EStrand s /\ msg_of p_i1 = h.
Admitted.
End P7_1_a.

Section P7_1_b.
Variable g h : msg.
Lemma P7_1_b : 
  SStrand s /\ (msg_of p_i1 = h \/ msg_of p_i1 = g).
Admitted.
End P7_1_b.
End P7_1.
Check P7_1a.
Check P7_1.
  
 

(*********************************************************************)

(** * Proposition 10 *)
Section Proposition_10.
Variable p : path.

(* TODO : move to right place *)
Lemma ssuccs_trans' : 
  forall x y z, ssuccs x y -> ssuccs y z -> ssuccs x z.
Proof.
intros x y z Hxy. induction Hxy.
  intros. apply ssuccs_trans with (y':= z0).
    auto. auto.
    intros. apply ssuccs_trans with (y':= y').
      auto.
      apply IHHxy. auto.
Qed.

Lemma ssuccs_eq : 
  forall x y z, ssuccs x y -> ssuccseq y z -> ssuccs x z.
Proof.
intros x y z Hxy Hyz.
inversion Hyz. 
  rewrite H in Hxy. auto.
  apply ssuccs_trans' with (y:=y); auto.
Qed.
 
Lemma trans_path_ssuccs : 
  is_trans_path p -> forall (n:nat), 
     n < length p - 1 -> L p n <> L p (n+1) ->
     ssuccs (nd p n) (nd p (n+1)) /\ recv (nd p n) /\ xmit (nd p (n+1)). 
Proof.
intros.
unfold is_trans_path in H.
destruct H as ((H3,H4),H5).
remember (H5 n) as H6.
destruct H6 as (H61, H62).
remember (H62 H0) as H7.
case H7.
  intros. apply False_ind. apply H1. auto.
  intros. remember (H H1) as H8.
  destruct H8 as (Hrec, (Hxmit, (Hss, (m, (H9, (H10, (H11, H12))))))).
repeat split.
apply ssuccs_eq with (y:= m); auto.
auto.
auto.
Qed.


Lemma Proposition_10 : 
  is_trans_path p -> 
  forall (n:nat), n < length p - 1 -> L p n <> L p (n+1) ->
  p_node (nd p n) -> 
  ssuccs (nd p n) (nd p (n+1)) /\ 
  (DStrand (strand_of (nd p n)) \/ 
   EStrand (strand_of (nd p n))).
Proof.
intros. 
assert (Hs : ssuccs (nd p n) (nd p (n + 1)) /\ recv (nd p n) /\ xmit (nd p (n+1))).
apply trans_path_ssuccs; auto.
unfold is_trans_path in H.
destruct H as (Ha, Hb).
split.
  apply Hs.
  
  assert (Hp : PenetratorStrand (strand_of (nd p n))).
  apply (P_node_strand (nd p n)); auto.
  unfold PenetratorStrand in Hp.
  destruct Hp as [Hp1 | [Hp2 | [Hp3 | [Hp4 | [Hp5 |Hp6 ]]]]].
  apply False_ind. apply (MStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply Hs.
    apply Hs.

  apply False_ind. apply (KStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand; apply Hs.
    apply Hs.

  apply False_ind. apply (CStrand_not (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply Hs.
    repeat split. apply Hs. apply Hs. apply Hs.
    exists (L p n). exists (L p (n+1)).
    split. apply Hb. omega.
    split. apply Hb with (n:= n+1). omega.
    auto.

  apply False_ind. apply (SStrand_not (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply Hs.
    repeat split. apply Hs. apply Hs. apply Hs.
    exists (L p n). exists (L p (n+1)).
    split. apply Hb. omega.
    split. apply Hb with (n:= n+1). omega.
    auto.

  auto.
  auto.
Qed.

End Proposition_10.

(*********************************************************************)
  
(** * Proposition 11 *)
(** For every atomic ingredient of a message, there exists 
a component of the message so that the atomic value is 
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

Section Proposition11.
Variable a : msg.
Variable n : node.
Definition P_ingred : node -> Prop:=
  fun (n':node) => ssuccs n' n /\ ingred a (msg_of n').

(* Since ssuccs implies prec, if a element x is prec-accessible
then it is ssuccs-accessible *)
Lemma acc_prec_ssuccs : forall x, Acc prec x -> Acc ssuccs x.
Proof.
intros x Hprec.
induction Hprec. constructor.
intros. apply H0.
apply ssuccs_prec; auto.
Qed.

(* Ssuccs is a well-founded relation *)
(* Notice that every sub-relation of a well-founded relation is 
also well-founded *)
Lemma wf_ssuccs : well_founded ssuccs.
Proof.
unfold well_founded. intros x.
apply acc_prec_ssuccs.
apply wf_prec.
Qed.

Lemma ingred_of_earlier : 
  forall (n':node), 
   a <st (msg_of n) -> xmit n -> ~ orig_at n a -> exists n', P_ingred n'.
Proof.
intros n' Hst Hxmit Hnorig.
apply Peirce.
intros.
apply False_ind.
apply Hnorig. unfold orig_at.
repeat split.
  auto. 
  auto.
  intros n1 Hssuc Hastn1. apply H.
  exists n1. split; auto.
Qed.

Lemma not_orig_exists : 
  a <st (msg_of n) -> xmit n -> ~ orig_at n a -> has_min_elt P_ingred.
Proof.
intros Hxmit Hst Hnorig.
apply always_min_elt.
apply ingred_of_earlier; assumption.
Qed.

End Proposition11. 

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
      assumption.
      assumption.
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

Definition Proposition_11_aux : node -> Prop := 
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
  forall (n':node), Proposition_11_aux n'.
Proof.
apply well_founded_ind with (R:=prec).
exact wf_prec.
intros.
unfold Proposition_11_aux.
unfold Proposition_11_aux in H.
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

(*********************************************************************)

(** * Proposition 13 *)
Section P13. 
Variable pl : path.
Let p := fst (split pl).
Let l := snd (split pl).
Hypothesis Hpp : p_path p.
Hypothesis Hp1 : simple (msg_of (nth_node 0 p)).
Definition P13_1_aux (n:nat) : Prop :=
   msg_of (nth_node n p) = (nth_msg (length p - 1) l) /\
    forall (i:nat), i >= n -> i <= length p - 1 -> 
       nth_msg i l = nth_msg (length p - 1) l.
Lemma P13_1 : 
  exists (n:nat), P13_1_aux n /\ 
    (forall m, m > n -> ~ P13_1_aux m) /\
    exists i, i < length p - 1 -> nth_msg i l <> nth_msg (i+1) l ->
      xmit (nth_node n p) /\ EStrand (strand_of (nth_node n p)).
    
