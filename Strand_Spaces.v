
(* Add LoadPath "./". *)
(* Add LoadPath "./Classical_Wf". *)
Require Import Classical.
Require Import Message_Algebra.
Require Import Lists.ListSet Lists.List.
Require Import Omega ZArith.
Require Import Relation_Definitions Relation_Operators.

Open Scope list_scope.
Import ListNotations.
Open Scope ma_scope.

(* Strand Spaces *)
(*  *************************************** *)

(** * Strands *)
(** ** Strand Definition *)
Definition strand : Type := list smsg.

(** ** Decidable equality for strands *)
Definition eq_strand_dec : forall x y : strand,{x = y} + {x <> y}.
Proof. 
intros. decide equality.
Qed.
Hint Resolve eq_strand_dec.

(*********************************************************************)

(** * Nodes *)
(** ** Definition *)
Definition node : Type := {n:(prod strand nat)| snd n < length (fst n)}. 

(** ** Strand of a node *)
Definition strand_of (n:node) : strand := match n with 
  | exist apair _ => fst apair end.

(** ** Index of a node *)
Definition index_of (n:node) : nat := match n with 
  | exist apair _ => snd apair end.

(** ** Decidable equality for nodes *)
Definition eq_node_dec : forall x y : node,
 {x = y} + {x <> y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (eq_strand_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  left. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  right. intros C. inversion C. auto.
  right. intros C. inversion C. auto.
Qed.
Hint Resolve eq_node_dec.

(** ** Signed message of a node *)
Definition option_smsg_of (n:node) : (option smsg) :=
  match n with 
  | exist (s,i) _ => nth_error s i end.

Lemma nth_error_len : 
  forall (A:Type) (l:list A) (n:nat), 
    nth_error l n = None -> (length l) <= n.
Proof.
intros A l n. generalize dependent l.
induction n.
intros l H.
unfold nth_error in H.
unfold error in H. destruct l. auto. inversion H.

intros l1 H. destruct l1. simpl; omega.
inversion H. apply IHn in H. simpl. omega.
Qed.

Lemma valid_smsg : forall (n:node), {m:smsg | option_smsg_of n = Some m}.
Proof.
intros n.
remember (option_smsg_of n) as opn.
destruct n. destruct opn.
exists s. auto.

unfold option_smsg_of in Heqopn.
destruct x. simpl in l.
symmetry in Heqopn.
apply nth_error_len in Heqopn.
omega.
Qed.

Definition smsg_of (n:node) : smsg := match (valid_smsg n) with
  | exist m _  => m end.

(** ** Unsigend message of a node *)
Definition msg_of (n:node) : msg := smsg_2_msg (smsg_of n).

(** ** Predicate for positive and negative nodes *)
Definition xmit (n:node) : Prop := exists (m:msg), smsg_of n = + m.

Definition recv (n:node) : Prop := exists (m:msg), smsg_of n = - m.


(*********************************************************************)

(** * Penetrator Strands *)
Section PenetratorStrand.
  Parameter K_p : set Key. 

  (** ** Text Message Strand *)
  Inductive MStrand (s : strand) : Prop := 
  | P_M : forall t : Text, s = [+ (T t)] -> MStrand s.
  Hint Constructors MStrand.

  (** ** Key Strand *)
  Inductive KStrand (s : strand) : Prop := 
  | P_K : forall k : Key, set_In k K_p -> s = [+ (K k)] -> KStrand s.
  Hint Constructors KStrand.

  (** ** Concatenation Strand *)
  Inductive CStrand (s : strand) : Prop := 
  | P_C : forall (g h : msg), s = [- g; - h; + (P g h)] -> CStrand s.
  Hint Constructors CStrand.

  (** ** Separation Strand *)
  Inductive SStrand (s : strand) : Prop := 
  | P_S : forall (g h : msg), s = [- (P g h); + g ; + h] -> SStrand s.
  Hint Constructors SStrand.

  (** ** Encryption Strand *)
  Inductive EStrand (s : strand) : Prop := 
  | P_E : forall (k : Key) (h :msg), s = [- (K k); - h; + (E h k)] -> EStrand s.
  Hint Constructors EStrand.

  (** ** Decryption Strand *)
  Inductive DStrand (s : strand) : Prop := 
  | P_D : forall (k k' : Key) (h :msg), 
    inv k k' -> s = [- ( K k'); - (E h k); + h] -> DStrand s.
  Hint Constructors DStrand.

  (** ** Definition for PenetratorStrand *)
  Inductive PenetratorStrand (s:strand) :Prop :=
  | PM : MStrand s -> PenetratorStrand s
  | PK : KStrand s -> PenetratorStrand s
  | PC : CStrand s -> PenetratorStrand s
  | PS : SStrand s -> PenetratorStrand s
  | PE : EStrand s -> PenetratorStrand s
  | PD : DStrand s -> PenetratorStrand s.
  Hint Constructors PenetratorStrand.

  (** ** Predicates for penetrable nodes and regular nodes *)
  (* A node is a penetrator node if the strand it lies on is a penetrator strand *)
  Definition p_node (n:node) : Prop := PenetratorStrand (strand_of(n)).

  (* A non-penetrator node is called a regular node *)
  Definition r_node (n:node) : Prop := ~ p_node n.

  (** ** Axiom for penetrator node and regular node *)
  (* Every node is either a penatrator node or regular node *)
  Axiom node_p_or_r : forall (n:node), p_node n \/ r_node n.

End PenetratorStrand.

(*********************************************************************)

(** * Edges *)
(** ** Inter-strand Edges *)
Inductive msg_deliver : relation node :=
  | msg_deliver_step : forall (x y : node) (m:msg), 
    smsg_of x = +m /\ smsg_of y = -m /\ strand_of(x) <> strand_of(y)
    -> msg_deliver x y.
Hint Constructors msg_deliver.
Notation "x --> y" := (msg_deliver x y) (at level 0, right associativity) : ss_scope.

(** ** Iner-strand Edges - Strand ssuccessor *)
Inductive ssucc : relation node :=
  | ssucc_step : forall (x y : node), strand_of(x) = strand_of(y) /\
    index_of(x) + 1 = index_of(y) -> ssucc x y.
Hint Constructors ssucc.     
Notation "x ==> y" := (ssucc x y) (at level 0, right associativity) : ss_scope.

(** Transitive closure of strand ssuccessor *)
Definition ssuccs : relation node := clos_trans node ssucc.
Notation "x ==>+ y" := (ssuccs x y) (at level 0, right associativity) : ss_scope.

(** Reflexive Transitive Closure of strand successor *)
Definition ssuccseq : relation node := clos_refl_trans node ssucc.

(** ** Edges on Strand *)
Inductive strand_edge : relation node :=
  | strand_edge_single : forall x y, msg_deliver x y -> strand_edge x y
  | strand_edge_double : forall x y, ssucc x y -> strand_edge x y.
Hint Constructors strand_edge.

(** Transitive closure of edge *)
Definition prec := clos_trans node strand_edge.
Notation "x ==>* y" := (ssuccseq x y) (at level 0, right associativity) : ss_scope.

(** ** Constructive and Destructive Edges *)
Inductive cons_edge : relation node :=
  | cons_e : forall x y, ssuccs x y -> EStrand (strand_of x)  -> cons_edge x y
  | cons_c : forall x y,  ssuccs x y -> CStrand (strand_of x) -> cons_edge x y.
Hint Constructors cons_edge.

Inductive des_edge : relation node :=
  | des_d : forall x y, ssuccs x y -> DStrand (strand_of x)  -> des_edge x y
  | des_s : forall x y,  ssuccs x y -> SStrand (strand_of x) -> des_edge x y.
Hint Constructors des_edge.

(*********************************************************************)

(** * Origination *)

Definition orig_at (n:node) (m:msg) : Prop :=
  xmit(n) /\  (ingred m (msg_of n)) /\
  (forall (n':node), ((ssuccs n' n) -> 
  (ingred m (msg_of n')) -> False)).

Definition non_orig (m:msg) : Prop := forall (n:node), ~orig_at n m.

Definition unique (m:msg) : Prop :=
  (exists (n:node), orig_at n m) /\
  (forall  (n n':node),(orig_at n m) /\ (orig_at n' m) -> n=n').

(*********************************************************************)


(** * Axioms *)
(*  ******** *)

(** ** The bundle axiom: every received  message was sent  *)
Axiom was_sent : forall x : node, (recv x) -> 
  (exists y : node,  msg_deliver y x).


(** ** Normal bundle axiom *)
Axiom not_k_k : forall k k', inv k k' -> DStrand  [-(K k); -(E (K k) k'); + (K k)].

(** ** Well-foundedness *)
Axiom wf_prec: well_founded prec.

(*********************************************************************)

(** Minimal nodes *)

Definition is_minimal: (node -> Prop) -> node -> Prop :=
  fun P x => (P x) /\ forall y, (prec y x) -> ~( P y).

Definition has_min_elt: (node -> Prop) -> Prop :=
  fun P  =>   exists x:node, is_minimal P x.

(*********************************************************************)

(** * New Component *)
(** ** Component of a node *)
(* A message is a component of a node if it is a component 
of the message at that node %//%*)
Definition comp_of_node (m:msg) (n:node) : Prop := comp m (msg_of n). 
Notation "x <[node] y" := (comp_of_node x y) (at level 50) : ss_scope.

(** ** New at *)
(** A message is new at a node if it is a component of that node
and the message is not a component of any ealier node in the same 
strand with the node *)
Definition new_at  (m:msg) (n:node) : Prop :=
  m <[node] n /\ forall (n' : node) , ssuccs n' n -> m <[node] n'-> False.

(*********************************************************************)

(** * Paths *)
Section Path.
  Parameter default_node : node.

(** ** Path condition *)
  Inductive path_edge (m n : node) : Prop :=
  | path_edge_single :  msg_deliver m n -> path_edge m n
  | path_edge_double : ssuccs m n /\ recv(m) /\ xmit(n) -> path_edge m n.
  Hint Constructors path_edge.
  Notation "m |--> n" := (path_edge m n) (at level 30) : ss_scope.

(** ** ith node of a path *)
  Definition nth_node (i:nat) (p:list node) : node := 
    nth_default default_node p i.
  Hint Resolve nth_node.

(** ** Definitions for paths *)
  Definition is_path (p:list node) : Prop := 
    forall i, i < length(p) - 1 -> path_edge (nth_node i p) (nth_node (i+1) p).

(** ** Axiom for paths *)
(** All paths begin on a positive node and end on a negative node *)
  Axiom path_begin_pos_end_neg : forall (p:list node),
    xmit(nth_node 0 p) /\ recv(nth_node (length(p)-1)  p).

(** ** Penetrator Paths *)
Definition p_path (p:list node): Prop := is_path p /\ forall i,
  (i > 0 /\ i < length p - 1) -> p_node (nth_node i p).

Lemma p_path_cons_or_des : 
  forall p, p_path p -> r_node (nth_node 0 p) ->
  (forall i, i < length p - 1 -> 
  cons_edge (nth_node i p) (nth_node (i+1) p) \/
  des_edge (nth_node i p) (nth_node (i+1) p)).	
Admitted.

(** ** Falling and rising paths *)
  Definition falling_path ( p : list node) : Prop := 
    p_path p /\ forall i, i < length(p)-1 ->
    ingred (msg_of (nth_node (i+1) p)) (msg_of (nth_node i p)).

  Definition rising_path (p : list node) : Prop := 
    p_path p /\ forall i, i < length(p)-1 ->
    ingred (msg_of (nth_node i p)) (msg_of (nth_node (i+1) p)).

(** ** Destructive and Constructive Paths *)
Definition cons_path (p :list node) : Prop := 
  p_path p /\ (forall i, i < length p - 1 -> 
               ssuccs (nth_node i p) (nth_node (i+1) p) ->
               cons_edge (nth_node i p) (nth_node (i+1) p)).

Definition cons_path_not_key (p : list node) : Prop := 
  cons_path p /\ (forall i, i < length p - 1 -> 
  des_edge (nth_node i p) (nth_node (i+1) p) ->  
  EStrand (strand_of (nth_node i p)) -> 
  exists k , msg_of (nth_node i p) = K k -> False).

Definition des_path (p :list node) : Prop := 
  p_path p /\ (forall i, i < length p - 1 -> 
               ssuccs (nth_node i p) (nth_node (i+1) p) ->
               des_edge (nth_node i p) (nth_node (i+1) p)).

Definition des_path_not_key (p : list node) : Prop := 
  des_path p /\ (forall i, i < length p - 1 -> 
  des_edge (nth_node i p) (nth_node (i+1) p) ->  
  DStrand (strand_of (nth_node i p)) -> 
  exists k, msg_of (nth_node i p) = K k -> False).

End Path.

(*********************************************************************)

(** * Penetrable Keys and Safe Keys *)
(* Penetrable key is already penetrated (K_p) or some regular strand
puts it in a form that could allow it to be penetrated, because for each key
protecting it, the matching key decryption key is already pentrable *)
Section Penetrable_Keys.
  Parameter Kp : Set.
  Parameter Pk : nat -> Key -> Prop.
  Axiom init_pkeys : sig (Pk 0) = Kp.
  Axiom next_pkeys : forall (i:nat) (k:Key), (exists (n:node) (t:msg),
    r_node n /\ xmit n /\ new_at t n /\ 
    k_ingred (sig (Pk i)) (K k) t) -> Pk (i+1) k.  

  Inductive PKeys (k:Key) : Prop :=
  | pkey_step : (exists (i:nat), Pk i k) -> PKeys k.

End Penetrable_Keys.

(*********************************************************************)

(** * Transformation paths *)
Section Trans_path.
  Definition path : Type := list (prod node msg).
  Variable p : path.
  Variable a : msg.
  Parameter default_msg : msg.
  Definition ln := fst (split p).
  Hint Resolve ln.
  Definition lm := snd (split p).
  Hint Resolve lm.

  Definition nth_msg : nat -> list msg -> msg :=
    fun (n:nat) (p:list msg) => nth_default default_msg p n.
  Hint Resolve nth_msg.

  Definition L (n:nat) := nth_msg n lm.
  Hint Resolve L.
  Definition nd (n:nat) := nth_node n ln.
  Hint Resolve nd.

  Definition transformed_edge (x y : node) (a:msg) : Prop :=
    ssuccs x y /\ atomic a /\
    exists z Ly, ssuccs x z /\ ssuccseq z y /\
    new_at Ly z /\ a <st Ly /\ Ly <[node] y.

  Definition transformed_edge_for (x y : node) (a :msg) : Prop :=
    transformed_edge x y a /\ xmit x /\ recv y.

  Definition transforming_edge_for (x y : node) (a :msg) : Prop :=
    transformed_edge x y a /\ recv x /\ xmit y.

  Definition is_trans_path : Prop := 
    (is_path ln \/ (ssuccs (nd 0) (nd 1) /\  xmit (nd 0) /\
                    xmit (nd 1) /\ is_path (tl ln))) /\
    atomic a /\
    forall (n:nat), (n < length p -> a <st (L n) /\ (L n) <[node] (nd n)) /\
                    (n < length p - 1 -> (L n = L (n+1) \/ (L n <> L (n+1) -> 
                    transformed_edge (nd n) (nd (n+1)) a))).
  
  Definition not_traverse_key : Prop :=
    forall i, i < length p - 1 -> (DStrand (strand_of (nd i)) \/ EStrand (strand_of (nd i))) ->
    exists k, msg_of (nd i) =  K k -> False.

End Trans_path.
Check not_traverse_key.
Check ln.
(*********************************************************************)

Parameter default_smsg : smsg.

(*********************************************************************)

(** ** Axiom about penetrator strands and penetrator nodes *)
  Lemma P_node_strand : 
    forall (n:node), p_node n -> PenetratorStrand (strand_of n).
  Proof.
  intros n Pn. auto.
  Qed.
 
(*********************************************************************)

