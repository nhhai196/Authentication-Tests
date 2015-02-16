     (* Time-stamp: <Mon 2/9/15 16:19 Dan Dougherty Strands.v> *)

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

  (** Concatenation Strand *)
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

(** ** Falling and rising paths *)
  Definition falling_path ( p : list node) : Prop := 
    p_path p /\ forall i, i < length(p)-1 ->
    ingred (msg_of (nth_node (i+1) p)) (msg_of (nth_node i p)).

  Definition rising_path (p : list node) : Prop := 
    p_path p /\ forall i, i < length(p)-1 ->
    ingred (msg_of (nth_node i p)) (msg_of (nth_node (i+1) p)).

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

  Definition transformed_edge (x y : node): Prop :=
    ssuccs x y /\ exists z, xmit z /\ ssuccs x z /\ ssuccseq z y. 

  Definition is_trans_path : Prop := 
    (is_path ln \/ (ssuccs (nd 0) (nd 1) /\  xmit (nd 0) /\ xmit (nd 1) /\ is_path (tl ln))) /\
    forall (n:nat), (n < length p -> (L n) <[node] (nd n)) /\
      (n < length p - 1 -> (L n = L (n+1) \/ (L n <> L (n+1) -> 
        recv (nd n) /\ xmit (nd (n+1)) /\ ssuccs (nd n) (nd (n+1)) /\
        (exists m, xmit m /\ new_at (L (n+1)) m  /\ 
          ssuccs (nd n) m /\ ssuccseq m (nd (n+1)))))).

End Trans_path.

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


(*
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
Lemma MStrand_not_edge :
  forall (s:strand), MStrand s -> ~ exists (n1 n2 : node),
    strand_of n1 = s /\ strand_of n2 = s /\ ssuccs n1 n2.
Proof.
intros s Hm Hex.
destruct Hex as (n1, (n2, (Hs1, (Hs2, Hss)))). 
inversion Hm.
assert (Hin1 : set_In (smsg_of n1) s). apply smsg_on_strand. auto.
assert (Hin2 : set_In (smsg_of n2) s). apply smsg_on_strand. auto.
rewrite H in Hin1, Hin2. elim Hin1.
intro. elim Hin2.
Admitted.
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

(** * Edges *)
(** ** Transformed edges *)
(** ** Transforming edges *)

(*********************************************************************)

(* I want to define some constant of type msg here but we don't know any constant 
of this type, so I just say it is some variable *)
Variable default_msg : msg.


(* Baby result : a single pair (n, L) is a trans-foramtion path *)
Open Scope list_scope.
Check [1].
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
Admitted.
End P13.
End Path.    
*)
