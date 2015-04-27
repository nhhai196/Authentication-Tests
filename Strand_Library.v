
(* This chapter contains all basic results for strand spaces. *)

Require Import Lists.List Omega Ring ZArith.
Require Import Strand_Spaces Message_Algebra.
Require Import ProofIrrelevance Classical.
Require Import Relation_Definitions Relation_Operators.
Require Import List_Library.

Import ListNotations.


(** * Messages *)
(** Convert signed messages to (unsigned) messages *)

Lemma smsg_2_msg_xmit : forall n m, smsg_of n = +m -> msg_of n = m.
Proof.
intros. unfold msg_of. rewrite H. auto.
Qed.

Lemma smsg_2_msg_recv : forall n m, smsg_of n = -m -> msg_of n = m.
Proof.
intros. unfold msg_of. rewrite H. auto.
Qed.


(** *)
Lemma node_smsg_msg_xmit : forall n t,
smsg_of(n) = (+ t) ->
msg_of(n) = t.
Proof.
  intros n t H.
  unfold msg_of. rewrite H. reflexivity. 
Qed.
Hint Resolve node_smsg_msg_xmit.

Lemma node_smsg_msg_recv : forall n t,
smsg_of(n) = (- t) ->
msg_of(n) = t.
Proof.
  intros n t H.
  unfold msg_of. rewrite H. reflexivity. 
Qed.
Hint Resolve node_smsg_msg_recv.

Lemma nth_error_some_In {X:Type}: forall l i (x:X),
nth_error l i = Some x ->
List.In x l.
Proof.
  intros l. induction l.
  intros i x nth. destruct i. simpl in nth; inversion nth.
  simpl in nth; inversion nth.
  intros i x nth.
  destruct i. simpl in nth. inversion nth. left. reflexivity.
  simpl in nth. right. eapply IHl. exact nth.
Qed.
Hint Resolve nth_error_some_In.

Lemma nth_error_node : forall n,
nth_error (strand_of n) (index_of n) = Some (smsg_of n).
Proof.
  intros n.
  unfold smsg_of. destruct valid_smsg. 
  destruct n. simpl in *.
  destruct x0. simpl. auto.
Qed.
Hint Resolve nth_error_node.

Lemma strand_node : forall (s: strand) (i: nat),
i < length s ->
exists n, strand_of n = s /\ index_of n = i.
Proof.
  intros s i len.  
  eexists (exist _ (s,i) _). simpl.
  split; reflexivity.
  Grab Existential Variables.
  simpl. exact len.
Qed.
Hint Resolve strand_node.

(** Every signed message of a node must be some signed message
in the node's strand %\\%*)
Lemma smsg_in_strand : forall n s,
(strand_of n) = s ->
List.In (smsg_of n) s.
Proof.
  intros.
  eapply nth_error_some_In. subst.
  apply nth_error_node. 
Qed. 

(** * Xmit and recv *)

(** No node is both transmit and receive. %\\% *)
Lemma xmit_vs_recv: forall (n:node),  xmit(n) -> recv(n) -> False.
Proof.
intros n Hx Hr.
inversion Hx. inversion Hr.
rewrite H in H0. discriminate.
Qed.

(** every  node is either transmit or receive %\\% *)
Lemma xmit_or_recv: forall (n: node), xmit n \/ recv n.
Proof.
intros n. unfold xmit, recv. case (smsg_of n).
intros. left. exists m. auto.
intros. right. exists m. auto.
Qed.

(* TODO : move to right place *)
Lemma eq_nodes : forall (x y : node), strand_of(x) = strand_of(y) -> 
  index_of(x) = index_of(y) -> x = y.
Proof.
  intros [[xs xn] xp] [[ys yn] yp] eq_index eq_strand.
  simpl in eq_index, eq_strand. subst.
  rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.
Qed.

(** * Predecessor and message deliver *)
(** ** Baby result about msg_deliver *)
Lemma msg_deliver_xmit : forall x y, msg_deliver x y -> xmit x.
Proof.
intros x y Md.
destruct Md. 
unfold xmit. exists m; apply H.
Qed.

Lemma msg_deliver_recv : forall x y, msg_deliver x y -> recv y.
Proof.
intros x y Md.
destruct Md.
unfold recv. exists m; apply H.
Qed.

(** ** Baby results about prec *)

Theorem prec_transitive:
  forall x y z, (prec x y) -> (prec y z) -> (prec x z).
Proof.
  apply t_trans.
Qed.

Lemma deliver_prec:
  forall x y, (msg_deliver x y) -> (prec x y).
Proof.
  intros. constructor. constructor. auto.
Qed.

(** * Succsessor *)
(** This section contains lemmas about successor, transitive closure, reflexive
transitive closure, and the relations between succsessor and index of nodes.
For example, if $y$ is a successor of $x$, then the index of $y$ is greater than
the index of $x$. *)

Lemma ssucc_index_lt :
  forall x y, ssucc x y -> index_of x < index_of y.
Proof.
intros x y Sxy.
inversion Sxy. omega.
Qed.

Lemma ssuccs_index_lt :
  forall x y, ssuccs x y -> index_of x < index_of y.
Proof.
intros x y Sxy.
induction Sxy. apply ssucc_index_lt. auto.
omega.
Qed.

Lemma ssuccseq_index_lteq :
  forall x y, ssuccseq x y -> index_of x <= index_of y.
Proof.
intros x y Sxy.
induction Sxy. assert (index_of x < index_of y).
apply ssucc_index_lt. auto. omega. auto. omega.
Qed.

Lemma index_lt_one_ssucc :
  forall x y, strand_of x = strand_of y -> index_of x + 1= index_of y -> ssucc x y.
Proof. auto. Qed.

Lemma index_lt_ssuccs :
  forall x y, strand_of x = strand_of y -> index_of x < index_of y -> ssuccs x y.
Proof. 
intros x y Sxy lt.
Admitted.

Lemma ssuccs_imp_ssuccseq :
  forall x y, ssuccs x y -> ssuccseq x y.
Proof.
intros x y Sxy. 
induction Sxy. apply rt_step. auto.
apply rt_trans with (y:=y); auto.
Qed.

Lemma index_lteq_ssuccseq :
  forall x y, strand_of x = strand_of y -> index_of x <= index_of y -> ssuccseq x y.
Proof. 
intros x y Sxy lt.
assert (index_of x = index_of y \/ index_of x < index_of y). omega.
case H. intros. assert (x=y). apply eq_nodes; auto.
rewrite H1. apply rt_refl.
intros. apply ssuccs_imp_ssuccseq.
apply index_lt_ssuccs; auto.
Qed.

(** Strand-successor is irreflexive. %\\% *)
Lemma ssucc_acyclic: forall (n:node),  ssucc n n -> False.
Proof.
intros n Hs. inversion Hs. destruct H. omega.
Qed.

(** Transitive closure of strand successor is also irreflexive. *)

Lemma ssuccs_acyclic : forall (n:node), ssuccs n n -> False.
Proof.
intros n Snn.
assert (index_of n < index_of n). apply ssuccs_index_lt.
auto. omega.
Qed.

(** Strand-successors are unique. %\\% *)
Lemma ssucc_unique: 
  forall (x y z: node),  ssucc x y -> ssucc x z  -> y = z.
Proof.
  intros x y z Hxy Hxz.
  destruct Hxy, Hxz.
  apply eq_nodes; destruct H, H0; try omega; congruence.
Qed.
Hint Resolve ssucc_unique.

(** Every node and its successor are on the same strand.%\\%*)
Lemma ssucc_same_strand :
  forall (x y : node), ssucc x y -> strand_of(x) = strand_of(y).
Proof.
intros x y Sxy. inversion Sxy. destruct H; auto.
Qed.
Hint Resolve ssucc_same_strand. 

Lemma ssuccs_same_strand :
  forall (x y : node), ssuccs x y -> strand_of x = strand_of y.
Proof.
  intros x y Sxy.
  induction Sxy.
  auto. congruence.
Qed.
Hint Resolve ssuccs_same_strand.

Lemma ssuccseq_same_strand : 
  forall (x y : node), ssuccseq x y -> strand_of x = strand_of y.
Proof.
  intros x y Sxy. 
  induction Sxy.
  apply ssucc_same_strand. auto.
  auto. congruence.
Qed.

(** Successor reverses prec *)

Lemma ssucc_prec:
  forall x y, (ssucc x y) -> (prec x y).
Proof.
  intros. constructor. apply strand_edge_double. auto.
Qed.

(** Successor implies prec. *)

Lemma ssuccs_prec:
  forall x y, (ssuccs x y) -> (prec x y).
Proof.
  intros x y Sxy.
  induction Sxy.
  apply ssucc_prec; auto.
  apply prec_transitive with (y:=y); auto.
Qed.

(** Ssuccs is transitive *)

Lemma ssuccs_trans :
  forall x y z, ssuccs x y -> ssuccs y z -> ssuccs x z.
Proof.
intros x y z Sxy Syz.
apply t_trans with (y:=y); auto.
Qed.

Lemma path_edge_prec :
  forall x y, path_edge x y -> prec x y.
Proof.
  intros x y Pxy.
  inversion Pxy. 
  apply deliver_prec; auto.
  apply ssuccs_prec; apply H.
Qed.

(** * Basic Results for Penetrator Strands *)
  Lemma strand_1_node : forall n x, strand_of n = [x] -> smsg_of n = x.
  Proof.
  intros n x Snx.
  assert (H : List.In (smsg_of n) [x]).
  apply smsg_in_strand; auto.
  elim H; auto.
  intro. elim H0.
  Qed.

  (** If n is a node of a MStrand or KStrand, then n is a positive node *)
  Lemma MStrand_xmit_node : 
    forall (n:node), MStrand (strand_of n) -> xmit n.
  Proof.
    unfold xmit.
    intros n Ms. inversion Ms. exists (T t).
    apply strand_1_node. auto.
  Qed.

  Lemma KStrand_xmit_node :
    forall (n:node), KStrand (strand_of n) -> xmit n.
  Proof.
    unfold xmit.
    intros n Ms. inversion Ms. exists (K k).
    apply strand_1_node. auto.
  Qed.

  (** If n is a node of a strand of lenght 3, the singed message of n is one of the
  3 messages on the strand. *)
 
  Lemma strand_3_nodes :
    forall n x y z, strand_of n = [x;y;z] ->
    smsg_of n = x \/ smsg_of n = y \/ smsg_of n = z.
  Proof.
    intros n x y z Sxyz.
    assert (Lxyz : List.In (smsg_of n) [x;y;z]) .
    apply smsg_in_strand; auto.
    elim Lxyz. auto.
    intro Lyz. elim Lyz; auto.
    intro Lz. elim Lz; auto.
    intro Le. elim Le; auto.
  Qed.
  
  (** A function to extract the singed message of a positive node which lies on 
  a strand of lenght 3 including only one positive node. *)
  Lemma strand_3_nodes_nnp_xmit :
   forall n x y z, strand_of n = [-x;-y;+z] -> xmit n -> smsg_of n = +z.
  Proof.
  intros n x y z Sxyz Xn.
  assert (Hxyz : smsg_of n = -x \/ smsg_of n = -y \/ smsg_of n = +z).
  apply strand_3_nodes. auto.
  case Hxyz. intro. apply False_ind. apply (xmit_vs_recv n).
    auto. unfold recv; auto; exists x; auto.
  intros Hyz. case Hyz. intro. apply False_ind. apply (xmit_vs_recv n).
    auto. unfold recv; auto; exists y; auto.
  auto.
  Qed.

  (** A function to extract the singed message of a negative node which lies on 
  a strand of lenght 3. *)
 
  Lemma strand_3_nodes_nnp_recv :
   forall n x y z, strand_of n = [-x;-y;+z] -> recv n -> 
   smsg_of n = -x \/ smsg_of n = -y.
  Proof.
  intros n x y z Sxyz Xn.
  assert (Hxyz : smsg_of n = -x \/ smsg_of n = -y \/ smsg_of n = +z).
  apply strand_3_nodes. auto.
  case Hxyz. intro. left; auto.
  intro Hyz. case Hyz. right; auto.
  intro Hz. apply False_ind. apply (xmit_vs_recv n).
    unfold xmit. exists z ; auto. auto.
  Qed.

  (** A function to extract the singed message of a negative node which lies on 
  a strand of lenght 3 including only one negative node. *)

  Lemma strand_3_nodes_npp_recv :
   forall n x y z, strand_of n = [-x;+y;+z] -> recv n -> 
   smsg_of n = -x.
  Proof.
  intros n x y z Sxyz Xn.
  assert (Hxyz : smsg_of n = -x \/ smsg_of n = +y \/ smsg_of n = +z).
  apply strand_3_nodes. auto.
  case Hxyz. intro. auto.
  intro Hyz. case Hyz. intro. apply False_ind. apply (xmit_vs_recv n).
    unfold xmit. exists y. auto. auto.
  intro Hz. apply False_ind. apply (xmit_vs_recv n).
    unfold xmit. exists z ; auto. auto.
  Qed.

  (** TODO : move to right place *)
  Lemma pair_not_ingred_comp_l : forall x y, ~(P x y) <st x.
  Proof.
    intros x y Hingred.
    assert (Hlt : size (P x y ) <= size x).
    apply ingred_lt. auto.
    assert (Hgt : size (P x y) > size x).
    simpl. apply size_lt_plus_l. omega.
  Qed.

  Lemma pair_not_ingred_comp_r :
    forall x y, ~(P x y) <st y.
  Proof.
    intros x y Hst.
    assert (Hlt : size (P x y ) <= size y).
    apply ingred_lt. auto.
    assert (Hgt : size (P x y) > size y).
    simpl. rewrite (plus_comm (size x) (size y)).
    apply size_lt_plus_l. omega.
  Qed.

  Lemma enc_not_ingred_comp_l : forall x y, ~(E x y) <st x.
  Proof.
    intros x y Hingred.
    assert (Hlt : size (E x y ) <= size x).
    apply ingred_lt. auto.
    assert (Hgt : size (E x y) > size x).
    simpl. omega. omega.
  Qed.

  Lemma enc_not_ingred_comp_r :
    forall x y, ~(E x y) <st (K y).
  Proof.
    intros x y Hst.
    assert (Hlt : size (E x y ) <= size (K y)).
    apply ingred_lt. auto.
    assert (Hgt : size (E x y) > size (K y)).
    simpl. admit. (* TODO : Prove *)
    omega.
  Qed.
  
  Lemma CStrand_not_falling : 
    forall (s:strand), CStrand s -> 
      ~ exists (n1 n2 : node), recv n1 /\ xmit n2 /\ 
        strand_of n1 = s /\ strand_of n2 = s /\ 
        ingred (msg_of n2) (msg_of n1).
  Proof.
  intros s Hcs Hc.
  destruct Hc as (n1,(n2,(Hre, (Hxmit,(Hs1,(Hs2,Hingred)))))).
  inversion Hcs.
  assert (Smn2 : smsg_of n2 = + P g h).
   apply strand_3_nodes_nnp_xmit with (x:=g) (y:=h).
   congruence. auto.
  assert (Mn2 : msg_of n2 = P g h). unfold msg_of. rewrite Smn2. auto.
  assert (Smn1 : smsg_of n1 = -g \/ smsg_of n1 = -h).
    apply strand_3_nodes_nnp_recv with (x:=g) (y:=h) (z:=P g h).
    congruence. auto.
  case Smn1.
    intro Sg. assert (Mn1 : msg_of n1 = g). unfold msg_of. rewrite Sg; auto.
    apply (pair_not_ingred_comp_l g h). rewrite Mn1, Mn2 in Hingred. auto.
    intro Sh. assert (Mn1 : msg_of n1 = h). unfold msg_of. rewrite Sh; auto.
    apply (pair_not_ingred_comp_r g h). rewrite Mn1, Mn2 in Hingred. auto. 
  Qed.

  Lemma EStrand_not_falling : 
    forall (s:strand), EStrand s -> 
      ~ exists (n1 n2 : node), recv n1 /\ xmit n2  /\ 
        strand_of n1 = s /\ strand_of n2 = s /\ 
        ingred (msg_of n2) (msg_of n1).
  Proof.
  intros s Hes Hc.
  destruct Hc as (n1,(n2,(Hre, (Hxmit,(Hs1,(Hs2,Hingred)))))).
  inversion Hes.
  assert (Smn2 : smsg_of n2 = + E h k).
   apply strand_3_nodes_nnp_xmit with (x:=K k) (y:=h).
   congruence. auto.
  assert (Mn2 : msg_of n2 = E h k). unfold msg_of. rewrite Smn2. auto.
  assert (Smn1 : smsg_of n1 = -K k \/ smsg_of n1 = -h).
    apply strand_3_nodes_nnp_recv with (x:=K k) (y:=h) (z:=E h k).
    congruence. auto.
  case Smn1.
    intro Sg. assert (Mn1 : msg_of n1 = K k). unfold msg_of. rewrite Sg; auto.
    apply (enc_not_ingred_comp_r h k). rewrite Mn1, Mn2 in Hingred. auto.
    intro Sh. assert (Mn1 : msg_of n1 = h). unfold msg_of. rewrite Sh; auto.
    apply (enc_not_ingred_comp_l h k). rewrite Mn1, Mn2 in Hingred. auto.
  Qed.

(** ** Basic results about penetrator strands related to components *)
(* A MStrand or KStrand cannot have an edge *)
Lemma strand_1_node_index_0 : 
  forall x s, strand_of x  = [s] -> index_of x = 0.
Proof.
intros [[xs xn] xp] s Snx. simpl in *.
rewrite Snx in xp. simpl in xp. omega.
Qed.

Lemma MStrand_not_edge :
  forall (s:strand), MStrand s -> ~ exists (x y : node),
    strand_of x = s /\ strand_of y = s /\ ssuccs x y.
Proof.
intros s Ms (x ,(y, (Sx,(Sy, Sxy)))).
inversion Ms.
apply ssuccs_acyclic with (n:=x).
assert (Heq : x=y). apply eq_nodes.
congruence. assert (index_of x = 0).
apply strand_1_node_index_0 with (s := +T t). congruence.
assert (index_of y = 0).
apply strand_1_node_index_0 with (s := +T t). congruence.
congruence. congruence.
Qed.

Lemma KStrand_not_edge :
  forall (s:strand), KStrand s -> ~ exists (n1 n2 : node),
    strand_of n1 = s /\ strand_of n2 = s /\ ssuccs n1 n2.
Proof.
intros s Ms (x ,(y, (Sx,(Sy, Sxy)))).
inversion Ms.
apply ssuccs_acyclic with (n:=x).
assert (Heq : x=y). apply eq_nodes.
congruence. assert (index_of x = 0).
apply strand_1_node_index_0 with (s := +K k). congruence.
assert (index_of y = 0).
apply strand_1_node_index_0 with (s := +K k). congruence.
congruence. congruence.
Qed.  

Lemma CStrand_not_edge : 
  forall (s:strand), CStrand s -> ~ exists (x y : node) (a :msg), 
    strand_of x = s /\ strand_of y = s /\
    recv x /\ xmit y /\ transformed_edge x y a.
(*Proof.
intros s Cs (x,(y,(Lx,(Ly,(Sx,(Sy,(Rx,(Xy,(Sxy,(z,(Xz,(Sxz,(Szy, NLyz))))))))))))).
inversion Cs.
assert (P1 : msg_of y = P g h). apply smsg_2_msg_xmit. 
apply strand_3_nodes_nnp_xmit with (x:=g) (y:=h). congruence. auto.
assert (P2 : smsg_of x = -g \/ smsg_of x = -h).
apply strand_3_nodes_nnp_recv with (z:= P g h); auto. congruence.
case P2.
intro.*)
Admitted.

Axiom SStrand_not_edge : 
forall (s:strand), SStrand s -> ~ exists (x y : node) (a:msg), 
    strand_of x = s /\ strand_of y = s /\
    recv x /\ xmit y /\ transformed_edge x y a.


(* (** ** Baby results about xmit and recv *)

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
*)

(*
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
*)
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

(** TODO : *)
Lemma smsg_xmit_msg : 
  forall n m, smsg_of(n) = (+ m) -> msg_of(n) = m.
Proof.
  intros n m H.
  unfold msg_of. rewrite H. reflexivity. 
Qed.
Hint Resolve smsg_xmit_msg.

Lemma smsg_recv_msg : 
  forall n m, smsg_of(n) = (- m) -> msg_of(n) = m.
Proof.
  intros n m H.
  unfold msg_of. rewrite H. reflexivity. 
Qed.

Hint Resolve smsg_recv_msg.

Lemma msg_deliver_msg_eq : 
  forall x y, x --> y -> msg_of x = msg_of y.
Proof.
  intros x y edge.
  destruct edge. destruct H as (H1, (H2, H3)).
  assert (msg_of(x) = m). apply smsg_xmit_msg. auto.
  assert (msg_of(y) = m). apply smsg_recv_msg. auto.
  congruence.
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
    apply msg_deliver_msg_eq. auto.
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
    case (xmit_or_recv n). auto.
    intro. apply False_ind. apply (minimal_not_recv n); auto.
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

Lemma path_nth_app_left : 
  forall p q n, n < length p -> nth_node n (p++q) = nth_node n p.
Proof.
intros p q n. apply list_nth_app_left.
Qed. 

Lemma path_nth_app_right : 
  forall p q n, n >= length p -> n < length (p++q) -> 
    nth_node n (p++q) = nth_node (n-length p) q.
Proof.
intros p q n. apply list_nth_app_right.
Qed.

Lemma length_zero_nil : forall (p : list node), length p = 0 -> p = [].
Proof.
intros. induction p. auto. simpl in H. omega.
Qed.

Lemma path_extend : 
  forall (p : list node) (n:node) , is_path p -> 
    path_edge (nth_node (length p - 1) p) n -> is_path (p++[n]).
Proof.
intros p n Pp Pe.
unfold is_path in *. intros i Hlt.
rewrite app_length in Hlt. simpl in *. 
assert ( i < length p - 1 \/ i = length p - 1).
omega. case H.
intros. repeat rewrite path_nth_app_left. apply Pp. auto. omega. omega.
intros. 
  assert (length p = 0 \/ length p > 0). omega.
  case H1. intros. rewrite (length_zero_nil p). rewrite app_nil_l. assert (i=0).
  omega. rewrite H3. simpl. omega. auto.
  intros. assert (i+1=length p). omega. 
  rewrite path_nth_app_left. rewrite path_nth_app_right. rewrite H3.
  rewrite H0. rewrite minus_diag. apply Pe. omega. rewrite app_length.
  simpl. omega. omega.
Qed.

Lemma comp_of_node_imp_ingred : 
  forall (m:msg) (n:node), m <[node] n -> m <st (msg_of n).
Proof.
  intros.
  unfold comp_of_node in H.
  apply comp_imp_ingred.
  assumption.
Qed.

Section Trans_path.
Variable p : path.
Variable n : node.
Variable a t : msg.
Let lns := fst (split p).
Let lms := snd (split p).
Let n':= nth_node (length p - 1) lns.
Let t' := nth_msg (length p - 1) lms.
Lemma transpath_extend :
  is_trans_path p a -> (path_edge n' n) \/ (ssuccs n' n  /\ xmit n' /\ xmit n) ->
  (t' <[node] n' /\ (t' = t \/ (t'<>t -> transformed_edge n' n a))) -> 
  a <st t -> a <st t' ->
  ((is_trans_path [(n',t'); (n,t)] a /\ orig_at n' a) \/ is_trans_path (p++[(n,t)]) a).
Proof.
  intros Tp Hor (Ct'n', C) At At'.
  destruct Tp. 
  case Hor.
    intro Pe. right. 
      split. case H. 
      intro. left. unfold ln. rewrite list_split_fst.
      apply path_extend. auto. rewrite split_length_l. auto.

      intros. destruct H1 as (H2, (H3, (H4, H5))). right. unfold nd.
      unfold ln. repeat rewrite list_split_fst.
      repeat rewrite path_nth_app_left. split; auto.
      split. auto. split. auto. rewrite list_tl_extend. apply path_extend.
      auto. 
Admitted.
End Trans_path.

Lemma comp_trans : forall a L n, a <st L -> L <[node] n -> a <st (msg_of n).
Proof.
intros a L n aL Ln.
apply ingred_trans with (y:= L).
auto. apply comp_of_node_imp_ingred. auto.
Qed.
Hint Resolve comp_trans.

Section Prop_11.
  Variable a L : msg.
  Variable n : node.
  Definition P_ingred : node -> Prop:=
    fun (n':node) => ssuccs n' n /\ ingred a (msg_of n').

  Definition P_comp : node -> Prop :=
    fun (n':node) => ssuccs n' n /\ L <[node] n' /\ a <st L.

  Lemma P_comp_imp_P_ingred : 
    forall x, P_comp x -> P_ingred x.
  Proof.
    intros x Pcom.
    split. apply Pcom.
    apply comp_trans with (L:=L); apply Pcom.
  Qed.

  Lemma ingred_of_earlier : 
      a <st (msg_of n) -> xmit n -> ~ orig_at n a -> exists n', P_ingred n'.
  Proof.
    intros Hst Hxmit Hnorig.
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

  Lemma new_at_earlier :
     a <st L -> L <[node] n -> ~ new_at L n -> exists n', P_comp n'.
  Proof.
    intros aL Can Nan. apply Peirce. intros.
    apply False_ind. apply Nan.
    split; auto. intros. apply H.
    exists n'. split. auto.
    split; auto.
  Qed.

  Lemma not_orig_exists : 
    a <st (msg_of n) -> xmit n -> ~ orig_at n a -> has_min_elt P_ingred.
  Proof.
    intros Hxmit Hst Hnorig.
    apply always_min_elt.
    apply ingred_of_earlier; assumption.
  Qed.
  Hint Resolve not_orig_exists.

  Lemma not_new_at_exists :
    a <st L -> L <[node] n -> ~new_at L n -> has_min_elt P_comp.
  Proof.
    intros aL Can Nan. apply always_min_elt.
    apply new_at_earlier; auto.
  Qed.

  Lemma min_xmit_orig : 
    forall (x:node), xmit x -> is_minimal P_ingred x -> orig_at x a.
  Proof.
    intros. unfold orig_at. destruct H0. unfold P_ingred in H0.
    repeat split. auto. apply H0.
    intros. apply (H1 n'). apply ssuccs_prec. auto. 
    unfold P_ingred. split. apply ssuccs_trans with (y:=x).
    auto. apply H0. auto.
   Qed.

  Lemma min_new_at : 
    forall (x:node), is_minimal P_comp x -> new_at L x.
  Proof.
    intros. destruct H.
    split. apply H.
    intros. apply (H0 n'). apply ssuccs_prec. auto.
    split. apply ssuccs_trans with (y:=x).
    auto. apply H. split; auto. apply H.
  Qed.
  
  Lemma eq_strand_trans : 
    forall x y z, strand_of x = strand_of y -> strand_of y = strand_of z ->
    strand_of x = strand_of z.
  Proof.
    intros x y z Sxy Syz.
    congruence.
  Qed.

  Lemma not_ssuccseq : 
    forall (x y : node), ~(x ==>* y) -> strand_of x = strand_of y -> y ==>+ x.
  Proof.
    intros x y N Sxy. apply index_lt_ssuccs. auto. 
    case lt_dec with (m:= index_of x) (n:= index_of y).
    intro. omega.
    intro. apply False_ind. apply N. apply index_lteq_ssuccseq.
    auto. omega.
  Qed.

  Lemma orig_precede_new_at :
    forall x y, is_minimal P_ingred x -> is_minimal P_comp y -> ssuccseq x y.
  Proof.
    intros x y Pin Pcom.
    apply Peirce. intros. assert (Syx : y ==>+ x).
    apply not_ssuccseq. auto.
    apply eq_strand_trans with (y:=n).
    apply ssuccs_same_strand. apply Pin.
    symmetry. apply ssuccs_same_strand. apply Pcom.
    apply False_ind. destruct Pin. apply (H1 y).
    apply ssuccs_prec; auto. apply P_comp_imp_P_ingred.
    apply Pcom.
  Qed.
    
End Prop_11.

Lemma msg_deliver_same_comp : 
  forall x y Ly, msg_deliver x y -> Ly <[node] y -> 
  exists Lx, Lx <[node] x /\ Lx = Ly.
Proof.
  intros x y Ly Mxy Lyy.
  exists Ly. split. unfold comp_of_node.  
  assert (msg_of x = msg_of y). 
  apply msg_deliver_msg_eq. auto.
  rewrite H. auto. auto.
Qed.

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

Lemma msg_deliver_comp : 
  forall (n1 n2:node) (m:msg),
    msg_deliver n1 n2 /\ 
    comp_of_node m n2 -> comp_of_node m n1.
Proof.
  intros.
  destruct H as (H1,H2).
  unfold comp_of_node.
  assert (msg_of n1 = msg_of n2).
  apply msg_deliver_msg_eq. auto.
  rewrite H.
  unfold comp_of_node in H2. auto.
Qed.
Hint Resolve msg_deliver_comp.

Lemma new_at_imp_comp : forall m n, new_at m n -> m <[node] n.
Proof.
  intros m n H.
  unfold new_at in H.
  apply H.
Qed.

Lemma orig_dec : forall n a, orig_at n a \/ ~ orig_at n a.
Proof. intros; tauto. Qed.

Lemma new_at_dec : forall (n:node) (L:msg) , new_at L n \/ ~new_at L n.
Proof.
  intros n L. tauto.
Qed.

Lemma orig_imp_ingred : forall n a, orig_at n a -> a <st msg_of n.
Proof.
intros. apply H.
Qed.

Lemma orig_precede : 
  forall (x y : node) (a Ly : msg), atomic a -> orig_at x a -> 
  a <st Ly -> Ly <[node] y -> strand_of x = strand_of y -> ssuccseq x y.
Proof.
intros x y a Ly Atom Oxa aLy Lyy Sxy.
apply Peirce. intros. assert (Syx : y ==>+ x).
apply not_ssuccseq; auto. apply False_ind.
destruct Oxa as (_, (_, Contra)).
apply Contra with (n':=y). auto.
apply comp_trans with (L:=Ly); auto.
Qed.

Lemma ssuccseq_imp_eq_or_ssuccs :
  forall x y, ssuccseq x y -> x = y \/ ssuccs x y.
Proof.
intros x y Sxy. induction Sxy.
right. apply t_step; auto.
left. reflexivity.
case IHSxy1.
  intro. subst. auto. 
  intro. case IHSxy2.
    intro. subst. auto.
    intro. right. 
    apply ssuccs_trans with (y:=y); auto.
Qed.

(*
Lemma orig_new_at : 
  forall (x y : node) (a Ly : msg), xmit y -> atomic a ->
  ssuccs x y -> orig_at x a -> a <st Ly -> Ly <[node] y -> 
  exists  x' Lx, a <st Lx /\ Lx <[node] x' /\ (transformed_edge x y Lx Ly \/Lx = Ly).
Proof.
intros x y a Ly Xy Atom Sxy Oxa ALy Lyy.

case (new_at_dec y Ly).
  intro NLyy.
  assert (Ex : exists Lx, a<st Lx /\ Lx <[node] x).
  apply ingred_exists_comp_of_node. auto. 
  apply orig_imp_ingred. auto. destruct Ex as (Lx, (aLx, Lxx)).
  exists x, Lx. split. auto. split; auto.
  left. unfold transformed_edge. 
  split. auto.
  intros. exists y. split; auto. apply ssuccs_imp_ssuccseq; auto.
  split. apply rt_refl. auto.

  intro NNLyy.
  assert (Hmin : has_min_elt (P_comp Ly y)).
  apply not_new_at_exists; auto. 
  destruct Hmin as (z, (H1, H2)).
  assert (Sxz : ssuccseq x z). apply orig_precede with (a:=a) (Ly:=Ly); auto.
  apply H1. apply eq_strand_trans with (y:=y).
  apply ssuccs_same_strand; auto. symmetry. apply ssuccs_same_strand. apply H1.
  case (ssuccseq_imp_eq_or_ssuccs x z); auto.
    intro Exz. exists x, Ly. subst. split. auto. split. apply H1.
    right; auto.

    intro SSxz.
    case (xmit_or_recv z).
    intro Xz.  assert (Ex : exists Lx, a<st Lx /\ Lx <[node] x).
    apply ingred_exists_comp_of_node. auto. 
    apply orig_imp_ingred. auto. destruct Ex as (Lx, (aLx, Lxx)). 
    exists x, Lx.  split; auto. split; auto. left.
    split; auto. exists z. split; auto.
    split. apply ssuccs_imp_ssuccseq. apply H1. apply min_new_at with (n:=y).
    split; auto.

    intro Rz. exists z, Ly. split; auto. split; auto. apply H1.
Qed.

*)
Section back_ward.
  Variable a L: msg.
  Variable n : node.

Lemma backward_construction :  
    atomic a -> a <st L -> L <[node] n -> ~ orig_at n a ->
    exists (n':node) (L':msg), (path_edge n' n \/ (ssuccs n' n  /\ xmit n' /\ xmit n /\ orig_at n' a)) /\
      (a <st L' /\ L' <[node] n' /\ (L' = L \/ (L'<>L -> transformed_edge n' n a))).
Proof.
  intros Hatom Hcom Hst Norig.
  case (xmit_or_recv n).
  Focus 2. intros Hrecv.
  assert (Hex : exists (n':node), msg_deliver n' n). 
  apply was_sent. auto.
  destruct Hex as (n', Hmsg_deli).
  exists n'; exists L. 
  split. left. apply path_edge_single. auto.
  split. exact Hcom.
  split. apply msg_deliver_comp with (n1:=n') (n2:=n).
  split; assumption.
  left. trivial.  

  intros Hxmit.
    assert (Hmin : has_min_elt (P_ingred a n)).
    apply not_orig_exists. apply comp_trans with (L:= L); auto. auto. auto.
    destruct Hmin as (n', Hm).
    case (xmit_or_recv n').
    intros Xn'.
    assert (Orign : orig_at n' a). 
    apply min_xmit_orig with (n:=n); auto.

    assert (Cn' : exists L', a <st L' /\ L' <[node] n').
    apply ingred_exists_comp_of_node. auto. 
    apply orig_imp_ingred; auto. destruct Cn' as (L', (aL', L'n')). 
    case (new_at_dec n L).
 
      intros NLn.    
      exists n', L'. split. right. split. destruct Hm. apply H. auto.
      split. auto. split. auto. case (eq_msg_dec L' L). auto.
      intros. right. intros. split. apply Hm. split; auto. exists n, L. 
      split. apply Hm. split. apply rt_refl. split; auto.

      intros NNLn.
      assert (Hmin : has_min_elt (P_comp a L n)).
      apply not_new_at_exists; auto. 
      destruct Hmin as (z, (H1, H2)).
      assert (Sn'z : ssuccseq n' z). 
      apply orig_precede with (a:=a) (Ly:=L); auto.
      apply H1. apply eq_strand_trans with (y:=n).
      apply ssuccs_same_strand; auto. apply Hm. symmetry.
      apply ssuccs_same_strand. apply H1.
      case (ssuccseq_imp_eq_or_ssuccs n' z); auto.
        
        intros Eqn'z.
        exists n', L.
        split. right. split. apply Hm. split; auto.
        split; auto. split. subst. apply H1. left. auto.

        intros SSn'z.
        exists n', L'. split. right. split; auto. apply Hm.
        split; auto. split. auto.
        right. intros Neq. split. apply Hm. split; auto.
        exists z, L. split; auto. split. apply ssuccs_imp_ssuccseq. apply H1.
        split. apply min_new_at with (a:=a) (n:=n). split; auto. split; auto.

  intros Hrecv.
    assert (Cn' : exists L', a <st L' /\ L' <[node] n').
    apply ingred_exists_comp_of_node. auto. 
    apply Hm. destruct Cn' as (L', (aL', L'n')).
    case (new_at_dec n L).
    intros NLn.

    exists n', L'. split. left. apply path_edge_double. split; auto. apply Hm. 
    split; auto. split. auto. right.
    intros Neq. split. apply Hm. split; auto. exists n, L.
    split. apply Hm. split. apply rt_refl. split. auto. split; auto.

   intros NNLn.
      assert (Hmin : has_min_elt (P_comp a L n)).
      apply not_new_at_exists; auto. 
      destruct Hmin as (z, (H1, H2)).
      assert (Sn'z : ssuccseq n' z). 
      apply orig_precede_new_at with (a:=a) (L:=L) (n:=n). auto.
      split; auto.
      case (ssuccseq_imp_eq_or_ssuccs n' z); auto.
        
        intros Eqn'z.
        exists n', L.
        split. left. apply path_edge_double; auto. 
        split. apply Hm. split; auto.
        split; auto. split. subst. apply H1. left. auto.

        intros SSn'z.
        exists n', L'. split. left. apply path_edge_double; auto.
        split; auto. apply Hm. split; auto.
        split. auto.
        right. intros Neq. split. apply Hm. split; auto.
        exists z, L. split; auto. split. apply ssuccs_imp_ssuccseq. apply H1.
        split.
        apply min_new_at with (a:=a) (n:=n). split; auto. split; auto.
 Qed.
   
End back_ward.

