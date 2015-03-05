
(* This file contains all the propositions needed for authentication tets *)

Require Import Strand_Spaces Message_Algebra Strand_Library.
Require Import Lists.List Relation_Definitions Relation_Operators.
Require Import List_Library.
Import ListNotations.

(** * Proposition 7 *)
Section P7_1.
  Variable i : nat.
  Variable p : list node.
  Let p_i := nth_node i p.
  Let p_i1 := nth_node (i+1) p.
  Hypothesis Hc : 0 < i /\ i < length p - 1.
  Hypothesis Hfp : falling_path p.
  Hypothesis Hrec : recv p_i.
  Hypothesis Hpn : p_node p_i.
  Let s := strand_of p_i.

  Lemma path_edge_pi_pi1 : path_edge p_i p_i1.
  Proof.
  destruct Hfp as (Hp,_). destruct Hp as (P, _).
  unfold is_path in P.
  apply (P i); apply Hc.
  Qed.

  Lemma P7_1_aux1 : xmit p_i1 /\ strand_of p_i1 = strand_of p_i.
  Proof.
  assert (Pe : path_edge p_i p_i1).
  apply path_edge_pi_pi1; auto.
  inversion Pe. apply False_ind. apply xmit_vs_recv with (n:=p_i).
  apply msg_deliver_xmit with (y:=p_i1). auto. auto.
  split. apply H.
  destruct H. symmetry. apply ssuccs_same_strand. auto.
  Qed.
  
  Lemma pi1_ingred_pi : msg_of p_i1 <st msg_of p_i.
  Proof.
  destruct Hfp. apply (H0 i). apply Hc.
  Qed.

  Lemma P7_1_aux : DStrand (strand_of p_i) \/ SStrand (strand_of p_i).
  Proof.
    assert (Ps : PenetratorStrand s). apply Hpn. 
    inversion Ps. 
    apply False_ind. apply xmit_vs_recv with (n:=p_i).
      apply MStrand_xmit_node; auto. auto.
    
    apply False_ind. apply xmit_vs_recv with (n:=p_i).
      apply KStrand_xmit_node; auto. auto.
   
    apply False_ind. apply (CStrand_not_falling s) ; auto.
      exists p_i, p_i1. split; auto. split. apply P7_1_aux1.
      split; auto. split. apply P7_1_aux1. apply pi1_ingred_pi.

    auto.

    apply False_ind. apply False_ind. apply (EStrand_not_falling s) ; auto.
      exists p_i, p_i1. split; auto. split. apply P7_1_aux1.
      split; auto. split. apply P7_1_aux1. apply pi1_ingred_pi.

    auto.
    Qed.  

Section P7_1_a.
  Variable h : msg.
  Variable k : Key.
  Hypothesis Heq : msg_of p_i = E h k.
  Lemma P7_1a : 
    DStrand s /\ msg_of p_i1 = h.
  Proof.
    case P7_1_aux.
    intro Ds. split; auto.
    inversion Ds.
    assert (Smpi : smsg_of p_i = - K k' \/ smsg_of p_i = - E h0 k0).
      apply strand_3_nodes_nnp_recv with (z:=h0); auto.
      case Smpi. intro Kk. assert (msg_of p_i = K k').
      unfold msg_of. rewrite Kk; auto. rewrite H1 in Heq. discriminate.
   intro. assert (msg_of p_i = E h0 k0). unfold msg_of; rewrite H1; auto.
     rewrite Heq in H2. assert (h=h0 /\ k = k0). apply ((enc_free h k h0 k0)); auto.
     destruct H3; subst.
     apply node_smsg_msg_xmit. 
     apply strand_3_nodes_nnp_xmit with (x:= K k') (y:=E h0 k0). 
     assert (strand_of p_i1 = strand_of p_i). apply P7_1_aux1. congruence.
     apply P7_1_aux1.
  intro. inversion H.
    assert (smsg_of p_i = - P g h0). 
    apply strand_3_nodes_npp_recv with (y:= g) (z:=h0). auto. auto.
    assert (msg_of p_i= P g h0). apply node_smsg_msg_recv; auto. 
    rewrite H2 in Heq. discriminate.
  Qed.

End P7_1_a.

Section P7_1_b.
  Variable g h : msg.
  Lemma P7_1_b : 
    SStrand s /\ (msg_of p_i1 = h \/ msg_of p_i1 = g).
Admitted.
End P7_1_b.
End P7_1.

(*********************************************************************)

(** * Proposition 10 *)
Section Proposition_10.
  Variable p : path.
  Variable n : nat.
  Hypothesis Htp : is_trans_path p.
  Hypothesis Hn : n < length p - 1.
  Hypothesis Hcom : L p n <> L p (n+1).
  Hypothesis Pnode : p_node (nd p n).

  Lemma trans_path_ssuccs : 
      ssuccs (nd p n) (nd p (n+1)). 
  Proof.
    destruct Htp as (H3,H4).
    destruct (H4 n)as (H41, H42).
    destruct H42. auto.
      apply False_ind. apply Hcom. auto.
    destruct H. auto.
    destruct H0 as (m,(Hxmit,(Hnew,(Hssuc,Hsseq)))).
    auto.
  Qed.

  Lemma Prop10_recv_xmit : recv (nd p n) /\ xmit (nd p (n+1)).
  Admitted.

  Lemma Proposition_10 :  ssuccs (nd p n) (nd p (n+1)) /\ 
    (DStrand (strand_of (nd p n)) \/ EStrand (strand_of (nd p n))).
  Proof.
    destruct Htp as (Ha, Hb).
    destruct (Hb n) as (Q1,Q2).
    split.
      apply trans_path_ssuccs.
    
    assert (Hp : PenetratorStrand (strand_of (nd p n))).
    apply (P_node_strand (nd p n)); auto.
    elim Hp.
    intro. apply False_ind. apply (MStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply trans_path_ssuccs.
    apply trans_path_ssuccs.

    intro. apply False_ind. apply (KStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand; apply trans_path_ssuccs.
    apply trans_path_ssuccs.

    intro. apply False_ind. apply (CStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n). exists (nd p (n+1)). exists (L p n). exists (L p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply trans_path_ssuccs.
    split. apply Prop10_recv_xmit.
    split. apply Prop10_recv_xmit.
    case (Q2 Hn). intro. apply False_ind. apply Hcom. auto.
    intro. apply (H0 Hcom).
    
    intro. apply False_ind. apply (SStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n). exists (nd p (n+1)). exists (L p n). exists (L p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply trans_path_ssuccs.
    split. apply Prop10_recv_xmit.
    split. apply Prop10_recv_xmit.
    case (Q2 Hn). intro. apply False_ind. apply Hcom. auto.
    intro. apply (H0 Hcom).

    auto.
    auto.
  Qed.

End Proposition_10.

(*********************************************************************)

Section Proposition_11.

Lemma single_node_tp : 
  forall (n:node) (m:msg), 
    m <[node] n -> is_trans_path [(n,m)].
Proof.
  intros n m Hcom.
  unfold is_trans_path.
  simpl. split. left. unfold is_path. simpl. intros i Hcontra. 
  apply False_ind; omega.

  intros n0. split. intro Hn0. assert (n0=0). omega. rewrite H. 
  assert ( L [(n,m)] 0 = m). auto.
  assert (nd [(n,m)] 0 = n). auto. congruence.

  intros n1.
  apply False_ind. omega.
Qed.

Definition p11_aux (n:node) (a t : msg) p : Prop := 
  let ln := fst (split p) in 
  let lm := snd (split p) in 
  is_trans_path p /\ 
  orig_at (nth_node 0 ln) a /\
  nth_node (length p - 1) ln = n /\ 
  nth_msg (length p -1) lm = t /\
  forall (i:nat), i < length p -> a <st (nth_msg i lm).

Definition p11_aux2 (n:node): Prop := 
  forall (a t : msg), atomic a -> a <st t -> t <[node] n ->
  exists p, p11_aux n a t p.
  
Lemma tpath_extend : 
  forall x a t, a <st t -> t <[node] x ->
  (exists (x':node) (t':msg), (path_edge x' x \/ (ssuccs x' x  /\ xmit x' /\ xmit x /\ orig_at x' a)) /\
  (a <st t' /\ t' <[node] x' /\ (t' = t \/ (t'<>t -> transformed_edge x' x t' t))) /\ 
  exists p, p11_aux x' a t' p) ->
  exists p, p11_aux x a t p.
Proof.
intros x a t Sat Ntx (x', (t', (C1, (C2, (p, C4))))).
unfold p11_aux in *.
destruct C4 as (C5, (C6, (C7, (C8, C9)))).
assert (S : is_trans_path [(nth_node (length p - 1) (fst (split p)), 
                            nth_msg (length p - 1) (snd (split p))); (x,t)] /\
                            orig_at (nth_node (length p - 1) (fst (split p))) a
            \/ is_trans_path (p++[(x,t)])).
apply transpath_extend; auto. rewrite C7.
  case C1.
  intro. left. auto.
  intro. right. repeat split; apply H.
  rewrite C7, C8 in *. destruct C2. auto.
  rewrite C8. apply C2.
  rewrite C7, C8 in *.
case S.
  intro. exists [(x', t'); (x, t)].
  split. apply H. split. simpl. assert (nth_node 0 [x'; x] = x'). auto.
  rewrite H0. apply H. 
  simpl. split. auto. split. auto.
  intros. assert (i=0 \/ i=1). omega.
    case H1. intro. rewrite H2. assert((nth_msg 0 [t';t]) = t'). auto.
    rewrite H3. apply C2.
    intro. assert (nth_msg 1 [t';t] = t). auto. rewrite H2. rewrite H3. auto.
    
  intro. exists (p++[(x,t)]).
  split. auto. rewrite list_split_fst. rewrite path_nth_app_left.
  split; auto. rewrite app_length. simpl. assert (length p + 1- 1=length p). omega.
  rewrite H0. split. admit. split. admit.
  intro.
Admitted.

Lemma Prop_11 : forall (n' : node), p11_aux2 n'.
Proof.
apply well_founded_ind with (R:=prec).
exact wf_prec.
  intros x IH.                                 
  intros a t Sat Atoma Stx. 
  assert (Orig : orig_at x a \/ ~ orig_at x a). tauto.
  case Orig.
  intros Oxa. exists ([(x, t)]). split.
  apply single_node_tp with (n:=x) (m:=t). auto.
  split; auto. split; auto. split; auto.
  intros. simpl in H. assert (i=0). omega. rewrite H0;auto.

  intro NOrig. case (xmit_or_recv x).
  Focus 2. intro Recvx. assert (exists y, msg_deliver y x).
  apply was_sent; auto. apply tpath_extend; auto. destruct H as (y, Dyx).
  exists y, t. split. left. apply path_edge_single. auto.
  split. split. auto. split. auto. apply msg_deliver_comp with (n2:=x).
  split; auto. left; auto. apply IH. apply deliver_prec; auto. auto.
  auto. apply msg_deliver_comp with (n2:=x). split; auto.

  intros. 
    assert (exists (x':node) (t':msg), (path_edge x' x \/ (ssuccs x' x  /\ xmit x' /\ xmit x /\ orig_at x' a)) /\
           (a <st t' /\ t' <[node] x' /\ (t' = t \/ (t'<>t -> transformed_edge x' x t' t)))).
  apply backward_construction; auto. destruct H0 as (y, (Ly, (H1, H2))).
  apply tpath_extend; auto. exists y, Ly. split. apply H1.
  split. apply H2.
  apply IH. case H1.
    intro. apply path_edge_prec. auto.
    intro. apply ssuccs_prec. apply H0.
  auto. apply H2. apply H2.
Qed.

End Proposition_11.
