
(* This file contains all the propositions needed for authentication tets *)

Require Import Strand_Spaces Message_Algebra Strand_Library.
Require Import Lists.List.

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

  Lemma ssuccs_eq : 
    forall x y z, ssuccs x y -> ssuccseq y z -> ssuccs x z.
  Admitted.

  Lemma trans_path_ssuccs : 
      ssuccs (nd p n) (nd p (n+1)) /\ recv (nd p n) /\ xmit (nd p (n+1)). 
  Proof.
    unfold is_trans_path in Htp.
    destruct Htp as ((H3,H4),H5).
    remember (H5 n) as H6.
    destruct H6 as (H61, H62).
    remember (H62 Hn) as H7.
    case H7.
    intros. apply False_ind. apply Hcom. auto.
    intros. remember (H Hcom) as H8.
    destruct H8 as (Hrec, (Hxmit, (Hss, (m, (H9, (H10, (H11, H12))))))).
    repeat split.
    apply ssuccs_eq with (y:= m); auto.
    auto.
    auto.
  Qed.
(*
  Lemma Proposition_10 : p_node (nd p n) -> ssuccs (nd p n) (nd p (n+1)) /\ 
    (DStrand (strand_of (nd p n)) \/ EStrand (strand_of (nd p n))).
  Proof.
    intro Hpn. 
    assert (Hs : ssuccs (nd p n) (nd p (n + 1)) /\ recv (nd p n) /\ xmit (nd p (n+1))).
    apply trans_path_ssuccs; auto.
    unfold is_trans_path in Htp.
    destruct Htp as (Ha, Hb).
    split.
    apply Hs.
    
    assert (Hp : PenetratorStrand (strand_of (nd p n))).
    apply (P_node_strand (nd p n)); auto.
    elim Hp.
    intro. apply False_ind. apply (MStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply Hs.
    apply Hs.

    intro. apply False_ind. apply (KStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n).
    exists (nd p (n+1)).
    split. auto.
    split. symmetry. apply ssuccs_same_strand; apply Hs.
    apply Hs.

    intro. apply False_ind. apply (CStrand_not (strand_of (nd p n))).
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

    intro. apply False_ind. apply (SStrand_not (strand_of (nd p n))).
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
*)
End Proposition_10.
