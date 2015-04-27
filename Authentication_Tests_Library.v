
(* This file contains all the propositions needed for authentication tets *)

Require Import Strand_Spaces Message_Algebra Strand_Library.
Require Import Lists.List Relation_Definitions Relation_Operators.
Require Import List_Library.
Import ListNotations.

(** * Proposition 6 *)
Lemma P6_1 : forall p, des_path_not_key p -> falling_path p.
Proof.
  intros p Dp. destruct Dp.
  split. apply H.
  intros i Hlt. destruct H as (pp, H). destruct pp. 
  unfold is_path in H1.
  assert (path_edge (nth_node i p) (nth_node (i + 1) p)).
  apply (H1 i); auto. inversion H3. 
  assert (msg_of (nth_node i p) = msg_of (nth_node (i+1) p)).
  apply msg_deliver_msg_eq with (y:=nth_node (i+1) p). auto. 
  rewrite H5. apply ingred_refl. destruct H4 as (H5, (H6, H7)).
Admitted.

Lemma P6_2 : forall p, cons_path_not_key p -> rising_path p.
Admitted.  
  
(*********************************************************************)

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
  Variable a : msg.
  Hypothesis Htp : is_trans_path p a.
  Hypothesis Hn : n < length p - 1.
  Hypothesis Hcom : L p n <> L p (n+1).
  Hypothesis Pnode : p_node (nd p n).

  Lemma trans_path_ssuccs : 
      ssuccs (nd p n) (nd p (n+1)). 
  Proof.
    destruct Htp as (H2, (H3,H4)).
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
    destruct Htp as (Ha, (Ha', Hb)).
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
    exists (nd p n),(nd p (n+1)), a.
    split. auto.
    split. symmetry. apply ssuccs_same_strand. apply trans_path_ssuccs.
    split. apply Prop10_recv_xmit.
    split. apply Prop10_recv_xmit.
    case (Q2 Hn). intro. apply False_ind. apply Hcom. auto.
    intro. apply (H0 Hcom).
    
    intro. apply False_ind. apply (SStrand_not_edge (strand_of (nd p n))).
    auto.
    exists (nd p n),(nd p (n+1)), a.
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

(** * Proposition 11 *)

Section Proposition_11.

Lemma single_node_tp : 
  forall (n:node) (m a:msg), 
    atomic a -> a <st m -> m <[node] n -> is_trans_path [(n,m)] a.
Proof.
  intros n m a Atom Ingred Hcom.
  unfold is_trans_path.
  simpl. split. left. unfold is_path. simpl. intros i Hcontra. 
  apply False_ind; omega.

  split. auto.
  intros n0. split. intro Hn0. assert (n0=0). omega. rewrite H. 
  assert ( L [(n,m)] 0 = m). auto.
  assert (nd [(n,m)] 0 = n). auto.
  split; congruence.

  intros n1.
  apply False_ind. omega.
Qed.

Lemma single_node_not_traverse_key :
  forall (n:node) (m a : msg), atomic a -> a <st m -> m <[node] n ->
  is_trans_path [(n,m)] a -> not_traverse_key [(n,m)].
Proof.
intros.
unfold not_traverse_key. intros.
simpl in H3. omega.
Qed.

Definition p11_aux (n:node) (a t : msg) p : Prop := 
  let ln := fst (split p) in 
  let lm := snd (split p) in 
  is_trans_path p a /\ 
  orig_at (nth_node 0 ln) a /\
  nth_node (length p - 1) ln = n /\ 
  nth_msg (length p -1) lm = t /\
  forall (i:nat), i < length p -> a <st (nth_msg i lm) /\
  not_traverse_key p.

Definition p11_aux2 (n:node): Prop := 
  forall (a t : msg), atomic a -> a <st t -> t <[node] n ->
  exists p, p11_aux n a t p.
  
Lemma tpath_extend : 
  forall x a t, a <st t -> t <[node] x ->
  (exists (x':node) (t':msg), (path_edge x' x \/ (ssuccs x' x  /\ xmit x' /\ xmit x /\ orig_at x' a)) /\
  (a <st t' /\ t' <[node] x' /\ (t' = t \/ (t'<>t -> transformed_edge x' x a))) /\ 
  exists p, p11_aux x' a t' p) ->
  exists p, p11_aux x a t p.
Proof.
(*intros x a t Sat Ntx (x', (t', (C1, (C2, (p, C4))))).
unfold p11_aux in *.
destruct C4 as (C5, (C6, (C7, (C8, C9)))).
assert (S : is_trans_path [(nth_node (length p - 1) (fst (split p)), 
                            nth_msg (length p - 1) (snd (split p))); (x,t)] a /\
                            orig_at (nth_node (length p - 1) (fst (split p))) a
            \/ is_trans_path (p++[(x,t)]) a).
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
  intro. *)
Admitted.

Lemma Prop_11 : forall (n' : node) , p11_aux2 n'.
Proof.
apply well_founded_ind with (R:=prec).
exact wf_prec.
  intros x IH.                                 
  intros a t Sat Atoma Stx. 
  assert (Orig : orig_at x a \/ ~ orig_at x a). tauto.
  case Orig.
  intros Oxa. exists ([(x, t)]). split.
  apply single_node_tp with (n:=x) (m:=t); auto.
  split; auto. split; auto. split; auto.
  intros. simpl in H. assert (i=0). omega.
  split. rewrite H0;auto. apply single_node_not_traverse_key with (a:=a); auto.
  apply single_node_tp with (n:=x) (m:=t); auto.

  intro NOrig. case (xmit_or_recv x).
  Focus 2. intro Recvx. assert (exists y, msg_deliver y x).
  apply was_sent; auto. apply tpath_extend; auto. destruct H as (y, Dyx).
  exists y, t. split. left. apply path_edge_single. auto.
  split. split. auto. split.  apply msg_deliver_comp with (n2:=x). 
  split; auto. left; auto. apply IH. apply deliver_prec; auto. auto.
  auto. apply msg_deliver_comp with (n2:=x). split; auto.

  intros. 
  assert (exists (x':node) (t':msg), 
         (path_edge x' x \/ (ssuccs x' x  /\ xmit x' /\ xmit x /\ orig_at x' a)) /\
         (a <st t' /\ t' <[node] x' /\ (t' = t \/ (t'<>t -> transformed_edge x' x a)))).
  apply backward_construction; auto. destruct H0 as (y, (Ly, (H1, H2))).
  apply tpath_extend; auto. exists y, Ly. split. apply H1.
  split. apply H2.
  apply IH. case H1.
    intro. apply path_edge_prec. auto.
    intro. apply ssuccs_prec. apply H0.
  auto. apply H2. apply H2.
Qed.

End Proposition_11.

(*********************************************************************)

(** * Proposition 13 *)
(*
Section P13. 
  Variable pl : path.
  Let p := fst (split pl).
  Let l := snd (split pl).
  Hypothesis Hpp : p_path p.
  Hypothesis Hp1 : simple (msg_of (nth_node 0 p)).

  Lemma Prop13 : 
    forall (i:nat), i < length p - 1 -> 
    exists (j:nat), (j <= i /\ msg_of (nth_node j p) = nth_msg i l).
  Proof.
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

(*********************************************************************)
(** * Proposition 17 *)

Section P17.
Definition Prop17_aux (n:node) : Prop :=
  forall (k : Key), msg_of n = K k -> PKeys k.

Lemma Prop17 : forall (n:node), Prop17_aux n.
Proof.
  apply well_founded_ind with (R:=prec).
  exact wf_prec.
  intros x IH. unfold Prop17_aux in *.
Admitted.
End P17.

(*********************************************************************)

Definition not_proper_subterm (t:msg) :=  
  exists (n': node) (L : msg), 
  t <st L -> t <> L -> r_node n' -> L <[node] n' -> False.

Definition r_comp (L:msg) (n:node) := L <[node] n /\ r_node n.

Definition not_constant_tp (p:path) :=
  (nth_msg 0 (lm p)) <> (nth_msg (length p - 1) (lm p)).

Definition largest_index (p:path) (i:nat) :=
  not_constant_tp p /\ i < length p - 1 /\ 
  nth_msg i (lm p) <> nth_msg (i+1) (lm p) /\ 
  forall j, j < length p -> j > i -> 
  nth_msg j (lm p) = nth_msg (length p - 1) (lm p).

Definition smallest_index (p:path) (i:nat) :=
  not_constant_tp p /\ i < length p - 1 /\ 
  nth_msg i (lm p) <> nth_msg (i+1) (lm p) /\ 
  forall j, j <= i -> nth_msg j (lm p) = nth_msg 0 (lm p).

Lemma largest_index_imp_eq_last :
  forall p i j, largest_index p i -> j < length p -> j > i -> 
  nth_msg j (lm p) = nth_msg (length p - 1) (lm p).
Proof.
intros.
apply H; auto.
Qed.

Lemma not_constant_exists : 
  forall p, not_constant_tp p -> exists i, i < length p - 1 ->
  nth_msg i (lm p) <> nth_msg (i+1) (lm p).
Admitted.

Lemma not_constant_exists_smallest :
  forall p, not_constant_tp p -> exists i, smallest_index p i.
Admitted.

Lemma not_constant_exists_largest :
  forall p, not_constant_tp p -> exists i, largest_index p i.
Admitted.

Lemma one : 0 < 1.
Proof.
auto.
Qed.

Lemma strand_length_3 : 
  forall (s:strand) (x y z : smsg), s = [x;y;z] -> length s = 3.
Proof.
intros. unfold length. subst. auto.
Qed.

Lemma DS_exists_key : 
  forall y h k k', DStrand (strand_of y) -> msg_of y = E h k -> inv k k' ->
  exists x, ssuccs x y /\ msg_of x = K k'.
Admitted.

Lemma DS_node_0 : 
  forall x, DStrand (strand_of x) -> index_of x = 0 -> exists k, msg_of x = K k.
Admitted.

Lemma DS_node_1 : 
  forall x, DStrand (strand_of x) ->  (exists h k, msg_of x = E h k) -> index_of x = 1.
Admitted.

Lemma msg_of_nth :
  forall p n, n < length p -> msg_of (nd p n) = nth_msg n (lm p).
Admitted.

(*********************************************************************)
(** * Proposition 18 *)

Section P18.
Variable p : path.
Variable a : msg.
Hypothesis t_path: is_trans_path p a.
Hypothesis no_key : not_traverse_key p.
Hypothesis p1 : r_node (nth_node 0 (ln p)).
Hypothesis lp : r_node (nth_node (length p - 1) (ln p)).
Hypothesis nconst : (nth_msg 0 (lm p)) <> (nth_msg (length p - 1) (lm p)).

  Section P18_1.
  Variable h1 : msg.
  Variable k1 k1' : Key.
  Hypothesis enc_form : nth_msg 0 (lm p) = E h1 k1.
  Hypothesis key_pair : inv k1 k1'.
  Hypothesis not_pen : ~PKeys k1'.
  Hypothesis not_subterm : not_proper_subterm (nth_msg 0 (lm p)).

  Lemma Prop18_1 : 
    forall n, smallest_index p n ->
    r_node (nth_node n (ln p)) /\ 
    transforming_edge_for (nth_node n (ln p)) (nth_node (n+1) (ln p)) a.
  Proof.
  intros n Sm.
  split. unfold r_node. intro pn.
  destruct Sm as (nc, (S1, (S2, S3))).
  assert (ssuccs (nd p n) (nd p (n+1)) /\ 
          (DStrand (strand_of (nd p n)) \/ EStrand (strand_of (nd p n)))).
  apply Proposition_10 with (a:=a); auto. 
  destruct H. 
  case H0.
  intro ds. apply not_pen. 
  assert (nth_msg n (lm p) = E h1 k1). rewrite <- enc_form. apply S3. auto.
  assert (exists x, ssuccs x (nd p n) /\ msg_of x = K k1').
  apply DS_exists_key with (h:=h1) (k:=k1). auto.
  rewrite <- H1. apply msg_of_nth. omega. auto.
  destruct H2 as (x, (H2, H3)).
  assert (Prop17_aux x). apply Prop17. apply H4. unfold Prop17_aux in H1.
  auto.

  intros es.
  Admitted.
  End P18_1.

  Section P18_2.
  Variable hp : msg.
  Variable kp kp' : Key.
  Hypothesis enc_form : nth_msg (length p - 1) (lm p)= E hp kp.
  Hypothesis key_pair : inv kp kp'.
  Hypothesis not_pen : ~PKeys kp'.
  Hypothesis not_subterm : not_proper_subterm (nth_msg (length p - 1) (lm p)).

  Lemma Prop18_2 : 
    forall n, largest_index p n ->
    r_node (nth_node n (ln p)) /\ 
    transforming_edge_for (nth_node n (ln p)) (nth_node (n+1) (ln p)) a.
  Admitted.
  End P18_2.
End P18.

(*********************************************************************)



