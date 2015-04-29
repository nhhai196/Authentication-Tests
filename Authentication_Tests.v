(** This chapter contains the proofs of the two authentication tests, outgoing test 
and incoming test, which are the main results of this project. *)

Require Import Strand_Spaces Strand_Library Message_Algebra 
               Authentication_Tests_Library.
(** * Definitions *)
(* REF: Definition 13 *)

(** ** Test component and test *)
(** Tests can use their test components in at least two different ways. If the
uniquely originating value is sent in encrypted form, and the challenge is to
decrypt it, then that is an outgoing test. If it is received back in encrypted
form, and the challenge is to produce that encrypted form, then that is an
incoming test %\cite{Guttman}%. These two kinds of test are illustrated in Figure 7.1.
%\\%*)

(** %\begin{figure}
     \includegraphics[scale=0.7]{outgoing_incoming_tests}
     \centering
     \caption{Outgoing and Incoming Tests}
     \end{figure} 
    % *)

Definition test_component (a t: msg) (n:node) : Prop :=
  (exists h k, t = E h k) /\ a <st t /\ t <[node] n /\ not_proper_subterm t.

Definition test (x y : node) (a : msg) : Prop :=
  unique a /\ orig_at x a /\ transformed_edge_for x y a.

(* REF: Definition 14 *) 
(** ** Incoming test *)
Definition incoming_test (x y : node) (a t: msg)  : Prop := 
  (exists h k, t = E h k /\ ~ PKeys k) /\ test x y a /\ test_component a t y.

(** Outgoing test *)  
Definition outgoing_test (x y : node) (a t : msg) : Prop :=
  (exists h k k', t = E h k /\ inv k k' /\ ~ PKeys k') /\
  test x y a /\ test_component a t x.

(** * Some basic results *)
(** Below are some basic results following directly form the definitions for test,
test component, outgoing test, and incoming test. *)

(** ** Unique *)
Lemma test_imp_unique : forall x y a, test x y a -> unique a.
Proof.
intros. apply H.
Qed.
Hint Resolve test_imp_unique.

Lemma incoming_test_imp_unique : 
  forall x y a t, incoming_test x y a t  -> unique a.
Proof.
intros. apply H. 
Qed.
Hint Resolve incoming_test_imp_unique.

Lemma outgoing_test_imp_unique : 
  forall x y a t, outgoing_test x y a t  -> unique a.
Proof.
intros. apply H. 
Qed.
Hint Resolve outgoing_test_imp_unique.


(** ** Transformed edge *)
Lemma test_imp_trans_edge :
  forall x y a, test x y a -> transformed_edge_for x y a.
Proof.
intros. apply H.
Qed.
Hint Resolve test_imp_trans_edge.

Lemma incoming_test_imp_trans_edge : 
  forall x y a t, incoming_test x y a t  -> transformed_edge_for x y a.
Proof.
intros. apply H. 
Qed.
Hint Resolve incoming_test_imp_trans_edge.

Lemma outgoing_test_imp_trans_edge : 
  forall x y a t, outgoing_test x y a t  -> transformed_edge_for x y a.
Proof.
intros. apply H. 
Qed.
Hint Resolve outgoing_test_imp_trans_edge.


(** Origination *)
Lemma test_imp_orig : forall x y a, test x y a -> orig_at x a.
Proof.
intros. apply H.
Qed.
Hint Resolve test_imp_orig.

Lemma incoming_test_imp_orig : 
  forall x y a t, incoming_test x y a t  -> orig_at x a.
Proof.
intros. apply H. 
Qed.
Hint Resolve incoming_test_imp_orig.

Lemma outgoing_test_imp_orig : 
  forall x y a t, outgoing_test x y a t  -> orig_at x a.
Proof.
intros. apply H. 
Qed.
Hint Resolve outgoing_test_imp_orig.

(** ** Ingredient *)
Lemma tc_ingred : forall a t n, test_component a t n -> a <st t.
Proof.
intros a t n Tc.
apply Tc.
Qed.
Hint Resolve tc_ingred.

(** ** Incoming test (outging test) implies test_component *)
Lemma incoming_test_imp_tc :
  forall x y a t, incoming_test x y a t  -> test_component a t y.
Proof.
intros. apply H. 
Qed.
Hint Resolve incoming_test_imp_tc.

Lemma outgoing_test_imp_tc :
  forall x y a t, outgoing_test x y a t  -> test_component a t x.
Proof.
intros. apply H. 
Qed.
Hint Resolve outgoing_test_imp_tc.

(** Component *)
Lemma tc_comp : forall a t n, test_component a t n -> t <[node] n.
Proof.
intros a t n Tc.
apply Tc.
Qed.
Hint Resolve tc_comp.

Lemma outgoing_test_comp : 
  forall x y a t, outgoing_test x y a t  -> t <[node] x.
Proof.
intros. apply tc_comp with (a:=a).
apply outgoing_test_imp_tc with (y:=y).
auto.
Qed.
Hint Resolve outgoing_test_comp.

Lemma incoming_test_comp : 
  forall x y a t, incoming_test x y a t  -> t <[node] y.
Proof.
intros. apply tc_comp with (a:=a).
apply incoming_test_imp_tc with (x:=x).
auto.
Qed.
Hint Resolve incoming_test_comp.

(** Others *)
Lemma unique_orig : 
  forall x y a, unique a -> orig_at x a -> orig_at y a -> x = y.
Proof.
intros.  destruct H. apply (H2 x y); auto.
Qed.

Lemma transpath_not_constant :
  forall p a, is_trans_path p a -> 
  transformed_edge_for (nth_node 0 (ln p)) (nth_node (length p - 1) (ln p)) a -> 
  not_constant_tp p.
Admitted.

Lemma ssuccs_both_r_nodes :
  forall x y, ssuccs x y -> r_node x -> r_node y.
Proof.
intros.
unfold r_node in *. unfold p_node in *.
rewrite (ssuccs_same_strand x y) in H0; auto.
Qed.

Lemma trans_ef_imp_ssuccs :
  forall x y a, transforming_edge_for x y a -> ssuccs x y.
Proof.
intros. apply H.
Qed.
Hint Resolve trans_ef_imp_ssuccs.

Lemma tp_comp : 
  forall p a i, is_trans_path p a -> i < length p -> 
  nth_msg i (lm p) <[node] nth_node i (ln p).
Proof.
intros. apply H. auto.
Qed. 

Lemma tf_edge_exists : 
  forall x y a, transformed_edge_for x y a -> 
  exists Ly, a <st Ly /\ Ly <[node] y.
Proof.
intros.
destruct H as ((H1, (H2, (z, (Ly, (H3, (H4, (H5, (H6, H7)))))))), (H8, H9)).
exists Ly. auto.
Qed.

(** * Aunthentication tests *)

Section Authentication_tests.
Variable n n' : node.
Variable a t: msg.
Hypothesis Atom : atomic a.

(** ** Outgoing test *)
(** If a regular pricipal sends out a messages in encrypted form, 
the original component, and sometime later receives it back in a new component. 
Then we can conclude that there exists a regular transforming edge. The meaning
of this test is illusrated in the Figure 7.2. *)

(** %\begin{figure}[h]
     \includegraphics[scale=0.7]{outgoing_test}
     \centering
     \caption{Authentication provided by an Outgoing Test}
     \end{figure}% *)

Theorem Authentication_test1 :
  outgoing_test n n' a t ->
  exists m m', r_node m /\ r_node m' /\ t <[node] m /\
  transforming_edge_for m m' a.
Proof.
intros.
assert (p11_aux2 n').
apply Prop_11.
assert (Ha : exists t', a <st t' /\ t' <[node] n').
apply tf_edge_exists with (x:=n).
apply outgoing_test_imp_trans_edge with (t:=t). auto.
destruct Ha as (t', (Hst, Hcomp)).
destruct (H0 a t'); auto.
destruct H1. destruct H2 as (H2, (H3, (H4, H5))).
assert (nth_node 0 (ln x) = n).
apply unique_orig with (a:=a).
apply outgoing_test_imp_unique with (x:=n) (y:=n') (t:=t). auto.
apply H2. apply outgoing_test_imp_orig with (y:=n') (t:=t). auto.
assert (not_constant_tp x).
apply transpath_not_constant with (a:=a). auto.
apply outgoing_test_imp_trans_edge with (t:=t).
unfold ln in *. rewrite H3. rewrite H6. auto.
assert (exists i, smallest_index x i).
apply not_constant_exists_smallest. auto.
destruct H8 as (i, H8).
exists (nth_node i (ln x)), (nth_node (i+1) (ln x)).
assert (r_node (nth_node i (ln x)) /\
transforming_edge_for (nth_node i (ln x)) (nth_node (i + 1) (ln x)) a).
apply Prop18_1. apply H8. destruct H8 as (H8, (H81, (H82, H83))).
split. apply H9.
split. apply ssuccs_both_r_nodes with (x := nth_node i (ln x)). 
apply trans_ef_imp_ssuccs with (a:=a); apply H9. apply H9.
split. assert (nth_msg i (snd (List.split x)) = 
               nth_msg 0 (snd (List.split x))).
apply H83. omega.
assert (nth_msg 0 (lm x) = t). admit. (* TODO : add assumption about a to make this true*)
unfold lm in H11. rewrite H11 in H10. unfold ln.  rewrite <- H10.
apply tp_comp with (a:=a). auto. omega. apply H9. 
Qed.

(** ** Incoming test *)
(** Incoming tests can be used to infer the existence of a regular 
transforming edge in protocols in which the nonce is emitted in paintext,
and later received in cnrypted form %\cite{Guttman}%. *)

(** %\begin{figure}[h]
     \includegraphics[scale=0.7]{outgoing_test}
     \centering
     \caption{Authentication provided by an Incoming Test}
     \end{figure}% *)

Theorem Authentication_test2 : 
  incoming_test n n' a t ->
  exists m m', r_node m /\ r_node m' /\ t <[node] m' /\
  transforming_edge_for m m' a.
Proof.
intros.
assert (p11_aux2 n').
apply Prop_11. destruct (H0 a t). auto.
apply tc_ingred with (n:=n').
apply incoming_test_imp_tc with (x:=n). auto.
apply incoming_test_comp with (x:=n) (a:=a). auto.
destruct H1. destruct H2 as (H2, (H3, (H4, H5))).
assert (nth_node 0 (ln x) = n).
apply unique_orig with (a:=a).
apply incoming_test_imp_unique with (x:=n) (y:=n') (t:=t). auto.
apply H2. apply incoming_test_imp_orig with (y:=n') (t:=t). auto.
assert (not_constant_tp x).
apply transpath_not_constant with (a:=a). auto.
apply incoming_test_imp_trans_edge with (t:=t).
unfold ln in *. rewrite H3. rewrite H6. auto.
assert (exists i, largest_index x i).
apply not_constant_exists_largest. auto.
destruct H8 as (i, H8).
exists (nth_node i (ln x)), (nth_node (i+1) (ln x)).
assert (r_node (nth_node i (ln x)) /\
transforming_edge_for (nth_node i (ln x)) (nth_node (i + 1) (ln x)) a).
apply Prop18_2. apply H8. destruct H8 as (H8, (H81, (H82, H83))).
split. apply H9.
split. apply ssuccs_both_r_nodes with (x := nth_node i (ln x)). 
apply trans_ef_imp_ssuccs with (a:=a); apply H9. apply H9.
split. assert (nth_msg (i+1) (snd (List.split x)) = 
               nth_msg (length x - 1) (snd (List.split x))).
apply H83. omega. omega.
rewrite H4 in H10. unfold ln. rewrite <- H10.
apply tp_comp with (a:=a). auto. omega. apply H9. 
Qed.

End Authentication_tests.  
