
Require Import Strand_Spaces Strand_Library Message_Algebra Authentication_Tests_Library.

Definition test_component (a t: msg) (n:node) : Prop :=
  (exists h k, t = E h k) /\ a <st t /\ t <[node] n /\ not_proper_subterm t.

Definition test (x y : node) (a : msg) : Prop :=
  unique a /\ orig_at x a /\ transformed_edge_for x y a.

Definition incoming_test (x y : node) (a t: msg)  : Prop := 
  (exists h k, t = E h k /\ ~ PKeys k) /\ test x y a /\ test_component a t y.
  
Definition outgoing_test (x y : node) (a t : msg) : Prop :=
  (exists h k k', t = E h k /\ inv k k' /\ ~ PKeys k') /\ test x y a /\ test_component a t x.

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

Lemma test_imp_trans_edge : forall x y a, test x y a -> transformed_edge_for x y a.
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

Lemma tc_ingred : forall a t n, test_component a t n -> a <st t.
Proof.
intros a t n Tc.
apply Tc.
Qed.
Hint Resolve tc_ingred.

Lemma tc_comp : forall a t n, test_component a t n -> t <[node] n.
Proof.
intros a t n Tc.
apply Tc.
Qed.
Hint Resolve tc_comp.

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

Lemma unique_orig : 
  forall x y a, unique a -> orig_at x a -> orig_at y a -> x = y.
Proof.
intros.  destruct H. apply (H2 x y); auto.
Qed.

Lemma tp_not_constant :
  forall p a, is_trans_path p a -> 
  transformed_edge_for (nth_node 0 (ln p)) (nth_node (length p - 1) (ln p)) a -> 
  exists n, n < length p - 1 /\ 
  (nth_msg n (lm p) <> nth_msg (n+1) (lm p)).
Admitted.

Section Authentication_tests.
Variable n n' : node.
Variable a t: msg.
Hypothesis incom : incoming_test n n' a t.
Hypothesis Atom : atomic a.

Theorem Authentication_test1 :
  outgoing_test n n' a t ->
  exists m m', r_node m /\ r_node m' /\ t <[node] m' /\
  transforming_edge_for m m' a.
Admitted.

Theorem Authentication_test2 : 
  incoming_test n n' a t ->
  exists m m', r_node m /\ r_node m' /\ t <[node] m /\
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
assert ( exists i, i < length x - 1 /\ 
  (nth_msg i (lm x) <> nth_msg (i+1) (lm x))).
apply tp_not_constant with (a:=a). auto.
apply incoming_test_imp_trans_edge with (t:=t).
unfold ln in *. rewrite H3. rewrite H6. auto.
Admitted.

End Authentication_tests.  
