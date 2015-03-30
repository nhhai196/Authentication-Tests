
Require Import Strand_Spaces Strand_Library Message_Algebra Authentication_Tests_Library.

Definition test_component (a t: msg) (n:node) : Prop :=
  (exists h k, t = E h k) /\ a <st t /\ t <[node] n /\ not_proper_subterm t.

Definition test (x y : node) (a : msg) : Prop :=
  unique a /\ orig_at x a /\ transformed_edge_for x y a.

Definition incoming_test (x y : node) (a t: msg)  : Prop := 
  exists h k, t = E h k /\ test x y a /\ ~ PKeys k /\ test_component a t y.
  
Definition outgoing_test (x y : node) (a t : msg) : Prop :=
  exists h k k', t = E h k /\ test x y a /\ inv k k' /\ ~ PKeys k' /\ test_component a t x.

Section Authentication_tests.
Variable n n' : node.
Variable a t: msg.
Hypothesis incom : incoming_test n n' a t.

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
Admitted.

End Authentication_tests.  
