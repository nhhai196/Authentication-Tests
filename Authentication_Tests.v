
Require Import Strand_Spaces Strand_Library Message_Algebra Authentication_Tests_Library.

Definition not_proper_subterm (t:msg) :=  
  exists (n': node) (L : msg), 
  t <st L -> t <> L -> r_node n' -> L <[node] n' -> False.

Definition test_component (a t h: msg) (n:node) (k:Key) : Prop :=
  t = E h k /\ a <st t /\ t <[node] n /\ not_proper_subterm t.

Definition test (x y : node) (a : msg) : Prop :=
  unique a /\ orig_at x a /\ transformed_edge_for x y a.

Definition incoming_test (x y : node) (a t h: msg) (k:Key) : Prop := 
  t = E h k /\ ~ (PKeys k) /\ test_component a t h y k.
  
Definition outgoing_test (x y : node) (a t h : msg) (k k' : Key) : Prop :=
  t = E h k /\ inv k k' /\ ~ (PKeys k') /\ test_component a t h x k.
