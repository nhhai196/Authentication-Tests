
Require Import Strand_Spaces Strand_Library Message_Algebra Authentication_Tests_Library.

Definition not_proper_subterm (t:msg) :=  
  exists (n': node) (L : msg), 
  t <st L -> t <> L -> r_node n' -> L <[node] n' -> False.

Section TestComponent.
Variable a t : msg.
Variable n : node. 

Definition test_component : Prop :=
  exists (h:msg) (k:Key), t = E h k /\ a <st t /\ t <[node] n /\ not_proper_subterm t.   

End TestComponent.
Check not_proper_subterm.
Check test_component.