(* Time-stamp: <Mon 7/7/14 10:43 Dan Dougherty Protocol_HD.v> *)


Add LoadPath "./".
(* Add LoadPath "./Classical_Wf". *)

Require Import Classical.
(* Require Import List Relations Wellfounded . *)
(** from Daniel Schepler's Zorn's Lemma development %\\%*) 
(* Require Import Classical_Wf.     *)

Require Import Message_Algebra Strands.




(** * A very simple protocol, the "half-duplex" example from EaPSGs. *)

(** 

 - Two roles, Init and Resp

 - role position predicates Init_1 and Init_2 and Resp_1 and Resp_2.
   Init_1 and Init_2 are xmit and recv, respectively.
   Resp_1 and Resp_2 are recv and xmit, respectively.

 - Init has parameters (Nonce I_N) and (Name) I_B

 - Resp has two parameters  (Nonce R_N) and (Name) R_B

 - if Init_1(n) then msg(n) = enc( I_N(strand_of(n)), pk(I_B(strand_of(n)) ) )

 - if Init_2(n) then msg(n) = I_N(strand_of(n))

 - if Resp_1(n) then msg(n) = enc( R_N(strand_of(n)), pk(I_B(strand_of(n)) ) )

 - if Resp_2(n) then msg(n) = R_N(strand_of(n))

 - now supose a particular strans s is assumed, an initiator.

 - we assume that I_N(s) is uniquely originating

 - we assume that the *private* key of I_B(s) is non-originating.  
   That is, pk-inverse of I_B(s) is Non.


*)


Variable Init Resp : Type.

Variable tst: Prop.

Variable a: tst.

Variable s: Set.
Variable x: Init.

Variable Init_1: Init -> Prop.
Variable Init_2: node -> Prop.
Variable Resp_1: node -> Prop.
Variable Resp_2: node -> Prop.


