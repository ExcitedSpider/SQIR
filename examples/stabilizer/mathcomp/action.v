(* Refer to https://math-comp.github.io/htmldoc_2_2_0/mathcomp.fingroup.action.html *)
(* We do not use mathcomp's definition because it requires finite structures, but quantumLib *)
(* works on infinite structure (Hilbert Space) *)


(* From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq. *)
(* From mathcomp Require Import fintype bigop finset fingroup morphism perm. *)
From mathcomp Require Import ssreflect finset fingroup.
From QuantumLib Require Import Matrix.

Import GroupScope.

(* Section ok. *)
(* Variables S T R : Type. *)
(* Implicit Type op : S -> T -> R. *)
(* Definition left_injective op := forall x, injective (op^~ x). *)
(* End ok. *)

Section QuantumAction.

Variables (aT : finGroupType) (D : {set aT}) (m n: nat).
(* we restraint the applied set to be the hilbert space *)
Implicit Type (to : Matrix m n -> aT -> Matrix m n).

Definition act_morph to x := 
  forall a b, to x (mulg a b) = to (to x a) b.

Definition act_id to x := to x (oneg aT) = x.

(* From https://mathworld.wolfram.com/GroupAction.html *)
(* A group G is said to act on a set X when 
   there is a map to : G × X -> X  such that
   for all elements x in X 
   1. to(x, e) = x where e is the id of G 
   2. to(g, to(h, x)) = to(g * h, x)
   *)
(* In addition, we introduct a well-form assumption to make *) 
(* sure x has valid physical meaning *)
Definition is_action to :=
  forall x, WF_Matrix x -> act_id to x /\ act_morph to x.

Record action := Action {
  act :> Matrix m n -> aT -> Matrix m n; 
  _ : is_action act
}.

End QuantumAction.


