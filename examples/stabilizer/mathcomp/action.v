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

Section ActionDef.

Variables (aT : finGroupType) (D : {set aT}) (m n: nat).
(* we restraint the applied set to be the hilbert space *)
Implicit Type (to : Matrix m n -> aT -> Matrix m n).

(* compatibility *)
Definition act_comp to x := 
  forall a b, to x (mulg b a) = to (to x a) b.

(* identity *)
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
  forall x, WF_Matrix x -> act_id to x /\ act_comp to x.

Record action := Action {
  act :> Matrix m n -> aT -> Matrix m n; 
  _ : is_action act
}.

End ActionDef.

Require Import PauliGroup.
Require Import P1Props.

Section QuantumActions. 

Import P1Group.
Import P1GGroup.

(* Apply a single-qubit pauli operator *)
Definition apply_1 : Vector 2 -> GenPauliOp -> Vector 2 :=
  fun psi op => (p1g_int op) × psi.

Check is_action.

Lemma mult_phase_comp: forall a b, phase_int (a) * phase_int (b) = 
  phase_int (mult_phase a b).
Admitted.

Fact act_1_is_action:
  is_action _ _ _ apply_1.
Proof.
  rewrite /is_action => x Hwf.
  split.
  {
    rewrite /act_id /apply_1 /=.
    lma'.
  }
  {
    rewrite /act_comp /apply_1 => a b.
    case a; case b => sa pa sb pb.
    rewrite /p1g_int /=.
    rewrite !Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc.
    rewrite -!mult_phase_comp.
    rewrite Cmult_comm.
    rewrite -!Mmult_assoc.
    case sa; case sb; simpl; Qsimpl.
    all: autorewrite with C_db.
    all: case pa; case pb; simpl.
    all: Qsimpl.
    all: try easy.
    all: solve_matrix.
  }
Qed.

Canonical act_1 := Action _ _ _ _ act_1_is_action.

(* I don't know how to make param implicit *)
Goal act _ _ _ act_1 ∣0⟩ (% X) = ∣1⟩.
Proof.
  rewrite /= /apply_1 /=.
  lma'.
Qed.

End QuantumActions.


