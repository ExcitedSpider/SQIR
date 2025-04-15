(* Refer to https://math-comp.github.io/htmldoc_2_2_0/mathcomp.fingroup.action.html *)
(* We do not use mathcomp's definition because it requires finite structures, but quantumLib *)
(* works on infinite structure (Hilbert Space) *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.
From mathcomp Require Import automorphism quotient.

From QuantumLib Require Import Matrix.

Import GroupScope.

(* Section ok. *)
(* Variables S T R : Type. *)
(* Implicit Type op : S -> T -> R. *)
(* Definition left_injective op := forall x, injective (op^~ x). *)
(* End ok. *)

Section ActionDef.

(* aT: action operator type *)
(* D: the set of operators that is useful *)
Variables (aT : finGroupType) (D : {set aT}) (dim: nat).
(* we restraint the applied set to be the hilbert space *)
Definition ActionType := (Vector (2^dim) -> aT -> Vector (2^dim)).
Implicit Type (to : ActionType).
Implicit Type (x: Vector (2^dim)).

(* compatibility *)
Definition act_comp to x := 
  forall (a b: aT), WF_Matrix x -> to x (mulg b a) = to (to x a) b.

(* identity *)
Definition act_id to := forall x, WF_Matrix x -> to x (oneg aT) = x.

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
  act_id to /\ forall x, { in D &, act_comp to x}.

Record action := Action {
  act :> Vector (2^dim) -> aT -> Vector(2^dim); 
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
Proof.
  move => a b.
  all: case a; case b; lca.
Qed.

Definition aTs := [set: GenPauliOp].


Fact act_1_is_action:
  (is_action _ aTs 1 apply_1).
Proof.
  rewrite /is_action; split.
  {
    rewrite /act_id /apply_1 /= => x Hwf.
    lma'.
  }
  {
    move => x.
    rewrite /act_comp /apply_1 => a b Ha Hb.
    case a; case b => sa pa sb pb.
    rewrite /p1g_int /=.
    rewrite !Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc.
    rewrite -!mult_phase_comp.
    rewrite Cmult_comm.
    rewrite -!Mmult_assoc  p1_int_Mmult .
    rewrite Mscale_mult_dist_l.
    by rewrite -!Mscale_assoc.
  }
Qed.

Check (Action GenPauliOp aTs 1 _ act_1_is_action).

(* Interestingly, Coq can infer all types that depend on the final one. *)
Canonical act_1 := (Action _ _ _ _ act_1_is_action).


(* Sancheck *)
Goal act_1 ∣0⟩ (% X) = ∣1⟩.
Proof.
  rewrite /= /apply_1 /=.
  lma'.
Qed.

Import PNGroup.
Import PNGGroup.
Require Import PNProps.

Variable (n: nat).

Definition apply_n : Vector (2^n) -> GenPauliTuple n -> Vector (2^n) :=
  fun psi op => (png_int op) × psi.

Set Bullet Behavior "Strict Subproofs".

Definition aTsn := [set: GenPauliTuple n].

Fact act_n_is_action:
  is_action _ aTsn _ apply_n.
Proof.
  rewrite /is_action /act_id.
  split.
  {
    (* identity *)
    intros x Hwf.
    rewrite /act_id /apply_n id_png_int.
    by rewrite Mmult_1_l.
  }
  {
    (* compatibility *)
    intros x.
    rewrite /act_comp /apply_n /= => [[pa ta] [pb tb]] _ _ Hwf.
    induction n.
    - rewrite (tuple0 ta) (tuple0 tb) /=.
      case pa; case pb; simpl; Qsimpl.
      all: try easy.
      all: lma'.
    (* Need to find a way to do decomposition of x *)
    (* Mathematically, x can be represented by a linear combination *)
    (* of basic vectors in the Vector space *)
    (* x = Sum_i alpha_i x_i *)
    (* where { x_i } is the set of basic vectors *)
    (* But it's hard to do it in Coq *)
    - admit.
  }
Admitted.

Canonical act_n := (Action _ _ _ _ act_n_is_action).

(* Had to close here awardly because we don't want n to remain variable *)
End QuantumActions.

Import PNGroup.
Import PNGGroup.
Import P1GGroup.
Import P1Group.

Definition xxx: GenPauliTuple 3 := (One, [tuple of X :: X :: X :: []]).

(* sancheck *)
Goal act_n _ ∣0,0,0⟩ xxx = ∣1,1,1⟩.
Proof.
  rewrite /act_n /apply_n /=.
  Qsimpl.
  lma'.
Qed.



