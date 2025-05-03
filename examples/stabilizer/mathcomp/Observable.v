From QuantumLib Require Import Quantum.
From mathcomp Require Import seq tuple.
From mathcomp Require Import ssreflect ssrbool.
Require Import PauliGroup.
Require Import Action.
Require Import Stabilizer.
Require Import WellForm.
Open Scope form_scope.
Set Bullet Behavior "Strict Subproofs".

(* An operator is hermitian if it is self-adjoint   *)
Definition hermitian {n:nat} (H: Square (2^n)): Prop :=
  H† = H.

(* meas_to m M ψ captures the projective measurement postulate:
  if ψ is an eigenvector of Hermitian observable M with eigenvalue m, 
  then measuring M on ψ yields m with certainty (probability = 1). *)
Definition meas_to {n} (m: C) (M: Square (2^n)) (psi: Vector (2^n)) :=
  WF_Matrix M /\ hermitian M /\ M × psi = m .* psi.

(* 
  This section verifies the meas_to is consistent 
  with quantumlib measurement definition .
  Quantumlib only defines measurement in computational basis
  and if we want to achieve verification, we neeed to map
  the state and result to computational basis based on 
  the observable. 

  Which i find very hard to do because:
  - it involves a lot of theories in linear algebra, which we don't have in quantumlib
  - the theory is non-trivial. 
  - i don't have much time
  - The projective measurement postulate itself can be considered as an axiom,
    i.e. it is more foundamental in theory.
  - Quantumlib does not have sparse measurement primitive.
    e.g. for 4 qubits, only measure the 2nd and the 4th 
      (related to observables like Z2Z4 )
  
  And also, i find it is not our focus of research. 

  It will be more suitable to be considerred as a foundational change to quantumlib.
*)
Section QuantumLibMeas.

Require Import QuantumLib.Measurement.
(* QuantumLib only supports measure in computational basis *)
(* We need to apply reduction operations to measure *)
Variable (n:nat).

(* Perform basis tranformation (projection) in SQIR according to the observable *)
Variable proj_basis: Square (2^n) -> Vector (2^n) -> Vector (2^n).
(* Map the eigenvalue measurement result to a basic bitstring *)
Variable proj_result: Square (2^n) -> C -> Vector (2^n).

(* 
  This theorem tris verifies that measurement by observable
  can be converted to measurement on basis state by projection
 *)
Theorem meas_to_correct:
  forall (m: C) (M: Square (2^n)) (psi psi': Vector (2^n)) ,
  meas_to m M psi ->
  proj_basis M psi = psi' ->
  probability_of_outcome psi' (proj_result M m) = 1.
Admitted.

End QuantumLibMeas.

(* because every pauli operator is hermitian, 
  they can all be viewed as observable *)
Notation PauliObservable := PauliTuple.

Lemma pauli_base_hermitian:
  forall (p: PauliBase),
  @hermitian 1%nat (p1_int p).
Proof.
  move => p.
  rewrite /hermitian.
  case p; simpl.
  apply id_adjoint_eq.
  apply σx_hermitian.
  apply σy_hermitian.
  apply σz_hermitian.
Qed.

Fact pauli_hermitian {n} :
  forall (operator: PauliTupleBase n), hermitian (pn_int operator).
Proof.
  rewrite /hermitian /png_int /PauliObservable //= => pt.
  induction n.
  - by rewrite tuple0 /= id_adjoint_eq.
  - case: pt / tupleP => hx tx.
    rewrite /= theadCons .
    restore_dims.
    by rewrite kron_adjoint IHn pauli_base_hermitian.
Qed.



(* 
If a quantum state ψ is stabilized by a Pauli operator p (i.e., p ψ = ψ), 
then measuring the corresponding observable yields outcome 1 with certainty.
*)
Theorem stabilizer_meas_to_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  (One, p) ∝1 psi -> meas_to 1 (pn_int p) psi.
Proof.
  move => p psi H.
  rewrite /meas_to.
  split. apply pn_int_wf.
  split. apply pauli_hermitian.
  apply PauliOperator_stb in H.
  rewrite H. by Qsimpl.
Qed.

(* 
  What we are really interesting is to use pauli operator
  as observables.
 *)
Definition meas_p_to {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :=
  (pn_int P) × psi = m .* psi.

Lemma meas_p_to_correct {n}:
  forall (m:C) (P: PauliOperator n) (psi: Vector (2^n)),
  meas_p_to m P psi <-> meas_to m (pn_int P) psi.
Proof.
  move => m P psi.
  rewrite /meas_p_to /meas_to.
  split.
  - move => H.
    split => //. apply pn_int_wf.
    split => //. apply pauli_hermitian.
  - move => [_ [_ H]].
    exact H.
Qed. 

Theorem stabilizer_meas_to_1' {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  (* Maybe make a notation for (One, p) ∝1 psi *)
  (One, p) ∝1 psi -> meas_p_to 1 p psi.
Proof.
  move => p psi H.
  apply meas_p_to_correct.
  by apply stabilizer_meas_to_1.
Qed.

Notation "''Meas' P 'on' psi '-->' m " := (meas_p_to m P psi)
 (at level 8) : form_scope.

(* Example: Measure Z1Z2 on 00 yields 1. *)
Goal 'Meas [p Z, Z] on ∣ 0, 0 ⟩ --> 1.
Proof.
  rewrite /meas_p_to.
  Qsimpl.
  autorewrite with ket_db.
Abort.
