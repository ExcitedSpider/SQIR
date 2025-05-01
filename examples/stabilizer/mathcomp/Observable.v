From QuantumLib Require Import Quantum.
From mathcomp Require Import seq tuple.
From mathcomp Require Import ssreflect ssrbool.
Require Import PauliGroup.
Require Import Stabilizer.
Require Import WellForm.
Open Scope form_scope.

(* An operator is hermitian if it is self-adjoint   *)
Definition hermitian {n:nat} (H: Square (2^n)): Prop :=
  H† == H.

(* meas_to m M ψ captures the projective measurement postulate:
  if ψ is an eigenvector of Hermitian observable M with eigenvalue m, 
  then measuring M on ψ yields m with certainty. *)
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

(* This one proves a general  *)
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

Fact pauli_hermitian {n} :
  forall (operator: PauliTuple n), hermitian (png_int operator).
Admitted. (* refer to Quantum.Quantum *)

(* 
If a quantum state ψ is stabilized by a Pauli operator p (i.e., p ψ = ψ), 
then measuring the corresponding observable yields outcome 1 with certainty.
*)
Theorem stabilizer_meas_to_1 {n}:
  forall (p: PauliTuple n) (psi: Vector (2^n)),
  p ∝1 psi -> meas_to 1 (png_int p) psi.
Proof.
  move => p psi H.
  rewrite /meas_to.
Admitted. (* easy, do it later. now focus on the structure *)

(* an alternative meas_to definition for pauli operators  *)
Definition meas_p_to {n} (m: C) (P: PauliTuple n) (psi: Vector (2^n)) :=
  (png_int P) × psi = m .* psi.

Lemma meas_p_to_correct {n}:
  forall (m:C) (P: PauliTuple n) (psi: Vector (2^n)),
  meas_p_to m P psi <-> meas_to m (png_int P) psi.
Proof.
  move => m P psi.
  rewrite /meas_p_to /meas_to.
  split.
  - move => H.
    split => //. apply png_int_wf.
    split => //. apply pauli_hermitian.
  - move => [_ [_ H]].
    exact H.
Qed. 

Theorem stabilizer_meas_to_1' {n}:
  forall (p: PauliTuple n) (psi: Vector (2^n)),
  p ∝1 psi -> meas_p_to 1 p psi.
Proof.
  move => p psi H.
  apply meas_p_to_correct.
  by apply stabilizer_meas_to_1.
Qed.
