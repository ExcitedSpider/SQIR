Require Import PauliString.
Require Import SQIR.UnitaryOps.
Require Import Pauli.
Import Pauli.
Import PauliString.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* 
The stabilize relation is defined as:
An operator S (pauli string) stabilizes a (non-zero) state ∣ψ⟩ 
if S∣ψ⟩ = ∣ψ⟩ 
*)
Definition stb {n: nat} (pstring: PString n) (state: Vector (2^n))
  : Prop := (pstr_to_matrix pstring) × state = state.

(* Z stabilises ∣0⟩ *)
Example stb_z0:
  stb (One, Z::[]) ∣0⟩.
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

(* -Z stabilises ∣1⟩ *)
Example stb_nz0:
  stb (NegOne, Z::[]) ∣1⟩.
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

(* X stabilize the bell state *)
Example stb_xbell:
  stb (One, X::[]) ( 1/√2 .* (∣0⟩ .+ ∣1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

(* Y stabilize the |i> state *)
Example stb_yibell:
  stb (One, Y::[]) ( 1/√2 .* (∣0⟩ .+ Ci .* ∣1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

  