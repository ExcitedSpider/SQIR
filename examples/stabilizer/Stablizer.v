Require Import PauliString.
Require Import SQIR.UnitaryOps.
Require Import Pauli.
Import Pauli.
Import PauliString.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* 
The stabilize relation is defined as:
An operator S (pauli string) stabilizes a (non-zero) ψ ∣ψ⟩ 
if S∣ψ⟩ = ∣ψ⟩ 
*)
Definition stb {n: nat} (pstring: PString n) (ψ: Vector (2^n))
  : Prop := (pstr_to_matrix pstring) × ψ = ψ.

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

(* X stabilize the bell ψ *)
Example stb_xbell:
  stb (One, X::[]) ( 1/√2 .* (∣0⟩ .+ ∣1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

(* Y stabilize the |i> ψ *)
Example stb_yibell:
  stb (One, Y::[]) ( 1/√2 .* (∣0⟩ .+ Ci .* ∣1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.


Example stb_x2bell2:
  stb (One, X::X::[]) ( 1/2 .* (∣0,0⟩ .+ ∣1,1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  autorewrite with C_db.
  autorewrite with ket_db.
  solve_matrix.
Qed.

Example stb_z2bell2:
  stb (One, Z::Z::[]) ( 1/2 .* (∣0,0⟩ .+ ∣1,1⟩)).
Proof.
  unfold stb.
  simpl; Qsimpl.
  autorewrite with C_db.
  autorewrite with ket_db.
  solve_matrix.
Qed.

Lemma one_stb_everything:
  forall {n: nat} (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb (pstr_identity n) ψ.
Proof.
  intros.
  induction n.
  { 
    unfold stb.
    simpl; Qsimpl; easy. 
  }
  {
    unfold stb in *.
    simpl; Qsimpl.
    replace (pvec_to_matrix (const I n)) with (Matrix.I (2^n)). 
    rewrite id_kron.
    Qsimpl.
    reflexivity.
    rewrite pvec_id_to_matrix.
    reflexivity.
  }
Qed.

(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
Lemma inv_stb:
  forall {n: nat} (pstr: PString n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb pstr ψ -> stb (pstr_inv pstr) ψ.
Proof.
  intros n pstr ψ Hwf Hstb.
  unfold stb in *.
  rewrite <- Hstb at 1.
  rewrite <- Mmult_assoc.
  rewrite psmul_correct.
  rewrite pstr_inv_correct.
  unfold pstr_identity.
  apply one_stb_everything; easy.
Qed.
