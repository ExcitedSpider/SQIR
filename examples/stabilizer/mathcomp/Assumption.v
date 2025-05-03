(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.
Require Import Coq.Lists.List.
From mathcomp Require Import finset.

(* 
  TODO: This is apparent but actually hard to prove
  As QuantumLib does not provide any lemmas about inequality
  *)
Lemma negate_change_state n:
  forall (ψ:  Vector n), -C1 .* ψ <> ψ.
Admitted.

Definition σi := Matrix.I 2.

Definition is_basic_op U :=
  U = σx \/ U = σy \/ U = σz \/ U = σi.

(* Basic Pauli Operators are orthoganal to each other *)
Lemma basic_op_orthogonal U V:
  forall (c1 c2: C),
  is_basic_op U -> is_basic_op V -> 
  U <> V -> c1 .* U <> c2 .* V.
Admitted.

(* We assume that if you apply a nontrivial global phase 
to a quantum state vector, then the resulting vector 
is different from the original  *)
Lemma phase_change_state n:
  forall (ψ:  Vector n) (c: C),
  c <> C1 -> c .* ψ <> ψ.
Admitted.


Lemma phase_change_state' n:
  forall (ψ:  Vector n) (c1 c2: C),
  c1 <> c2 -> c1 .* ψ <> c2 .* ψ.
Admitted.

(* If P^2 = I, all eigenvalues λ of P satisfy λ^2 = 1 *)
Lemma involutive_eigenvalue n:
  forall (A: Square (2^n)) (psi: Vector (2^n)) (lambda: C),
    A × A = I (2^n) ->
    A × psi = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Admitted.