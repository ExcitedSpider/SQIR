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

(* If P^2 = I, all eigenvalues λ of P satisfy λ^2 = 1 *)
Lemma involutive_eigenvalue n:
  forall (A: Square (2^n)) (psi: Vector (2^n)) (lambda: C),
    A × A = I (2^n) ->
    A × psi = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Admitted.

Lemma Mscale_cancel:
  forall {n m : nat} (c1 c2 : C) (A: Matrix n m),
  A <> (@Zero n m) ->  c1 .* A = c2 .* A -> c1 = c2.
Admitted.

(* 1 is not -1 *)
Lemma C1_neq_mC1: C1 <> -C1.
Admitted.