(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.

(* 
  TODO: This is apparent but actually hard to prove
  As QuantumLib does not provide any lemmas about inequality
  *)
Lemma negate_change_state n:
  forall (ψ:  Vector n),
  -C1 .* ψ <> ψ.
Admitted. 