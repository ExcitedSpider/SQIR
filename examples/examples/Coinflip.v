Require SQIR.UnitaryOps.
Require SQIR.DensitySem.
Require SQIR.NDSem.
Require Import QuantumLib.Measurement.

(** Unitary Teleportation Circuit and Proof **)
Module CoinFlip.

Import UnitaryOps.
Import DensitySem.

Open Scope ucom.

Definition SWAP d a b : base_ucom d := CNOT a b; CNOT b a; CNOT a b.

Lemma swap2: forall (psi phi: Vector 2), 
  WF_Matrix psi -> 
  WF_Matrix phi -> 
  (uc_eval (SWAP 2 0 1)) × (psi ⊗ phi) =  (phi ⊗ psi).
Proof.
  intros.
  simpl.
  autorewrite with eval_db; simpl; try lia.
  solve_matrix.
Qed.
  


Open Scope com.

Definition single_coin_flip : base_com 1 := H 0; measure 0.

Lemma coin_flip_absurd : c_eval single_coin_flip ∣0⟩ = ∣1⟩.
Proof. Abort. (* Apparently wrong *)

(* You can reason about the probability by density matrix *)
(* By the way, it's ridiculously hard to prove. 
  I don't understand why coz this is a very simple fact *)
Lemma coin_flip_prob : 
  probability_of_outcome (c_eval single_coin_flip ∣0⟩)
   ∣1⟩ = (1 / 2)%R.
Proof.
  simpl. 
  simpl; autorewrite with eval_db; simpl.
Abort.



Lemma coin_flip_twice_prob : 
  probability_of_outcome
   ∣1⟩ (c_eval single_coin_flip ∣0⟩) = ((1 / 2)^2)%R.
Proof. Abort.

(* Similarly you can work on this*)
Definition two_coin_flip: base_com 1 :=
    H 0; meas 0 single_coin_flip skip.

Parameter compare_states : Square (2 ^ 1) -> Square (2 ^ 1) -> bool.

(* No idea how to work on this ?*)
Fixpoint coin_flips (n: nat): bool :=
  match n with
    | 0 => true
    | S n' => if compare_states (c_eval single_coin_flip ∣0⟩) ∣1⟩ then 
      coin_flips n' else false
  end.

(* 
  The lemma is absurd because it lacks a important output: probability.
  So it makes so sense at all

  *)
Lemma many_coin_flips_absurd: forall n, coin_flips n = true.
Proof. Abort.


(* So the function that we're looking for should return a pair (R * bool). *)
Parameter coin_flips' :nat -> (R * bool).

(* 
Then we can express the probability property 
  that do n time fair coin flip successfully is of probaiblity (1/2)^n
*)
Lemma many_coin_flips': forall n, coin_flips' n = (((1/2)^ n)%R, true). 
Proof. Abort.

(* 
To do this we want every function call has a probability.
This sounds like something monadic.
*)
