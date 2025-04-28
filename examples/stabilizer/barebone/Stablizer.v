(* 
This file contains an attempt to define the stabilizer group.
However, due to the lack of a proper definition of group,
it becomes hard to define the stabilizer and need to prove a bunch of lemmas that
are not already known in math.
For example, we need the notion of subgroup and generators. 

We turned to use mathcomp to define the stabilizer group.

Key Definitions:
- stb: The stabilizer proposition, which checks if a Pauli string stabilizes a given state.
  PString ∝1 ψ means PString stabilizes ψ.

Key Lemmas:
- stb_compose: The composition of two stabilizers results in a new stabilizer.
- stb_closed: The closure property of the stabilizer group, showing that the product of two stabilizers is also a stabilizer.
- stb_group_no_m1: The stabilizer group does not contain the negation of the identity.
- stb_by_id: The identity Pauli string stabilizes any state.
- stb_addition: The addition of two stabilizers results in a new stabilizer.
*)

Require Import PauliString.
Require Import SQIR.UnitaryOps.
Require Import Pauli.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

Locate PauliString_legacy.PauliString.
Import Pauli.

(* 
The stabilize relation is defined as:
An operator S (pauli string) stabilizes a (non-zero) ψ ∣ψ⟩ 
if S∣ψ⟩ = ∣ψ⟩ 
*)
(* TODO: update this to make it only works on well formed vector *)
Definition stb {n: nat} (pstring: PauliString n) (ψ: Vector (2^n))
  : Prop := (pstr_to_matrix pstring) × ψ = ψ.

(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stb pstring ψ) (at level 50).


(* Z stabilises ∣0⟩ *)
Example stb_z0:
  (One, p[Z]) ∝1 ∣0⟩.
Proof.
  unfold stb.
  simpl; Qsimpl.
  solve_matrix.
Qed.

(* -Z stabilises ∣1⟩ *)
Example stb_nz0:
  (NOne, Z::[]) ∝1 ∣1⟩.
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
  stb (One, p[Z, Z]) ( 1/2 .* (∣0,0⟩ .+ ∣1,1⟩)).
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
  forall {n: nat} (pstr: PauliString n) (ψ:  Vector (2^n)),
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

Print Vector.

(* 
If we take the tensor product of a two states, with stabiliser groups A and B (respectively), then the resulting tensor product state has stabiliser group given by the cartesian product A × B. 
*)
Theorem stb_compose:
  forall {n: nat} (pstr1 pstr2: PauliString n) (ψ1 ψ2:  Vector (2^n)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  intros.
  assert (Hcomp: pstr_to_matrix (compose_pstring pstr1 pstr2) = pstr_to_matrix pstr1 ⊗ pstr_to_matrix pstr2) by apply compose_pstring_correct.
  unfold stb in *.
  unfold cpstring.
  rewrite Hcomp.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.
  
(* The vector space of EPR Pair can be defined by generator <XX, ZZ> *)
Fact bell_stabilizer: 
  (One, p[X,X]) ∝1 ∣Φ+⟩ /\ (One, p[Z,Z]) ∝1 ∣Φ+⟩.
Proof.
  split.
  - unfold stb.
    lma'.
    simpl;Qsimpl.
    auto with wf_db. 
  - unfold stb.
    lma'.
    simpl;Qsimpl.
    auto with wf_db.
Qed. 

Fact three_qubit_state_stabilizer:
  (One, p[Z, Z, I]) ∝1 ∣000⟩ /\ (One, p[Z, Z, I]) ∝1 ∣000⟩.
Proof.
  split.
  - unfold stb.
    solve_matrix.
  - unfold stb.
    solve_matrix.
Qed.

Theorem stb_closed: 
  forall {n: nat} (pstr1 pstr2: PauliString n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  psmul pstr1 pstr2 ∝1 ψ
.
Proof.
  intros.
  unfold stb in *.
  (* Search psmul. *)
  remember (psmul pstr1 pstr2) as pstr_prod.
  assert (pstr_to_matrix pstr_prod = pstr_to_matrix pstr1 × pstr_to_matrix pstr2).
  {
    symmetry.
    apply psmul_implies_Mmult.
    easy.
  }
  rewrite H1. 
  rewrite Mmult_assoc.
  rewrite H0.
  rewrite H.
  easy.
Qed.

(* This is harder than expected *)
Lemma pvec_id_interpret:
  forall {n},
  pvec_to_matrix (const I n) = Matrix.I (2^n).
Proof.
  intros.
  induction n.
  {
    easy. 
  }
  {
    simpl; Qsimpl. 
    assert (Matrix.I (2 ^ n + (2 ^ n + 0)) = Matrix.I 2 ⊗ Matrix.I (2 ^ n)).
    {
      symmetry.
      apply id_kron.
    }
    rewrite H.
    rewrite IHn.
    reflexivity.
  }
Qed.

Theorem stb_by_id: 
  forall {n: nat} (ψ:  Vector (2^n)), 
  WF_Matrix ψ ->
  (One, Vector.const I n) ∝1 ψ.
Proof.
  intros.
  unfold stb.
  simpl.
  Qsimpl.
  (* Search Matrix.I. *)
  assert (pvec_to_matrix (const I n) = Matrix.I (2^n)) by apply pvec_id_interpret.
  rewrite H0.
  apply Mmult_1_l.
  easy.
Qed.

(* 
  TODO: This is apparent but actually hard to prove
  As QuantumLib does not provide usable lemmas about ineq
  *)
Lemma negate_change_state n:
  forall (ψ:  Vector n),
  -1 .* ψ <> ψ.
Admitted.

(* there is no -1 in any stabilizer group *)
Theorem stb_group_no_m1: 
  forall {n: nat} (pstr1 pstr2: PauliString n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  WF_Matrix ψ ->
  psmul pstr1 pstr2 <> (~𝟙 n).
Proof.
  unfold not.
  intros.
  assert ((~𝟙) n ∝1 ψ).
  {
    rewrite <- H2.
    apply stb_closed; easy.
  }
  contradict H3.
  unfold stb.
  rewrite pstr_negate_states; try easy.
  apply negate_change_state.
Qed.

Require Import ExtraSpecs.

Theorem stabilizer_must_commute: 
  forall {n: nat} (pstr1 pstr2: PauliString n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  commute_at psmul pstr1 pstr2.
Proof.
  intros.
  assert (Hbicom: bicommute (@psmul n) (@psneg n)) by apply psmul_bicommute.
  remember (Hbicom pstr1 pstr2) as HChoice.
  destruct HChoice as [| Hanti].
  easy.
  clear  HeqHChoice.
  remember (stb_closed pstr1 pstr2 ψ H H0) as HCompose.
  (* now let's make a contradict using HCompose  *)
  assert (Hcontra: ψ = -1 .* ψ). {
    unfold stb in HCompose.
    rewrite <- HCompose at 1.
    unfold anticommute_at in Hanti.
    clear HeqHCompose.
    rewrite Hanti.
    rewrite psneg_correct.
    rewrite Mscale_mult_dist_l.
    replace (pstr_to_matrix (psmul pstr2 pstr1) × ψ) with ψ.
    easy.
    symmetry.
    apply stb_closed; easy.
  }
  symmetry in Hcontra.
  apply negate_change_state in Hcontra.
  contradiction Hcontra.
Qed.

(* 
How to encode the idea of stabilizer group?
1. use math comp. too hard to learn and what's the benefit?
2. use custome define group in Group.v
*)

Theorem stb_compose_alt:
  forall {n m: nat} (pstr1: PauliString n) (pstr2: PauliString m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.  (* similar to stb_compose *)
  intros.
  assert (Hcomp: pstr_to_matrix (compose_pstring pstr1 pstr2) = pstr_to_matrix pstr1 ⊗ pstr_to_matrix pstr2) by apply compose_pstring_correct.
  unfold stb in *.
  unfold cpstring.
  rewrite Hcomp.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma stb_addition:
  forall {n: nat} (pstr: PauliString n) (ψ1 ψ2:  Vector (2^n)),
  pstr ∝1 ψ1 ->
  pstr ∝1 ψ2 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  intros.
  unfold stb in *.
  (* Search (_ × (_ .+ _) ). *)
  rewrite Mmult_plus_distr_l.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.


Ltac normalize_kron_notation :=
  repeat rewrite <- kron_assoc by auto 8 with wf_db;
  try easy.

Fact stb_04_fact:
  (One, p[Z, I, I, I]) ∝1 ∣0,0,0,0⟩.
(* 
  manually use stb_compose to break down large states
  we'll give a tactic later
  *)
Proof.
  replace ∣0,0,0,0⟩ with (∣0,0⟩ ⊗ ∣0,0⟩) by normalize_kron_notation.
  apply (stb_compose (One, p[Z, I]) (One, p[I, I])).
  all: unfold stb; simpl; Qsimpl; lma'.
Qed.

Definition shor_code_0 := (3 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

(* Check (
  (∣0,0,0⟩ .+ ∣1,1,1⟩) ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)
). *)

Check 
  (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ 
  (2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

Check (One, p[Z, Z]): PauliString 2.
Check (One, p[I]): PauliString 1.

Ltac by_compose_stb s1 s2 :=
  apply (stb_compose_alt s1 s2); Qsimpl;
  (unfold stb; simpl; Qsimpl; lma').

Ltac by_identity n := (* TODO: how to get n from the type*)
    match goal with
    | [ |- ((One, ?p) ∝1 _) ] =>
        replace (One, p) with (𝟙 n) by reflexivity;
        apply one_stb_everything;
        auto with wf_db
    end.

Fact shor_code_part_stb:
  (One, p[Z, Z, I])∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  apply stb_addition.
  by_compose_stb (One, p[Z, Z]) (One, p[I]).
  by_compose_stb (One, p[Z, Z]) (One, p[I]).
Qed.
  
Fact shor_code_stb_fact:
  (One, p[Z, Z, I, I, I, I, I, I, I]) ∝1 shor_code_0.
Proof.
  (* This could stuck Coq *)
  (* by_compose_stb  (One, p[Z, Z, I, I, I, I]) (One, p[I, I, I]). *)
  apply (stb_compose_alt (One, p[Z, Z, I, I, I, I]) (One, p[I, I, I])).
  Qsimpl.
  apply (stb_compose_alt (One, p[Z, Z, I]) (One, p[I, I, I])).
  - (* [Z; Z; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩)  *)
    apply shor_code_part_stb.
  - (* [I; I; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩) *)
    by_identity 3%nat.
  - by_identity 3%nat.
Qed.
