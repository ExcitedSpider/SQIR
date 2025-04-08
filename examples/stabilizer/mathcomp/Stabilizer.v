Require Import PauliGroup.
Require Import SQIR.UnitaryOps.

Section Stabilizer1. 

Import PauliGroup.P1Group.
Import PauliGroup.P1GGroup.


(* Stabilizer of Operator length 1 *)
Definition stb1 (op: PauliOp + GenPauliOp) (ψ: Vector 2) : Prop :=
  match op with
  | inl op => (p1_int op) × ψ = ψ
  | inr op => (p1g_int op) × ψ = ψ
  end.

Example stb1_z0:
  stb1 (inl Z) ∣ 0 ⟩.
Proof.
  unfold stb1.
  simpl; Qsimpl.
  rewrite Z0_spec.
  easy.
Qed.

Example stb1_m:
  stb1 (inr (NOne, X)) ∣ - ⟩.
Proof.
  unfold stb1.
  simpl; Qsimpl.
  distribute_plus.
  repeat rewrite Mscale_mult_dist_r.
  replace ∣ 0 ⟩ with ∣0⟩ by solve_matrix.
  replace ∣ 1 ⟩ with ∣1⟩ by solve_matrix.
  repeat rewrite Mscale_mult_dist_l.
  repeat rewrite Mscale_assoc.
  autorewrite with Q_db.
  solve_matrix.
Qed.

End Stabilizer1. 

From mathcomp Require Import seq tuple.

Section StabilizerN.
Import PauliGroup.P1Group.
Import PauliGroup.P1GGroup.
Import PauliGroup.PNGroup.
Import PauliGroup.PNGGroup.

Definition stb {n: nat} (op: (PauliTuple n) + (GenPauliTuple n)) (ψ: Vector (2^n)) : Prop := 
  match op with
  | inl opn => (pn_int opn)  × ψ = ψ
  | inr opn => (png_int opn)  × ψ = ψ
  end.

Open Scope form_scope.

(* Locate "[ tuple _ ; .. ; _ ]". *)
(* Check [tuple of X :: Y :: []]. *)

(* (1* Unknown interpretation for notation "_ ; _". *1) *)
(* Fail Check [tuple X; Z; Y; I]. *)

Notation "[ 'pauli' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..].

Check [pauli X, Y, Z].

(* Simplify Interpretations *)
Ltac simpl_int :=
  try unfold png_int;
  try unfold pn_int;
  try unfold pn_reducer; 
  simpl; Qsimpl.

Example stb_bell00:
  stb (inl [pauli X, X]) ∣Φ+⟩.
Proof.
  unfold stb.
  lma'.
  simpl_int.
  auto with wf_db.
Qed.

Definition EPRpairM : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ (-1) .* ∣1,1⟩).
Notation "∣Φ-⟩" := EPRpairM.

Lemma EPRpairM_WF: 
  WF_Matrix ∣Φ-⟩.
Proof.
  unfold EPRpairM.
  auto with wf_db.
Qed.

Example stb_bell11:
  stb (inr (NOne, [pauli X, X])) ∣Φ-⟩.
Proof.
  unfold stb.
  lma'.
  2: apply EPRpairM_WF.
  simpl_int.
  apply WF_mult.
  auto with wf_db.
  apply EPRpairM_WF.
Qed.

Require Import PNProps.
 From mathcomp Require Import ssreflect.

Theorem one_stb_all {n: nat}:
  forall (ψ:  Vector (2^n)), WF_Matrix ψ -> stb (inl (id_pn n)) ψ.
Proof.
  intros.
  unfold stb; simpl.
  rewrite id_pn_int.
  by rewrite Mmult_1_l.
Qed.
