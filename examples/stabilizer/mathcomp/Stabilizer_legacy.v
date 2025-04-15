(* This is deprecated *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import PauliGroup.
Require Import SQIR.UnitaryOps.
Require Import Action.
Import P1Group.
Import P1GGroup.

Check act_1 ∣0⟩ (% X) == ∣1⟩.

Section StabDef.

Import PauliGroup.P1Group.
Import PauliGroup.P1GGroup.

Check GenPauliOp: finGroupType.

Definition actionTo {dim: nat} {aT: finGroupType} := 
  ActionType aT dim.

Fail Definition astab {dim: nat} {aT: finGroupType} (to: actionTo) (A: {set aT}) (psi: Vector (2^dim)):= 
  (* Canot define. because mathcomp needs psi of eqType *) 
  [set x | x in A & to psi x == psi]. 

(* Let's try can we define Vector to be eqType *)
From HB Require Import structures.

(* reflect (x = y) (e x y) where e: T -> T -> bool *)
Print eq_axiom.

(* QuantumLib does not define `==` to be a computable process *)
(* i.e. A == B -> Prop not bool *) 
Check ∣0⟩==∣1⟩.

(* Therefore, we use this definition instead. *)
Definition stab {dim: nat} {aT: finGroupType} (to: actionTo) (x: aT) (psi: Vector(2^dim)):= 
  to psi x = psi.

End StabDef.

Check Z0_spec.

Ltac solve_stab1:=
  rewrite /stab /= /apply_1 /=;
  Qsimpl;
  autorewrite with ket_db;
  try by [];
  try by lma'.

Import P1GGroup.

Lemma Z0_stab: stab act_1 (% Z) ∣0⟩.
by solve_stab1. Qed.

Lemma Z1_stab: stab act_1 (p1g_of NOne Z) ∣1⟩.
by solve_stab1. Qed.

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

(* What can i gain from doing this? *)
Definition PauliString (n: nat) := sum .

Definition stb' {n: nat} (op: ((PauliTuple n)+ (GenPauliTuple n)) )(ψ: Vector (2^n)) : Prop := 
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
  simpl; Qsimpl.

Example stb'_bell00:
  stb' (inl [pauli X, X]) ∣Φ+⟩.
Proof.
  unfold stb'.
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

Example stb'_bell11:
  stb' (inr (NOne, [pauli X, X])) ∣Φ-⟩.
Proof.
  unfold stb'.
  lma'.
  2: apply EPRpairM_WF.
  simpl_int.
  apply WF_mult.
  auto with wf_db.
  apply EPRpairM_WF.
Qed.

Require Import PNProps.
From mathcomp Require Import ssreflect.

Theorem one_stb'_all {n: nat}:
  forall (ψ:  Vector (2^n)), WF_Matrix ψ -> stb' (inl (id_pn n)) ψ.
Proof.
  intros.
  unfold stb'; simpl.
  rewrite id_pn_int.
  by rewrite Mmult_1_l.
Qed.

(* It's hard to define this using current definitions *)
(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
(* Let's make an alternative *)

From mathcomp Require Import ssreflect fingroup.

(* This is the most general paulituple *)
Definition stb {n: nat} (pt: GenPauliTuple n) (ψ: Vector (2^n)) : Prop := 
  (png_int pt)  × ψ = ψ.

(* Sometimes the phase is just `One` *)
(* We can use this simplified version of stb *)
Definition stb_s {n: nat} (pt: PauliTuple n) (ψ: Vector (2^n)) : Prop := 
  (pn_int pt) × ψ = ψ.

(* Allow using simplified version when the phase is one *)
Lemma phase_one_stb n:
  forall (pt: PauliTuple n) (psi: Vector (2^n)),
  stb_s pt psi <-> stb (One, pt) psi.
Proof.
  move => pt psi.
  by rewrite /stb /stb_s png_int_one.
Qed.

(* The two definitions are equal *)
Lemma stb_eq_stb' n:
  forall (pt: GenPauliTuple n) (psi: Vector (2^n)),
  stb pt psi <-> stb' (inr pt) psi.
Proof.
  move => pt psi.
  by rewrite /stb' /stb.
Qed.


Lemma inv_stb_s:
  forall {n: nat} (pstr: PauliTuple n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb_s pstr ψ -> stb_s (inv_pn pstr) ψ.
Proof.
  move => n pstr psi Hpsi.
  rewrite /stb_s => Hstb.
  rewrite -Hstb -Mmult_assoc pn_int_Mmult.
  rewrite mulVg Hstb id_pn_int.
  by rewrite Mmult_1_l.
Qed.

(* From mathcomp Require Import fingroup. *)

(* Seems problematic. Do a math proof first *)
Lemma inv_stb:
  forall {n: nat} (pstr: GenPauliTuple n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb pstr ψ -> stb (inv_png pstr) ψ.
Proof.
  move => n [p str] psi Hwf.
  rewrite /stb /= => Hstb.
  rewrite <- Hstb at 1.
  rewrite <- Mmult_assoc.
  rewrite !Mscale_mult_dist_r !Mscale_mult_dist_l.
  rewrite !Mscale_assoc pn_int_Mmult mulVg.
  assert ((pn_int (id_pn n) × psi) = psi) by admit.
  rewrite H.
  assert (phase_int p * phase_int (inv_phase p) = phase_int (mulg p (inv_phase p))) by admit.
  rewrite H0 mulgV.
  by rewrite Mscale_1_l.
Abort.

