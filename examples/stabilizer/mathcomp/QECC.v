(* We present some examples of stabiliser code for case study. *)
(* TODO: add examples for 
  - pauli operator 
  - stabilizer 
*)

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Quantum.
Require Import Stabilizer.

Require Import Action.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import Observable.
Require Import Assumption.

(* Simply Goals like (pn_int _ × _) *)
Ltac SimplApplyPauli := 
    rewrite ?applyP_plus ?applyP_mscale;
    rewrite ?/meas_p_to ?/applyP ?/png_int ?/pn_int /=;
    Qsimpl;
    repeat (
      distribute_plus;
      repeat rewrite <- kron_assoc by auto with wf_db;
      restore_dims
    );
    rewrite ?Mmult_plus_distr_l ?kron_mixed_product; Qsimpl;
    autorewrite with ket_db.

Section QECCTheories.

Variable (dim: nat).

Variable (SyndromeMeas: {set (PauliOperator dim)}).
Variable (DetectableErrors: {set (PauliOperator dim)}).
Variable (psi: Vector (2^dim)).

(* Notation for applying an operator on a state *)
Notation "''Apply' P 'on' psi" := (applyP psi P) (at level 200).
(* 
  SyndromeMeas_stab shows that for all codewords,
  The measurement result is 1.
  Therefore, if we find any other measurement result, 
  we say the error is _detectable_.
  For pauli operators, the eigenvalue is always +-1 see `operator_eigenvalue` 
  so a error is detectable -> syndrome measurement is -1
*)
Definition detectable E := 
  let psi' := 'Apply E on psi in
    exists M,  M \in SyndromeMeas /\ 'Meas M on psi' --> -1.

Definition obs_be_stabiliser :=
  forall (M: Observable dim),
    M \in SyndromeMeas -> M ∝1 psi.

Definition errors_detectable :=
  forall (E: ErrorOperator dim),
  E \in DetectableErrors -> detectable E.


Definition isValidCode :=
  obs_be_stabiliser /\ errors_detectable .

(* Undetectable is that the error state has the same measurement
  as the codespace
  There is an implicit requirement that E should be non-trivial (not I)
*)
Definition undetectable E := 
  let psi' := 'Apply E on psi in
    forall M,  M \in SyndromeMeas -> 'Meas M on psi' --> 1.

(* 
Two errors are indistinguishable when all syndrome measurment
yields the same result
*)
Definition indistinguishable E1 E2 :=
  forall M, M \in SyndromeMeas -> 
  let psi_e1 := 'Apply E1 on psi in
  let psi_e2 := 'Apply E2 on psi in
    ('Meas M on psi_e1 --> -1) -> ('Meas M on psi_e2 --> -1)
  .

End QECCTheories.


Arguments obs_be_stabiliser {dim}.
Arguments errors_detectable {dim}.

Section Structure.

Record ErrorCorrectionCode := MkECC {
  dim: nat
; psi: Vector (2^dim)
; obs: {set Observable dim}
; err: {set PauliOperator dim}
; obligation: obs_be_stabiliser obs psi /\ errors_detectable obs err psi
}.

End Structure.

Check MkECC.

Require Export SQIR.UnitaryOps.
Module BitFlip311.

Section T.

Open Scope ucom.

Definition dim:nat := 3.

Variable (α β : C).

(* A quantum state (α .* ∣0⟩ .+ β .* ∣1⟩) is required to have norm = 1 *)
Hypothesis norm_obligation: α^* * α + β^* * β = 1.

Definition encode : base_ucom dim := 
  CNOT 0 1; CNOT 0 2.


(* The state before encoding, labeled by 'b' *)
Notation psi_b := ((α .* ∣0⟩ .+ β .* ∣1⟩)).

Notation L0 := ∣0,0,0⟩. (* Logical 0 *)
Notation L1 := ∣1,1,1⟩. (* Logical 1 *)
(* The state after encoding *)
Definition psi: Vector (2^dim) := (α .* L0.+ β .* L1).

Lemma psi_WF:
  WF_Matrix psi.
Proof. by rewrite /psi; auto with wf_db. Qed.

(* This should be make more generic, but i did not find a good one *)
Lemma encode_by_component: forall (u: Square (2^dim)),
  u × (∣0⟩ ⊗ ∣0,0⟩) = L0 ->
  u × (∣1⟩ ⊗ ∣0,0⟩) = L1 ->
  u × (psi_b ⊗ ∣0,0⟩) = psi.
Proof.
  move => H0 H1 H2.
  rewrite kron_plus_distr_r Mmult_plus_distr_l.
  rewrite !Mscale_kron_dist_l !Mscale_mult_dist_r.
  by rewrite H1 H2.
Qed.

Set Bullet Behavior "Strict Subproofs".

(* The encoding program is correct *)
Theorem encode_correct :
  (uc_eval encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ )
  = α .* L0 .+ β .* L1.
Proof.
  rewrite /= /L0 /L1.
  apply encode_by_component;
  autorewrite with eval_db; simpl; Qsimpl.
  all: repeat (
    distribute_plus;
    repeat rewrite <- kron_assoc by auto with wf_db;
    restore_dims
  );
  repeat rewrite kron_mixed_product; Qsimpl;
  by autorewrite with ket_db.
Qed.

(* After verifing the encoding circuit, we can 
  work sorely on abstract codespace and pauli operator
*)

Require Import PauliGroup.


Notation "[ 'set' a1 , a2 , .. , an ]" := (setU .. (a1 |: [set a2]) .. [set an]) (at level 200): form_scope.

Definition setexample := [set true, false, true ].


(* Set of single-qubit bit-flip error *)
Definition X1: PauliOperator 3 := [p X, I, I].
Definition X2: PauliOperator 3 := [p I, X, I].
Definition X3: PauliOperator 3 := [p I, I, X].
Definition BitFlipError: {set ErrorOperator 3 } := 
  [set X1, X2, X3].

(* Syndrome measurement *)
Definition Z12 := [p Z, Z, I].
Definition Z23 := [p I, Z, Z].
Definition SyndromeMeas: {set Observable 3} :=
  [set Z12, Z23].


(* Syndrome Measurement Does not change the correct code *)
Theorem SyndromeMeas_stab :
  forall (M: Observable dim),
    M \in SyndromeMeas -> 'Meas M on psi --> 1.
Proof.
  move => M.
  rewrite !inE => Hm.
  case/orP: Hm => Hm;
  move/eqP: Hm => Hm;
  rewrite Hm /meas_p_to /psi;
  rewrite !Mmult_plus_distr_l !Mscale_mult_dist_r;
  rewrite /psi;
  SimplApplyPauli.
  - by replace (β * (-1) * (-1)) with (β) by lca.
  - by replace (β * (-1) * (-1)) with (β) by lca.
Qed.

Notation I2 := (Matrix.I 2).
  
(* Apply any error in BitFlipError, there is at least one Syndrome Measurement
 can detect it *)

Theorem obs_be_stabiliser_i :
  obs_be_stabiliser SyndromeMeas psi.
Proof.
  rewrite /obs_be_stabiliser => M Mmem.
    rewrite stb_meas_p_to_1.
    by apply SyndromeMeas_stab.
Qed.

Theorem errors_detectable_i :
  errors_detectable SyndromeMeas BitFlipError psi.
Proof.
  rewrite /errors_detectable.
  move => E.
  rewrite !inE -orb_assoc /detectable => memE.
  case/or3P: memE => HE;
  move/eqP: HE => HE;
  rewrite /=; subst;
  rewrite !applyP_plus !applyP_mscale.
  - exists Z12. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
  (* Z23 also works for X2 Error *)
  - exists Z12. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
  - exists Z23. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
Qed.

Theorem itIsValidCode:
  isValidCode dim SyndromeMeas BitFlipError psi.
Proof.
  rewrite /isValidCode.
  split.
  - by apply obs_be_stabiliser_i.
  - by apply errors_detectable_i.
Qed.

Definition BitFlipCode := MkECC 3 psi SyndromeMeas BitFlipError itIsValidCode.

Definition PhaseFlip0: PauliOperator 3 := [p Z, I, I].

(* Notation for applying an operator on a state *)
Notation "''Apply' P 'on' psi" := (applyP psi P) (at level 200).
Fact phase_flip_error_effect:
  ('Apply PhaseFlip0 on psi) = (α .* L0 .+ -1 * β .* L1).

Proof. by rewrite /L0 /L1; SimplApplyPauli; lma. Qed.

(* This code is unable to detect phase flip *)
Fact undetectable_phase_flip_0: 
  undetectable dim SyndromeMeas psi PhaseFlip0.
Proof.
  rewrite /undetectable /= => M.
  (* ssreflect magic *)
  rewrite !inE => /orP [/eqP -> | /eqP ->].
  - SimplApplyPauli. lma.
  - SimplApplyPauli. lma.
Qed.

(* error E can be recovered by R *)
Definition recover_by {n} (E: ErrorOperator n) (R: PauliOperator n) :=
  mult_png R E = (@oneg (PauliElement n)).

(* Apply the error then the recover, the original state is restored *)
Theorem recover_by_correct {n} :
  forall (E: ErrorOperator n) (R: PauliOperator n) (phi: Vector (2^n)),
  WF_Matrix phi ->
  recover_by E R -> 
  let phi' := 'Apply E on phi in
  ('Apply R on phi') = phi.
Proof.
  rewrite /= => E R psi Hwf.
  rewrite /recover_by.
  rewrite applyP_comb /= /mulg /=.
  move => ->.
  rewrite /oneg /=.
  apply (applyP_id).
  apply Hwf.
Qed.

Fact flip0_recover_by_x0:
  (recover_by X1 X1).
Proof. by rewrite /recover_by; apply /eqP. Qed.

Notation psi_x1 := ('Apply X1 on psi).
Notation psi_x23 := ('Apply X3 on ('Apply X2 on psi)).


Lemma psi_x23_simpl:
  psi_x23 = α .* ∣0,1,1⟩ .+ β .* ∣1,0,0⟩.
Proof.
  rewrite applyP_comb.
  assert (mult_png X3 X2 = ([p1 I, X, X])).
   by apply /eqP.
  rewrite /mulg /= H.
  by SimplApplyPauli.
Qed.


Lemma psi_x1_simpl:
  psi_x1 = α .* ∣1,0,0⟩ .+ β .* ∣0,1,1⟩.
Proof.
  by SimplApplyPauli.
Qed.

(* If two basic states are identical, inner producr is 1 *)
(* Else 0 *)
Ltac simplify_inner_product :=
  repeat match goal with
  | |- context[⟨ ?v, ?v ⟩] =>
      let H := fresh in
      assert (H: ⟨ v, v ⟩ = 1)   by lca; rewrite H; clear H
  | |- context[⟨ ?v1, ?v2 ⟩] =>
      let H := fresh in
      assert (H: ⟨ v1, v2 ⟩ = 0) by lca; rewrite H; clear H
  end.


(* This one is apparent on paper but rediculusly hard  *)
(* in coq *)
Lemma psi_x23_nonzero:
  psi_x23 <> Zero.
Proof.
  rewrite psi_x23_simpl => F.
  apply inner_product_zero_iff_zero in F.
  contradict F.
  rewrite !inner_product_plus_l !inner_product_plus_r;
  rewrite !inner_product_scale_l !inner_product_scale_r.
  simplify_inner_product.
  Csimpl.
  rewrite norm_obligation.
  by nonzero.
  by auto with wf_db.
Qed.

Lemma psi_x1_nonzero:
  psi_x1 <> Zero.
Proof.
  rewrite psi_x1_simpl => F.
  apply inner_product_zero_iff_zero in F.
  contradict F.
  rewrite !inner_product_plus_l !inner_product_plus_r.
  rewrite !inner_product_scale_l !inner_product_scale_r.
  simplify_inner_product.
  Csimpl.
  rewrite norm_obligation.
  by nonzero.
  by auto with wf_db.
Qed.

(* the measurement of error {X1} and {X2, X3} are the same *)
(* Therefore, this code cannot determine which error has happened *)
Theorem indistinguishable_errors:
  forall (M: Observable dim) m, M \in SyndromeMeas -> 
    ('Meas M on psi_x1 --> m) -> ('Meas M on psi_x23 --> m)
  .
Proof.
  move => M m.
  rewrite psi_x23_simpl psi_x1_simpl.
  rewrite !inE => /orP [/eqP -> | /eqP ->] H.
  - assert (m = -1).
    {
      apply (meas_p_to_unique _ _ _ _ H). 
      SimplApplyPauli. lma.
      rewrite -psi_x1_simpl.
      apply psi_x1_nonzero.
    }
    subst. SimplApplyPauli. lma.
  - assert (m = 1).
    {
      apply (meas_p_to_unique _ _ _ _ H). 
      SimplApplyPauli. lma.
      rewrite -psi_x1_simpl.
      apply psi_x1_nonzero.
    }
    subst. SimplApplyPauli. lma.
Qed.

End T.

End BitFlip311.