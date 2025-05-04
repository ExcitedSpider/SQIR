(* We present some examples of stabiliser code for case study. *)
(* TODO: add examples for 
  - pauli operator 
  - stabilizer 
*)

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.
Require Import Stabilizer.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import Observable.

Module FourQubitDetection.

(* 1. Define Generators as <XXXX, ZZZZ> *)
(* 2. Prove number of detectable errors by showing distance=2 *)
(* 3. Prove Syndrome Detection *)

Definition zzzz := [p1 Z, Z, Z, Z]: PauliElement 4.
Definition xxxx := [p1 X, X, X, X]: PauliElement 4.
Definition iiii := [p1 I, I, I, I]: PauliElement 4.
Definition yyyy := [p1 Y, Y, Y, Y]: PauliElement 4.

(* We can use the stabilizer generator to generate the stabilizer group. *)

Import Commutativity.

Definition g422 := [set zzzz] :|: [set xxxx].
Definition s422 := g422 :|: [set (mulg zzzz xxxx)] :|: [set iiii].

(* We can use the stabilizer generator to generate the stabilizer group. *)

Definition ψ := ∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩.

Check generated.

Set Bullet Behavior "Strict Subproofs".

Lemma g422_full_group:
  <<g422>> = s422.
Proof.
  (* First we show that s44 forms a group *)
  have: group_set s422.
  {
     apply /group_setP.
     rewrite /=.
     split.
     -  have: (oneg (PauliElement 4) = id_png 4) by apply /eqP.
        move => ->. 
        by rewrite !inE.
      - move => x y.
        rewrite !inE.
        rewrite -!orb_assoc => Hx Hy.
        case/or4P: Hx => Hx;
        case/or4P: Hy => Hy;
        move/eqP: Hx => Hx; 
        move/eqP: Hy => Hy; 
        by subst.
  }
  move => H.
  apply /eqP.
  rewrite eqEsubset.
  apply /andP.
  split.
  (* <<g422>> \subset s422 *)
  - apply gen_set_id in H.
    rewrite <- H.
    apply genS.
    rewrite /s422.
    rewrite -setUA.
    apply subsetUl.
  - (* s422 \subst <<g422>> *)
Admitted. (* TODO: How to do case analysis for each element in s422? *)

Lemma is_stb_set_g422:
  is_stb_set g422.
Proof.
  rewrite /is_stb_set //= => x y.
  rewrite g422_full_group /s422.
  split.
  apply (stabilizer_must_commute _ _ ψ).
  {
    move: H.
    rewrite !inE.
    rewrite -!orb_assoc => orH.
    case/or4P: orH => Hx;
    move/eqP: Hx => Hx; rewrite Hx.
    (* it's tedious but definately doable. *)
  (* but actually this is not needed. *)
  (* We present a much easier proof below *)
    all: admit.
  }
  admit. (* same as x *)
  (* have H: (stb_group_no_m1 x y ψ).
Admitted. TODO *)
Abort.


Lemma is_stb_set_g422:
  is_stb_set g422.
Proof. 
  rewrite /is_stb_set //= => x y.
  rewrite g422_full_group => Hx Hy.
  split.
  {
    move: Hx Hy.
    rewrite !inE -!orb_assoc => Hx Hy.
    case/or4P: Hx => /eqP Hx;
    case/or4P: Hy => /eqP Hy;
    subst; by apply /eqP.
  }
  {
    move {Hx Hy}.
    apply /idP.
    by rewrite !inE.
  }
Qed.

Definition L00 := ∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩.
Definition L01 := ∣ 0, 0, 1, 1 ⟩ .+ ∣ 1, 1, 0, 0 ⟩.
Definition L10 := ∣ 0, 1, 0, 1 ⟩ .+ ∣ 1, 0, 1, 0 ⟩.
Definition L11 := ∣ 0, 1, 1, 0 ⟩ .+ ∣ 1, 0, 0, 1 ⟩.

Lemma zzzz_stb:
  zzzz ∝1 (L00).
Proof.
  rewrite /zzzz.
  apply stb_addition.
  - replace ∣ 0, 0, 0, 0⟩ with (∣ 0, 0⟩ ⊗ ∣ 0, 0 ⟩) by normalize_kron_notation. 
    apply (stb_compose_alt' ([p1 Z, Z]) ([p1 Z, Z])). by_compose_pstring. 
    simpl_stbn. simpl_stbn.
  - replace ∣ 1, 1, 1, 1⟩ with (∣ 1, 1⟩ ⊗ ∣ 1, 1 ⟩) by normalize_kron_notation. 
    apply (stb_compose_alt' ([p1 Z, Z]) ([p1 Z, Z])). by_compose_pstring. 
    simpl_stbn. simpl_stbn.
Qed.


Lemma xxxx_stb:
  xxxx ∝1 (L00).
Proof.
  rewrite /xxxx.
apply stb_symm_perm.
  - rewrite /act_n /applyP /=. Qsimpl.  
    repeat rewrite kron_assoc;  auto with wf_db.
    rewrite kron_mixed_product; Qsimpl.
    by rewrite !MmultX0.
  - rewrite /act_n /applyP /=. Qsimpl.  
    repeat rewrite kron_assoc;  auto with wf_db.
    rewrite kron_mixed_product; Qsimpl.
    by rewrite !MmultX1.
Qed.

Theorem is_stb_set_g422':
  is_stb_set_spec g422 L00.
Proof.
  rewrite /is_stb_set_spec /is_stb_set /= => x Hx.
  move: (stb_generator g422 (∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩)) => H.
  apply (H); auto.
  rewrite /= => a.
  rewrite inE => Ha.
  case/orP: Ha; rewrite inE => Ha;
  move/eqP: Ha => Ha; subst;
  rewrite /zzzz /xxxx.
  - by apply zzzz_stb. 
  - by apply xxxx_stb.
Qed.

Theorem g422_distance:
  distance_s _ g422 2.
Proof.
  rewrite /distance_s .
  exists ([p Z, Z, I, I]).
  split.
  - apply not_detactable.
    exists zzzz.
    split.
    {
      rewrite inE.
      apply/orP; left.
      by rewrite inE.
    }
    rewrite /zzzz /with_1 /=.
    by apply /eqP. (* this is benefit from mathcomp *)
  - by rewrite /weight /=. 
Qed.

Theorem g422_dimension_2: 
  dimension _ g422 = 2%nat.
Proof.
  by rewrite /dimension cards2 /=.
Qed.

Definition Error_X1 := [p1 X, I, I, I].

Definition E00X1 := applyP L00 Error_X1.

(* 
  An X1 error (single bit-flip on first qubit)
  can be detected by measurment ZZZZ
*)
Theorem error_x1_syndrome:
  'Meas (snd zzzz) on E00X1 --> -C1.
Proof.
(* This proof is still ugly *)
(* I am thinking speed up the computation of pauli operator application 
  on basis state.
  It might be very lovely in thesis  
*)
  rewrite /meas_p_to /zzzz /=.
  Qsimpl.
  rewrite /E00X1 /L00 /Error_X1 /applyP /=.
  Qsimpl.
  rewrite -!kron_assoc; auto with wf_db.
  repeat rewrite kron_mixed_product. Qsimpl.
  restore_dims.
  autorewrite with ket_db.
  replace (-C1) with (RtoC (-1)) by lca.
  replace (((-1) * (-1)) * (-1)) with (RtoC (-1)) by lca.
  by [].
Qed.

End FourQubitDetection.

Require Export SQIR.UnitaryOps.

Section ThreeQubitCorrectionCode.

Open Scope ucom.

Definition dim:nat := 3.

Variable (α β : C).

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

(* Notation Just for readability *)
Notation ErrorOperator := PauliOperator.
Notation Observable := PauliOperator.

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
  
(* Notation for applying an operator on a state *)
Notation "''Apply' P 'on' psi" := (applyP psi P) (at level 200).
(* Apply any error in BitFlipError, there is at least one Syndrome Measurement
 can detect it *)

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

(* Undetectable is that the error state has the same measurement
  as the codespace
  There is an implicit requirement that E should be non-trivial (not I)
*)
Definition undetectable E := 
  let psi' := 'Apply E on psi in
    forall M,  M \in SyndromeMeas -> 'Meas M on psi' --> 1.

Theorem detectable_bit_flip :
  forall (E: ErrorOperator dim),
  E \in BitFlipError -> detectable E.
Proof.
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

Definition PhaseFlip0: PauliOperator 3 := [p Z, I, I].

Fact phase_flip_error_effect:
  ('Apply PhaseFlip0 on psi) = (α .* L0 .+ -1 * β .* L1).
Proof. by rewrite /L0 /L1; SimplApplyPauli; lma. Qed.

(* This code is unable to detect phase flip *)
Fact undetectable_phase_flip_0: 
  undetectable PhaseFlip0.
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

End ThreeQubitCorrectionCode.
