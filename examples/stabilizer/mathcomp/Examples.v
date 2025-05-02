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
  - rewrite /act_n /apply_n /=. Qsimpl.  
    repeat rewrite kron_assoc;  auto with wf_db.
    rewrite kron_mixed_product; Qsimpl.
    by rewrite !MmultX0.
  - rewrite /act_n /apply_n /=. Qsimpl.  
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

Definition E00X1 := apply_n _ L00 Error_X1.

(* 
  An X1 error (single bit-flip on first qubit)
  can be detected by measurment ZZZZ
*)
Theorem error_x1_syndrome:
  (meas_p_to (-C1) (snd zzzz) E00X1).
Proof.
(* This proof is still ugly *)
(* I am thinking speed up the computation of pauli operator application 
  on basis state.
  It might be very lovely in thesis  
*)
  rewrite /meas_p_to /zzzz /=.
  Qsimpl.
  rewrite /E00X1 /L00 /Error_X1 /apply_n /=.
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