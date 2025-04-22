(* We present some examples of stabiliser code for case study. *)
(* TODO: add examples for 
  - pauli operator 
  - stabilizer 
*)


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple finset.
Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.
Require Import Stabilizer.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import PauliGroup.
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.
Require Import WellForm.

Open Scope ucom.

(* 4 + 2 ancillas for error correction *)
Definition dim : nat := 4.

Module FourQubitDetection.

(* 1. Define Generators as <XXXX, ZZZZ> *)
(* 2. Prove number of detectable errors by showing distance=2 *)
(* 3. Prove Syndrome Detection *)

Definition zzzz := [p1 Z, Z, Z, Z]: PString 4.
Definition xxxx := [p1 X, X, X, X]: PString 4.

Definition g422 := setU [set zzzz] [set xxxx].

Lemma is_stb_set_g422:
  is_stb_set g422.
Proof.
  (* Ask Zeo about this  *)
Admitted. (* TODO *)

Lemma zzzz_stb:
  zzzz ∝1 (∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩).
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
  xxxx ∝1 (∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩).
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
  is_stb_set_spec g422 (∣ 0, 0, 0, 0 ⟩ .+ ∣ 1, 1, 1, 1 ⟩).
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

End FourQubitDetection.