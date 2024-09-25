Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.

Require Import Common.

Module ThreeQubitCode.

Open Scope ucom.

(* 4 + 2 ancillas for error correction *)
Definition dim : nat := 4.

Module FourQubitDetection.

(* ====
Encoding Correct
==== *)

Definition encode: base_ucom dim := 
  CNOT 0 2;
  H 3;
  CNOT 1 2;
  CNOT 3 2;
  CNOT 3 1;
  CNOT 3 0.

Lemma encode_correct_zero:
  (@uc_eval dim encode) × ∣ 0,0,0,0 ⟩ =  / √ 2 .* (∣ 0,0,0,0 ⟩ .+ ∣ 1,1,1,1 ⟩).
Proof.
  simpl.
  autorewrite with eval_db; simpl.
  remember (I 4).
  Msimpl.
  (* Can't do automation: too slow *)
  (* solve_matrix. *)
  (* Need to do it manually *)
  repeat rewrite Mmult_assoc.
  restore_dims; rewrite kron_mixed_product.
  Msimpl. 
  (* rewrite H0_spec.  *)
  (* Success first simplication step *)
  replace ((∣1⟩⟨1∣ ⊗ I 2 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) × ∣ 0, 0, 0 ⟩) with (∣ 0, 0, 0 ⟩). 2: { 
    restore_dims.
    rewrite Common.zero_3_f_to_vec.
    simpl.
    solve_matrix.
  }
  (* restore_dims; rewrite kron_mixed_product.  *)
  (* Sucess *)
  replace (∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2) with cnot by solve_matrix.
  restore_dims.
  replace ( I 2 ⊗ cnot × ∣ 0, 0, 0 ⟩ ) with (∣0⟩ ⊗ cnot × ∣ 0, 0 ⟩) by solve_matrix.
  replace ( ∣0⟩ ⊗ cnot × ∣ 0, 0 ⟩ ) with  ∣ 0, 0, 0 ⟩ by solve_matrix.
  rewrite <- Mmult_assoc.
  restore_dims.
  (* This does not apply? supper annoying *)
  (* Ask Christine how she thinks about it*)
  Fail rewrite kron_mixed_product.
  Abort.

Lemma zero_4_f_to_vec:
  ∣ 0, 0, 0, 0 ⟩ = f_to_vec 4 (fun _ : nat => false).
Proof. 
  apply mat_equiv_eq.
  - (* left well formed *) auto with wf_db.
  - (* right well formed *) unfold f_to_vec. simpl. auto with wf_db.
  - by_cell; lca.
Qed.


(* Simpler to work entirely as vectors *)
Lemma encode_correct_zero':
  (@uc_eval dim encode) × ∣ 0,0,0,0 ⟩ =  / √ 2 .* (∣ 0,0,0,0 ⟩ .+ ∣ 1,1,1,1 ⟩).
Proof.
  rewrite zero_4_f_to_vec.
  
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  restore_dims.
  (* This is the key that vector representation can be used to simplify verification*)
  repeat Common.f_to_vec_simpl_light; simpl.
  Qsimpl.
  replace (0 * PI)%R with 0%R by lra.
  (* Simplify Trigonometrics *)
  autorewrite with Cexp_db.
  rewrite Mscale_1_l.
  reflexivity.
Qed.

(* Distinguish Ancilla Qubits and Physical Qubits *)
Lemma encode_correct_zero'':
  (@uc_eval dim encode) × (∣ 0,0 ⟩ ⊗ ∣ 0, 0 ⟩) =  / √ 2 .* (∣ 0,0,0,0 ⟩ .+ ∣ 1,1,1,1 ⟩).
Proof.
  assert (∣ 0, 0, 0, 0 ⟩ = ∣ 0, 0 ⟩ ⊗ ∣ 0, 0 ⟩).
  {
    repeat rewrite <- kron_assoc by auto with wf_db.
    reflexivity.
  }
  rewrite <- H.
  apply encode_correct_zero'.
Qed.

Lemma f_to_vec_one:
  ∣ 0, 1, 0, 0 ⟩ = f_to_vec 4 (fun n => n =? 1).
Proof.
lma'. simpl. auto with wf_db.
Qed.

(* Solve equations in vector representation *)
(* Copy from nine-qubit code *)
Ltac compute_vec :=
  simpl uc_eval;
  repeat rewrite Mmult_assoc; restore_dims;
  repeat Common.f_to_vec_simpl_light;
  simpl;
  replace (0 * PI)%R with 0%R by lra;
  replace (1 * PI)%R with PI by lra;
  autorewrite with Cexp_db;
  repeat rewrite Mscale_1_l;
  restore_dims;
  autorewrite with ket_db.

Lemma encode_correct_one:
  (@uc_eval dim encode) × (∣ 0, 1 ⟩ ⊗ ∣ 0, 0 ⟩) =  
    / √ 2 .* (∣ 0,1,1,0 ⟩ .+ ∣ 1,0,0,1 ⟩).
Proof.
  assert (∣ 0, 1 ⟩ ⊗ ∣ 0, 0 ⟩ = ∣ 0, 1, 0, 0 ⟩).
  {
    repeat rewrite <- kron_assoc by auto with wf_db.
    reflexivity.
  }
  rewrite H.
  rewrite f_to_vec_one.
  now compute_vec.
Qed.

Lemma encode_correct_two:
  (@uc_eval dim encode) × (∣ 1, 0 ⟩ ⊗ ∣ 0, 0 ⟩) =  
    / √ 2 .* (∣ 1,0,1,0 ⟩ .+ ∣ 0,1,0,1 ⟩).
Proof. Admitted. (* Similar to encode_correct_one. Fill the proof later*)


Lemma encode_correct_three:
  (@uc_eval dim encode) × (∣ 1, 1 ⟩ ⊗ ∣ 0, 0 ⟩) =  
    / √ 2 .* (∣ 1,1,0,0 ⟩ .+ ∣ 0,0,1,1 ⟩).
Proof. Admitted. (* Similar to encode_correct_one. Fill the proof later*)

Definition two_qubit_system (c1 c2 c3 c4: C) := 
  c1 .* ∣ 0,0 ⟩ .+ c2 .*  ∣ 0,1 ⟩ .+ c3 .*  ∣ 1,0 ⟩ .+ c4 .*  ∣ 1,1 ⟩.

Definition code_space (c1 c2 c3 c4: C) := 
  / √ 2 * c1 .*  (∣ 0,0,0,0 ⟩ .+ ∣ 1,1,1,1 ⟩ ) .+ 
  / √ 2 * c2 .*  (∣ 0,1,1,0 ⟩ .+ ∣ 1,0,0,1 ⟩ ) .+ 
  / √ 2 * c3 .*  (∣ 1,0,1,0 ⟩ .+ ∣ 0,1,0,1 ⟩ ) .+ 
  / √ 2 * c4 .*  (∣ 1,1,0,0 ⟩ .+ ∣ 0,0,1,1 ⟩ ).

(*
  Correctness for encoding circuit
*)
Lemma encode_correct_wordy:
  forall c1 c2 c3 c4: C,
  let state := two_qubit_system c1 c2 c3 c4 in 
  (@uc_eval dim encode) × (state ⊗ ∣ 0,0 ⟩) = 
  code_space c1 c2 c3 c4.
Proof.
  intros.
  subst state.
  unfold code_space, two_qubit_system.
  restore_dims; repeat rewrite kron_plus_distr_r.
  restore_dims; repeat rewrite Mmult_plus_distr_l.
  distribute_scale.
  repeat rewrite Mscale_mult_dist_r.
  restore_dims; rewrite encode_correct_zero''.
  restore_dims; rewrite encode_correct_one.
  restore_dims; rewrite encode_correct_two.
  restore_dims; rewrite encode_correct_three.
  (* try to find the association rule*)
  Search (_ .* (_ .* _) = _).
  repeat rewrite Mscale_assoc.
  (* try to find the commutative rule*)
  Search (_ * _ = _ * _).
  (* This looks awful. How to simplify it*)
  replace (c1 * / √ 2) with (/ √ 2 * c1) by lca.
  replace (c2 * / √ 2) with (/ √ 2 * c2) by lca.
  replace (c3 * / √ 2) with (/ √ 2 * c3) by lca.
  replace (c4 * / √ 2) with (/ √ 2 * c4) by lca.
  reflexivity.
Qed.


(* ====
Error Detection
==== *)

(* Simplified one error *)

Inductive error: Set :=
  NoError |
  X0 | X1 | X2 | X3 |
  Z0 | Z1 | Z2 | Z3.

Definition apply_error (e : error) : base_ucom dim :=
  match e with
  | NoError => SKIP
  | X0 => SQIR.X 0
  | X1 => SQIR.X 1
  | X2 => SQIR.X 2
  | X3 => SQIR.X 3
  | Z0 => SQIR.Z 0
  | Z1 => SQIR.Z 1
  | Z2 => SQIR.Z 2
  | Z3 => SQIR.Z 3
  end.


