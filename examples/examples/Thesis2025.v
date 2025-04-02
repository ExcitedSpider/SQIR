Require SQIR.UnitaryOps.
Require SQIR.DensitySem.
(* Require SQIR.NDSem. *)

Import UnitaryOps.
Import DensitySem.

Open Scope ucom.

Definition SWAP d a b : base_ucom d := CNOT a b; CNOT b a; CNOT a b.

Lemma swap2: forall (psi phi: Vector 2), 
  WF_Matrix psi -> 
  WF_Matrix phi -> 
  (uc_eval (SWAP 2 0 1)) × (psi ⊗ phi) =  (phi ⊗ psi).
Proof.
  intros psi phi psi_wf phi_wf.
  simpl uc_eval.
  autorewrite with eval_db; simpl; try lia.
  Qsimpl.
  solve_matrix.
Qed.