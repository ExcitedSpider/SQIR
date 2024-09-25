Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.


(* Formalize the pauli group . Not complete! need to include scalars *)

Inductive Pauli : Type :=
  | I : Pauli
  | X : Pauli
  | Y : Pauli
  | Z : Pauli.

(* map to matrix  *)
Definition pauli_to_matrix (p : Pauli): Square 2 :=
  match p with
  | I => QuantumLib.Matrix.I 2 
  | X => σx          
  | Y => σy        
  | Z => σz
  end.

Definition Pauli_X := pauli_to_matrix X.
Definition Pauli_Y := pauli_to_matrix Y.
Definition Pauli_I := pauli_to_matrix I.
Definition Pauli_Z := pauli_to_matrix Z.

Lemma pauli_fact_id: Pauli_X × Pauli_X = Pauli_I.
Proof.
  unfold Pauli_X, Pauli_I.
  solve_matrix.
Qed.

Definition pauli_identity : Pauli := I.

Definition pauli_inverse (p : Pauli) : Pauli :=
  match p with
  | I => I
  | X => X
  | Y => Y
  | Z => Z
  end.

(* This is too ugly. I need to define the operation (multiplication) explicitly*)
Lemma pauli_inverse_correct: forall (p: Pauli),
  (pauli_to_matrix p) × (pauli_to_matrix (pauli_inverse p)) = pauli_to_matrix pauli_identity.
Proof.
  simpl.
  intros.
  destruct p; simpl; solve_matrix.
Qed.

Theorem pauli_associative : forall p1 p2 p3 : Pauli,
  pauli_to_matrix p1 × (
    pauli_to_matrix p2 × 
    pauli_to_matrix p3) = (pauli_to_matrix p1 × pauli_to_matrix p2) × pauli_to_matrix p3.
Proof.
  intros.
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.

Theorem pauli_identity_left : forall p : Pauli,
  (pauli_to_matrix pauli_identity) × (pauli_to_matrix p) = pauli_to_matrix p.
Proof.
  intros. destruct p; solve_matrix.
Qed.

