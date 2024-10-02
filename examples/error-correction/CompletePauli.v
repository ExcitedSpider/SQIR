Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.

(* 
  Complete pauli group (operations with scalars) 
  However, we expect it will not be used in the stabilizer formalism
  because for stabilizer, scalars are useless. It only acts as unneccesary
  complexity. 

  But it's still valueable to have this complete formalism
*)

Inductive pauli_op : Type :=
  | I : pauli_op
  | X : pauli_op
  | Y : pauli_op
  | Z : pauli_op.

Inductive scalar : Type :=
  | One : scalar      (* 1 *)
  | Iphase : scalar   (* i *)
  | NegOne : scalar   (* -1 *)
  | NegIphase : scalar. (* -i *)

Inductive pauli_group : Type :=
  | PauliElem : scalar -> pauli_op -> pauli_group.

(* Define a custom notation for elements of the Pauli group *)
Notation "s · p" := (PauliElem s p) (at level 40, left associativity).

Check One · X.
Check Iphase · Z.

Definition scalar_to_complex (s : scalar) : C :=
  match s with
  | One => 1
  | Iphase => Ci
  | NegOne => -1
  | NegIphase => - Ci 
  end.

Definition op_to_matrix (p : pauli_op) : Square 2 :=
  match p with
  | I => QuantumLib.Matrix.I 2 
  | X => σx
  | Y => σy
  | Z => σz
  end.

Definition pauli_to_matrix (p: pauli_group): Square 2 := 
    match p with
      | PauliElem s op => (scalar_to_complex s) .* (op_to_matrix op)
    end.

Example negY: pauli_to_matrix (NegOne · Y) = -1 .* σy.
Proof. reflexivity. Qed.


Example negIX: pauli_to_matrix (NegIphase · X) = -Ci .* σx.
Proof. reflexivity. Qed.

(* The operation on the pauli group *)
Inductive multi_pauli: pauli_group -> pauli_group -> pauli_group -> Prop := 
  | PauliMultRel: forall (a b c: pauli_group),
    (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
    multi_pauli a b c.

Lemma fact_square_x: 
  multi_pauli (One · X)  (One · X) (One · I).
Proof.
  apply PauliMultRel.
  simpl.
  solve_matrix.
Qed.

Definition ID := (One · I).

Lemma pauli_op_wf: 
  forall (a: pauli_group), WF_Matrix (pauli_to_matrix a).
Proof.
  intros.
  destruct a.
  destruct s, p;
  simpl;
  auto with wf_db.
Qed.

Lemma pauli_identity_correct_left:
  forall (a: pauli_group), multi_pauli ID a a.
Proof.
  intros.
  apply PauliMultRel.
  simpl.
  rewrite Mscale_1_l.
  (* Search (Matrix.I _ = _). *)
  apply mat_equiv_eq.
  - apply WF_mult.
    + auto with wf_db.
    + apply pauli_op_wf.
  - apply pauli_op_wf.  
  - apply Mmult_1_l_mat_eq.
Qed.

Lemma pauli_identity_correct:
  forall (a: pauli_group), multi_pauli a ID a.
Proof.
  intros.
  apply PauliMultRel; simpl.
  rewrite Mscale_1_l.
  apply mat_equiv_eq.
  - apply WF_mult.
    + apply pauli_op_wf.
    + auto with wf_db. 
  - apply pauli_op_wf.  
  - apply Mmult_1_r_mat_eq.
Qed.
