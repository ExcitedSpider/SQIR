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
Inductive pmult: pauli_group -> pauli_group -> pauli_group -> Prop := 
  | PauliMultRel: forall (a b c: pauli_group),
    (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
    pmult a b c.

Lemma fact_square_x: 
  pmult (One · X)  (One · X) (One · I).
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
  forall (a: pauli_group), pmult ID a a.
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
  forall (a: pauli_group), pmult a ID a.
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

Definition inverse_op (op: pauli_op): pauli_op := 
  match op with
  | I => I
  | X => X
  | Y => Y
  | Z => Z
  end.

Definition inverse_scala (op: scalar): scalar := 
  match op with
  | One => One
  | Iphase => NegIphase
  | NegOne => NegOne
  | NegIphase => Iphase 
  end.

Definition pauli_inverse (p : pauli_group) : pauli_group :=
  match p with
  | PauliElem s op => PauliElem (inverse_scala s) (inverse_op op)
  end.

Lemma pauli_inverse_correct:
  forall (a: pauli_group), exists (a': pauli_group),
  pmult a a' ID.
Proof.
  intros.
  exists (pauli_inverse a). 
  apply PauliMultRel. 
  destruct a.
  destruct s, p;
  solve_matrix.
Qed.


Lemma pauli_closure:
  forall a b,
  exists (c: pauli_group), pmult a b c.
Proof.
  intros a b.
  destruct a as [sa pa], b as [sb pb].
  destruct sa, pa, sb, pb.
  Abort. (* 256 cases. not feasible to prove directly *)

Lemma scalar_closure:
  forall a b,
  exists (c: scalar), 
    (scalar_to_complex a) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
  intros.
  destruct a, b.
  all: simpl.
  all: try (exists One; simpl; lca).
  all: try (exists Iphase; simpl; lca).
  all: try (exists NegOne; simpl; lca).
  all: try (exists NegIphase; simpl; lca).
Qed.

Lemma op_closure:
  forall a b,
  exists (c: pauli_op), 
    (op_to_matrix a) × (op_to_matrix b) = (op_to_matrix c).
Proof.
  intros a b.
  destruct a, b.
  all: simpl.
  all: try(exists I; simpl;Qsimpl;easy).
  all: try(exists X; simpl;Qsimpl;easy).
  all: try(exists Z; simpl;Qsimpl;easy).
  all: try(exists Y; simpl;Qsimpl;easy).
  Abort. (* The lemma is not correct, one need to introduce scalar into this lemma *)


(* This one succeed by using two lemmas *)
Lemma pauli_closure':
  forall a b,
  exists (c: pauli_group), pmult a b c.
Proof.
  intros a b.
  destruct a as [sa pa], b as [sb pb].
  specialize (scalar_closure sa sb) as [sc Hsc].
  specialize (op_closure pa pb) as [pc Hpc].
  exists (PauliElem sc pc).
  apply PauliMultRel; simpl.
  (* Search (_ × (_ .* _)). *)
  repeat rewrite Mscale_mult_dist_r.
  (* Search (_ .* (_ × _)). *)
  rewrite Mscale_mult_dist_l.
  rewrite Hpc.
  rewrite Mscale_assoc.
  rewrite <- Hsc.
  (* Search ((_ * _) = (_ * _)). *)
  rewrite Cmult_comm.
  reflexivity.
Qed.

