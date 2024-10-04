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

Inductive pauli : Type :=
  | PauliElem : scalar -> pauli_op -> pauli.

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

Definition pauli_to_matrix (p: pauli): Square 2 := 
    match p with
      | PauliElem s op => (scalar_to_complex s) .* (op_to_matrix op)
    end.

Example negY: pauli_to_matrix (NegOne · Y) = -1 .* σy.
Proof. reflexivity. Qed.


Example negIX: pauli_to_matrix (NegIphase · X) = -Ci .* σx.
Proof. reflexivity. Qed.

(* The operation on the pauli group *)
(* Define the operation as relation makes it so hard *)
Inductive pmult: pauli -> pauli -> pauli -> Prop := 
  | PauliMultRel: forall (a b c: pauli),
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
  forall (a: pauli), WF_Matrix (pauli_to_matrix a).
Proof.
  intros.
  destruct a.
  destruct s, p;
  simpl;
  auto with wf_db.
Qed.

Lemma pauli_identity_correct_left:
  forall (a: pauli), pmult ID a a.
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
  forall (a: pauli), pmult a ID a.
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

Definition pauli_inverse (p : pauli) : pauli :=
  match p with
  | PauliElem s op => PauliElem (inverse_scala s) (inverse_op op)
  end.

Lemma pauli_inverse_correct:
  forall (a: pauli), exists (a': pauli),
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
  exists (c: pauli), pmult a b c.
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

Ltac MRefl :=
  simpl; Qsimpl; try reflexivity; try solve_matrix.

Ltac MReflExists scale op :=
  try (exists op, scale; MRefl).
  

Lemma op_closure:
  forall a b,
  exists (c: pauli_op) (s: scalar), 
    (op_to_matrix a) × (op_to_matrix b) = (scalar_to_complex s) .* (op_to_matrix c).
Proof.
  intros a b.
  destruct a, b.
  all: simpl; Qsimpl.
  (* This is so painful. don't know how to revert `exists` *)
  MReflExists One I.
  MReflExists One X.
  MReflExists One Y.
  MReflExists One Z.
  MReflExists One X.
  MReflExists One I.
  MReflExists Iphase Z.
  MReflExists NegIphase Y.
  MReflExists One Y.
  MReflExists NegIphase Z.
  MReflExists One I.
  MReflExists Iphase X.
  MReflExists One Z.
  MReflExists Iphase Y.
  MReflExists NegIphase X.
  MReflExists One I.
Qed.


(* This one succeed by using two lemmas *)
Lemma pauli_closure':
  forall a b,
  exists (c: pauli), pmult a b c.
Proof.
  intros a b.
  destruct a as [sa pa], b as [sb pb].
  specialize (scalar_closure sa sb) as [sc Hsc].
  specialize (op_closure pa pb) as [pc Hpc].
  destruct Hpc as [s Hpc].
  specialize (scalar_closure sc s) as [sc' Hsc'].
  exists (PauliElem sc' pc).
  apply PauliMultRel; simpl.
  (* Search (_ × (_ .* _)). *)
  repeat rewrite Mscale_mult_dist_r.
  (* Search (_ .* (_ × _)). *)
  rewrite Mscale_mult_dist_l.
  rewrite Hpc.
  rewrite Mscale_assoc.
  rewrite <- Hsc'.
  (* Search ((_ * _) = (_ * _)). *)
  rewrite Cmult_comm.
  rewrite Hsc.
  rewrite Mscale_assoc.
  reflexivity.
Qed.

Lemma pmult_assoc : forall a b ab c abc : pauli,
  pmult a b ab ->
  pmult ab c abc ->
  exists bc, pmult b c bc /\ pmult a bc abc.
Proof.
  intros a b ab c abc HL HR.
  specialize (pauli_closure' b c) as Hbc.
  destruct Hbc as [bc Hbc].
  exists bc.
  split.
  - assumption.
  - apply PauliMultRel.
    inversion Hbc; subst.
    rewrite <- H; clear H Hbc.
    inversion HR; subst.
    rewrite <- H; clear H HR.
    inversion HL; subst.
    rewrite <- H; clear H HL.
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.

(* The pauli operator forms a group *)
Theorem PauliGroupProperties:
  (forall a, pmult ID a a) /\
  (forall a, exists a', pmult a a' ID) /\
  (forall a b, exists c, pmult a b c) /\ 
  (forall a b ab c abc,
    pmult a b ab ->
    pmult ab c abc ->
    exists bc, pmult b c bc /\ pmult a bc abc
  ).
Proof.
  split. apply pauli_identity_correct_left.
  split. apply pauli_inverse_correct.
  split. apply pauli_closure'.
  apply pmult_assoc.
Qed.

(* Definition inverse_scala (op: scalar): scalar := 
  match op with
  | One => One
  | Iphase => NegIphase
  | NegOne => NegOne
  | NegIphase => Iphase 
  end.

Definition pauli_inverse (p : pauli) : pauli :=
  match p with
  | PauliElem s op => PauliElem (inverse_scala s) (inverse_op op)
  end. *)

(* 
  =======================================================
  Define pmult as a function
  
  We found reasoing pmult as a relation is tiresome.
  So it is better that we define it as a function.
  Fortunately, as we have proved many facts about pmult,
  it will be much easier now.
  =======================================================
*)

Definition op_prod(a b: pauli_op): (scalar * pauli_op) := 
    match a, b with
    | I, p => (One, p)
    | p, I => (One, p)  
    
    | X, X => (One, I)
    | Y, Y => (One, I) 
    | Z, Z => (One, I)

    | X, Y => (Iphase, Z) 
    | Y, X => (NegIphase, Z)

    | Y, Z => (Iphase, X)
    | Z, Y => (NegIphase, X)

    | Z, X => (Iphase, Y)
    | X, Z => (NegIphase, Y) 
  end.

Definition scalar_prod(a b: scalar): scalar := 
  match a, b with
    | One, s => s
    | s, One => s
    | NegOne, Iphase => NegIphase
    | Iphase, NegOne => NegIphase
    | NegOne, NegOne => One
    | NegOne, NegIphase => Iphase
    | NegIphase, NegOne => Iphase
    | Iphase, NegIphase => One
    | NegIphase, Iphase => One
    | Iphase, Iphase => NegOne
    | NegIphase, NegIphase => NegOne
  end.

Definition combined_scalars (s1 s2 s3: scalar) : scalar := 
  scalar_prod s1 (scalar_prod s2 s3).

Definition pmult_prod (a b: pauli): pauli := 
  match a, b with
  | PauliElem sa pa, PauliElem sb pb => 
      let (sab, pab) := (op_prod pa pb) in
      let combined_scalar := combined_scalars sab sa sb in
      PauliElem combined_scalar pab
  end.

(* verify our function version of pmult is correct *)
Lemma pmult_prod_correct_r: forall (a b c: pauli),
  (pmult_prod a b) = c -> pmult a b c. 
Proof.
  intros.
  subst.
  destruct a, b.
  destruct s, p, s0, p0.
  all:  simpl; apply PauliMultRel; simpl; Qsimpl.
  (* this is not necessary but slightly improve performance *)
  all: try (rewrite Mscale_mult_dist_r). 
  all: try(Qsimpl; try(reflexivity)).
  all: try(rewrite Mmult_1_l).
  (* tried of finding patterns. *)
  all: try(solve_matrix).
Qed.

Lemma pmult_prod_correct_l: forall (a b c: pauli),
  pmult a b c -> (pmult_prod a b) = c. 
Proof.
  intros.
  destruct a, b.
  destruct s, p, s0, p0.
  all: simpl.
  - inversion H; subst.
    simpl in H0.
    destruct c.
    destruct s, p.
    + reflexivity.
    + simpl in H0.
    (* Apperantly, H0 is a contradiction in mathematical sense, 
    but i don't know how to prove it *)
    (* TODO: work on this later *)
Admitted.

(* A more focused example to show the problem *)
Example contra_matrix_eq:
  not (C1 .* Matrix.I 2 × (C1 .* Matrix.I 2) = C1 .* σx).
Proof.
  unfold not.
  intros.
  (* this can be used to simplyfy hypothesis*)
  autorewrite with M_db_light M_db Q_db in H.
  (* now we have H: Matrix.I 2 = σx *)
  unfold σx, Matrix.I in H.
  (* we have unfolded them into their function forms*)
  (* It fails because functional_extensionality cannot apply to curreid funcs ? *)
  Fail apply functional_extensionality in H.
  Abort.

(* Successful attempt, but too complicated for a simple fact. 
   It requires mannuallu point out for what location, the two matrix are different
   this will not scale well to prove pmult_prod_correct_l *)
Example contra_matrix_eq':
  not (C1 .* Matrix.I 2 × (C1 .* Matrix.I 2) = C1 .* σx).
Proof.
  unfold not.
  intros.
  (* this can be used to simplyfy hypothesis*)
  autorewrite with M_db_light M_db Q_db in H.
  assert (Matrix.I 2 0%nat 0%nat = σx 0%nat 0%nat). {
    rewrite H.
    reflexivity.
  }
  unfold Matrix.I in H0.
  simpl in H0.
  inversion H0; subst.
  lra.
Qed.

Theorem pmul_prod_correct: forall (a b c: pauli),
  pmult a b c <-> (pmult_prod a b) = c. 
Proof.
  split.
  apply pmult_prod_correct_l.
  apply pmult_prod_correct_r.
Qed.


