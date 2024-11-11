Require Import Pauli.
(* This line helps to write X instead of Pauli.X *)
Import Pauli.

(*
================================
the PauliTerm string
================================
*)

(* 
Use the Coq's list libs or QuantumLib.Vector
- The type carries the length of the list.
- For Coq's list, it needs to assume the same lengths.

Notation pstring n := list PauliOp

https://coq.inria.fr/doc/master/stdlib/Stdlib.Vectors.Vector.html

Keep multiple verisons of things and compare which one is most appropriate

Keep doc of everything, particularly of the desgin, how proofs differ from manual proofs 

(* Notation pstring n := Vector n *)
*)
Inductive pstring : Type := 
| pnil:  pstring
| pcons: PauliOp -> pstring -> pstring.

Definition p_string_example := (pcons X pnil).

Notation "x :: xs" := (pcons x xs) (at level 60, right associativity).
Notation "[]" := pnil.

Fixpoint p_length (ps : pstring) : nat :=
match ps with
| pnil => 0
| _::tail => 1 + p_length tail
end.

Example length_correct_exp0:
p_length (Pauli.X :: Y :: Z :: []) = 3%nat.
Proof. reflexivity. Qed.

Fixpoint p_app (ps1 ps2 : pstring) : pstring :=
match ps1 with
| pnil => ps2
| head::tail => head::(p_app tail ps2)
end.

Lemma length_app_correct: 
forall (s1 s2: pstring),
  plus (p_length s1) (p_length s2) = p_length (p_app s1 s2).
Proof.
intros.
induction s1.
- simpl. reflexivity.
- simpl. apply eq_S. assumption.
Qed.

Example p_app_exp: p_app (X::Y::[]) (Z::I::[]) = X::Y::Z::I::[].
Proof. reflexivity. Qed.

(*
================================
The n-qubit PauliTerm group
================================
*)

Inductive pauli_n: Type :=
  | PauliElemN : Scalar-> pstring -> pauli_n.

Notation "s · p" := (PauliElemN s p) (at level 40, left associativity).

(* Need to revise this to force the two pstring have the same length
  refer to `Mmult`
*)
Fixpoint pstring_prod (p1 p2 : pstring) : Scalar * pstring :=
  match p1, p2 with
  | pnil, p => (One, p)
  | p, pnil => (One, p)
  | op1::ps1, op2:: ps2 =>
      let (s_op, res_op) := op_prod op1 op2 in
      let (s_ps, res_ps) := pstring_prod ps1 ps2 in
      (s_prod s_op s_ps, res_op :: res_ps)
  end.

    
Definition pauli_n_prod (p1 p2 : pauli_n) : pauli_n :=
  match p1, p2 with
  | PauliElemN s1 ps1, PauliElemN s2 ps2 =>
      let (s_ps, res_ps) := pstring_prod ps1 ps2 in
      PauliElemN (combined_scalars s1 s2 s_ps) res_ps
  end.

Infix "◦" := pauli_n_prod (at level 40, left associativity).

Example pauli_n_mult_exp:
  (One · (Z::X::X::I::[])) ◦ (One · (X::X::Y::Y::[])) = 
    (NegOne · (Y::I::Z::Y::[])).
Proof. reflexivity. Qed.

Lemma pauli_n_prod_deterministic:
  forall (a b c d: pauli_n),
  a ◦ b = c ->
  a ◦ b = d ->
  c = d.
Proof.
  intros.
  induction H.
  assumption.
Qed.

Lemma pauli_n_prod_total:
  forall (a b: pauli_n), exists (c: pauli_n),
  a ◦ b = c.
Proof.
  intros a b.
  exists (a ◦ b).
  reflexivity.
Qed.

Fixpoint pstring_to_matrix(p: pstring): Square (2^(p_length p)) :=
  match p with
  | pnil => Matrix.I 1
  | head::tail => (pauli_to_matrix (ScaledOp One head)) ⊗ pstring_to_matrix(tail)
  end.


Example pstring_to_matrix_exp0:
  pstring_to_matrix (Y::I::Z::Y::[]) = σy ⊗ Matrix.I 2 ⊗ σz ⊗ σy.
Proof.
  simpl.
  repeat (rewrite Mscale_1_l).
  rewrite kron_1_r.
  repeat (restore_dims;
  rewrite kron_assoc by auto with wf_db).
  easy.
Qed.

Definition dimOf(p: pauli_n): nat :=
  match p with
  | PauliElemN _ p => (p_length p)
  end.

Definition paulin_to_matrix(p: pauli_n): Square (2^(dimOf p)) :=
  match p with
  | PauliElemN s p => (scalar_to_complex s) .* (pstring_to_matrix p)
  end.

Lemma nil_pstring_semantics:
  forall pstr, p_length pstr = 0%nat  -> pstring_to_matrix pstr = Matrix.I 1.
Proof.
  intros.
  destruct pstr.
  - reflexivity.
  - inversion H.
Qed.  


Example pauli_n_prod_correct_exp:
  let s1 := (One · (Z::X::X::I::[])) in
  let s2 := (One · (X::X::Y::Y::[])) in
  paulin_to_matrix (s1 ◦ s2) = paulin_to_matrix s1 × paulin_to_matrix s2.
Proof.
  intros.
  simpl.
  Msimpl.
  solve_matrix.
Qed.

Lemma dim_0_semantics:
  forall s p,
    dimOf (s · p) = 0%nat ->
    paulin_to_matrix (s · p) = (scalar_to_complex s) .* Matrix.I 1.
Admitted. 


  (* Use explicit Mmult because Coq cannot figure out the correct dimension *)
Theorem pauli_n_prod_correct: forall (p1 p2: pauli_n) dim,
  dimOf p1 = dimOf p2 ->
  dimOf p1 = dim ->
  (@Mmult (2^dim) (2^dim) (2^dim)) (paulin_to_matrix p1) (paulin_to_matrix p2) = paulin_to_matrix (p1 ◦ p2).
Proof.
  intros p1.
  destruct p1 as [s pstr].
  induction pstr.
  - intros.
    simpl in H, H0.
    symmetry in H.
    destruct p2.
    inversion H.
    (* This line rewrites the phantom dimension paramter
        which does not appears in the goal.
       This is by the design of SQIR.  *)
    rewrite H2; rewrite <- H0.
    apply dim_0_semantics in H.
    assert (paulin_to_matrix (s · []) = (scalar_to_complex s) .* Matrix.I 1). 
    { apply dim_0_semantics; simpl; easy. }
    rewrite H.
    rewrite H1.
    simpl.
    unfold combined_scalars.
    (* any autorewrite db ?? *)
    rewrite s_prod_identity.
    rewrite s_prod_correct.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    rewrite Cmult_comm.
    replace (Matrix.I 1 × Matrix.I 1) with (Matrix.I 1) by solve_matrix.
    apply nil_pstring_semantics in H2.
    rewrite H2.
    easy.
  - intros.
    destruct p2 as [s0 p2].
    destruct p2.
    + Abort. (* similar to the basic branch *) 
   



  (* - intros.
    subst.
    simpl in H.
    destruct p2.
    unfold dimOf in H; simpl in H.
    symmetry in H.
    apply nil_pstring_semantics in H.
    simpl. 
    rewrite H; clear H.
    simpl in H0; subst.
    unfold combined_scalars.
    rewrite s_prod_identity.
    rewrite s_prod_correct.
    Fail rewrite Mscale_mult_dist_r.
Abort. *)

