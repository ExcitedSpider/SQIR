Require Import Pauli.
(* This line helps to write X instead of Pauli.X *)
Import Pauli.

(*
================================
First we define the pauli string
================================
*)

Inductive pstring : Type := 
| pnil:  pstring
| pcons: pauli_op -> pstring -> pstring.

Definition p_string_example := (pcons X pnil).

Notation "x :: xs" := (pcons x xs) (at level 60, right associativity).
Notation "[]" := pnil.

Fixpoint p_length (ps : pstring) : nat :=
match ps with
| pnil => 0
| pcons _ tail => 1 + p_length tail
end.

Example length_correct_exp0:
p_length (Pauli.X :: Y :: Z :: []) = 3%nat.
Proof. reflexivity. Qed.

Fixpoint p_app (ps1 ps2 : pstring) : pstring :=
match ps1 with
| pnil => ps2
| pcons head tail => pcons head (p_app tail ps2)
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
The n-qubit pauli group
================================
*)

Inductive pauli_n: Type :=
  | PauliElemN : scalar-> pstring -> pauli_n.

Notation "s · p" := (PauliElemN s p) (at level 40, left associativity).

Fixpoint pstring_prod (p1 p2 : pstring) : scalar * pstring :=
  match p1, p2 with
  | pnil, p => (One, p)
  | p, pnil => (One, p)
  | op1::ps1, op2:: ps2 =>
      let (s_op, res_op) := op_prod op1 op2 in
      let (s_ps, res_ps) := pstring_prod ps1 ps2 in
      (s_prod s_op s_ps, pcons res_op res_ps)
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


