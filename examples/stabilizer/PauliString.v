Require Import Pauli.
(* This line helps to write X instead of Pauli.X *)
Import Pauli.

(* The pauli string *)
Inductive p_string : Type := 
| pnil:  p_string
| pcons: pauli_op -> p_string -> p_string.

Definition p_string_example := (pcons X pnil).

Notation "x :: xs" := (pcons x xs) (at level 60, right associativity).
Notation "[]" := pnil.

Fixpoint p_length (ps : p_string) : nat :=
match ps with
| pnil => 0
| pcons _ tail => 1 + p_length tail
end.

Example length_correct_exp0:
p_length (Pauli.X :: Y :: Z :: []) = 3%nat.
Proof. reflexivity. Qed.

Fixpoint p_app (ps1 ps2 : p_string) : p_string :=
match ps1 with
| pnil => ps2
| pcons head tail => pcons head (p_app tail ps2)
end.

Lemma length_app_correct: 
forall (s1 s2: p_string),
  plus (p_length s1) (p_length s2) = p_length (p_app s1 s2).
Proof.
intros.
induction s1.
- simpl. reflexivity.
- simpl. apply eq_S. assumption.
Qed.
