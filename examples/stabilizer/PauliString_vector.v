Require Import Pauli.
(* This line helps to write X instead of Pauli.X *)
Import Pauli.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

Definition v : Vector.t R 3 := 1::2::3::[].

Definition PauliVector n := Vector.t pauli_op n.

Definition a: PauliVector 3 := X :: Y :: Z :: [].
Definition empty: PauliVector 0 := [].

Fixpoint pvec_prod {n: nat} (a b : PauliVector n) : scalar * PauliVector n :=
  (* Looks like dark magic *)
  match a in Vector.t _ n return Vector.t _ n -> scalar * PauliVector n  with 
  | ha :: ta => fun b => 
    let hb := Vector.hd b in
    let tb := Vector.tl b in 
    let (stl, ptl) := pvec_prod ta tb in
    let (sh, ph) := op_prod ha hb in
    (s_prod stl sh, ph::ptl)
  | [] => fun _ => (One, [])
  end b.

Example pstring_prod_exp: 
  pvec_prod (Z::X::X::I::[]) (X::X::Y::Y::[]) = (NegOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

Definition PString (n : nat) : Set := scalar * PauliVector n.

Definition p_prod {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  let (sab, vab) := pvec_prod va vb in 
  ((combined_scalars sab sa sb), vab).

(* Good !*)
Example pauli_calc0:
  p_prod (One, (X::X::Y::Y::[])) (One, (Z::X::X::I::[]))
  = (NegOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

(* Translate a pauli string into a matrix *)
Definition to_matrix {n:nat} (p: PString n) : Square (2^n).
Admitted.

Theorem pstring_prod_is_correct: 
  forall (n:nat) (a b: PString n),
  to_matrix(p_prod a b) = (to_matrix a) × (to_matrix b).
Proof.
Abort.


  
