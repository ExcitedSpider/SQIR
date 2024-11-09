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

Module PaliGroupFail.




Inductive PauliGroup: nat -> Type :=
| PG: forall n, scalar -> PauliVector n -> PauliGroup n.

(* Don't understand how to correctly do this in Gallina *)
Fixpoint p_prod0 {n: nat} (a b : PauliGroup n) : PauliGroup n.
Proof.
  destruct a as [n sa veca].
  destruct b as [n sb vecb].
  apply PG.
  Check pvec_prod.
  remember (pvec_prod veca vecb) as p.
  destruct p as [sp].
  remember (combined_scalars sp sa sb).
  exact s.
  remember (pvec_prod veca vecb). 
  destruct p as [sp vecp].
  exact vecp.
Qed.


Fail Definition p_prod{n: nat} (a b : PauliGroup n) : PauliGroup n :=
  let (_, sa, va) := a in
  let (_, sb, vb) := b in
  PG n sa va. (* the dependent type infor in va is lost*)
  End PaliGroupFail.
  Module PauliGroupSigma.

Notation "x ~ y" := (x, y) (at level 40, left associativity) : pair_scope.
Open Scope pair_scope.

Definition PauliGroup (n: nat) := {s: scalar & PauliVector n}.
Definition p_prod {n: nat} (a b : PauliGroup n) : PauliGroup n :=
  match a, b with
  | existT _ sa va, existT _ sb vb =>
      let (sab, vab) := pvec_prod va vb in
      existT _ (combined_scalars sab sa sb) vab 
  end.

(* very ugly but ok *)
Example pauli_calc:
  p_prod (existT _  One (Z::X::X::I::[])) (existT _ One (X::X::Y::Y::[]))
  = (existT _ NegOne (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

  
End PauliGroupSigma.



Definition p_prod {n: nat} (a b: (scalar * PauliVector n)) : scalar * PauliVector n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  let (sab, vab) := pvec_prod va vb in 
  ((combined_scalars sab sa sb), vab).

Example pauli_calc:
  p_prod (One, (X::X::Y::Y::[])) (One, (Z::X::X::I::[]))
  = (NegOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.