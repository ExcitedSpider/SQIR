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

(* The Pauli String *)
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

(* Translate a pauli vector into a matrix *)
Fixpoint pvec_to_matrix {n:nat} (p: PauliVector n) : Square (2^n) :=
match p with
| [] => Matrix.I 1
| x::xs => (pauli_to_matrix (PauliElem One x)) ⊗ (pvec_to_matrix xs)
end.

Example pvec_interpret:
pvec_to_matrix (X::X::Y::Y::[]) = σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite <- kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Definition pstr_to_matrix {n: nat} (pstr: PString n): Square (2^n) :=
let (s, pvec) := pstr in
(scalar_to_complex s) .* (pvec_to_matrix pvec).

Example pstr_interpret:
pstr_to_matrix (NegOne, (X::X::Y::Y::[])) = -1 .* σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite  kron_assoc by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.

Search (Vector.t 0).

Lemma length_0_pvector:
  forall (p: PauliVector 0), p = [].
Proof. Admitted.

Lemma p_prod_one_step:
  forall n (p1 p2: PauliVector (S n)) h1 tl1 h2 tl2,
  p1 = h1::tl1 ->
  p2 = h2::tl2 ->
  (pvec_to_matrix p1) × (pvec_to_matrix p2) = 
    (pauli_to_matrix (PauliElem One h1) × pauli_to_matrix (PauliElem One h2))
    ⊗ ((pvec_to_matrix tl1) × (pvec_to_matrix tl2)).
Proof.
  intros.
  rewrite H, H0.
  simpl.
  Qsimpl.
  reflexivity.
Qed.

Lemma pvec_prod_correct:
  forall (n: nat) (p1 p2: PauliVector n) sc vecc, 
  (sc, vecc) = pvec_prod p1 p2 ->
  (pvec_to_matrix p1) × (pvec_to_matrix p2) = (scalar_to_complex sc) .* (pvec_to_matrix vecc).
Proof.
  intros n p1.
  induction p1.
  - intros.
    assert (p2 = []) by apply length_0_pvector.
    subst.
    simpl in H.
    inversion H; subst.
    simpl.
    solve_matrix.
  - intros. 
    assert (p2 = Vector.hd p2 :: Vector.tl p2) by apply eta.
    rewrite H0.
    remember (pvec_prod p1 (Vector.tl p2)) as rest.
    destruct rest as [stl vectl]. 
    assert (
      pvec_to_matrix p1 × pvec_to_matrix (Vector.tl p2) = scalar_to_complex stl .* pvec_to_matrix vectl
    ). { apply IHp1. }
    clear IHp1.
    simpl.
    Qsimpl.
    rewrite H1.
    rewrite Mscale_kron_dist_r.
    assert (H2: exists p, op_to_matrix h × op_to_matrix (hd p2) = pauli_to_matrix p) by admit.
    destruct H2.
    rewrite H2.
    assert (H3: exists sx opx, pauli_to_matrix x = (scalar_to_complex sx) .* (op_to_matrix opx)) by admit.
    destruct H3. destruct H3.
    rewrite H3.
    repeat rewrite <- Mscale_kron_dist_l.
    Search (_ .* (_ .* _)).
    rewrite Mscale_assoc.
    assert (H4: scalar_to_complex stl * scalar_to_complex x0 = scalar_to_complex sc) by admit.
    rewrite H4. 
    rewrite Mscale_kron_dist_l.
    assert (H5: op_to_matrix x1 ⊗ pvec_to_matrix vectl = pvec_to_matrix vecc) by admit.
    rewrite H5.
    reflexivity.
    (* Need to fill in the blank *)
Abort.
    


Theorem p_prod_correct:
  forall (n: nat) (p1 p2: PString n), 
  (pstr_to_matrix p1) × (pstr_to_matrix p2) = pstr_to_matrix (p_prod p1 p2).
Proof.
  intros.
  destruct p1 as [s1 p1].
  destruct p2 as [s2 p2].
  induction p1.
  - simpl.
    assert (p2 = []) by apply length_0_pvector.
    subst.
    simpl.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_assoc.
    rewrite s_prod_correct.
    Qsimpl.
    reflexivity.
  - unfold PauliVector in p2. 
    assert (p2 = Vector.hd p2 :: Vector.tl p2) by apply eta.
    rewrite H.
    simpl.
    Abort.
    