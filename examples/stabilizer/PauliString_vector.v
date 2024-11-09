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

Search (Vector.t _ 0).

Lemma length_0_vector:
  forall A (p: Vector.t A 0), p = [].
Proof.
  intros.
  dependent destruction p. (* regular destruct cannot handle this*)
  reflexivity.
Qed.

Lemma length_0_pvector:
  forall (p: PauliVector 0), p = [].
Proof. apply length_0_vector. Qed.

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

(* Ltac contradict_c_eq H :=
field_simplify_eq in H;
inversion H as [HC];
contradict HC;
lra. *)

Lemma scalar_to_complex_deterministic: forall (a b: scalar),
  scalar_to_complex a = scalar_to_complex b ->
  a = b.
Proof.
  intros a b H.
  destruct a, b.
  all: try reflexivity.
  all: try (
    simpl in H;
    inversion H as [HC];
    contradict HC;
    lra
  ).
Qed.


(* Move these four to Pauli.v *)
Lemma s_prod_correct_eq: forall (a b c: scalar),
  s_prod a b = c <->
  (scalar_to_complex a ) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
  intros a b c.
  split; intros H.
  - subst. rewrite s_prod_correct; reflexivity.
  - rewrite <- s_prod_correct in H. 
    apply scalar_to_complex_deterministic in H.
    assumption.
Qed.

Lemma s_prod_comm: forall (a b c: scalar),
  s_prod a b = c <->
  s_prod b a = c.
Proof.
  intros a b c.
  split; intros H.
  - destruct a, b, c.
    all: try easy.
  - destruct a, b, c.
    all: try easy.
Qed.

Lemma pvec_head:
  forall (n: nat) (va vb: PauliVector (S n)) s v hab sab,
  (s, v) = pvec_prod va vb ->
  (sab, hab) = op_prod (Vector.hd va) (Vector.hd vb) ->
  Vector.hd v = hab.
Proof.
  intros.
  assert (va = Vector.hd va :: Vector.tl va) by apply eta.
  rewrite H1 in H.
  assert (vb = Vector.hd vb :: Vector.tl vb) by apply eta.
  rewrite H2 in H.
  simpl in H.
  rewrite <- H0 in H.
  remember (pvec_prod (tl va) (tl vb)) as vrest.
  destruct vrest.
  inversion H; subst.
  easy.
Qed.


Lemma pvec_tail:
  forall (n: nat) (va vb: PauliVector (S n)) s v vtl stl,
  (s, v) = pvec_prod va vb ->
  (stl, vtl) = pvec_prod (Vector.tl va) (Vector.tl vb) ->
  Vector.tl v = vtl.
Proof.
  intros.
  assert (va = Vector.hd va :: Vector.tl va) by apply eta.
  rewrite H1 in H.
  assert (vb = Vector.hd vb :: Vector.tl vb) by apply eta.
  rewrite H2 in H.
  simpl in H.
  rewrite <- H0 in H.
  remember (op_prod (hd va) (hd vb)) as vhd.
  destruct vhd.
  inversion H; subst.
  easy.
Qed.

Lemma pvec_to_matrix_one_step:
  forall (n: nat) (pvector: PauliVector (S n)) h t,
  Vector.hd pvector = h ->
  Vector.tl pvector = t ->
  pvec_to_matrix pvector = op_to_matrix h ⊗ pvec_to_matrix t.
Proof.
  intros.
  replace pvector with (h::t).
  2: { symmetry. subst. apply VectorSpec.eta. }
  simpl.
  rewrite Mscale_1_l.
  reflexivity.
Qed.


Lemma pvec_prod_scalar_comb:
  forall (n:nat) (va vb: PauliVector (S n)) sab vab ha hb sh hab stl tlab,
  (sab, vab) = pvec_prod va vb ->
  Vector.hd va = ha ->
  Vector.hd vb = hb ->
  (sh, hab) = op_prod ha hb ->
  (stl, tlab) = pvec_prod (Vector.tl va) (Vector.tl vb) ->
  sab = s_prod sh stl.
Proof.
  intros.
  replace va with (ha::(tl va)) in H. 
  2: {
    subst.
    symmetry.
    apply VectorSpec.eta.
  }
  replace vb with (hb::(tl vb)) in H.
  2: {
    subst.
    symmetry.
    apply VectorSpec.eta.
  }
  simpl in H.
  rewrite <- H3 in H.
  rewrite <- H2 in H.
  inversion H; subst.
  apply s_prod_comm.
  reflexivity.
Qed.

Lemma op_prod_clousre_pauli: 
  forall (oa ob: pauli_op),
  exists (p: pauli),
  (op_to_matrix oa) × (op_to_matrix ob) = pauli_to_matrix p.
Proof.
  intros.
  specialize (op_closure oa ob) as Heop.
  destruct Heop as [c [s Hep]].
  exists (PauliElem s c).
  simpl.
  rewrite <- Hep.
  reflexivity.
Qed.

(* assert (H3: exists sx opx, pauli_to_matrix x = (scalar_to_complex sx) .* (op_to_matrix opx)). *)
Lemma pauli_construct:
  forall (p: pauli),
  exists s op,
  pauli_to_matrix p = (scalar_to_complex s) .* (op_to_matrix op).
Proof.
  intros.
  destruct p as [sp opp].
  exists sp, opp.
  reflexivity.
Qed.

Lemma pvec_prod_correct_ind_correct:
  forall (n: nat) (ls1 ls2: PauliVector (S n))
  tl1 h1 tl2 h2 sprod vprod stl vtl,
  (h1::tl1) = ls1 ->
  (h2::tl2) = ls2 ->
  (sprod, vprod) = pvec_prod ls1 ls2 ->
  (stl, vtl) = pvec_prod tl1 tl2 ->
  pvec_to_matrix tl1 × pvec_to_matrix tl2 =
     scalar_to_complex stl .* pvec_to_matrix vtl ->
  pvec_to_matrix ls1 × pvec_to_matrix ls2 = scalar_to_complex sprod .* pvec_to_matrix vprod.
Proof.
  intros.
  remember (pvec_prod tl1 tl2) as ptl.
  destruct ptl.
  remember (op_prod h1 h2) as phd.
  destruct phd as [shd ohd].
  rewrite <- H, <- H0.
  simpl; Qsimpl.
  rewrite H3.
  clear H3.
  rewrite Mscale_kron_dist_r.
  specialize (op_prod_clousre_pauli h1 h2) as H3.
  destruct H3 as [hp H3].
  rewrite H3.
  destruct hp as [sh oh]; simpl.
  rewrite Mscale_kron_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Mscale_kron_dist_l.
  subst.
  destruct H2. 
  assert (H4: scalar_to_complex stl * scalar_to_complex sh = scalar_to_complex sprod).
  {
    apply s_prod_correct_eq.
    rewrite s_prod_comm.
    symmetry.
    eapply pvec_prod_scalar_comb.
    - apply H1.
    - easy.
    - easy.
    - simpl.
      symmetry; eapply op_prod_correct_eq_var.
      apply H3.
    - simpl. apply Heqptl. 
  }
  rewrite H4. 
  rewrite Mscale_kron_dist_l.
  assert (H5: op_to_matrix oh ⊗ pvec_to_matrix vtl = pvec_to_matrix vprod).
  {
    symmetry.
    apply pvec_to_matrix_one_step.
    - eapply pvec_head.
      apply H1.
      simpl.
      apply op_prod_correct_eq_var in H3.
      rewrite H3 in Heqphd.
      inversion Heqphd; subst.
      symmetry.
      apply H3.
    - eapply pvec_tail.
      apply H1.
      simpl.
      apply Heqptl.
  }
  rewrite H5.
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
    assert (H0: p2 = Vector.hd p2 :: Vector.tl p2) by apply eta.
    rewrite H0.
    remember (pvec_prod p1 (Vector.tl p2)) as rest.
    destruct rest as [stl vectl].
    specialize (IHp1 (Vector.tl p2) stl vectl Heqrest) as H1. 
    clear IHp1.
    eapply pvec_prod_correct_ind_correct.
    + remember (h::p1) as p1f. 
      symmetry.
      apply Heqp1f.
    + rewrite <- H0. reflexivity.
    + rewrite <- H0. assumption.
    + apply Heqrest.
    + assumption.
Qed.  

(* multiplication on pauli string respects with matrix multiplication *)
Theorem p_prod_correct:
  forall (n: nat) (p1 p2: PString n), 
  (pstr_to_matrix p1) × (pstr_to_matrix p2) = pstr_to_matrix (p_prod p1 p2).
Proof.
  intros.
  destruct p1 as [sp1 ls1].
  destruct p2 as [sp2 ls2].
  unfold pstr_to_matrix.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  remember (p_prod (sp1, ls1) (sp2, ls2)) as ps.
  destruct ps.
  unfold p_prod in Heqps.
  remember (pvec_prod ls1 ls2) as pv.
  destruct pv as (sp, vp). 
  inversion Heqps; subst.
  (* !Important *)
  apply pvec_prod_correct in Heqpv.
  rewrite Heqpv.
  rewrite Mscale_assoc.
  rewrite combinded_scalars_correct.
  rewrite Cmult_comm.
  rewrite Cmult_assoc.
  reflexivity.
Qed.