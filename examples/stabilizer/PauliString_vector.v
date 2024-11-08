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

Lemma pauli_comb_unique:
  forall sa opa sb opb,
  scalar_to_complex sa .* op_to_matrix opa =
  scalar_to_complex sb .* op_to_matrix opb ->
  sa = sb /\ opa = opb.
Proof. Admitted.
Search scalar_to_complex.
(* Have some troubles proving function inequalities*)
(* But this is a known simple fact in math that all pauli operators are orthogonal*)
(* So we skip this proof *)

Lemma pauli_to_matrix_correct:
  forall p s op, 
  p = PauliElem s op <->
  pauli_to_matrix p = scalar_to_complex s .* op_to_matrix op.
Proof.
  intros.
  split; intros H.
  - subst. reflexivity.
  - destruct p as [sp opp]. 
    simpl in H.
    apply pauli_comb_unique in H.
    destruct H.
    subst.
    reflexivity.
Qed.

Lemma op_prod_correct_eq:
  forall oa ob sab oab p,
  op_to_matrix oa × op_to_matrix ob = pauli_to_matrix p ->
  p = PauliElem sab oab ->
  op_prod oa ob = (sab, oab).
Proof.
  intros.
  specialize (op_prod_correct oa ob) as Hexists.
  destruct Hexists as [s [op [Heq Hprod]]].
  subst.
  simpl in H.
  assert (sab = s /\ oab = op).
  { apply pauli_comb_unique.
    congruence. }
  destruct H0.
  congruence.
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
    ). { apply IHp1. assumption. }
    clear IHp1.
    simpl.
    Qsimpl.
    rewrite H1.
    rewrite Mscale_kron_dist_r.
    assert (H2: exists p, op_to_matrix h × op_to_matrix (hd p2) = pauli_to_matrix p). 
    {
      remember (op_closure h (hd p2)).
      destruct e as [c [s Hsc]].
      exists (PauliElem s c).
      simpl.
      assumption. 
    }
    destruct H2.
    rewrite H2.
    assert (H3: exists sx opx, pauli_to_matrix x = (scalar_to_complex sx) .* (op_to_matrix opx)).
    {
       destruct x.
       exists s, p.
       reflexivity.
    }
    destruct H3. destruct H3.
    rewrite H3.
    repeat rewrite <- Mscale_kron_dist_l.
    rewrite Mscale_assoc.
    assert (H4: scalar_to_complex stl * scalar_to_complex x0 = scalar_to_complex sc).
    {
      rename x0 into sx.
      apply s_prod_correct_eq.
      rewrite s_prod_comm.
      symmetry.
      eapply pvec_prod_scalar_comb.
      - apply H.
      - easy.
      - easy.
      - simpl.
        rewrite <- pauli_to_matrix_correct in H3.
        symmetry.
        eapply op_prod_correct_eq.
        + apply H2.
        + apply H3.
      - simpl.
        apply Heqrest. 
    }
    rewrite H4. 
    rewrite Mscale_kron_dist_l.
    assert (H5: op_to_matrix x1 ⊗ pvec_to_matrix vectl = pvec_to_matrix vecc).
    {
      symmetry.
      apply pvec_to_matrix_one_step.
      rename x1 into oph.
      rename x0 into sh.
      assert (op_prod h (hd p2) = (sh, oph)).
      - eapply op_prod_correct_eq.
        + apply H2.
        + rewrite pauli_to_matrix_correct. 
          assumption.
      - eapply pvec_head.
        + apply H.
        + simpl. symmetry. apply H5.
      - eapply pvec_tail.
        + apply H.
        + simpl. apply Heqrest.
    }
    rewrite H5.
    reflexivity.
Qed.

Theorem p_prod_correct:
  forall (n: nat) (p1 p2: PString n), 
  (pstr_to_matrix p1) × (pstr_to_matrix p2) = pstr_to_matrix (p_prod p1 p2).
Proof. Abort. (* TBD *)
    