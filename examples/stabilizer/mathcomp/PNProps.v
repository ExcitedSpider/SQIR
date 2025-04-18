(*
TODO: use PauliGroup.v to refactor PauliString
- [x] imports PauliTuple
- [x] make a convert function for PauliTuple <-> PauliString ?
- [ ] completly wipe out Coq.Vector stuff
*)

Require Import P1Props.
Import Pauli.
From mathcomp Require Import ssrfun fingroup eqtype tuple seq fintype.

Require Import PauliGroup.
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Check X: PauliOp.
Check Img: phase.
Check tuple_of.

Module PauliString.
Definition PauliVector n := Vector.t PauliOp n.
Definition PVector0 := Vector.nil PauliOp.
Check PVector0.

Fixpoint pvmul {n: nat} (a b : PauliVector n) : phase * PauliVector n :=
  (* Looks like dark magic *)
  match a in Vector.t _ n return Vector.t _ n -> phase * PauliVector n  with 
  | ha :: ta => fun b => 
    let hb := Vector.hd b in
    let tb := Vector.tl b in 
    let (stl, ptl) := pvmul ta tb in
    let (sh, ph) := op_prod ha hb in
    (s_prod stl sh, ph::ptl)
  | [] => fun _ => (One, [])
  end b.

Fixpoint pvmul_v {n: nat} (a b : PauliVector n) : PauliVector n :=
  match a in Vector.t _ n return Vector.t _ n -> PauliVector n  with 
  | ha :: ta => fun b => 
    let hb := Vector.hd b in
    let tb := Vector.tl b in 
    let ptl := pvmul_v ta tb in
    let ph := op_prod_op ha hb in
    ph::ptl
  | [] => fun _ => []
  end b.

Fixpoint pvmul_s {n: nat} (a b : PauliVector n) : phase  :=
    (* Looks like dark magic *)
    match a in Vector.t _ n return Vector.t _ n -> phase with 
    | ha :: ta => fun b => 
      let hb := Vector.hd b in
      let tb := Vector.tl b in 
      let stl := pvmul_s ta tb in
      let sh := op_prod_s ha hb in
      s_prod stl sh
    | [] => fun _ => One
    end b.

(* Easier to use in verification *)
Definition pvmul_alt  {n: nat} (a b : PauliVector n) : phase * PauliVector n 
  := (pvmul_s a b, pvmul_v a b).

Lemma pvmul_alt_correct: 
  forall n (pa pb: PauliVector n),
  pvmul_alt pa pb = pvmul pa pb.
Proof.
  intros.
  induction n.
  - dependent destruction pa.
    dependent destruction pb.
    unfold pvmul_alt.
    simpl.
    reflexivity.
  - dependent destruction pa.
    dependent destruction pb.
    specialize (IHn pa pb).
    simpl.
    unfold pvmul_alt in IHn.
    rewrite <- IHn.
    unfold pvmul_alt; simpl.
    simpl.
    f_equal.
Qed.

Example pstring_prod_exp: 
  pvmul (Z::X::X::I::[]) (X::X::Y::Y::[]) = (NOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

(* The Pauli String *)
Definition PString (n : nat) : Set := phase * PauliVector n.

(* [X;Y;Z] has been occupied by QuantumLib *)
(* We defined a new annotation here Use a prefix `p` to avoid mess up *)
(* TODO: Maybe I should use a scope for this *)

Notation "p[ x , y , .. , z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) (at level 60).

Notation "p[ x ]" := (x :: []) (at level 60).

Definition pstring_example0 : PString 3 :=
  (One, p[X, Y, Z]).

(* `::` is interpreted correctly *)
Definition pstring_example1 : PString 3 :=
  (One, X::Y::Z::[]).

Definition pstring_example2 : PString 0 :=
  (One, []).

Definition pstring_example3 : PString 1 :=
  (One, p[X]).

Definition psmul {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  let (sab, vab) := pvmul va vb in 
  ((combined_scalars sab sa sb), vab).

Definition apply_s {n: nat} (s: phase) (pstr: PString n): PString n :=
  let (s', pv) := pstr in
  (s_prod s s', pv).




(* Good !*)
Example pauli_calc0:
  psmul (One, (p[X,X,Y,Y])) (One, (p[Z,X,X,I]))
  = (NOne, (p[Y,I,Z,Y])).
Proof.
  simpl.
  reflexivity.
Qed.

Set Bullet Behavior "Strict Subproofs".
(* Simpler definition *)
Definition psmul_alt {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  ((combined_scalars (pvmul_s va vb)  sa sb), pvmul_v va vb).

Lemma psmul_alt_correct: 
  forall n (pa pb: PString n),
  psmul_alt pa pb = psmul pa pb.
Proof.
  intros n pa pb.
  induction n.
  - destruct pa as [s p], pb as [s0 p0].
    dependent destruction p.
    dependent destruction p0.
    unfold psmul_alt.
    simpl.
    reflexivity.
  - destruct pa as [s p], pb as [s0 p0].
    unfold psmul_alt.
    dependent destruction p.
    dependent destruction p0.
    specialize (IHn (s, p) (s0, p0)).
    simpl.
    specialize (pvmul_alt_correct _ p p0) as Hpvmul.
    unfold pvmul_alt in Hpvmul.
    rewrite <- Hpvmul.
    simpl.
    f_equal.
Qed.

(* Translate a GenPauliOp vector into a matrix *)
Fixpoint pvec_to_matrix {n:nat} (p: PauliVector n) : Square (2^n) :=
match p with
| [] => Matrix.I 1
| x::xs => (pauli_to_matrix (One, x)) ⊗ (pvec_to_matrix xs)
end.

Example pvec_interpret:
pvec_to_matrix (p[X,X,Y,Y]) = σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite <- kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Definition pstr_to_matrix {n: nat} (pstr: PString n): Square (2^n) :=
let (s, pvec) := pstr in
(scalar_to_complex s) .* (pvec_to_matrix pvec).

Lemma pstr_to_matrix_WF n: 
  forall (pstr: PString n),
  WF_Matrix (pstr_to_matrix pstr).
Proof.
  intros.
  destruct pstr as [s p].
  simpl.
  apply WF_scale.
  dependent induction p.
  {
    simpl.
    auto with wf_db. 
  }
  {
    simpl.
    (* Search (_ .* _ ⊗ _).  *)
    rewrite Mscale_kron_dist_l.
    apply WF_scale.
    (* Search (WF_Matrix (_ ⊗ _)). *)
    apply WF_kron; try easy.
    destruct h; simpl; auto with wf_db. 
  }
Qed.


Example pstr_interpret:
pstr_to_matrix (NOne, (X::X::Y::Y::[])) = -C1 .* σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite  kron_assoc by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.


Lemma length_0_vector:
  forall A (p: Vector.t A 0), p = [].
Proof.
  intros.
  dependent destruction p. (* regular destruct cannot handle this*)
  reflexivity.
Qed.

Lemma vector0:
  forall (p: PauliVector 0), p = [].
Proof. apply length_0_vector. Qed.

Lemma p_prod_one_step:
  forall n (p1 p2: PauliVector (S n)) h1 tl1 h2 tl2,
  p1 = h1::tl1 ->
  p2 = h2::tl2 ->
  (pvec_to_matrix p1) × (pvec_to_matrix p2) = 
    (pauli_to_matrix (p1g_of One h1) × pauli_to_matrix (p1g_of One h2))
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

Lemma scalar_to_complex_deterministic: forall (a b: phase),
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
Lemma s_prod_correct_eq: forall (a b c: phase),
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

Lemma s_prod_comm: forall (a b c: phase),
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
  (s, v) = pvmul va vb ->
  (sab, hab) = op_prod (Vector.hd va) (Vector.hd vb) ->
  Vector.hd v = hab.
Proof.
  intros.
  assert (va = Vector.hd va :: Vector.tl va) by apply eta.
  rewrite H1 in H.
  assert (vb = Vector.hd vb :: Vector.tl vb) by apply eta.
  rewrite H2 in H.
  simpl in H.
  unfold op_prod in H0.
  inversion H0.
  rewrite <- H4 in H.
  rewrite <- H5 in H.
  remember (pvmul (tl va) (tl vb)) as vrest.
  destruct vrest.
  inversion H; subst.
  easy.
Qed.


Lemma pvec_tail:
  forall (n: nat) (va vb: PauliVector (S n)) s v vtl stl,
  (s, v) = pvmul va vb ->
  (stl, vtl) = pvmul (Vector.tl va) (Vector.tl vb) ->
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
  (sab, vab) = pvmul va vb ->
  Vector.hd va = ha ->
  Vector.hd vb = hb ->
  (sh, hab) = op_prod ha hb ->
  (stl, tlab) = pvmul (Vector.tl va) (Vector.tl vb) ->
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
  inversion H2.
  rewrite <- H5 in H.
  rewrite <- H6 in H.
  inversion H; subst.
  apply s_prod_comm.
  reflexivity.
Qed.

Lemma op_prod_clousre_pauli: 
  forall (oa ob: PauliOp),
  exists (p: GenPauliOp),
  (op_to_matrix oa) × (op_to_matrix ob) = pauli_to_matrix p.
Proof.
  intros.
  specialize (op_closure oa ob) as Heop.
  destruct Heop as [c [s Hep]].
  exists (p1g_of s c).
  simpl.
  unfold scalar_to_complex, op_to_matrix in Hep.
  rewrite <- Hep.
  reflexivity.
Qed.

(* assert (H3: exists sx opx, pauli_to_matrix x = (scalar_to_complex sx) .* (op_to_matrix opx)). *)
Lemma pauli_construct:
  forall (p: GenPauliOp),
  exists s op,
  pauli_to_matrix p = (scalar_to_complex s) .* (op_to_matrix op).
Proof.
  intros.
  destruct p as [sp opp].
  exists sp, opp.
  reflexivity.
Qed.

Ltac unalias :=
  unfold op_to_matrix, pauli_to_matrix, scalar_to_complex in *.

Lemma pvec_prod_correct_ind_correct:
  forall (n: nat) (ls1 ls2: PauliVector (S n))
  tl1 h1 tl2 h2 sprod vprod stl vtl,
  (h1::tl1) = ls1 ->
  (h2::tl2) = ls2 ->
  (sprod, vprod) = pvmul ls1 ls2 ->
  (stl, vtl) = pvmul tl1 tl2 ->
  pvec_to_matrix tl1 × pvec_to_matrix tl2 =
     scalar_to_complex stl .* pvec_to_matrix vtl ->
  pvec_to_matrix ls1 × pvec_to_matrix ls2 = scalar_to_complex sprod .* pvec_to_matrix vprod.
Proof.
  intros.
  remember (pvmul tl1 tl2) as ptl.
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
  unalias.
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
  unalias.
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
  unalias.
  rewrite H5.
  reflexivity.
Qed.

Lemma pvmul_correct:
  forall (n: nat) (p1 p2: PauliVector n) sc vecc, 
  (sc, vecc) = pvmul p1 p2 ->
  (pvec_to_matrix p1) × (pvec_to_matrix p2) = (scalar_to_complex sc) .* (pvec_to_matrix vecc).
Proof.
  intros n p1.
  induction p1.
  - intros.
    assert (p2 = []) by apply vector0.
    subst.
    simpl in H.
    inversion H; subst.
    simpl.
    solve_matrix.
  - intros. 
    assert (H0: p2 = Vector.hd p2 :: Vector.tl p2) by apply eta.
    rewrite H0.
    remember (pvmul p1 (Vector.tl p2)) as rest.
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

(* multiplication on GenPauliOp string respects with matrix multiplication *)
Theorem psmul_correct:
  forall (n: nat) (p1 p2: PString n), 
  (pstr_to_matrix p1) × (pstr_to_matrix p2) = pstr_to_matrix (psmul p1 p2).
Proof.
  intros.
  destruct p1 as [sp1 ls1].
  destruct p2 as [sp2 ls2].
  unfold pstr_to_matrix.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  remember (psmul (sp1, ls1) (sp2, ls2)) as ps.
  destruct ps.
  unfold psmul in Heqps.
  remember (pvmul ls1 ls2) as pv.
  destruct pv as (sp, vp). 
  inversion Heqps; subst.
  (* !Important *)
  apply pvmul_correct in Heqpv.
  rewrite Heqpv.
  rewrite Mscale_assoc.
  rewrite combinded_scalars_correct.
  rewrite Cmult_comm.
  rewrite Cmult_assoc.
  reflexivity.
Qed.


End PauliString.

Module Adaptor.

Import PauliString.


From Coq Require Import ssreflect.

(* This one does work but the type is inconvinient*)
Definition TtoV_l {n:nat} (l: PauliTuple n): PauliVector (size l) :=
  of_list l.

(* I can prove n = (size l) in tupleToVector *)
Lemma tuple_size:
  forall (n:nat) (tuple: PauliTuple n),
  size tuple = n.
Proof.
  by move => *; rewrite size_tuple.
Qed.


Fixpoint tupleToVector {n}: (PauliTuple n) -> PauliVector n :=
  if n is S n return n.-tuple PauliOp -> PauliVector n 
  then fun xs => (thead xs)::(tupleToVector (behead_tuple xs))
  else fun xs => PVector0.

Fixpoint vectorToTuple {n} (v : PauliVector n) : PauliTuple n :=
  match v with
  | nil => List.nil
  | cons h _ t => List.cons h (vectorToTuple t)
  end.


Theorem vt_isomorphism n:
    cancel (@vectorToTuple n) (@tupleToVector n) /\
    cancel (@tupleToVector n) (@vectorToTuple n).
Proof.
  split.
  {
    move => v.
    induction n.
      by rewrite (vector0 v).
    rewrite (eta v) /=.
    rewrite beheadCons theadCons.
    by rewrite {1}(IHn (VectorDef.tl v)).
  }
  {
    move => t.
    induction n.
      by rewrite (tuple0 t).
    case: t / tupleP => ht tt.
    by rewrite /= theadCons beheadCons IHn.
  }
Qed.

Theorem tupleToVector_correct n:
  forall tup: PauliTuple n,
  pn_int tup = pvec_to_matrix (tupleToVector tup).
Proof.
  move => tup.
  induction n.
    by rewrite (tuple0 tup).
  case: tup / tupleP => h t.
  rewrite /= Mscale_1_l theadCons beheadCons.
  by rewrite IHn.
Qed.

Lemma vector_view n:
  forall (a b: PauliVector n),
  pvmul_v a b = tupleToVector (mult_pn (vectorToTuple a) (vectorToTuple b)).
Proof.
  Admitted.

Definition pngToPString {n} (png: GenPauliTuple n): PString n :=
  match png with
  |  (phase, tuple) => (phase, tupleToVector tuple)
  end.

Definition pstringToTupleG {n} (pstr: PString n): GenPauliTuple n :=
  match pstr with 
  | (phase, vector) => (phase, vectorToTuple vector)
  end.


Theorem ps_isomorphism n:
    cancel (@pstringToTupleG n) (@pngToPString n) /\
    cancel (@pngToPString n) (@pstringToTupleG n).
Proof.  
  have H0 := vt_isomorphism.
  destruct (H0 n) as [Hvt Htv].
  split. 
  {
    move => [phase vec] /=.
    f_equal.
    by rewrite Hvt.
  }
  {
    move => [phase tup] /=.
    f_equal.
    by rewrite Htv.
  }
Qed.

Theorem pngToPstring_correct n:
  forall tupg: GenPauliTuple n,
  png_int tupg = pstr_to_matrix (pngToPString tupg).
Proof.
  move => tupg.
  case tupg => pha p.
  rewrite /png_int /pstr_to_matrix /scalar_to_complex /=.
  by rewrite tupleToVector_correct.
Qed.

End Adaptor.

From mathcomp Require Import ssreflect.

Theorem pn_int_wf n:
  forall (op: PauliTuple n),
  WF_Matrix (pn_int op).
Proof.
  intros.
  induction n.
  - rewrite tuple0.
    unfold pn_int.
    simpl.
    auto with wf_db.
  - case: op / tupleP => x t.
    apply WF_kron; try easy.
    by apply p1_int_WF.
Qed.


Theorem png_int_wf n:
  forall (op: GenPauliTuple n),
  WF_Matrix (png_int op).
Proof.
  move => [p t].
  rewrite /png_int.
  apply: WF_scale. 
  by apply: pn_int_wf.
Qed.

Lemma id_pn_int:
  forall (n: nat), pn_int (id_pn n) = Matrix.I (2^n).
Proof.
  intros.
  induction n.
    by rewrite /pn_int.
  rewrite pn_idP.
  rewrite /= beheadCons IHn.
  restore_dims.
  rewrite id_kron.
  lma'.
Qed.


Lemma id_png_int:
  forall (n: nat), png_int (id_png n) = Matrix.I (2^n).
Proof.
  move => n.
  rewrite /id_png /png_int /=.
  by rewrite Mscale_1_l id_pn_int.
Qed.


