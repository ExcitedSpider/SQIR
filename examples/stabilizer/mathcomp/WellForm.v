Require Import PauliGroup.
Require Import Action.
From mathcomp Require Import tuple ssreflect.

Require Import SQIR.UnitaryOps.

Section WellFormness. 
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.


Lemma p1_int_wf:
  forall p: PauliBase,
  WF_Matrix (p1_int p).
Proof.
  case;
  rewrite /=;
  by auto with wf_db.
Qed.

Lemma p1g_int_wf:
  forall p: PauliOp,
  WF_Matrix (p1g_int p).
Proof.
  move => p.
  case p => ph op.
  rewrite /p1g_int.
  apply WF_scale.
  apply p1_int_wf.
Qed.

Theorem pn_int_wf n:
  forall (op: PauliTupleBase n),
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
    by apply p1_int_wf.
Qed.

Theorem png_int_wf n:
  forall (op: PauliTuple n),
  WF_Matrix (png_int op).
Proof.
  move => [p t].
  rewrite /png_int.
  apply: WF_scale. 
  by apply: pn_int_wf.
Qed.

Lemma apply_1_wf:
  forall (op: PauliOp) (v: Vector 2),
  WF_Matrix v -> WF_Matrix (apply_1 v op).
Proof.
  move => op v.
  rewrite /apply_1.
  apply WF_mult.
  apply p1g_int_wf.
Qed.

Lemma apply_n_wf n:
  forall (op: PauliTuple n) (v: Vector (2^n)),
  WF_Matrix v -> WF_Matrix (applyP v op).
Proof.
  move => op v.
  rewrite /applyP.
  apply WF_mult.
  apply png_int_wf.
Qed.

End WellFormness.