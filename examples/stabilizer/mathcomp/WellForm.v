Require Import PauliGroup.
Require Import Action.
From mathcomp Require Import tuple ssreflect.

Require Import SQIR.UnitaryOps.

Section WellFormness. 
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.

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


Lemma apply_n_wf n:
  forall (op: GenPauliTuple n) (v: Vector (2^n)),
  WF_Matrix v -> WF_Matrix (apply_n _ v op).
Proof.
  move => op v.
  rewrite /apply_n.
  apply WF_mult.
  apply png_int_wf.
Qed.


End WellFormness.