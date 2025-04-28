Require Import PauliGroup.
Require Import QuantumLib.Quantum.
From mathcomp Require Import all_ssreflect fingroup.

Section Operations.
Import PNGGroup.
Import PNGroup.
Import P1GGroup.
Import P1Group.

Definition compose_pstring {n m: nat} 
  (ps1 : PauliTuple n) (ps2 : PauliTuple m) : PauliTuple (n + m) :=
  let s := mulg ps1.1 ps2.1 in
  let v := [tuple of ps1.2 ++ ps2.2] in
  (s, v).

Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.
  

Goal compose_pstring ([p1 X, Y]) ([p1 Z, I]) = ([p1 X, Y, Z, I]).
Proof.
  rewrite /compose_pstring /mulg /=.
  apply injective_projections.
  - by rewrite /=.
  - apply /eqP. by [].
Qed.

Lemma pn_int_comp_concat :
  forall {n m: nat} (ps1: PauliTupleBase n) (ps2: PauliTupleBase m),
  pn_int ([tuple of ps1 ++ ps2]) =
  pn_int ps1 ⊗ pn_int ps2.
Proof.
  move => n m ps1 ps2.
  induction n.
  - rewrite (tuple0 ps1) /=.
    Qsimpl.
    rewrite tupleE.
    by rewrite catNil.
    Fail by apply pn_int_wf.
    admit. (* Dependency Issues, fix later *) 
  - induction m.
    + case: ps1 / tupleP => hx tx.
      Qsimpl.
      rewrite (tuple0 ps2) /=.
      assert (tx ++ [::] = tx). admit.
      (* Some dependent type eroor *)
      Fail rewrite cats0.
Admitted. (* Coq dependent type error*)


Theorem compose_pstring_correct:
  forall {n m: nat}  (ps1: PauliTuple n) (ps2: PauliTuple m),
  png_int (compose_pstring ps1 ps2) =
  png_int ps1 ⊗ png_int ps2.
Proof.
  move => n m [p1 t1] [p2 t2].
  rewrite /compose_pstring /png_int /=.
  rewrite Mscale_kron_dist_l Mscale_kron_dist_r.
  rewrite pn_int_comp_concat.
  by rewrite Mscale_assoc phase_int_comp.
Qed.

Definition pstr_negate_phase (n: nat) := (NOne, id_pn n).
Notation "-1.⊗ n" := (pstr_negate_phase n) (at level 40).

End Operations.