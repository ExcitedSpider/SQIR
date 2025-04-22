Require Import Pauli.
(* This line helps to write X instead of Pauli.X *)
Import Pauli.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
From mathcomp Require Import ssrfun fingroup eqtype fintype.

Locate PauliOp.

Module PauliString.
Definition PauliVector n := Vector.t PauliOp n.

Fixpoint pvmul {n: nat} (a b : PauliVector n) : Scalar * PauliVector n :=
  (* Looks like dark magic *)
  match a in Vector.t _ n return Vector.t _ n -> Scalar * PauliVector n  with 
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

Fixpoint pvmul_s {n: nat} (a b : PauliVector n) : Scalar  :=
    (* Looks like dark magic *)
    match a in Vector.t _ n return Vector.t _ n -> Scalar with 
    | ha :: ta => fun b => 
      let hb := Vector.hd b in
      let tb := Vector.tl b in 
      let stl := pvmul_s ta tb in
      let sh := op_prod_s ha hb in
      s_prod stl sh
    | [] => fun _ => One
    end b.

(* Easier to use in verification *)
Definition pvmul_alt  {n: nat} (a b : PauliVector n) : Scalar * PauliVector n 
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
    rewrite <- op_prod_alt_correct.
    simpl.
    f_equal.
Qed.

Example pstring_prod_exp: 
  pvmul (Z::X::X::I::[]) (X::X::Y::Y::[]) = (NegOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

(* The Pauli String *)
Definition PString (n : nat) : Set := Scalar * PauliVector n.

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

Definition apply_s {n: nat} (s: Scalar) (pstr: PString n): PString n :=
  let (s', pv) := pstr in
  (s_prod s s', pv).




(* Good !*)
Example pauli_calc0:
  psmul (One, (p[X,X,Y,Y])) (One, (p[Z,X,X,I]))
  = (NegOne, (p[Y,I,Z,Y])).
Proof.
  simpl.
  reflexivity.
Qed.

(* Simpler definition *)
Definition psmul_alt {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  ((combined_scalars (pvmul_s va vb)  sa sb), pvmul_v va vb).

Lemma psmul_alt_correct: 
  forall n (pa pb: PString n),
  psmul_alt pa pb = psmul pa pb.
Proof.
  intros.
  induction n.
  - destruct pa, pb.
    dependent destruction p.
    dependent destruction p0.
    unfold psmul_alt.
    simpl.
    reflexivity.
  - destruct pa, pb.
    unfold psmul_alt.
    dependent destruction p.
    dependent destruction p0.
    specialize (IHn (s, p) (s0, p0)).
    simpl.
    specialize (pvmul_alt_correct _ p p0) as Hpvmul.
    unfold pvmul_alt in Hpvmul.
    rewrite <- Hpvmul.
    rewrite <- op_prod_alt_correct.
    simpl.
    f_equal.
Qed.

(* Translate a PauliTerm vector into a matrix *)
Fixpoint pvec_to_matrix {n:nat} (p: PauliVector n) : Square (2^n) :=
match p with
| [] => Matrix.I 1
| x::xs => (pauli_to_matrix (ScaledOp One x)) ⊗ (pvec_to_matrix xs)
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
  destruct pstr.
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
    (pauli_to_matrix (ScaledOp One h1) × pauli_to_matrix (ScaledOp One h2))
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

Lemma scalar_to_complex_deterministic: forall (a b: Scalar),
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
Lemma s_prod_correct_eq: forall (a b c: Scalar),
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

Lemma s_prod_comm: forall (a b c: Scalar),
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
  rewrite <- H0 in H.
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
  rewrite <- H2 in H.
  inversion H; subst.
  apply s_prod_comm.
  reflexivity.
Qed.

Lemma op_prod_clousre_pauli: 
  forall (oa ob: PauliOp),
  exists (p: PauliTerm),
  (op_to_matrix oa) × (op_to_matrix ob) = pauli_to_matrix p.
Proof.
  intros.
  specialize (op_closure oa ob) as Heop.
  destruct Heop as [c [s Hep]].
  exists (ScaledOp s c).
  simpl.
  rewrite <- Hep.
  reflexivity.
Qed.

(* assert (H3: exists sx opx, pauli_to_matrix x = (scalar_to_complex sx) .* (op_to_matrix opx)). *)
Lemma pauli_construct:
  forall (p: PauliTerm),
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

Lemma pvmul_correct:
  forall (n: nat) (p1 p2: PauliVector n) sc vecc, 
  (sc, vecc) = pvmul p1 p2 ->
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

(* multiplication on PauliTerm string respects with matrix multiplication *)
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




Lemma psmul_implies_Mmult:
  forall (n:nat) (a b c: PString n),
  psmul a b = c -> 
  (pstr_to_matrix a) × (pstr_to_matrix b) = pstr_to_matrix c.
Proof.
  intros.
  rewrite <- H. 
  rewrite psmul_correct. 
  reflexivity.
Qed. 


  
End PauliString.

Export PauliString.

(* Additional Group Theory Stuff *)

Section PnZ4Group.

(* The global phase factors (scalars) usually aren’t very important for practical applications. *)
(* And scalars make verificaiton process much complicated *)
(* So we choose to formalize the P_n / Z_4 group instead. *)
(*  the quotient group P_n / Z_4 is exactly the 
n-qubit Pauli group but with the phases ignored. *)

(* So we use @pvmul_v to define the P_n / Z_4 group*)

Print pvmul_v.

Variable (n:nat).

Lemma pvmul_v_assoc:
  associative (@pvmul_v n).
Proof.
  unfold associative.
  intros.
  induction n.
  - dependent destruction x.
    dependent destruction y.
    dependent destruction z.
    reflexivity.
  - dependent destruction x.
    dependent destruction y.
    dependent destruction z.
    simpl.
    rewrite IHn0.
    f_equal.
    apply op_prod_op_assoc.
Qed.

(* the unit element *)
Definition pmul_id (n:nat): PauliVector n :=
  Vector.const I n.

Definition e := pmul_id n.

Lemma pmul_v_left_id:
forall n', left_id (pmul_id n') (@pvmul_v n').
Proof.
  unfold left_id.
  intros.
  unfold e.
  induction n'.
  - dependent destruction x.
    reflexivity.
  - simpl.
    unfold PauliVector in x.
    rewrite IHn'.
    apply caseS with (v := x).
    intros.
    reflexivity.
Qed.

Definition pninv (p: PauliVector n): PauliVector n :=
  map inverse_op p.

Lemma pvmul_v_id_correct:
  left_inverse e pninv pvmul_v.
Proof.
  unfold left_inverse.
  intros.
  unfold e, pninv.
  induction n.
  - dependent destruction x.
    easy.
  - dependent destruction x.
    simpl.
    f_equal.
    apply inverse_op_correct.
    apply IHn0.
Qed.

Lemma pvmul_s_id_correct:
  left_inverse One pninv pvmul_s.
Proof.
  unfold left_inverse.
  intros.
  unfold pninv.
  induction n.
  - dependent destruction x.
    easy.
  - dependent destruction x.
    simpl.
    rewrite IHn0.
    destruct h; simpl; reflexivity.
Qed.

From HB Require Import structures.

(* 
HB: FinGroup is a factory for the following mixins:
	- isMulBaseGroup
  - choice.hasChoice
  - choice.Choice_isCountable
  - hasDecEq
  - isFinite
  - BaseFinGroup_isGroup
*)
HB.about FinGroup.
(*
HB: isMulBaseGroup operations and axioms are:
	- mulg_subdef
  - oneg_subdef
  - invg_subdef
  - mulgA_subproof
  - mul1g_subproof
  - invgK_subproof
  - invMg_subproof
*)
HB.about isMulBaseGroup.
Print mulg_subdef.
Locate mulg_subdef.
Locate isMulBaseGroup.
Locate "isMulBaseGroup".
(* 
Check PauliVector. *)

(* Coq cannot figure out dependent types  *)
(* I'm going to use Mathcomp tuples *)
(* Fail HB.instance Definition _ := Finite.on (PauliVector n).


Check pvmul_v.

Check pmul_v_left_id.

Check left_id. 

Lemma pvmul_left_id:
  left_id e pvmul_v.
Admitted. *)

(* Do not use isMulBaseGroup. this is provided by isMulGroup *)
(* Fail HB.instance Definition isMulBaseGroup.Type _ := 
isMulBaseGroup.Build 
  (PauliVector n)
  pvmul_v_assoc
  pvmul_left_id
  pninv_involutive
  pvmul_v 
  e 
  pvmul_v_assoc 
  pvmul_v_id_correct. *)

(* Definition sort := PauliVector n. *)


End PnZ4Group.

Definition pstr_identity (n: nat) := (One, Vector.const I n).
Notation "𝟙" := pstr_identity (at level 40).

Definition pstr_negate_phase (n: nat) := (NegOne, Vector.const I n).
Notation "~𝟙" := pstr_negate_phase (at level 40).

(* negation by .*-1 *)
Definition psneg {n: nat}(pstr: PString n): PString n :=
  psmul (~𝟙 n) pstr.

Lemma pstr_id_interprete n:
  pstr_to_matrix (𝟙 n) = Matrix.I (2^n).
Proof.
  induction n.
  - simpl. Qsimpl. reflexivity.  
  - assert (pstr_to_matrix (𝟙 (S n)) = Matrix.I 2 ⊗ pstr_to_matrix (𝟙 n)).
    {
      simpl.
      Qsimpl.
      reflexivity. 
    }
    rewrite H.
    rewrite IHn.
    rewrite id_kron. (* TODO: check how robert proves this *)
    restore_dims.
    reflexivity.
Qed.

(* id is the eigenvector of all states *)
Theorem pstr_identity_eigenvector n: 
  forall (ψ: Vector (2^n)),
  WF_Matrix ψ -> pstr_to_matrix (𝟙 n) × ψ = ψ.
Proof.
  intros.
  rewrite pstr_id_interprete.
  (* Search (Matrix.I _ × _). *)
  apply Mmult_1_l.
  easy.
Qed.

(* similar to pstr_id_interprete but idk how to simplify it  *)
Lemma pstr_negate_interprete n:
  pstr_to_matrix (~𝟙 n) = -1 .* Matrix.I (2^n).
Proof.
induction n.
- simpl. Qsimpl. reflexivity.  
- assert (pstr_to_matrix (~𝟙 (S n)) = Matrix.I 2 ⊗ pstr_to_matrix (~𝟙 n)).
  {
    simpl.
    Qsimpl.
    (* Search (_ ⊗ (_ .* _)). *)
    rewrite Mscale_kron_dist_r.
    reflexivity. 
  }
  rewrite H.
  rewrite IHn.
  rewrite Mscale_kron_dist_r.
  rewrite id_kron.
  restore_dims.
  reflexivity.
Qed.

Lemma psneg_correct :
forall {n: nat} (pstr: PString n),
  pstr_to_matrix (psneg pstr) = -1 .* pstr_to_matrix pstr.
Proof.
  intros.
  unfold psneg.
  rewrite <- psmul_correct.
  rewrite pstr_negate_interprete.
  rewrite Mscale_mult_dist_l.
  rewrite Mmult_1_l. easy.
  apply pstr_to_matrix_WF.
Qed.

Theorem pstr_negate_states n:
  forall (ψ: Vector (2^n)),
  WF_Matrix ψ -> pstr_to_matrix (~𝟙 n) × ψ = -1 .* ψ.
Proof.
  intros.
  rewrite pstr_negate_interprete.
  rewrite Mscale_mult_dist_l.
  rewrite Mmult_1_l; easy.
Qed.

(* Very loose definition of pauli string group *)
(* Refine later *)
Section PStrGroup.

Lemma pvmul_id_correct:
forall n (pvec: PauliVector  n), pvmul (pmul_id n) pvec = (One, pvec)
.
Proof.
  intros.
  rewrite <- pvmul_alt_correct.
  unfold pvmul_alt.
  f_equal.
  {
    induction n.
    + reflexivity.
    + simpl. rewrite IHn. reflexivity.
  }
  {
    apply pmul_v_left_id.
  }
Qed.

(* replace (pvec_to_matrix (const I n)) with (Matrix.I n). *)

Example pstr_id_to_matrix_exp: 
  pstr_to_matrix (pstr_identity 3) = Matrix.I (2 ^ 3).
Proof.
  simpl.
  Qsimpl.
  repeat rewrite id_kron.
  reflexivity.
Qed.

Lemma pstr_id_to_matrix:
  forall n, pstr_to_matrix (pstr_identity n) = Matrix.I (2^n).
Proof.
  intros.
  induction n.
  { simpl. Qsimpl. solve_matrix. }
  {
    simpl; Qsimpl.
    simpl in IHn.
    rewrite Mscale_1_l in IHn.
    rewrite IHn.
    rewrite id_kron.
    reflexivity.
  }
Qed.

Lemma pvec_id_to_matrix:
  forall n, Matrix.I (2 ^ n) = pvec_to_matrix (pmul_id n).
Proof.
  intros.
  specialize (pstr_id_to_matrix n) as H.
  simpl in H.
  rewrite <- H.
  Qsimpl.
  reflexivity.
Qed.

Lemma psmul_id_left:
  forall n, left_id (pstr_identity n) (@psmul n).
Proof.
  unfold left_id, pstr_identity; intros n [sx vx].
  simpl.
  replace (const I n) with (pmul_id n) by reflexivity.
  assert (Hid: forall n (pvec: PauliVector  n), pvmul (pmul_id n) pvec = (One, pvec)) by apply pvmul_id_correct.
  rewrite Hid.
  simpl.
  reflexivity.
Qed.

Locate pstr.

Definition pstr_inv {n: nat} (pstr: PString n)
: (PString n) :=
  let (sp, vp) := pstr in
  ((inverse_scalar sp), (pninv n vp)).

Lemma pstr_inv_correct:
  forall n (pstr: PString n),
  psmul (pstr_inv pstr) pstr = (pstr_identity n)
.
  intros n [sp vp].
  simpl.
  rewrite <- pvmul_alt_correct; unfold pvmul_alt.
  rewrite pvmul_v_id_correct.
  unfold pstr_identity; f_equal.
  rewrite pvmul_s_id_correct.
  simpl.
  rewrite s_prod_comm.
  rewrite inverse_scalar_correct.
  easy.
Qed.

(* Definition of how to compose two PStrings *)

Definition extract_scalar {n: nat} (ps : PString n) : Scalar :=
  fst ps.

Definition s_prod_of_pstrings {n: nat} {m: nat} (ps1: PString n) (ps2: PString m) : Scalar :=
  let s1 := extract_scalar ps1 in
  let s2 := extract_scalar ps2 in
  s_prod s1 s2.

(* Example *)
Check s_prod_of_pstrings (One, p[X, Z]) (Iphase, p[Y, X]) = Iphase.

Definition compose_pstring {n m: nat} (ps1 : PString n) (ps2 : PString m) : PString (n + m) :=
  let s := s_prod_of_pstrings ps1 ps2 in
  let v := (snd ps1) ++ (snd ps2) in
  (s, v).

Check compose_pstring (One, p[X, Z]) (Iphase, p[Y, X]) = (Iphase, p[ X, Z, Y, X]).

(* Hard to prove due to dependent type *)
Lemma pvec_concat_correct:
  forall {n m: nat}  (pv1: PauliVector  n) (pv2: PauliVector  m),
  pvec_to_matrix (pv1 ++ pv2) = pvec_to_matrix pv1 ⊗ pvec_to_matrix pv2.
Admitted.


Theorem compose_pstring_correct: 
  forall {n m: nat}  (ps1: PString n) (ps2: PString m),
  pstr_to_matrix (compose_pstring ps1 ps2) =
  pstr_to_matrix ps1 ⊗ pstr_to_matrix ps2.
Proof.
  intros.
  unfold compose_pstring.
  induction ps1.
  induction ps2.
  simpl.
  (* Search (_ ⊗ (_ .* _)). *)
  rewrite Mscale_kron_dist_r.
  (* Search (_ .* (_ .* _)). *)
  Fail rewrite Mscale_assoc.
  (* Search (_ .* _  ⊗ _). *)
  rewrite Mscale_kron_dist_l.
  rewrite Mscale_assoc.
  assert (
    Hscale: scalar_to_complex (s_prod_of_pstrings (a, b) (a0, b0)) = 
    scalar_to_complex a0 * scalar_to_complex a
  ).
    {
      unfold  s_prod_of_pstrings .
      simpl.
      rewrite s_prod_correct.
      rewrite Cmult_comm.
      reflexivity.
    }
  rewrite Hscale.
  rewrite pvec_concat_correct.
  reflexivity.
Qed.

End PStrGroup.

Section PStringProperties.

Require Import ExtraSpecs.

Print PString.

(* Hard to make type correct due to dependent type *)
Fail Lemma pstring_tail n: 
  forall (pstr: PString (n + 1)),
  exists (ptail: PString n) (ph: PauliOp),
    let (s, pv) := ptail in
    pstr = (s, shiftin ph pv).



(* Hard to prove since the lemma pstring_tail cannot define *)
Lemma psmul_bicommute n: 
  bicommute (@psmul n) (@psneg n).
Proof.
  unfold bicommute; intros.
  dependent induction n.
Admitted.


End PStringProperties.



