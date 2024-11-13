Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.
Require Import Group.
From mathcomp Require Import ssrfun fingroup.

Module Pauli.

(* 
  Complete PauliTerm group (operations with scalars) 
  However, we expect it will not be used in the stabilizer formalism
  because for stabilizer, scalars are useless. It only acts as unneccesary
  complexity. 

  But it's still valueable to have this complete formalism
*)

(* The PauliOperator *)
Inductive PauliOp : Type :=
| I : PauliOp
| X : PauliOp
| Y : PauliOp
| Z : PauliOp.

Inductive Scalar : Type :=
| One : Scalar      (* 1 *)
| Iphase : Scalar   (* i *)
| NegOne : Scalar   (* -1 *)
| NegIphase : Scalar. (* -i *)

(* A Pauli Term is a scaled Pauli Operator *)
Inductive PauliTerm : Type :=
| ScaledOp : Scalar -> PauliOp -> PauliTerm.

(* Define a custom notation for elements of the Pauli group *)
Notation "s · p" := (ScaledOp s p) (at level 40, left associativity).

Check One · X.
Check Iphase · Z.

Lemma pauli_eq_comp:
forall sa pa sb pb,
sa = sb -> pa = pb -> sa · pa = sb · pb.
Proof.
intros.
subst.
reflexivity.
Qed.

Definition scalar_to_complex (s : Scalar) : C :=
match s with
| One => 1
| Iphase => Ci
| NegOne => -1
| NegIphase => - Ci 
end.

Definition op_to_matrix (p : PauliOp) : Square 2 :=
match p with
| I => QuantumLib.Matrix.I 2 
| X => σx
| Y => σy
| Z => σz
end.

Definition pauli_to_matrix (p: PauliTerm): Square 2 := 
  match p with
    | ScaledOp s op => (scalar_to_complex s) .* (op_to_matrix op)
  end.

Example negY: pauli_to_matrix (NegOne · Y) = -1 .* σy.
Proof. reflexivity. Qed.


Example negIX: pauli_to_matrix (NegIphase · X) = -Ci .* σx.
Proof. reflexivity. Qed.

Lemma pauli_to_matrix_determinsitic: forall a b c,
pauli_to_matrix a = b ->
pauli_to_matrix a = c ->
b = c.
Proof.
intros.
subst.
reflexivity.
Qed.

Lemma pauli_to_matrix_total: forall a,
exists b, pauli_to_matrix a = b.
Proof.
intros.
destruct a.
simpl.
exists (scalar_to_complex s .* op_to_matrix p).
reflexivity.
Qed.

Check Matrix.I 2.

Lemma square_2_eq_semantics : forall a b: Square 2,
a = b ->
a 0%nat 0%nat = b 0%nat 0%nat /\
a 0%nat 1%nat = b 0%nat 1%nat /\ 
a 1%nat 0%nat = b 1%nat 0%nat /\
a 1%nat 1%nat = b 1%nat 1%nat.
Proof.
intros.
subst.
repeat (split).
Qed.

Example one_semantics:
Matrix.I 2 0%nat 0%nat = 1.
Proof.
unfold Matrix.I.
simpl.
reflexivity.
Qed.

(* 
Transform 
(C1 .* Matrix.I 2) 0%nat 0%nat = (C1 .* σx) 0%nat 0%nat
to 
C1 * (Matrix.I 2 0%nat 0%nat) = ...
*)

Lemma scalar_asso_mapply:
forall (c: C) (m: Square 2) (i j: nat),
Nat.lt i 2%nat -> 
Nat.lt j 2%nat ->
(c .* m) i j = c * (m i j).
Proof.
unfold scale.
reflexivity.
Qed.  

Ltac contradict_c_eq H :=
field_simplify_eq in H;
inversion H as [HC];
contradict HC;
lra.

Lemma pauli_matrix_no_overlap : forall sa sb pa pb,
pauli_to_matrix (sa · pa) = pauli_to_matrix (sb · pb) ->
pa <> pb \/ sa <> sb ->
False.
Proof.
intros.
destruct H0.
{
  apply H0; clear H0.     
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: try(
    apply square_2_eq_semantics in H;
    simpl in H;
    unfold Matrix.I, σx, σz, σy in H;
    destruct H as [H0 [H1 [H2 H3]]];
    repeat (rewrite scalar_asso_mapply in H0, H1, H2, H3 by lia);
    simpl in H0, H1, H2, H3
  ).
  all: try(contradict_c_eq H0).
  all: try(contradict_c_eq H1).
  all: try(contradict_c_eq H2).
  all: try(contradict_c_eq H3).
}
{
  apply H0; clear H0.     
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: try(
    apply square_2_eq_semantics in H;
    simpl in H;
    unfold Matrix.I, σx, σz, σy in H;
    destruct H as [H0 [H1 [H2 H3]]];
    repeat (rewrite scalar_asso_mapply in H0, H1, H2, H3 by lia);
    simpl in H0, H1, H2, H3
  ).
  all: try(contradict_c_eq H0).
  all: try(contradict_c_eq H1).
  all: try(contradict_c_eq H2).
  all: try(contradict_c_eq H3).
}
Qed.

Lemma pauli_to_matrix_comp: forall sa pa sb pb,
pauli_to_matrix (sa · pa) = pauli_to_matrix (sb · pb) ->
sa = sb /\ pa = pb.
Proof.
intros.
split.
{
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: exfalso; eapply pauli_matrix_no_overlap ; try(apply H); 
    try(left; discriminate);
    try(right;discriminate).
}
{
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: exfalso; eapply pauli_matrix_no_overlap ; try(apply H); 
    try(left; discriminate);
    try(right;discriminate).
}
Qed.


Lemma pauli_to_matrix_injective: forall a b,
pauli_to_matrix a = pauli_to_matrix b <-> a = b.
Proof.
split.
{ 
  intros.
  destruct a, b.
  apply pauli_to_matrix_comp in H.
  destruct H.
  subst.
  reflexivity.
}
{
  intros.
  subst.
  reflexivity.
}
Qed.

(* The operation on the PauliTerm group *)
(* Define the operation as relation makes it so hard *)
Inductive pmultrel: PauliTerm -> PauliTerm -> PauliTerm -> Prop := 
| PauliMultRel: forall (a b c: PauliTerm),
  (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
  pmultrel a b c.

Example fact_square_x: 
pmultrel (One · X)  (One · X) (One · I).
Proof.
apply PauliMultRel.
simpl.
solve_matrix.
Qed.

Definition ID := (One · I).

Lemma pauli_op_wf: 
forall (a: PauliTerm), WF_Matrix (pauli_to_matrix a).
Proof.
intros.
destruct a.
destruct s, p;
simpl;
auto with wf_db.
Qed.

Lemma pauli_identity_correct_left:
forall (a: PauliTerm), pmultrel ID a a.
Proof.
intros.
apply PauliMultRel.
simpl.
rewrite Mscale_1_l.
(* Search (Matrix.I _ = _). *)
apply mat_equiv_eq.
- apply WF_mult.
  + auto with wf_db.
  + apply pauli_op_wf.
- apply pauli_op_wf.  
- apply Mmult_1_l_mat_eq.
Qed.

Lemma pauli_identity_correct:
forall (a: PauliTerm), pmultrel a ID a.
Proof.
intros.
apply PauliMultRel; simpl.
rewrite Mscale_1_l.
apply mat_equiv_eq.
- apply WF_mult.
  + apply pauli_op_wf.
  + auto with wf_db. 
- apply pauli_op_wf.  
- apply Mmult_1_r_mat_eq.
Qed.

Definition inverse_op (op: PauliOp): PauliOp := 
match op with
| I => I
| X => X
| Y => Y
| Z => Z
end.

Definition inverse_scala (op: Scalar): Scalar := 
match op with
| One => One
| Iphase => NegIphase
| NegOne => NegOne
| NegIphase => Iphase 
end.

Definition pinv (p : PauliTerm) : PauliTerm :=
match p with
| ScaledOp s op => ScaledOp (inverse_scala s) (inverse_op op)
end.

Lemma pinv_correct:
forall (a: PauliTerm), exists (a': PauliTerm),
pmultrel a a' ID.
Proof.
intros.
exists (pinv a). 
apply PauliMultRel. 
destruct a.
destruct s, p;
solve_matrix.
Qed.


Lemma pauli_closure:
forall a b,
exists (c: PauliTerm), pmultrel a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
destruct sa, pa, sb, pb.
Abort. (* 256 cases. not feasible to prove directly *)

Lemma scalar_closure:
forall a b,
exists (c: Scalar), 
  (scalar_to_complex a) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
intros.
destruct a, b.
all: simpl.
all: try (exists One; simpl; lca).
all: try (exists Iphase; simpl; lca).
all: try (exists NegOne; simpl; lca).
all: try (exists NegIphase; simpl; lca).
Qed.

Ltac MRefl :=
simpl; Qsimpl; try reflexivity; try solve_matrix.

Ltac MReflExists scale op :=
try (exists op, scale; MRefl).


Lemma op_closure:
forall a b,
exists (c: PauliOp) (s: Scalar), 
  (op_to_matrix a) × (op_to_matrix b) = (scalar_to_complex s) .* (op_to_matrix c).
Proof.
intros a b.
destruct a, b.
all: simpl; Qsimpl.
(* This is so painful. don't know how to revert `exists` *)
MReflExists One I.
MReflExists One X.
MReflExists One Y.
MReflExists One Z.
MReflExists One X.
MReflExists One I.
MReflExists Iphase Z.
MReflExists NegIphase Y.
MReflExists One Y.
MReflExists NegIphase Z.
MReflExists One I.
MReflExists Iphase X.
MReflExists One Z.
MReflExists Iphase Y.
MReflExists NegIphase X.
MReflExists One I.
Qed.


(* This one succeed by using two lemmas *)
Lemma pauli_closure':
forall a b,
exists (c: PauliTerm), pmultrel a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
specialize (scalar_closure sa sb) as [sc Hsc].
specialize (op_closure pa pb) as [pc Hpc].
destruct Hpc as [s Hpc].
specialize (scalar_closure sc s) as [sc' Hsc'].
exists (ScaledOp sc' pc).
apply PauliMultRel; simpl.
(* Search (_ × (_ .* _)). *)
repeat rewrite Mscale_mult_dist_r.
(* Search (_ .* (_ × _)). *)
rewrite Mscale_mult_dist_l.
rewrite Hpc.
rewrite Mscale_assoc.
rewrite <- Hsc'.
(* Search ((_ * _) = (_ * _)). *)
rewrite Cmult_comm.
rewrite Hsc.
rewrite Mscale_assoc.
reflexivity.
Qed.

Lemma pmultrel_assoc : forall a b ab c abc : PauliTerm,
pmultrel a b ab ->
pmultrel ab c abc ->
exists bc, pmultrel b c bc /\ pmultrel a bc abc.
Proof.
intros a b ab c abc HL HR.
specialize (pauli_closure' b c) as Hbc.
destruct Hbc as [bc Hbc].
exists bc.
split.
- assumption.
- apply PauliMultRel.
  inversion Hbc; subst.
  rewrite <- H; clear H Hbc.
  inversion HR; subst.
  rewrite <- H; clear H HR.
  inversion HL; subst.
  rewrite <- H; clear H HL.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

(* The PauliTerm operator forms a group *)
Theorem PauliGroupProperties:
(forall a, pmultrel ID a a) /\
(forall a, exists a', pmultrel a a' ID) /\
(forall a b, exists c, pmultrel a b c) /\ 
(forall a b ab c abc,
  pmultrel a b ab ->
  pmultrel ab c abc ->
  exists bc, pmultrel b c bc /\ pmultrel a bc abc
).
Proof.
split. apply pauli_identity_correct_left.
split. apply pinv_correct.
split. apply pauli_closure'.
apply pmultrel_assoc.
Qed.

(* Definition inverse_scala (op: Scalar): Scalar := 
match op with
| One => One
| Iphase => NegIphase
| NegOne => NegOne
| NegIphase => Iphase 
end.

Definition pinv (p : PauliTerm) : PauliTerm :=
match p with
| ScaledOp s op => ScaledOp (inverse_scala s) (inverse_op op)
end. *)

(* 
=======================================================
Define pmultrel as a function

We found reasoing pmultrel as a relation is tiresome.
So it is better that we define it as a function.
Fortunately, as we have proved many facts about pmultrel,
it will be much easier now.
=======================================================
*)

Definition op_prod(a b: PauliOp): (Scalar * PauliOp) := 
  match a, b with
  | I, p => (One, p)
  | p, I => (One, p)  
  
  | X, X => (One, I)
  | Y, Y => (One, I) 
  | Z, Z => (One, I)

  | X, Y => (Iphase, Z) 
  | Y, X => (NegIphase, Z)

  | Y, Z => (Iphase, X)
  | Z, Y => (NegIphase, X)

  | Z, X => (Iphase, Y)
  | X, Z => (NegIphase, Y) 
end.

Definition s_prod(a b: Scalar): Scalar := 
match a, b with
  | One, s => s
  | s, One => s
  | NegOne, Iphase => NegIphase
  | Iphase, NegOne => NegIphase
  | NegOne, NegOne => One
  | NegOne, NegIphase => Iphase
  | NegIphase, NegOne => Iphase
  | Iphase, NegIphase => One
  | NegIphase, Iphase => One
  | Iphase, Iphase => NegOne
  | NegIphase, NegIphase => NegOne
end.

Lemma s_prod_total:
  forall s1 s2,
  exists s3,
  s_prod s1 s2 = s3.
Proof.
  intros.
  destruct s1, s2.
  all: simpl.
  all: try(exists One; reflexivity).
  all: try(exists Iphase ; reflexivity).
  all: try(exists NegOne  ; reflexivity).
  all: try(exists NegIphase  ; reflexivity).
Qed.

Definition combined_scalars (s1 s2 s3: Scalar) : Scalar := 
s_prod s1 (s_prod s2 s3).

Lemma combined_scalars_total:
  forall s1 s2 s3,
  exists s4,
  combined_scalars s1 s2 s3 = s4.
Proof.
  intros.
  unfold combined_scalars.
  apply s_prod_total.
Qed.

Definition pmul (a b: PauliTerm): PauliTerm := 
match a, b with
| ScaledOp sa pa, ScaledOp sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    let combined_scalar := combined_scalars sab sa sb in
    ScaledOp combined_scalar pab
end.

Lemma s_prod_identity:
  forall s, s_prod s One = s.
Proof.
  intros.
  destruct s.
  all: simpl; reflexivity.
Qed.

Lemma s_prod_correct:
  forall s0 s1,
  scalar_to_complex (s_prod s0 s1) = scalar_to_complex s0 * scalar_to_complex s1.
Proof.
  intros.
  destruct s0, s1.
  all: simpl; lca.
Qed.

Lemma combinded_scalars_correct:
  forall s0 s1 s2,
  scalar_to_complex (combined_scalars s0 s1 s2) = 
    scalar_to_complex s0 *
    scalar_to_complex s1 *
    scalar_to_complex s2.
Proof.
  intros.
  unfold combined_scalars.
  repeat rewrite s_prod_correct.
  lca.
Qed.

Lemma op_prod_total:
  forall op1 op2,
  exists prod_s prod_op,
  op_prod op1 op2 = (prod_s, prod_op).
Proof.
  intros.
  remember (op_prod op1 op2).
  destruct p.
  exists s, p.
  reflexivity.
Qed.

Lemma op_prod_correct:
  forall op1 op2,
  exists prod_s prod_op,
  op_prod op1 op2 = (prod_s, prod_op) /\
  (op_to_matrix op1) × (op_to_matrix op2) = (scalar_to_complex prod_s) .* (op_to_matrix prod_op).
Proof. 
  intros.
  specialize (op_prod_total op1 op2) as [s [p H]].
  exists s, p.
  split.
  - assumption.
  - destruct op1, op2.
    all: simpl in H; inversion H; subst.
    all: simpl; Qsimpl.
    all: try(reflexivity).
    all: solve_matrix. (* these facts can be lemmas? *) 
Qed.



Lemma pmul_is_Mmult:
forall a b, pauli_to_matrix (pmul a b) = 
  (pauli_to_matrix a) × (pauli_to_matrix b).
Proof.
  intros.
  destruct a, b.
  specialize (op_prod_correct p p0) as [s_prod [op_prod [Heq H]]].
  unfold pmul.
  rewrite Heq.
  unfold pauli_to_matrix .
  distribute_scale.
  rewrite H.
  rewrite Mscale_assoc.
  rewrite combinded_scalars_correct.
  assert (scalar_to_complex s_prod * scalar_to_complex s * scalar_to_complex s0 = scalar_to_complex s * scalar_to_complex s0 * scalar_to_complex s_prod) by lca.
  rewrite H0.
  reflexivity.
Qed.


Definition apply_s (s: Scalar) (p: PauliTerm): PauliTerm :=
match p with
  | ScaledOp s0 op => ScaledOp (s_prod s s0) op
end.

Definition pmul_alt (a b: PauliTerm): PauliTerm := 
match a, b with
| ScaledOp sa pa, ScaledOp sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    (* let combined_scalar := combined_scalars sab sa sb in *)
    apply_s sab (ScaledOp (s_prod sa sb) pab)
end.

Lemma pmul_alt_correct:
forall a b,
pmul_alt a b = pmul a b.
Proof.
intros.
destruct a, b.
simpl.
destruct s, s0.
all: simpl.
all: destruct p, p0.
all: simpl.
all: reflexivity.
Qed. 

(* verify our function version of pmultrel is correct *)
Lemma pmul_correct_r: forall (a b c: PauliTerm),
(pmul a b) = c -> pmultrel a b c. 
Proof.
intros.
subst.
destruct a, b.
destruct s, p, s0, p0.
all:  simpl; apply PauliMultRel; simpl; Qsimpl.
(* this is not necessary but slightly improve performance *)
all: try (rewrite Mscale_mult_dist_r). 
all: try(Qsimpl; try(reflexivity)).
all: try(rewrite Mmult_1_l).
(* tried of finding patterns. *)
all: try(solve_matrix).
Qed.

Lemma pmul_correct_l: forall (a b c: PauliTerm),
pmultrel a b c -> (pmul a b) = c. 
Proof.
intros.
inversion H; subst.
rewrite <- pmul_is_Mmult in H0.
rewrite pauli_to_matrix_injective in H0.
assumption.
Qed.

Theorem pmul_prod_eq: forall (a b c: PauliTerm),
pmultrel a b c <-> (pmul a b) = c. 
Proof.
split.
apply pmul_correct_l.
apply pmul_correct_r.
Qed.

(* 
The commute / anticommute are two very important properties in stabilizer formalism. we want to show that Scalar does not affect commute / anticommute relation.
We also hope to inspect how our new defined prod function can simplify the proof.
*)

Inductive commute: PauliTerm -> PauliTerm -> Prop :=
| CommuteRel: forall (pa pb: PauliTerm),
  (pmul pa pb) = (pmul pb pa) -> commute pa pb.

Lemma commute_self:
forall (p: PauliTerm), commute p p.
Proof.
intros.
apply CommuteRel. reflexivity.
Qed.

Lemma commute_identity:
forall (p: PauliTerm), commute p ID.
Proof.
intros.
apply CommuteRel.
simpl.
(* no need to work on relations anymore! 
   just destruct everything and let coq do the calculation.
*)
destruct p.
destruct p.
all: destruct s.
all: try(reflexivity).
Qed.

(* Can you think a better name *)
Lemma scalar_does_not_affect_commute:
forall p1 p2 s1 s2, commute (One · p1) (One · p2) ->
commute (s1 · p1) (s2 · p2).
Proof.
intros.
inversion H; subst.
apply CommuteRel.
simpl.
unfold combined_scalars.
destruct s1, s2, p1, p2.
(* some can be resolved by performing multiplication *)
all: try (reflexivity).
(* some can be resolved by contradiction *)
all: try (inversion H0).
Qed.

(* 
the definition has a slight issue: it depends on how `apply_s` is defiend. Although `apply_s` is straightforward, but it is not certified. 
*)
Inductive anticommute: PauliTerm -> PauliTerm -> Prop :=
| AnticommuteRel: forall (pa pb: PauliTerm),
  (pmul pa pb) = apply_s (NegOne) (pmul pb pa) -> anticommute pa pb.

Example anticommute_exp0:
anticommute (One · X) (One · Y).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

Example anticommute_exp1:
anticommute (One · Y) (One · Z).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

Example anticommute_exp2:
anticommute (One · X) (One · Z).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

(* 
very similar to `scalar_does_not_affect_commute`
I wonder if there is a way to extract the same pattern
*)
Lemma scalar_does_not_affect_anticommute:
forall p1 p2 s1 s2, anticommute (One · p1) (One · p2) ->
anticommute (s1 · p1) (s2 · p2).
Proof.
intros.
inversion H; subst.
apply AnticommuteRel.
simpl.
unfold combined_scalars.
destruct s1, s2, p1, p2.
(* some can be resolved by performing multiplication *)
all: try (reflexivity).
(* some can be resolved by contradiction *)
all: try (inversion H0).
Qed.

(* 
At this point, it is guranteed that scalars do not affect us
to reasoing about (anti)commute. so we can throw them away.
*)

Example anticommute_exp3:
anticommute (NegIphase · X) (Iphase · Z).
Proof.
apply scalar_does_not_affect_anticommute.
apply AnticommuteRel.
reflexivity.
Qed.

(* It seems that the proof of anticommute_exp3 is pretty mechanical.
we can work on some automation later. 
*)

Example ix_ineq: Matrix.I 2 <> σx.
Proof.
  unfold not.
  intros H.
  assert (Hcontra: Matrix.I 2 0%nat 0%nat = σx 0%nat 0%nat).
  { rewrite H. reflexivity. }
  unfold Matrix.I in Hcontra.
  simpl in Hcontra.
  inversion Hcontra.
  contradict H1.
  lra.
Qed.

Example iy_ineq: Matrix.I 2 <> σy.
Proof.
  unfold not.
  intros H.
  assert (Hcontra: Matrix.I 2 0%nat 0%nat = σy 0%nat 0%nat).
  { rewrite H. reflexivity. }
  unfold Matrix.I in Hcontra.
  simpl in Hcontra.
  inversion Hcontra.
  contradict H1.
  lra.
Qed.


(* Additonal Lemmas *)

(* Have some troubles proving function inequalities*)
(* But this is a known simple fact in math that all PauliTerm operators are orthogonal*)
(* So we skip this proof *)
Lemma pauli_orthogonal:
  forall sa opa sb opb,
  scalar_to_complex sa .* op_to_matrix opa =
  scalar_to_complex sb .* op_to_matrix opb ->
  sa = sb /\ opa = opb.
Proof. 
  intros.
  destruct sa, sb, opa, opb.
  all: simpl in H; try easy.
  all: contradict H; Qsimpl.
  apply ix_ineq.
  apply iy_ineq.
  (* There are 238 cases just like ix_ineq and iy_ineq *)
  (* Let me write a ltac later *)
  Admitted. 
 


Lemma pauli_to_matrix_correct:
  forall p s op, 
  p = ScaledOp s op <->
  pauli_to_matrix p = scalar_to_complex s .* op_to_matrix op.
Proof.
  intros.
  split; intros H.
  - subst. reflexivity.
  - destruct p as [sp opp]. 
    simpl in H.
    apply pauli_orthogonal in H.
    destruct H.
    subst.
    reflexivity.
Qed.

Lemma op_prod_correct_eq:
  forall oa ob sab oab p,
  op_to_matrix oa × op_to_matrix ob = pauli_to_matrix p ->
  p = ScaledOp sab oab ->
  op_prod oa ob = (sab, oab).
Proof.
  intros.
  specialize (op_prod_correct oa ob) as Hexists.
  destruct Hexists as [s [op [Heq Hprod]]].
  subst.
  simpl in H.
  assert (sab = s /\ oab = op).
  { apply pauli_orthogonal.
    congruence. }
  destruct H0.
  congruence.
Qed.

Lemma s_prod_assoc:
  associative s_prod.
Proof.
  unfold associative.
  intros.
  destruct x, y, z; reflexivity.
Qed.

Search "commutative".

Lemma s_prod_comm:
  commutative s_prod.
Admitted.

Lemma s_prod_left_id: left_id One s_prod.
Proof.
  unfold left_id.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma s_prod_right_id: right_id One s_prod.
Proof.
  unfold right_id.
  intros.
  simpl.
  destruct x; easy.
Qed.

(* A More Usable Variant *)
Lemma op_prod_correct_eq_var:
  forall oa ob s op,
  op_to_matrix oa × op_to_matrix ob = pauli_to_matrix (s · op) ->
  op_prod oa ob = (s, op).
Proof.
  intros.
  remember (s · op) as p.
  apply (op_prod_correct_eq _ _ _ _ p); assumption.
Qed.  

Lemma op_prod_snd_assoc:
  forall a b c, 
  (op_prod a (op_prod b c).2).2 = (op_prod (op_prod a b).2 c).2.
Proof.
  intros.
  simpl.
  destruct a, b, c.
  all: simpl; reflexivity.
Qed.

Lemma op_prod_snd_helper:
  forall a b s p,
  (s, p) = op_prod a b ->
  p =  (op_prod a b).2.
Proof.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.


Lemma pmul_assoc: associative pmul.
Proof.
  unfold associative; intros.
  destruct x, y, z.
  simpl.
  unfold combined_scalars.
  remember (op_prod p p0) as p00.
  destruct p00.
  remember (op_prod p0 p1) as p01.
  destruct p01.
  remember (op_prod p p3) as p03.
  destruct p03; simpl.
  remember (op_prod p2 p1) as p21.
  destruct p21.
  assert (p4 = p5).
  {
    apply op_prod_snd_helper in Heqp21.
    apply op_prod_snd_helper in Heqp03.
    apply op_prod_snd_helper in Heqp01.
    apply op_prod_snd_helper in Heqp00.
    subst.
    apply op_prod_snd_assoc.
  }
  subst.
  unfold combined_scalars.
  repeat rewrite s_prod_assoc.
  assert (
    s_prod (s_prod (s_prod (s_prod s4 s) s3) s0) s1 =
    s_prod (s_prod (s_prod (s_prod s5 s2) s) s0) s1
  ).
  {
    destruct p, p0, p1;
    inversion Heqp00; subst;
    inversion Heqp01; subst;
    inversion Heqp03; subst;
    inversion Heqp21; subst.
    all: simpl.
    all: try (apply s_prod_left_id).
    all: try (
      rewrite s_prod_right_id; 
      rewrite <- s_prod_assoc;
      reflexivity
    ).
   all:  try(destruct s, s0, s1; easy).
  }
  rewrite H.
  reflexivity.
Qed.

Definition e: PauliTerm :=  ScaledOp One I.

Lemma pmul_left_id: left_id e pmul.
Proof.
  unfold left_id.
  intros.
  simpl.
  destruct x.
  reflexivity.
Qed.

Lemma pmul_left_inverse: left_inverse e pinv pmul.
Proof.
  unfold left_inverse.
  intros.
  destruct x.
  destruct s, p; easy.
Qed.

End Pauli.