Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.
From mathcomp Require Import ssrfun fingroup eqtype fintype.
Require Import Assumption.

Require Import PauliGroup.
Import PauliGroup.P1Group.
Import PauliGroup.P1GGroup.

Module Pauli.

(* PauliOperator directly from group definition *)
Check PauliBase.

Check phase.

(* PauliBase with phase *)
Check PauliOp.

Definition p1g_of (s: phase) (op: PauliBase): PauliOp:=
  pair s op.

(* Define a custom notation for elements of the Pauli group *)
Notation "s · p" := (p1g_of s p) 
  (at level 40, left associativity).

Check One · X: PauliOp.
Check Img · Z: PauliOp.

Lemma pauli_eq_comp:
forall sa pa sb pb,
sa = sb -> pa = pb -> sa · pa = sb · pb.
Proof.
intros.
subst.
reflexivity.
Qed.

Definition scalar_to_complex: phase -> C := phase_int.

(* use the interpretation function in group definition *)
Definition op_to_matrix: PauliBase -> Square 2 := p1_int.

Definition pauli_to_matrix: PauliOp -> Square 2 := p1g_int.

Example negY: pauli_to_matrix (NOne · Y) = -C1 .* σy.
Proof. reflexivity. Qed.

Example negIX: pauli_to_matrix (NImg · X) = -Ci .* σx.
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

(* The operation on the PauliOp group *)
(* Define the operation as relation makes it so hard *)
Inductive pmultrel: PauliOp -> PauliOp -> PauliOp -> Prop := 
| PauliMultRel: forall (a b c: PauliOp),
  (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
  pmultrel a b c.

Example fact_square_x: 
pmultrel (One · X)  (One · X) (One · I).
Proof.
apply PauliMultRel.
simpl.
solve_matrix.
Qed.

(* Definition id_p1g := (One · I). *)
Definition id := id_p1g.

Lemma pauli_op_wf: 
forall (a: PauliOp), WF_Matrix (pauli_to_matrix a).
Proof.
intros.
destruct a as [s p].
destruct s, p;
simpl;
auto with wf_db.
Qed.

Definition inverse_op: PauliBase -> PauliBase := inv_p1.

Definition inverse_scalar: phase -> phase := inv_phase.


Definition pinv := inv_p1g.

Lemma pinv_correct:
forall (a: PauliOp), exists (a': PauliOp),
  pmultrel a a' id_p1g.
Proof.
intros.
exists (pinv a). 
apply PauliMultRel. 
destruct a as [s p].
destruct s, p;
solve_matrix.
Qed.

Lemma scalar_closure:
forall a b,
exists (c: phase), 
  (scalar_to_complex a) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
intros.
destruct a, b.
all: simpl.
all: try (exists One; simpl; lca).
all: try (exists Img; simpl; lca).
all: try (exists NOne; simpl; lca).
all: try (exists NImg; simpl; lca).
Qed.

Ltac MRefl :=
simpl; Qsimpl; try reflexivity; try solve_matrix.

Ltac MReflExists scale op :=
try (exists op, scale; MRefl).


Lemma op_closure:
forall a b,
exists (c: PauliBase) (s: phase), 
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
MReflExists Img Z.
MReflExists NImg Y.
MReflExists One Y.
MReflExists NImg Z.
MReflExists One I.
MReflExists Img X.
MReflExists One Z.
MReflExists Img Y.
MReflExists NImg X.
MReflExists One I.
Qed.


(* This one succeed by using two lemmas *)
Lemma pauli_closure':
forall a b,
exists (c: PauliOp), pmultrel a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
specialize (scalar_closure sa sb) as [sc Hsc].
specialize (op_closure pa pb) as [pc Hpc].
destruct Hpc as [s Hpc].
specialize (scalar_closure sc s) as [sc' Hsc'].
exists (pair sc' pc).
apply PauliMultRel; simpl.
(* Search (_ × (_ .* _)). *)
repeat rewrite Mscale_mult_dist_r.
(* Search (_ .* (_ × _)). *)
rewrite Mscale_mult_dist_l.
replace op_to_matrix  with p1_int in Hpc by easy. 
rewrite Hpc.
rewrite Mscale_assoc.
replace scalar_to_complex with phase_int  in Hsc' by easy. 
rewrite <- Hsc'.
(* Search ((_ * _) = (_ * _)). *)
rewrite Cmult_comm.
replace scalar_to_complex  with phase_int in Hsc by easy.
rewrite Hsc.
rewrite Mscale_assoc.
reflexivity.
Qed.

Lemma pmultrel_assoc : forall a b ab c abc : PauliOp,
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


(* 
=======================================================
Define pmultrel as a function

We found reasoing pmultrel as a relation is tiresome.
So it is better that we define it as a function.
Fortunately, as we have proved many facts about pmultrel,
it will be much easier now.
=======================================================
*)

Definition op_prod_op := mult_p1.


Definition op_prod_s := get_phase.


Definition op_prod (a b: PauliBase): (phase * PauliBase) := 
  (get_phase a b, mult_p1 a b).

Definition op_prod_alt(a b: PauliBase): (phase * PauliBase) := 
    ( op_prod_s a b, op_prod_op a b).

Lemma op_prod_alt_correct: 
forall a b,
op_prod_alt a b = op_prod a b.
Proof.
  intros.
  destruct a, b; easy.
Qed.



Definition s_prod := mult_phase.

Lemma inverse_scalar_correct:
  forall sc, s_prod sc (inverse_scalar sc) = One
. 
intros.
destruct sc; easy.
Qed.

Lemma s_prod_total:
  forall s1 s2,
  exists s3,
  s_prod s1 s2 = s3.
Proof.
  intros.
  destruct s1, s2.
  all: simpl.
  all: try(exists One; reflexivity).
  all: try(exists Img ; reflexivity).
  all: try(exists NOne  ; reflexivity).
  all: try(exists NImg  ; reflexivity).
Qed.

Definition combined_scalars (s1 s2 s3: phase) : phase := 
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

Definition pmul (a b: PauliOp): PauliOp := 
match a, b with
| pair sa pa, pair sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    let combined_scalar := combined_scalars sab sa sb in
    pair combined_scalar pab
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
  destruct p as [s p].
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
  - unfold scalar_to_complex. 
    destruct op1, op2.
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
  destruct a as [s p], b as [s0 p0].
  specialize (op_prod_correct p p0) as [s_prod [op_prod [Heq H]]].
  unfold pmul.
  rewrite Heq.
  unfold pauli_to_matrix .
  replace op_to_matrix with p1_int in H by easy. 
  replace scalar_to_complex with phase_int in H by easy.
  unfold p1g_int.
  distribute_scale. 
  rewrite H.
  rewrite Mscale_assoc.
  rewrite combinded_scalars_correct.
  assert (scalar_to_complex s_prod * scalar_to_complex s * scalar_to_complex s0 = scalar_to_complex s * scalar_to_complex s0 * scalar_to_complex s_prod) by lca.
  rewrite H0.
  reflexivity.
Qed.


Definition apply_s (s: phase) (p: PauliOp): PauliOp :=
match p with
  | pair s0 op => pair (s_prod s s0) op
end.

Definition pneg (p: PauliOp): PauliOp := apply_s (NOne) p.

Definition pmul_alt (a b: PauliOp): PauliOp := 
match a, b with
| pair sa pa, pair sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    (* let combined_scalar := combined_scalars sab sa sb in *)
    apply_s sab (pair (s_prod sa sb) pab)
end.

Lemma pmul_alt_correct:
forall a b,
pmul_alt a b = pmul a b.
Proof.
intros.
destruct a as [s p], b as [s0 p0].
simpl.
destruct s, s0.
all: simpl.
all: destruct p, p0.
all: simpl.
all: reflexivity.
Qed. 

(* verify our function version of pmultrel is correct *)
Lemma pmul_correct_r: forall (a b c: PauliOp),
(pmul a b) = c -> pmultrel a b c. 
Proof.
intros.
subst.
destruct a as [s p], b as [s0 p0].
destruct s, p, s0, p0.
all:  simpl; apply PauliMultRel; simpl; Qsimpl.
(* this is not necessary but slightly improve performance *)
all: try (rewrite Mscale_mult_dist_r). 
all: try(Qsimpl; try(reflexivity)).
all: try(rewrite Mmult_1_l).
all: try (Qsimpl; autorewrite with Q_db).
(* tried of finding patterns. *)
all: try(solve_matrix).
Qed.

Lemma pmul_correct_l: forall (a b c: PauliOp),
pmultrel a b c -> (pmul a b) = c. 
Proof.
intros.
inversion H; subst.
rewrite <- pmul_is_Mmult in H0.
rewrite pauli_to_matrix_injective in H0.
assumption.
Qed.

Theorem pmul_prod_eq: forall (a b c: PauliOp),
pmultrel a b c <-> (pmul a b) = c. 
Proof.
split.
apply pmul_correct_l.
apply pmul_correct_r.
Qed.

(* 
The commute / anticommute are two very important properties in stabilizer formalism. we want to show that phase does not affect commute / anticommute relation.
We also hope to inspect how our new defined prod function can simplify the proof.
*)

Inductive commute: PauliOp -> PauliOp -> Prop :=
| CommuteRel: forall (pa pb: PauliOp),
  (pmul pa pb) = (pmul pb pa) -> commute pa pb.

Lemma commute_self:
forall (p: PauliOp), commute p p.
Proof.
intros.
apply CommuteRel. reflexivity.
Qed.

Lemma commute_identity:
forall (p: PauliOp), commute p id_p1g.
Proof.
intros.
apply CommuteRel.
simpl.
(* no need to work on relations anymore! 
   just destruct everything and let coq do the calculation.
*)
destruct p.
destruct p.
all: destruct p0.
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
TODO: Replace this with ExtraSpecs
the definition has a slight issue: it depends on how `apply_s` is defiend. Although `apply_s` is straightforward, but it is not certified. 
*)
Inductive anticommute: PauliOp -> PauliOp -> Prop :=
| AnticommuteRel: forall (pa pb: PauliOp),
  (pmul pa pb) = apply_s (NOne) (pmul pb pa) -> anticommute pa pb.

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
anticommute (NImg · X) (Img · Z).
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

Lemma inverse_op_correct:
  left_inverse I inverse_op op_prod_op.
Proof.
  unfold left_inverse.
  intros.
  destruct x; reflexivity.
Qed.

Lemma s_prod_comm:
  commutative s_prod.
Proof.
  unfold commutative.
  intros.
  now destruct x, y; simpl.
Qed.

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

End Pauli.

Import PNGroup.
Import PNGGroup.

From mathcomp Require Import ssreflect.

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

From mathcomp Require Import seq tuple.

Lemma pn_int_cons:
  forall {n: nat} (pt: PauliTupleBase n) (p: PauliBase),
  pn_int [tuple of p::pt] = (p1_int p) ⊗ pn_int pt.
Proof.
  rewrite /=  => n pt p.
  rewrite theadCons.
  apply kron_simplify.
  - by easy.
  - apply f_equal .
    by rewrite beheadCons.
Qed.