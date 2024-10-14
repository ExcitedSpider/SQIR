Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.

Module Pauli.

(* 
  Complete pauli group (operations with scalars) 
  However, we expect it will not be used in the stabilizer formalism
  because for stabilizer, scalars are useless. It only acts as unneccesary
  complexity. 

  But it's still valueable to have this complete formalism
*)

Inductive pauli_op : Type :=
| I : pauli_op
| X : pauli_op
| Y : pauli_op
| Z : pauli_op.

Inductive scalar : Type :=
| One : scalar      (* 1 *)
| Iphase : scalar   (* i *)
| NegOne : scalar   (* -1 *)
| NegIphase : scalar. (* -i *)

Inductive pauli : Type :=
| PauliElem : scalar -> pauli_op -> pauli.

(* Define a custom notation for elements of the Pauli group *)
Notation "s · p" := (PauliElem s p) (at level 40, left associativity).

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

Definition scalar_to_complex (s : scalar) : C :=
match s with
| One => 1
| Iphase => Ci
| NegOne => -1
| NegIphase => - Ci 
end.

Definition op_to_matrix (p : pauli_op) : Square 2 :=
match p with
| I => QuantumLib.Matrix.I 2 
| X => σx
| Y => σy
| Z => σz
end.

Definition pauli_to_matrix (p: pauli): Square 2 := 
  match p with
    | PauliElem s op => (scalar_to_complex s) .* (op_to_matrix op)
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

(* The operation on the pauli group *)
(* Define the operation as relation makes it so hard *)
Inductive pmult: pauli -> pauli -> pauli -> Prop := 
| PauliMultRel: forall (a b c: pauli),
  (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
  pmult a b c.

Example fact_square_x: 
pmult (One · X)  (One · X) (One · I).
Proof.
apply PauliMultRel.
simpl.
solve_matrix.
Qed.

Definition ID := (One · I).

Lemma pauli_op_wf: 
forall (a: pauli), WF_Matrix (pauli_to_matrix a).
Proof.
intros.
destruct a.
destruct s, p;
simpl;
auto with wf_db.
Qed.

Lemma pauli_identity_correct_left:
forall (a: pauli), pmult ID a a.
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
forall (a: pauli), pmult a ID a.
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

Definition inverse_op (op: pauli_op): pauli_op := 
match op with
| I => I
| X => X
| Y => Y
| Z => Z
end.

Definition inverse_scala (op: scalar): scalar := 
match op with
| One => One
| Iphase => NegIphase
| NegOne => NegOne
| NegIphase => Iphase 
end.

Definition pauli_inverse (p : pauli) : pauli :=
match p with
| PauliElem s op => PauliElem (inverse_scala s) (inverse_op op)
end.

Lemma pauli_inverse_correct:
forall (a: pauli), exists (a': pauli),
pmult a a' ID.
Proof.
intros.
exists (pauli_inverse a). 
apply PauliMultRel. 
destruct a.
destruct s, p;
solve_matrix.
Qed.


Lemma pauli_closure:
forall a b,
exists (c: pauli), pmult a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
destruct sa, pa, sb, pb.
Abort. (* 256 cases. not feasible to prove directly *)

Lemma scalar_closure:
forall a b,
exists (c: scalar), 
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
exists (c: pauli_op) (s: scalar), 
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
exists (c: pauli), pmult a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
specialize (scalar_closure sa sb) as [sc Hsc].
specialize (op_closure pa pb) as [pc Hpc].
destruct Hpc as [s Hpc].
specialize (scalar_closure sc s) as [sc' Hsc'].
exists (PauliElem sc' pc).
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

Lemma pmult_assoc : forall a b ab c abc : pauli,
pmult a b ab ->
pmult ab c abc ->
exists bc, pmult b c bc /\ pmult a bc abc.
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

(* The pauli operator forms a group *)
Theorem PauliGroupProperties:
(forall a, pmult ID a a) /\
(forall a, exists a', pmult a a' ID) /\
(forall a b, exists c, pmult a b c) /\ 
(forall a b ab c abc,
  pmult a b ab ->
  pmult ab c abc ->
  exists bc, pmult b c bc /\ pmult a bc abc
).
Proof.
split. apply pauli_identity_correct_left.
split. apply pauli_inverse_correct.
split. apply pauli_closure'.
apply pmult_assoc.
Qed.

(* Definition inverse_scala (op: scalar): scalar := 
match op with
| One => One
| Iphase => NegIphase
| NegOne => NegOne
| NegIphase => Iphase 
end.

Definition pauli_inverse (p : pauli) : pauli :=
match p with
| PauliElem s op => PauliElem (inverse_scala s) (inverse_op op)
end. *)

(* 
=======================================================
Define pmult as a function

We found reasoing pmult as a relation is tiresome.
So it is better that we define it as a function.
Fortunately, as we have proved many facts about pmult,
it will be much easier now.
=======================================================
*)

Definition op_prod(a b: pauli_op): (scalar * pauli_op) := 
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

Definition s_prod(a b: scalar): scalar := 
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

Definition combined_scalars (s1 s2 s3: scalar) : scalar := 
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

Definition pmult_prod (a b: pauli): pauli := 
match a, b with
| PauliElem sa pa, PauliElem sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    let combined_scalar := combined_scalars sab sa sb in
    PauliElem combined_scalar pab
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

(* TODO: revise this later *)
Lemma pmult_prod_is_Mmult:
forall a b, pauli_to_matrix (pmult_prod a b) = 
  (pauli_to_matrix a) × (pauli_to_matrix b).
Proof.
  intros.
  destruct a, b.
  specialize (op_prod_correct p p0) as [s_prod [op_prod [Heq H]]].
  unfold pmult_prod.
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


Definition apply_s (s: scalar) (p: pauli): pauli :=
match p with
  | PauliElem s0 op => PauliElem (s_prod s s0) op
end.

Definition pmult_prod_alt (a b: pauli): pauli := 
match a, b with
| PauliElem sa pa, PauliElem sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    (* let combined_scalar := combined_scalars sab sa sb in *)
    apply_s sab (PauliElem (s_prod sa sb) pab)
end.

Lemma pmult_prod_alt_correct:
forall a b,
pmult_prod_alt a b = pmult_prod a b.
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

(* verify our function version of pmult is correct *)
Lemma pmult_prod_correct_r: forall (a b c: pauli),
(pmult_prod a b) = c -> pmult a b c. 
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

Lemma pmult_prod_correct_l: forall (a b c: pauli),
pmult a b c -> (pmult_prod a b) = c. 
Proof.
intros.
inversion H; subst.
rewrite <- pmult_prod_is_Mmult in H0.
rewrite pauli_to_matrix_injective in H0.
assumption.
Qed.

Theorem pmul_prod_eq: forall (a b c: pauli),
pmult a b c <-> (pmult_prod a b) = c. 
Proof.
split.
apply pmult_prod_correct_l.
apply pmult_prod_correct_r.
Qed.

(* 
The commute / anticommute are two very important properties in stabilizer formalism. we want to show that scalar does not affect commute / anticommute relation.
We also hope to inspect how our new defined prod function can simplify the proof.
*)

Inductive commute: pauli -> pauli -> Prop :=
| CommuteRel: forall (pa pb: pauli),
  (pmult_prod pa pb) = (pmult_prod pb pa) -> commute pa pb.

Lemma commute_self:
forall (p: pauli), commute p p.
Proof.
intros.
apply CommuteRel. reflexivity.
Qed.

Lemma commute_identity:
forall (p: pauli), commute p ID.
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
Inductive anticommute: pauli -> pauli -> Prop :=
| AnticommuteRel: forall (pa pb: pauli),
  (pmult_prod pa pb) = apply_s (NegOne) (pmult_prod pb pa) -> anticommute pa pb.

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

End Pauli.
