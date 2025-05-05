(* The quantum stabilizer theories and examples          *)
(* also provided some ltacs to prove stabilize relations *) 


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import PauliGroup.
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.
Require Import WellForm.
Require Import Assumption.

Require Import Operations.


Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-1' x1 , .. , xn ]" := (NOne, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'pi' x1 , .. , xn ]" := (Img, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-i' x1 , .. , xn ]" := (NImg, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Definition stb {n:nat} (pstring: PauliElement n) (psi: Vector (2^n)):= 
  act_n n psi pstring = psi.
(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stb pstring ψ) (at level 50).

Definition stb_1 (p: PauliBase) (psi: Vector 2) :=
  act_1 psi (One, p) = psi.

(* TODO: Move to stabiliser.v *)
Section HermitianOperator.

Lemma PauliOperator_stb {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi -> (pn_int p) × psi = psi. 
Proof.
  rewrite /stb /= /Action.applyP /png_int /= => p psi.
  move => H.
  rewrite Mscale_1_l in H.
  by exact H.
Qed.

End HermitianOperator.

Ltac simpl_stbn := 
  rewrite /stb /act_n /applyP /=;
  Qsimpl;
  try (lma'; try (apply apply_n_wf);auto with wf_db).

(* Z stabilises ∣0⟩ *)
Example stb_z0:
  [p1 Z] ∝1 ∣0⟩.
Proof. by simpl_stbn. Qed.

Example stb_z1:
  [p-1 Z] ∝1 ∣1⟩.
Proof. by simpl_stbn. Qed.

(* this proof can scale to two and three qubits *)
Example stb_z00:
  (One, [p Z , Z]) ∝1 ∣0,0⟩.
Proof. by simpl_stbn. Qed.

(* For length >= 4, it becomes unscalable *)
Example stb_z0000:
  [p1 Z,Z,Z,Z] ∝1 ∣0,0,0,0⟩.
Proof. 
Fail Timeout 1 by simpl_stbn. 
Abort.

Example stb_y0:
  [p1 Y] ∝1  ∣R⟩.
Proof. by simpl_stbn. Qed.

Example stb_y1:
  [p-1 Y] ∝1 ∣L⟩.
Proof. by simpl_stbn. Qed.

Example stb_x0:
  [p1 X] ∝1 ∣+⟩.
Proof. by simpl_stbn. Qed.

Example stb_x1:
  [p-1 X] ∝1 ∣-⟩.
Proof. by simpl_stbn. Qed.

(* this does not auto applied because of a hypothesiss *)
Lemma stb_id:
  forall psi,
  WF_Matrix psi -> [p1 I] ∝1 psi.
Proof.
  move => psi H.
  rewrite /stb /act_n /= /applyP.
  rewrite /png_int /pn_int /=.
  Qsimpl; auto.
Qed.

#[export] Hint Resolve stb_z0 stb_z1 stb_y0 stb_y1 stb_x0 stb_x1 stb_id : stab_db.


Lemma one_stb_everything:
  forall {n: nat} (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb (id_png n) ψ.
Proof.
  intros.
  unfold stb. 
  (* This is how you get obligations *)
  case act_n => to obligations.
  simpl.
  case obligations => act_to_id _.
  by apply act_to_id.
Qed.


(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
Lemma inv_stb:
  forall {n: nat} (pstr: PauliElement n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb pstr ψ -> stb (pstr^-1) ψ.
Proof.
  intros n pstr ψ Hwf Hstb.
  unfold stb in *.
  rewrite <- Hstb at 1.
  rewrite /act_n /applyP /=.
  rewrite <- Mmult_assoc.
  (* Search png_int "×". *)
  rewrite png_int_Mmult.
  rewrite mulVg /=.
  apply one_stb_everything; easy.
Qed.

Print Vector.

Ltac unfold_stb := 
rewrite /stb /act_n /applyP /=.



(* 
If we take the tensor product of a two states, with stabiliser groups A and B (respectively), then the resulting tensor product state has stabiliser group given by the cartesian product A × B. 
*)
Theorem stb_compose:
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stb  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  by rewrite H1 H2;
  reflexivity.
  all: try by rewrite - Nat.pow_add_r.
Qed.
  
(* The vector space of EPR Pair can be defined by generator <XX, ZZ> *)
Fact bell_stabilizer: 
  (One, [p X,X]) ∝1 ∣Φ+⟩ /\ (One, [p Z,Z]) ∝1 ∣Φ+⟩.
Proof.
  split.
  - unfold stb.
    lma'.
    unfold_stb.
    simpl;Qsimpl.
    auto with wf_db. 
  - unfold stb.
    lma'.
    unfold_stb.
    simpl;Qsimpl.
    auto with wf_db.
Qed. 

Fact three_qubit_state_stabilizer:
  (One, [p Z, Z, I]) ∝1 ∣000⟩ /\ (One, [p Z, Z, I]) ∝1 ∣000⟩.
Proof.
  split.
  - unfold_stb; Qsimpl.
    solve_matrix.
  - unfold_stb; Qsimpl.
    solve_matrix.
Qed.

Theorem stb_closed: 
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  mulg pstr1 pstr2 ∝1 ψ
.
Proof.
  unfold_stb => n pstr1 pstr2 psi H0 H1.
  rewrite -png_int_Mmult.
  by rewrite Mmult_assoc H1 H0.
Qed.

Import Commutativity.


(* there is no -1 in any stabilizer group *)
Theorem stb_group_no_m1: 
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  WF_Matrix ψ ->
  mulg pstr1 pstr2 <> (NOne, id_pn n).
Proof.
  unfold not.
  intros.
  assert ((NOne, id_pn n) ∝1 ψ) as H3.
  {
    rewrite <- H2.
    apply stb_closed; easy.
  }
  contradict H3.
  move: (one_stb_everything ψ H1).
  unfold_stb; Qsimpl => Hid.
  rewrite Mscale_mult_dist_l Hid.
  apply negate_change_state. 
Qed.

Require Import ExtraSpecs.


Theorem stabilizer_must_commute: 
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  fingroup.commute pstr1 pstr2.
Proof.
  move => n.
  move: (pstring_bicommute n).
  rewrite /commute_at /fingroup.commute /= /mulg /= => H0 pstr1 pstr2 psi H1 H2.
  case (H0 pstr1 pstr2) => H3.
  {
    apply H3.
  }
  {
    exfalso.
    assert (-C1 .* psi = psi) as HC. {
      move: H1 H2.
      unfold_stb => H1 H2.
    rewrite -{2}H1 -{2}H2.
    rewrite -Mmult_assoc png_int_Mmult H3.
    rewrite -png_int_Mmult Mscale_mult_dist_l Mmult_assoc.
    by rewrite H1 H2.
    }
    contradict HC.
    apply negate_change_state.
  }
Qed.

(* TODO This is not so efficient *)
(* Try using seq.take and drop  *)
Theorem stb_compose_alt:
  forall {n m: nat} (pstr1: PauliElement n) (pstr2: PauliElement m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n m ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stb  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  by rewrite H1 H2;
  reflexivity.
  all: try by rewrite - Nat.pow_add_r.
Qed.



Lemma stb_addition:
  forall {n: nat} (pstr: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  pstr ∝1 ψ1 ->
  pstr ∝1 ψ2 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  unfold_stb => n pstr psi1 psi2 H0 H1.
  (* Search (_ × (_ .+ _) ). *)
  rewrite Mmult_plus_distr_l.
  by rewrite H0 H1.
Qed.

Lemma stb_scale: 
  forall {n: nat} (pstr: PauliElement n) (ψ:  Vector (2^n)) (phase: C),
  pstr ∝1 ψ ->
  pstr ∝1 (phase .* ψ).
Proof.
  move => n pstr psi s.
  unfold_stb.
  rewrite Mscale_mult_dist_r.
  by move => ->.
Qed.

Lemma stb_cons:
  forall {n: nat} (pstr: PauliTupleBase n) (hp: PauliBase) (hv: Vector 2) (tv:  Vector (2^n)),
  pstr ∝1 tv ->
  stb_1 hp hv ->
  (One, [tuple of hp::pstr]) ∝1 (hv ⊗ tv).
Proof.
  move => n pstr hp hv tv.
  unfold_stb.
  Qsimpl.
  rewrite theadCons beheadCons.
  rewrite kron_mixed_product'; try auto.
  rewrite /stb_1 /act_1 /= /apply_1 /=; Qsimpl.
  move => H1 H2.
  rewrite H2.
  apply kron_simplify; auto.
Qed.

Ltac normalize_kron_notation :=
  repeat rewrite <- kron_assoc by auto 8 with wf_db;
  try easy.

Fact stb_04_fact:
  (One, [p Z, I, I, I]) ∝1 ∣0,0,0,0⟩.
Proof.
  replace ∣0,0,0,0⟩ with (∣0,0⟩ ⊗ ∣0,0⟩) by normalize_kron_notation.
  apply (stb_compose ([p1 Z, I]) ([p1 I, I])).
  all: unfold stb; simpl; Qsimpl; lma'; apply apply_n_wf.
  all: auto with wf_db.
Qed.

Definition shor_code_0 := (3 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

Ltac by_compose_stb s1 s2 :=
  apply (stb_compose_alt s1 s2); Qsimpl;
  (unfold stb; simpl; Qsimpl; lma');
  apply apply_n_wf; auto with wf_db.

(* Sing part of shor's code  *)
Lemma shor_code_part_stb:
  [p1 Z, Z, I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  apply stb_addition.
  by_compose_stb ([p1 Z, Z]) ([p1 I]).
  by_compose_stb ([p1 Z, Z]) ([p1 I]).
Qed.

(* basically the same as the original *)
(* but it is more efficient in computing *)
Theorem stb_compose_alt':
  forall {n m: nat} 
    (substr1: PauliElement n) (substr2: PauliElement m) (pstr: PauliElement (n + m))
    (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
    (pstr = compose_pstring substr1 substr2) ->
   substr1 ∝1 ψ1 -> substr2 ∝1 ψ2 -> pstr ∝1 (ψ1 ⊗ ψ2).
Proof. move => *. by subst; apply stb_compose_alt. Qed.


(* Solves goals like [p ... ] = compose_pstring [p ...] [p ...]  *)
Ltac by_compose_pstring :=
    rewrite /compose_pstring /mulg /=;
    apply injective_projections; simpl;
    [by easy | by apply /eqP].


(* Solve goals like [p1 I ...] = id_png n *)
Ltac by_unify_ids :=
  rewrite /id_png;
  apply injective_projections; 
  [by easy | rewrite /id_pn /=; by apply /eqP]. 
  

Set Default Timeout 5.

Goal [p1 Z, Z, I, I, I, I] ∝1 ∣ 0, 0, 0, 1, 1, 1⟩.
Proof.
  (* this is theoritical not necessary, *)
  (* but without it coq will hanging *)
  replace ∣ 0, 0, 0, 1, 1, 1⟩ with (∣ 0, 0⟩ ⊗ ∣0, 1, 1, 1⟩) by normalize_kron_notation .
  apply (stb_compose_alt'([p1 Z, Z]) ([p1 I, I, I, I])).
  by_compose_pstring. 
  apply (stb_compose_alt' ([p1 Z ]) ([p1 Z])). by_compose_pstring.
  all: auto with stab_db.
  replace ([ p1 I, I, I, I]) with (id_png 4) by by_unify_ids.
  apply one_stb_everything. 
  auto with wf_db.
Qed.

(* solve goals like [p1 I ...] ∝1 ∣... ⟩ *)
Ltac by_id_stb n :=
  match goal with
  | [ |- (?pstr ∝1 _) ] =>
    replace pstr with (id_png n) by by_unify_ids;
    apply one_stb_everything;
    auto with wf_db
  end.

Lemma shor_code_stb: [p1 Z, Z, I, I, I, I, I, I, I] ∝1 shor_code_0.
Proof.
  rewrite /shor_code_0.
  rewrite /kron_n kron_1_l.
  apply (stb_compose_alt' ([p1 Z, Z, I, I, I, I]) ([p1 I, I, I])). 
    by_compose_pstring.
  apply (stb_compose_alt' ([p1 Z, Z, I]) ([p1 I, I, I])).
    by_compose_pstring.
  apply shor_code_part_stb.
  all: try (by_id_stb 3%nat).
  auto with wf_db.
Qed.

(* 
This section introduces additional properties and lemmas related to stabilizers.
It defines the concept of "flip_sign" (anti-stabilizer) and provides examples and theorems 
demonstrating how stabilizers and anti-stabilizers interact under operations like tensor products.
Key results include the combination of two anti-stabilizers into a stabilizer and 
the symmetry of stabilizers under certain transformations. *)
(* Section MoreProps. *)

(* aka anti-stabilizer *)
Definition flip_sign {n: nat} (pstring: PauliElement n) (psi: Vector (2^n)) :=
  act_n n psi pstring = -1 .* psi.

(* A fancy symbol for "stabilize" *)
Notation "pstring ∝-1 ψ" := (flip_sign pstring ψ) (at level 50).

Example z1_f:
  [ p1 Z ] ∝-1  ∣ 1 ⟩.
Proof. by simpl_stbn. Qed.

Goal ∣ 1, 0, 1 ⟩ == kron (kron (ket 1) (ket 0)) (ket 1).
Proof. by []. Qed.

Goal ∣ 1, 0, 1 ⟩ = ∣ 1  ⟩ ⊗ ∣ 0 ⟩ ⊗ ∣ 1 ⟩.
Proof. by []. Qed.

Check ∣ 1, 0, 1 ⟩: Square 8.

(* two anti-stabilizers combine into a stabilizer under the tensor product *)
Theorem stb_even_slign_flip:
  forall {n m: nat} (pstr1: PauliElement n) (pstr2: PauliElement m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝-1 ψ1 ->
  pstr2 ∝-1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n m ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stb  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  move: H1 H2. rewrite /flip_sign /act_n /= /applyP => H1 H2.
  rewrite H1 H2 Mscale_kron_dist_r.
  restore_dims. 
  rewrite Mscale_kron_dist_l.
  rewrite Mscale_assoc.
  replace (-1 * -1) with C1 by lca.
  by Qsimpl.
  all: try by rewrite - Nat.pow_add_r.
Qed.

Example stb_z11:
  ([ p1 Z, Z]) ∝1 ∣ 1, 1 ⟩.
Proof.
  apply (stb_even_slign_flip ([p1 Z]) ( [p1 Z])).
  by simpl_stbn.
  by simpl_stbn.
Qed.

Theorem stb_symm_perm:
  forall {n: nat} (pstr: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  act_n n ψ1 pstr =  ψ2 ->
  act_n n ψ2 pstr =  ψ1 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  unfold_stb => n pstr psi1 psi2 H0 H1.
  rewrite /stb /act_n /= /applyP /=.
  rewrite Mmult_plus_distr_l.
  rewrite H0 H1.
  by rewrite Mplus_comm.
Qed.
  
  
(* Cannot do this because quantumlib do not provide a computable process *)
(* of Mmult *)
Fail Definition stb_s {n: nat} (psi: Vector (2^n)) :=
  [set x | stb x psi].

(* Instead, we can define using Coq subtype  *)
Definition stb_s {n: nat} (psi: Vector (2^n)) := { 
  op: PauliElement n | op ∝1 psi \/ exists (a b:PauliElement n), a ∝1 psi /\ b ∝1 psi /\ op = mulg a b 
}.

Theorem stb_s_correct n:
  forall (psi: Vector (2^n)) (gen: stb_s psi),
    `gen ∝1 psi.
Proof.
  move => psi [op [Hop1 | Hop2]].
  - apply Hop1.
  - move: Hop2 => [a [b H]].
    move: H => [Ha [Hb Hc]].
    subst. simpl.
    by apply stb_closed.
Qed.

(* an n-qubit stabilizer group is any subgroup of P^n that is 
abelian (commutative) and dos not contain -1  *)
Definition is_stb_set {n} (S: { set PauliElement n }) :=
  forall a b, a \in <<S>> -> b \in <<S>> -> mulg a b = mulg b a /\ 
  ~~ (minus_id_png n \in << S >>).

Definition is_stb_set_spec {n} (S: {set PauliElement n}) (v: Vector (2^n)):=
  forall x, x \in << S >> -> x ∝1 v.

(* TODO: consider make this equivalent *)
Theorem is_stb_set_correct:
  forall {n} (S: {set PauliElement n}),
  (exists v, WF_Matrix v /\ is_stb_set_spec S v) <-> is_stb_set S.
Proof.
  move => n S.
  split.
  {
    rewrite /is_stb_set_spec /is_stb_set /=.
    move => [v [Hwf H]] a b Ha Hb.
    move: (H a Ha) => Has.
    move: (H b Hb) => Hbs.
    split.
    - move: (stabilizer_must_commute a b v Has Hbs).
      rewrite /fingroup.commute /= /mulg /= => H0.
      apply H0.
    (* - move: (stb_group_no_m1 a b v Ha Hb) => H0.
      apply H0 in Hwf; clear H0. *)
    - unfold minus_id_png.
      (* Search (_ \in << _ >>). *)
      rewrite /negb.
      move: (stb_group_no_m1 a b v Has Hbs Hwf) => H0.
      (* Ha : a  \in <<S>>
      Hb : b  \in <<S>>
      Has : a ∝1 v
      Hbs : b ∝1 v
      H0 : mulg a b <> (NOne, id_pn n) *)
      (* Do not know how to do this proof in ssreflect *)
      (* TODO: Ask Zoe *)
      admit.
  }
  {
    rewrite /is_stb_set /is_stb_set_spec /= => H.
    (* for this part, we need a way to construct the eigenvector
    of a and b  *)
    (* TODO Maybe Ask Udaya for this *)
Abort.

(* The weight of a stabilizer group is the number of qubits that are not I *)
(* in the stabilizer group *)
Definition weight {n} (pt: PauliTupleBase n): nat := 
  count (fun x => x != I) pt.

Goal weight ([p Z, Z, I]) = 2%nat.
Proof.
  by rewrite /weight.
Qed.

(* Describe the error detection ability *)
Section Syndrome.

(* The number of physical qubits *)
Variable n: nat.
(* The generator set *)
Variable g: {set PauliElement n}.
Hypothesis H: is_stb_set g.

Definition with_1 (pt: PauliTupleBase n): PauliElement n := (One, pt).

(* an detectable error is an error that  *)
(* note that we usually require the phase of error operator to be 1 *)
(* Otherwise, it will be Z (negate phase) *)
Definition detectable (E: PauliTupleBase n) := 
  exists (pstr: PauliElement n), pstr \in g /\ 
  (mulg pstr (with_1 E) != mulg (with_1 E) pstr).


(* The dimension of the code space 
, which is typically, the numbef of physical qubits - number of independent generator *)
(* A future work is to prove this holds in principle *)
Definition dimension := subn n #|g|.

(* the distance of a generator = weight(E)  *)
(* where E is an error and E cannot be detected *)
Definition distance_spec (E: PauliTupleBase n) (d: nat) :=
  not (detectable E) /\ weight E = d.

(* The distance of a code is the minimal weight of an undetectable error *)
Definition distance (d: nat):= 
  exists (E: PauliTupleBase n), distance_spec E d /\
    forall (E': PauliTupleBase n) d', distance_spec E' d' -> leq d d'.

(* A sound difinition of distance, which does not require to show 
  the error is the minimum in the whole world  
*)
Definition distance_s (d: nat):= 
  exists (E: PauliTupleBase n), distance_spec E d.
  

(* These definitions are very axiomatic and not verified from principle *)
(* It's nice if we can verify their physical meanning *)
(* Prove that detectable is correct *)
End Syndrome.

Lemma not_detactable n:
  forall (E: PauliTupleBase n) (s: {set PauliElement n}),
  ( exists (pstr: PauliElement n), 
    pstr \in s /\  mulg pstr (with_1 _ E) = mulg (with_1 _ E) pstr)
    -> not (detectable _ s E) 
    .
Admitted. (* Related to generated group *)


Lemma stb_generator {n}:
  forall (g: { set (PauliElement n) }) (v: Vector (2^n)), 
    (forall x, x \in g -> x ∝1 v) -> forall y, y \in <<g>> -> y ∝1 v.
Admitted. (* Related to generated group *)

Check kron_mixed_product.

Check ∣ 0, 0 ⟩: Vector 4.
Check ∣ 0 ⟩.

Lemma pn_int_apply_cons:
  forall {n} (p: PauliBase) (operator: PauliOperator n)  
    (head: Vector 2) (tail: Vector (2^(n))),
  (* A ⊗ B *)
  pn_int ([tuple of p::operator]) × (head ⊗ tail) = 
  ((p1_int p) × head) ⊗ ((pn_int operator) × tail).
Proof.
  move => n p pt vh vt.
  rewrite PauliProps.pn_int_cons.
  by rewrite kron_mixed_product.
Qed.