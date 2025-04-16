(* The stabilizer theories *)

(* This was copied from barebone/Stabilizer.v 
   and needs necessary refatorization before it can work *) 


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import PauliGroup.
Import P1Group.
Import P1GGroup.
Import PNGroup.
Import PNGGroup.

Definition PString := GenPauliTuple.

Notation "[ 'tuple' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

Definition stb {n:nat} (pstring: GenPauliTuple n) (psi: Vector (2^n)):= 
  act_n n psi pstring = psi.


(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stb pstring ψ) (at level 50).

Ltac simpl_stbn := 
  rewrite /stb /act_n /apply_n /=;
  Qsimpl;
  try (lma'; auto with wf_db).


Check [tuple Z, Z, X, Y].

(* Z stabilises ∣0⟩ *)
Example stb_z0:
  (One, [tuple Z]) ∝1 ∣0⟩.
Proof. by simpl_stbn. Qed.

Example stb_z00:
  (One, [tuple Z , Z]) ∝1 ∣0,0⟩.
Proof. by simpl_stbn. Qed.

Example stb_z000:
  (One, [tuple Z,Z,Z]) ∝1 ∣0,0,0⟩.
Proof. by simpl_stbn. Qed. 


(* For length >= 4, it becomes lagging *)
(* Try it if you trust your machine *)
(* Example stb_z0000: *)
(*   (One, [tuple of Z::Z::Z::Z::[]]) ∝1 ∣0,0,0,0⟩. *)
(* Proof. by simpl_stbn. Qed. *) 

(* -Z stabilises ∣1⟩ *)
Example stb_nz0:
  (NOne, [tuple Z]) ∝1 ∣1⟩.
Proof. by simpl_stbn. Qed.

(* X stabilize the bell ψ *)
Example stb_xbell:
  stb (One, [tuple X]) ( 1/√2 .* (∣0⟩ .+ ∣1⟩)).
Proof. by simpl_stbn. Qed.

(* Y stabilize the |i> ψ *)
Example stb_yibell:
  stb (One, [tuple Y]) ( 1/√2 .* (∣0⟩ .+ Ci .* ∣1⟩)).
Proof. by simpl_stbn. Qed. 

Lemma one_stb_everything:
  forall {n: nat} (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb (id_png n) ψ.
Proof.
  rewrite /stb => n psi Hwf.
  remember (act_id_le _ _ _ (act_n n)).
  apply mat_equiv_eq.
  rewrite /act_n /apply_n /=.
  2: auto.
  (* Search WF_Matrix ".*". *)
  apply WF_mult. 2: auto. 
  apply WF_scale. 
  apply PNProps.pn_int_wf.
  auto. 
Qed.

(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
Lemma inv_stb:
  forall {n: nat} (pstr: GenPauliTuple n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stb pstr ψ -> stb (pstr^-1) ψ.
Proof.
  intros n pstr ψ Hwf Hstb.
  unfold stb in *.
  rewrite <- Hstb at 1.
  rewrite /act_n /apply_n /=.
  rewrite <- Mmult_assoc.
  (* Search png_int "×". *)
  rewrite png_int_Mmult.
  rewrite mulVg /=.
  apply one_stb_everything; easy.
Qed.

Print Vector.

Ltac unfold_stb := 
rewrite /stb /act_n /apply_n /=.



(* 
If we take the tensor product of a two states, with stabiliser groups A and B (respectively), then the resulting tensor product state has stabiliser group given by the cartesian product A × B. 
*)
Theorem stb_compose:
  forall {n: nat} (pstr1 pstr2: GenPauliTuple n) (ψ1 ψ2:  Vector (2^n)),
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
  (One, [tuple X,X]) ∝1 ∣Φ+⟩ /\ (One, [tuple Z,Z]) ∝1 ∣Φ+⟩.
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
  (One, [tuple Z, Z, I]) ∝1 ∣000⟩ /\ (One, [tuple Z, Z, I]) ∝1 ∣000⟩.
Proof.
  split.
  - unfold_stb; Qsimpl.
    solve_matrix.
  - unfold_stb; Qsimpl.
    solve_matrix.
Qed.

Theorem stb_closed: 
  forall {n: nat} (pstr1 pstr2: PString n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  mulg pstr1 pstr2 ∝1 ψ
.
Proof.
  unfold_stb => n pstr1 pstr2 psi H0 H1.
  rewrite -png_int_Mmult.
  by rewrite Mmult_assoc H1 H0.
Qed.

(* This is harder than expected *)
(* Lemma pvec_id_interpret: *)
(*   forall {n}, *)
(*   pvec_to_matrix (const I n) = Matrix.I (2^n). *)
(* Proof. *)
(*   intros. *)
(*   induction n. *)
(*   { *)
(*     easy. *) 
(*   } *)
(*   { *)
(*     simpl; Qsimpl. *) 
(*     assert (Matrix.I (2 ^ n + (2 ^ n + 0)) = Matrix.I 2 ⊗ Matrix.I (2 ^ n)). *)
(*     { *)
(*       symmetry. *)
(*       apply id_kron. *)
(*     } *)
(*     rewrite H. *)
(*     rewrite IHn. *)
(*     reflexivity. *)
(*   } *)
(* Qed. *)

(* Theorem stb_by_id: *) 
(*   forall {n: nat} (ψ:  Vector (2^n)), *) 
(*   WF_Matrix ψ -> *)
(*   (One, Vector.const I n) ∝1 ψ. *)
(* Proof. *)
(*   intros. *)
(*   unfold stb. *)
(*   simpl. *)
(*   Qsimpl. *)
(*   (1* Search Matrix.I. *1) *)
(*   assert (pvec_to_matrix (const I n) = Matrix.I (2^n)) by apply pvec_id_interpret. *)
(*   rewrite H0. *)
(*   apply Mmult_1_l. *)
(*   easy. *)
(* Qed. *)

(* 
  TODO: This is apparent but actually hard to prove
  As QuantumLib does not provide usable lemmas about ineq
  *)
Lemma negate_change_state n:
  forall (ψ:  Vector n),
  -C1 .* ψ <> ψ.
Admitted.

(* there is no -1 in any stabilizer group *)
Theorem stb_group_no_m1: 
  forall {n: nat} (pstr1 pstr2: PString n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  WF_Matrix ψ ->
  mulg pstr1 pstr2 <>  (NOne, id_pn n).
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


Locate commute.

Lemma pair_inj:
(forall T R (a b: T) (x y: R), (a, x) = (b, y) -> a = b /\ x = y).
  {
    intros.
    by inversion H.
  }
Qed.

(* Cannot find this in Mathcomp *)
Lemma eq_by_contra n (a b : PString n):
  (a != b -> False) -> a = b.
Proof.
  by apply contra_not_eq.
Qed.
  
Import ExtraSpecs.

Lemma phase_comm n:
 forall (sx sy:phase) (pt: PauliTuple n),
 (* mulg cannot be inferenced here *)
 mult_png (sx, pt) (sy, pt) = mult_png (sy, pt) (sx, pt).
Proof.
  move => sx sy.
  by case sx; case sy.
Qed.

Import PNGroup.

Lemma commute_png_implies n:
  forall (px py: phase) (tx ty: PauliTuple n),
  commute_at mult_png (px, tx) (py, ty)-> mult_pn tx ty = mult_pn ty tx /\
   get_phase_png (px, tx) (py, ty) =
	get_phase_png (py, ty) (px, tx).
Proof.
  rewrite /commute_at /mult_png /= => px py tx ty H.
  apply pair_inj in H.
  destruct H as [H1 H2].
  by rewrite H1 H2.
Qed.

Lemma PauliOp_bicommute:
  forall x y,
  get_phase x y = get_phase y x \/
  phase_int (get_phase x y) = -C1 * phase_int (get_phase y x).
Proof.
  move => x y.
  case x; case y; rewrite /=.
  all: try(by left).
  all: try(right; lca).
Qed.

Lemma mult_p1_comm:
  commutative mult_p1.
Proof.
  rewrite /commuteg => x y.
  by case x; case y.
Qed.


(* all PauliOperators are either commute or anticommute *)
(* TODO: the definition of anticommute is too loose. *)
(* find something in mathcomp to make it work *)
Lemma pstring_bicommute n:
  forall (x y: PString n), commute_at mulg x y \/ 
  png_int (mulg x y) = -C1 .* png_int (mulg y x).
Proof.
  induction n.
  {
    move =>[sx px] [sy py].
    left.
    rewrite (trivial_tuples px py) /commute_at.
    by rewrite /mulg /= phase_comm.
  }
  {
    move => [px tx] [py ty].
    case: tx / tupleP => hx tx.
    case: ty / tupleP => hy ty.
    move: (IHn (px, tx) (py, ty)) => IHn'.
    rewrite /= /commute_at /= /mulg /= /mult_png !mult_pn_cons.
    destruct IHn'.
    apply commute_png_implies in H.
    destruct H as [Hmtuple  Hmphase].
    {
      (* tail commute *)
      rewrite !get_phase_png_cons !Hmphase.
      rewrite !Hmtuple.
      case (PauliOp_bicommute hx hy) => Hhead.
      - left; by rewrite !Hhead mult_p1_comm. 
      - right. rewrite !phase_int_comp Hhead !Mscale_assoc !Cmult_assoc. 
          by rewrite !beheadCons !theadCons mult_p1_comm.
    }
    {
      (* tail anticommute *)
      case (PauliOp_bicommute hx hy) => Hhead.
      - (* head commute *)
        right. admit.
      - left.
        assert (phase_neg:
          forall x y, phase_int x = -C1 * phase_int y -> 
            x = mult_phase NOne y
        ) by admit.
        apply phase_neg in Hhead.
        rewrite !get_phase_png_cons !Hhead.
        assert (pstring_neg: 
          forall n (x y: PString n), 
          png_int x = -C1 .* png_int y ->
            x = mult_png (NOne, id_pn n) y
        ) by admit.
        apply pstring_neg in H.
        rewrite /mulg /= /mult_png in H.
        apply pair_inj in H.
        destruct H.
        rewrite H H0 mult_p1_comm.
        rewrite mult_pn_id /get_phase_png get_phase_pn_id.
        rewrite mult_phase_id !mult_phase_assoc.
        by rewrite (mult_phase_comm _  NOne) mult_phase_assoc.
    }
Admitted.
      
  

Theorem stabilizer_must_commute: 
  forall {n: nat} (pstr1 pstr2: PString n) (ψ:  Vector (2^n)),
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


Theorem stb_compose_alt:
  forall {n m: nat} (pstr1: PString n) (pstr2: PString m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
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
  forall {n: nat} (pstr: PString n) (ψ1 ψ2:  Vector (2^n)),
  pstr ∝1 ψ1 ->
  pstr ∝1 ψ2 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  unfold_stb => n pstr psi1 psi2 H0 H1.
  (* Search (_ × (_ .+ _) ). *)
  rewrite Mmult_plus_distr_l.
  by rewrite H0 H1.
Qed.

Section StbExample.

Ltac normalize_kron_notation :=
  repeat rewrite <- kron_assoc by auto 8 with wf_db;
  try easy.

Fact stb_04_fact:
  (One, [tuple Z, I, I, I]) ∝1 ∣0,0,0,0⟩.
(* 
  manually use stb_compose to break down large states
  we'll give a tactic later
  *)
Proof.
  replace ∣0,0,0,0⟩ with (∣0,0⟩ ⊗ ∣0,0⟩) by normalize_kron_notation.
  apply (stb_compose (One, [tuple Z, I]) (One, [tuple I, I])).
  all: unfold stb; simpl; Qsimpl; lma'.
Qed.

Definition shor_code_0 := (3 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

(* Check (
  (∣0,0,0⟩ .+ ∣1,1,1⟩) ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)
). *)

Check 
  (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ 
  (2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

Check (One, p[Z, Z]): PString 2.
Check (One, p[I]): PString 1.

Ltac by_compose_stb s1 s2 :=
  apply (stb_compose_alt s1 s2); Qsimpl;
  (unfold stb; simpl; Qsimpl; lma').

Ltac by_identity n := (* TODO: how to get n from the type*)
    match goal with
    | [ |- ((One, ?p) ∝1 _) ] =>
        replace (One, p) with (𝟙 n) by reflexivity;
        apply one_stb_everything;
        auto with wf_db
    end.

Fact shor_code_part_stb:
  (One, p[Z, Z, I])∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  apply stb_addition.
  by_compose_stb (One, p[Z, Z]) (One, p[I]).
  by_compose_stb (One, p[Z, Z]) (One, p[I]).
Qed.
  
Fact shor_code_stb_fact:
  (One, p[Z, Z, I, I, I, I, I, I, I]) ∝1 shor_code_0.
Proof.
  (* This could stuck Coq *)
  (* by_compose_stb  (One, p[Z, Z, I, I, I, I]) (One, p[I, I, I]). *)
  apply (stb_compose_alt (One, p[Z, Z, I, I, I, I]) (One, p[I, I, I])).
  Qsimpl.
  apply (stb_compose_alt (One, p[Z, Z, I]) (One, p[I, I, I])).
  - (* [Z; Z; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩)  *)
    apply shor_code_part_stb.
  - (* [I; I; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩) *)
    by_identity 3%nat.
  - by_identity 3%nat.
Qed.

