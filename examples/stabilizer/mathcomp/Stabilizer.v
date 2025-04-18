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
Require Import WellForm.

Definition PString := GenPauliTuple.

Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Definition stb {n:nat} (pstring: PString n) (psi: Vector (2^n)):= 
  act_n n psi pstring = psi.

(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stb pstring ψ) (at level 50).

Ltac simpl_stbn := 
  rewrite /stb /act_n /apply_n /=;
  Qsimpl;
  try (lma'; auto with wf_db).


Check [p Z, Z, X, Y].
Check [p1 Z, Z, X, Y].

(* Z stabilises ∣0⟩ *)
Example stb_z0:
  (One, [p Z]) ∝1 ∣0⟩.
Proof. by simpl_stbn. Qed.

Example stb_z00:
  (One, [p Z , Z]) ∝1 ∣0,0⟩.
Proof. by simpl_stbn. Qed.

Example stb_z000:
  (One, [p Z,Z,Z]) ∝1 ∣0,0,0⟩.
Proof. by simpl_stbn. Qed. 


(* For length >= 4, it becomes lagging *)
(* Try it if you trust your machine *)
(* Example stb_z0000: *)
(*   (One, [p of Z::Z::Z::Z::[]]) ∝1 ∣0,0,0,0⟩. *)
(* Proof. by simpl_stbn. Qed. *) 

(* -Z stabilises ∣1⟩ *)
Example stb_nz0:
  (NOne, [p Z]) ∝1 ∣1⟩.
Proof. by simpl_stbn. Qed.

(* X stabilize the bell ψ *)
Example stb_xbell:
  stb (One, [p X]) ( 1/√2 .* (∣0⟩ .+ ∣1⟩)).
Proof. by simpl_stbn. Qed.

(* Y stabilize the |i> ψ *)
Example stb_yibell:
  stb (One, [p Y]) ( 1/√2 .* (∣0⟩ .+ Ci .* ∣1⟩)).
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
  apply pn_int_wf.
  auto. 
Qed.

(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
Lemma inv_stb:
  forall {n: nat} (pstr: PString n) (ψ:  Vector (2^n)),
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
  forall {n: nat} (pstr1 pstr2: PString n) (ψ1 ψ2:  Vector (2^n)),
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

Import Commutativity.


(* there is no -1 in any stabilizer group *)
Theorem stb_group_no_m1: 
  forall {n: nat} (pstr1 pstr2: PString n) (ψ:  Vector (2^n)),
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

(* TODO This is not so efficient *)
(* Try using seq.take and drop  *)
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

Definition take_pstr { n } m (pstr: PString n): PString (minn m n) :=
  (pstr.1, [tuple of take m pstr.2]).
  
Definition drop_pstr { n } m (pstr: PString n): PString (n - m) :=
  (One, [tuple of drop m pstr.2]).

Theorem stb_compose_split {n: nat} :
  forall m (pstr: PString n) (ψ1:  Vector (2^m)) (ψ2:  Vector (2^(n - m))),
  take_pstr m pstr ∝1 ψ1 ->
  drop_pstr m pstr ∝1 ψ2 ->
  pstr ∝1 (ψ1 ⊗ ψ2).
Admitted.


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
  (One, [p Z, I, I, I]) ∝1 ∣0,0,0,0⟩.
Proof.
  replace ∣0,0,0,0⟩ with (∣0,0⟩ ⊗ ∣0,0⟩) by normalize_kron_notation.
  apply (stb_compose ([p1 Z, I]) ([p1 I, I])).
  all: unfold stb; simpl; Qsimpl; lma'; apply apply_n_wf.
  all: auto with wf_db.
Abort.

Definition shor_code_0 := (3 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

Ltac by_compose_stb s1 s2 :=
  apply (stb_compose_alt s1 s2); Qsimpl;
  (unfold stb; simpl; Qsimpl; lma');
  apply apply_n_wf; auto with wf_db.


Fact shor_code_part_stb:
  [p1 Z, Z, I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  apply stb_addition.
  by_compose_stb ([p1 Z, Z]) ([p1 I]).
  by_compose_stb ([p1 Z, Z]) ([p1 I]).
Qed.

Fact shor_code_stb_fact:
  [p1 Z, Z, I, I, I, I, I, I, I] ∝1 shor_code_0.
Proof.
(* 
  apply (stb_compose_alt ([p1 Z, Z, I, I, I, I]) ([p1 I, I, I])).
  (* apply (stb_compose_alt ([p1 Z, Z, I, I, I, I]) ([p1 I, I, I])).
  Qsimpl.
  apply (stb_compose_alt (One, p[Z, Z, I]) (One, p[I, I, I])).
  - (* [Z; Z; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩)  *)
    apply shor_code_part_stb.
  - (* [I; I; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩) *)
    by_identity 3%nat.
  - by_identity 3%nat. *)
Qed. *)


(*
Ltac by_identity n := (* TODO: how to get n from the type*)
    match goal with
    | [ |- ((One, ?p) ∝1 _) ] =>
        replace (One, p) with (𝟙 n) by reflexivity;
        apply one_stb_everything;
        auto with wf_db
    end.

    Fact shor_code_stb_fact:
  (One, [p Z, Z, I, I, I, I, I, I, I]) ∝1 shor_code_0.
Proof.
  (* This could stuck Coq *)
  (* by_compose_stb  (One, p[Z, Z, I, I, I, I]) (One, p[I, I, I]). *)
  apply (stb_compose_alt (One, [p Z, Z, I, I, I, I]) (One, [p I, I, I])).
  Qsimpl.
  apply (stb_compose_alt (One, p[Z, Z, I]) (One, p[I, I, I])).
  - (* [Z; Z; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩)  *)
    apply shor_code_part_stb.
  - (* [I; I; I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩) *)
    by_identity 3%nat.
  - by_identity 3%nat.
Qed.

  

 *)

End StbExample.
