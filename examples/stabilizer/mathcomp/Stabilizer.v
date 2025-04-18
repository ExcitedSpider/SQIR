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

Definition PString := GenPauliTuple.

Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-1' x1 , .. , xn ]" := (NOne, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'pi' x1 , .. , xn ]" := (Img, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-i' x1 , .. , xn ]" := (NImg, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Definition stb {n:nat} (pstring: PString n) (psi: Vector (2^n)):= 
  act_n n psi pstring = psi.

(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stb pstring ψ) (at level 50).

Ltac simpl_stbn := 
  rewrite /stb /act_n /apply_n /=;
  Qsimpl;
  try (lma'; try (apply apply_n_wf);auto with wf_db).

Check [p Z, Z, X, Y].
Check [p1 Z, Z, X, Y].

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
  rewrite /stb /act_n /= /apply_n.
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
    (substr1: PString n) (substr2: PString m) (pstr: PString (n + m))
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

End StbExample.

(* theories related to syndrome detection *)
Section Syndrome.

(* aka anti-stabilizer *)
Definition flip_sign {n: nat} (pstring: PString n) (psi: Vector (2^n)) :=
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
Theorem even_sign_flip_stb:
  forall {n m: nat} (pstr1: PString n) (pstr2: PString m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := compose_pstring pstr1 pstr2 in
  pstr1 ∝-1 ψ1 ->
  pstr2 ∝-1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Admitted.

Example stb_z11:
  ([ p1 Z, Z]) ∝1 ∣ 1, 1 ⟩.
Proof.
  apply (even_sign_flip_stb ([p1 Z]) ( [p1 Z])).
  by simpl_stbn.
  by simpl_stbn.
Qed.

Theorem perm_symm_stb:
  forall {n: nat} (pstr: PString n) (ψ1 ψ2:  Vector (2^n)),
  act_n n ψ1 pstr =  ψ2 ->
  act_n n ψ2 pstr =  ψ1 ->
  pstr ∝1 (ψ1 .+ ψ2).
Admitted.
  
(* This is part of the [4,4,2] codewords which has to be proved *)
(* by perm_symm_stb *)
Example stb_422_part0:
  [p1 X,X,X,X] ∝1  (∣ 0, 0, 1, 1 ⟩ .+ ∣ 1, 1, 0, 0 ⟩).
Proof.
  apply perm_symm_stb.
  - rewrite /= /apply_n /=. Qsimpl. 
    repeat rewrite kron_assoc;  auto with wf_db.
    rewrite kron_mixed_product; Qsimpl.
    (* This does not work. why? TODO *)
    rewrite !MmultX1 !MmultX0.
    by rewrite -!kron_assoc; auto with wf_db.
  - rewrite /= /apply_n /=. Qsimpl. 
    repeat rewrite kron_assoc;  auto with wf_db.
    rewrite kron_mixed_product; Qsimpl.
    rewrite !MmultX1 !MmultX0.
    by rewrite -!kron_assoc; auto with wf_db.
Qed.


End Syndrome.



