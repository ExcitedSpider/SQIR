(* 
This file describe pauli operator as quantum observale.
Important Definition:
- "'Meas P on psi --> m" := measuring P on state psi yields m
*)
From QuantumLib Require Import Quantum.
From mathcomp Require Import seq tuple fingroup eqtype.
From mathcomp Require Import ssreflect ssrbool.
Require Import PauliGroup.
Require Import Action.
Require Import Assumption.
Require Import Stabilizer.
Require Import WellForm.
Require Import PauliProps.
Open Scope form_scope.
Set Bullet Behavior "Strict Subproofs".

(* An operator is hermitian if it is self-adjoint   *)
Definition hermitian {n:nat} (H: Square (2^n)): Prop :=
  H† = H.

(* meas_to m M ψ captures the projective measurement postulate:
  if ψ is an eigenvector of Hermitian observable M with eigenvalue m, 
  then measuring M on ψ yields m with certainty (probability = 1). *)
Definition meas_to {n} (m: C) (M: Square (2^n)) (psi: Vector (2^n)) :=
  WF_Matrix M /\ hermitian M /\ M × psi = m .* psi.

(* 
  This section verifies the meas_to is consistent 
  with quantumlib measurement definition .
  Quantumlib only defines measurement in computational basis and if we 
  want to achieve verification, we neeed to map the state and result to 
  computational basis based on the observable.  

  Which i find very hard to do because:
  - it involves a lot of theories in linear algebra, which we don't have in quantumlib
  - the theory is non-trivial. 
  - i don't have much time
  - The projective measurement postulate itself can be considered as an axiom,
    i.e. it is more foundamental in theory.
  - Quantumlib does not have sparse measurement primitive.
    e.g. for 4 qubits, only measure the 2nd and the 4th 
      (related to observables like Z2Z4 )
  - And also, i find it is not our focus of research. 

  A better way of doing this is that, make a more fundamental definition of 
  measurement. 
  For example, we can have _Quantum Measurement Postulate_[1], and then use this
  definition to verify both measurements are correct, that is, they are be proved
  by the postulate.

  It will be more suitable to be considerred as a foundational change to quantumlib.

  [1]: Nielsen, M. A., & Chuang, I. L. (2010). Quantum computation and quantum information. 
  Cambridge university press. Page 87.
*)
Section QuantumLibMeas.

Require Import QuantumLib.Measurement.
(* QuantumLib only supports measure in computational basis *)
(* We need to apply reduction operations to measure *)
Variable (n:nat).

(* Perform basis tranformation (projection) in SQIR according to the observable *)
Variable proj_basis: Square (2^n) -> Vector (2^n) -> Vector (2^n).
(* Map the eigenvalue measurement result to a basic bitstring *)
Variable proj_result: Square (2^n) -> C -> Vector (2^n).

(* 
  This theorem tris verifies that measurement by observable
  can be converted to measurement on basis state by projection
 *)
Theorem meas_to_correct:
  forall (m: C) (M: Square (2^n)) (psi psi': Vector (2^n)) ,
  meas_to m M psi ->
  proj_basis M psi = psi' ->
  probability_of_outcome psi' (proj_result M m) = 1.
Abort.

End QuantumLibMeas.

(* because every pauli operator is hermitian, 
  they can all be viewed as observable *)
Notation PauliObservable := PauliTuple.

Lemma pauli_base_hermitian:
  forall (p: PauliBase),
  @hermitian 1%nat (p1_int p).
Proof.
  move => p.
  rewrite /hermitian.
  case p; simpl.
  apply id_adjoint_eq.
  apply σx_hermitian.
  apply σy_hermitian.
  apply σz_hermitian.
Qed.

Fact pauli_hermitian {n} :
  forall (operator: PauliTupleBase n), hermitian (pn_int operator).
Proof.
  rewrite /hermitian /png_int /PauliObservable //= => pt.
  induction n.
  - by rewrite tuple0 /= id_adjoint_eq.
  - case: pt / tupleP => hx tx.
    rewrite /= theadCons .
    restore_dims.
    by rewrite kron_adjoint IHn pauli_base_hermitian.
Qed.



(* 
If a quantum state ψ is stabilized by a Pauli operator p (i.e., p ψ = ψ), 
then measuring the corresponding observable yields outcome 1 with certainty.
*)
Theorem stb_meas_to_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> meas_to 1 (pn_int p) psi.
Proof.
  split => H.
  - rewrite /meas_to.
    split. apply pn_int_wf.
    split. apply pauli_hermitian.
    apply PauliOperator_stb in H.
    rewrite H. by Qsimpl.
  - move: H. 
    rewrite /meas_to => [[_ [_ H]]].
    rewrite /stb /act_n /applyP /=. Qsimpl.
    rewrite H. by Qsimpl.
Qed.

(* 
  What we are really interesting is to use pauli operator
  as observables.
 *)
Definition meas_p_to {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :=
  (pn_int P) × psi = m .* psi.

Theorem meas_p_to_correct {n}:
  forall (m:C) (P: PauliOperator n) (psi: Vector (2^n)),
  meas_p_to m P psi <-> meas_to m (pn_int P) psi.
Proof.
  move => m P psi.
  rewrite /meas_p_to /meas_to.
  split.
  - move => H.
    split => //. apply pn_int_wf.
    split => //. apply pauli_hermitian.
  - move => [_ [_ H]].
    exact H.
Qed. 

Corollary stb_meas_p_to_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> meas_p_to 1 p psi.
Proof.
  split => HH.
  - rewrite meas_p_to_correct.
    by apply stb_meas_to_1.
  - rewrite meas_p_to_correct in HH.
    by rewrite stb_meas_to_1.
Qed.

Notation "''Meas' P 'on' psi '-->' m " := (meas_p_to m P psi)
 (at level 8) : form_scope.

(* this line is required *)
Import all_pauligroup. 

(* Example: Measure Z1Z2 on 00 yields 1. *)
Check 'Meas ([p Z, Z]) on ∣ 0, 0 ⟩ --> 1.

Section Eigenvalue. 

Lemma p1_involutive :
  forall (p: PauliBase), mulg p p = I.
Proof. by move => p; case p. Qed.

(* 
  this one should be moved to PauliProps.v
  However, the apply/eqP does not work there.
  and I don't know why.
*)
Lemma pauli_involutive {n}:
  forall (op: PauliTupleBase n),
  (mulg op op) = (id_pn n).
Proof.
  move => op.
  induction n.
  rewrite tuple0 /id_pn /=. 
  by apply /eqP.
  case: op / tupleP => h t.
  rewrite /mulg /= mult_pn_cons.
  rewrite /mulg /= in IHn.
  rewrite IHn.
  change mult_p1 with (@mulg PauliBase). 
  rewrite pn_idP.
  by rewrite p1_involutive.
Qed.

Lemma get_phase_pn_involutive n:
  forall (op: PauliTupleBase n),
  get_phase_pn op op = One.
Proof.
  move => op.
  induction n.
    by rewrite tuple0; apply /eqP.
   case: op / tupleP => h t.
   rewrite get_phase_pn_cons IHn.
   by case h.
Qed.

(* Pauli operators *)
Theorem operator_eigenvalue {n}:
  forall (op: PauliOperator n) (psi: Vector (2^n)) (lambda: C),
    applyP psi op = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Proof.
  move => op psi lambda Happ.
  rewrite /applyP in Happ.
  remember (png_int _) as m.
  apply (involutive_eigenvalue _ m psi).
  subst.
  move: (pauli_involutive op).
  rewrite /mulg /= => H.
  Qsimpl.
  rewrite -pn_int_Mmult H get_phase_pn_involutive PauliProps.id_pn_int //=. 
  by Qsimpl. by [].
Qed.

End Eigenvalue.

Require Import ExtraSpecs.

(* The Born rule is a postulate of quantum mechanics that gives 
the probability that a measurement of a quantum system will yield 
a given result. *)
Section BornRule.

Variable (n: nat).

(*  (The Born Rule) Let Pm be a projector. Upon measuring a state ψ, 
the probability of successful measurment is ⟨ ψ | Pm | ψ ⟩. 
https://en.wikipedia.org/wiki/Born_rule *)
Definition prob_meas_projector 
  (proj: Projector) (psi: Vector (2^n)) :=
 inner_product psi ((proj.(P)) × psi).

(* Nielsen, M. A., & Chuang, I. L. (2010). Quantum computation and quantum
 information. Cambridge university press. Page 72. *)
Definition spectrual_decomposition 
(M: Square (2^n)) (list: nat -> prod C (Projector)) (k:nat):=
  M = big_sum (
    fun k => 
      let item := list k in 
      let m := fst item in
      let projector := snd item in
      m .* projector.(P) 
  ) k.

(* This one attempt to verify the correctness of `meas_to m M psi` *)
(* If `meas_to m M psi` holds,  *)
(* Then the component (m, P) in the specturm decomposition of M *)
(* have the property that *)
(* The probability of getting the result m by measuring P is 1 *)
(* That is, it verifies meas_to is the sufficient condition that *)
(* Measuring P on psi yeilds m with certainty *)
(* However it does look horrible and i don't want to attempt *)
(* The main problem is that `big_sum` from quantumlib restricts *)
(* the set of specturm components to be represented in nat -> matrix.  *)
(* And this makes expression of member relation extremely complicated *)
(* It would be better to use some advanced representation like {set} *)
(* from mathcomp. *)
(* But this requires a major refactor of quantumlib, which is out of the scope *)
(* of our research *)
Theorem meas_to_correct':
  forall m (M: Square (2^n)) (psi: Vector (2^n)) setProj k,
  meas_to m M psi ->
  spectrual_decomposition M setProj k ->
  exists (i: nat), le i k /\ fst (setProj i) = m /\
    let P := (snd (setProj i)) in
    prob_meas_projector P psi = 1.
Abort.

End BornRule.


(* Notation Just for readability *)
Notation ErrorOperator := PauliOperator.
Notation Observable := PauliOperator.

Lemma meas_p_to_unique {n}:
  forall (phi: Vector (2^n)) (ob: Observable n)  (r q: C),
  'Meas ob on phi --> r ->
  'Meas ob on phi --> q ->
  phi <> Zero -> 
  r = q.
Proof.
  move => phi ob r q.
  rewrite /meas_p_to => H1 H2 Hnt.
  have: (pn_int ob × phi = pn_int ob × phi) by auto.
  rewrite {1}H1 H2.
  by apply Mscale_cancel.
Qed.

