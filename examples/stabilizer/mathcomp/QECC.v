(* We present some examples of stabiliser code for case study. *)
(* TODO: add examples for 
  - pauli operator 
  - stabilizer 
*)

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Quantum.
Require Import Stabilizer.

Require Import Action.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import Observable.
Require Import Assumption.

(* Simply Goals like (pn_int _ × _) *)
Ltac SimplApplyPauli := 
    rewrite ?applyP_plus ?applyP_mscale;
    rewrite ?/meas_p_to ?/applyP ?/png_int ?/pn_int /=;
    Qsimpl;
    repeat (
      distribute_plus;
      repeat rewrite <- kron_assoc by auto with wf_db;
      restore_dims
    );
    rewrite ?Mmult_plus_distr_l ?kron_mixed_product; Qsimpl;
    autorewrite with ket_db.

(* Notation for applying an operator on a state *)
Notation "''Apply' P 'on' psi" := (applyP psi P) (at level 200).
Section QECCTheories.

Variable (dim: nat).

Variable (SyndromeMeas: {set (PauliOperator dim)}).
Variable (DetectableErrors: {set (PauliOperator dim)}).
Variable (psi: Vector (2^dim)).

(* 
  SyndromeMeas_stab shows that for all codewords,
  The measurement result is 1.
  Therefore, if we find any other measurement result, 
  we say the error is _detectable_.
  For pauli operators, the eigenvalue is always +-1 see `operator_eigenvalue` 
  so a error is detectable -> syndrome measurement is -1
*)
Definition detectable E := 
  let psi' := 'Apply E on psi in
    exists M,  M \in SyndromeMeas /\ 'Meas M on psi' --> -1.

Definition obs_be_stabiliser :=
  forall (M: Observable dim),
    M \in SyndromeMeas -> M ∝1 psi.

Definition errors_detectable :=
  forall (E: ErrorOperator dim),
  E \in DetectableErrors -> detectable E.


(* error E can be recovered by R *)
Definition recover_by {n} (E: ErrorOperator n) (R: PauliOperator n) :=
  mult_png R E = (@oneg (PauliElement n)).

(* Apply the error then the recover, the original state is restored *)
Theorem recover_by_correct {n} :
  forall (E: ErrorOperator n) (R: PauliOperator n) (phi: Vector (2^n)),
  WF_Matrix phi ->
  recover_by E R -> 
  let phi' := 'Apply E on phi in
  ('Apply R on phi') = phi.
Proof.
  rewrite /= => E R phi Hwf.
  rewrite /recover_by.
  rewrite applyP_comb /= /mulg /=.
  move => ->.
  rewrite /oneg /=.
  apply (applyP_id).
  apply Hwf.
Qed.

(* Have to end here to make record *)
End QECCTheories.

Arguments obs_be_stabiliser {dim}.
Arguments errors_detectable {dim}.

Section Structure.

Record ErrorCorrectionCode := MkECC {
  dim: nat
(* Codespace *)
; psi: Vector (2^dim)
(* Observables *)
; obs: {set Observable dim}
(* Detectable Errors *)
; err: {set PauliOperator dim}
(* Obligation1: observables must be stabilisers of codespace *)
; ob1: obs_be_stabiliser obs psi 
(* Obligation2: all errors must be detectable by measurement *)
; ob2: errors_detectable obs err psi
}.

(* Undetectable is that the error state has the same measurement
  as the codespace
  There is an implicit requirement that E should be non-trivial (not I)
*)
Definition undetectable (ecc: ErrorCorrectionCode) E := 
  let psi' := 'Apply E on ecc.(psi) in
    forall M,  M \in ecc.(obs) -> 'Meas M on psi' --> 1.

(* 
Two errors are indistinguishable when all syndrome measurment
yields the same result
TODO: enforce E1 to be in the correctable error set
And derive distance of codewords based on the minimul weight of 
indistinguishable errors.
*)
Definition indistinguishable (ecc: ErrorCorrectionCode) E1 E2 :=
  forall M, M \in ecc.(obs) -> 
  let psi_e1 := 'Apply E1 on ecc.(psi) in
  let psi_e2 := 'Apply E2 on ecc.(psi) in
    ('Meas M on psi_e1 --> -1) -> ('Meas M on psi_e2 --> -1)
  .

(* (error, recover), in which recover operator can restore error  *)
Definition RecoverInstruction {n} := prod (PauliOperator n) (PauliOperator n).

(* The recover instruction is actaully 
apply the error operator again  *)
(* Therefore, it is trivial. we don't make this in example actually *)
(* But we provide a theorem here *)
Definition recover_insts (ecc: ErrorCorrectionCode) :=
  [set (x, x) | x in ecc.(err)].

(* for every pauli operator P we have PP = I *)
Theorem recover_insts_correct :
  forall ecc inst, inst \in (recover_insts ecc) ->
  recover_by (fst inst) (snd inst).
Admitted.


End Structure.

