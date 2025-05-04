(* 
This file includes the formalization of 
  - quantum group action.
  - phase negation
  - commutativity of Pauli operators
Key definitions:
  - applyP := apply a pauli operator
*)

(* Refer to https://math-comp.github.io/htmldoc_2_2_0/mathcomp.fingroup.action.html *)
(* We do not use mathcomp's definition because it requires finite structures, but quantumLib *)
(* works on infinite structure (Hilbert Space) *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.
From QuantumLib Require Import Matrix.

Import GroupScope.

(* Section ok. *)
(* Variables S T R : Type. *)
(* Implicit Type op : S -> T -> R. *)
(* Definition left_injective op := forall x, injective (op^~ x). *)
(* End ok. *)

Section ActionDef.

(* aT: action operator type *)
(* D: the set of operators that is useful *)
Variables (aT : finGroupType) (D : {set aT}) (dim: nat).
(* we restraint the applied set to be the hilbert space *)
Definition ActionType := (Vector (2^dim) -> aT -> Vector (2^dim)).
Implicit Type (to : ActionType).
Implicit Type (x: Vector (2^dim)).

(* compatibility *)
Definition act_comp to x := 
  forall (a b: aT), to x (mulg b a) = to (to x a) b.

(* identity *)
Definition act_id to := forall x, WF_Matrix x -> to x (oneg aT) = x.

(* From https://mathworld.wolfram.com/GroupAction.html *)
(* A group G is said to act on a set X when 
   there is a map to : G × X -> X  such that
   for all elements x in X 
   1. to(x, e) = x where e is the id of G 
   2. to(g, to(h, x)) = to(g * h, x)
   *)
(* In addition, we introduct a well-form assumption to make *) 
(* sure x has valid physical meaning *)

Definition is_action to :=
  act_id to /\ forall x, { in D &, act_comp to x}.

Record action := Action {
  act :> Vector (2^dim) -> aT -> Vector(2^dim); 
  _ : is_action act
}.


End ActionDef.

Require Import PauliGroup.
Require Import PauliProps.

Import all_pauligroup.
(* An n-qubit Pauli operator is a Hermitian element of the 
n-qubit Pauli group P_n *)
(* One detail to notice is that we only consider phase +1.
Technically, phase -1 also makes an element of P_n hermitian
But they are not very useful *)
Notation PauliOperator := PauliTupleBase.

(* We use PauliElement to refer to all elements in pauli groups
  note that not all elements are pauli operator
  for phase in {-i, i}, these elements are not hermitian
*)
Notation PauliElement := PauliTuple.

Definition PauliOpToElem {n} (x : PauliOperator n) : PauliElement n := (One,x).
Coercion PauliOpToElem : PauliOperator >-> PauliElement.

Definition PauliBaseToOp (x : PauliBase) : PauliOp := (One, x).
Coercion PauliBaseToOp : PauliBase >-> PauliOp.

Section QuantumActions. 


(* Apply a single-qubit pauli operator *)
Definition apply_1 : Vector 2 -> PauliOp -> Vector 2 :=
  fun psi op => (p1g_int op) × psi.

Check is_action.

Lemma mult_phase_comp: forall a b, phase_int (a) * phase_int (b) = 
  phase_int (mult_phase a b).
Proof.
  move => a b.
  all: case a; case b; lca.
Qed.

Definition aTs := [set: PauliOp].


Fact act_1_is_action:
  (is_action _ aTs 1 apply_1).
Proof.
  rewrite /is_action; split.
  {
    rewrite /act_id /apply_1 /= => x Hwf.
    lma'.
  }
  {
    move => x.
    rewrite /act_comp /apply_1 => a b Ha Hb.
    case a; case b => sa pa sb pb.
    rewrite /p1g_int /=.
    rewrite !Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc.
    rewrite -!mult_phase_comp.
    rewrite Cmult_comm.
    rewrite -!Mmult_assoc  p1_int_Mmult .
    rewrite Mscale_mult_dist_l.
    by rewrite -!Mscale_assoc.
  }
Qed.


Check Action.

(* Coq can infer these that depend on the final one. *)
Arguments Action {aT D dim act}.

Canonical act_1 := (Action act_1_is_action).

(* Sancheck *)
Goal act_1 ∣0⟩ (% X) = ∣1⟩.
Proof.
  rewrite /= /apply_1 /=.
  lma'.
Qed.


Variable (n: nat).

Definition applyP : Vector (2^n) -> PauliTuple n -> Vector (2^n) :=
  fun psi op => (png_int op) × psi.

Set Bullet Behavior "Strict Subproofs".

Definition aTsn := [set: PauliTuple n].


Fact applyP_is_action:
  is_action _ aTsn _ applyP.
Proof.
  rewrite /is_action /act_id /=.
  split.
  {
    intros x Hwf.
    rewrite /act_id /applyP id_png_int.
    by rewrite Mmult_1_l.
  }
  {
    move => x.
    rewrite /act_comp /= /applyP.
    move => *.
    by rewrite -png_int_Mmult Mmult_assoc.
  }
Qed.

Canonical act_n := (Action applyP_is_action).

(* Had to close here awardly because we don't want n to remain variable *)
End QuantumActions.

Arguments applyP {n}.



Definition xxx: PauliTuple 3 := (One, [tuple of X :: X :: X :: []]).

(* sancheck *)
Goal act_n _ ∣0,0,0⟩ xxx = ∣1,1,1⟩.
Proof.
  rewrite /act_n /applyP /=.
  Qsimpl.
  lma'.
Qed.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import PauliGroup.
Require Import SQIR.UnitaryOps.

Section StabDef.

Import all_pauligroup.

Definition actionTo {dim: nat} {aT: finGroupType} := 
  ActionType aT dim.

Fail Definition astab {dim: nat} {aT: finGroupType} (to: actionTo) (A: {set aT}) (psi: Vector (2^dim)):= 
  (* Canot define. because mathcomp needs psi of eqType *) 
  [set x | x in A & to psi x == psi]. 

(* Let's try can we define Vector to be eqType *)
From HB Require Import structures.

(* reflect (x = y) (e x y) where e: T -> T -> bool *)
Print eq_axiom.

(* QuantumLib does not define `==` to be a computable process *)
(* i.e. A == B -> Prop not bool *) 
Check ∣0⟩==∣1⟩.

(* Therefore, we use this definition instead. *)
Definition stab {dim: nat} {aT: finGroupType} (to: actionTo) (x: aT) (psi: Vector(2^dim)):= 
  to psi x = psi.

End StabDef.

Check Z0_spec.

Ltac solve_stab1:=
  rewrite /stab /= /apply_1 /=;
  Qsimpl;
  autorewrite with ket_db;
  try by [];
  try by lma'.


Import all_pauligroup.

Lemma Z0_stab: stab act_1 (% Z) ∣0⟩.
by solve_stab1. Qed.

Lemma Z1_stab: stab act_1 (p1g_of NOne Z) ∣1⟩.
by solve_stab1. Qed.

(* Theories about -1 * pt%g *)
Module Commutativity.

Require Import ExtraSpecs.
From mathcomp Require Import eqtype ssrbool.
Require Import Classical.

Section Prerequisites.

Lemma pair_inj:
(forall T R (a b: T) (x y: R), (a, x) = (b, y) -> a = b /\ x = y).
  {
    intros.
    by inversion H.
  }
Qed.


Lemma png_int_injection: forall n px py (tx ty: PauliTupleBase n),
  png_int (px, tx) = png_int (py, ty) -> px = py /\ tx = ty.
Proof.
  move => n px py tx ty.
  rewrite /png_int /=.
  case: (classic (px=py)) => Hc.
  - rewrite Hc.
    case : (classic (tx = ty)) => Hc2.
    + by rewrite Hc2.
    + intros H. 
      (* tx <> ty -> there exists an index i such that tx[i] <> ty[i] *)
      (* therefore, we know that pn_int tx <> pn_int ty *)
      (* because pauli string are interpreted by component *)
      (* e.g. [[X, Y]] = σx ⊗ σy  *)
      (* and this contradict with H *)
      admit.
  - intros H.
    case : (classic (tx = ty)) => Hc2.
    + exfalso.
      apply Hc. subst.
      (* since H:  phase_int px .* pn_int ty = phase_int py .* pn_int ty  *)
      (* we know that px = py *)
      (* this contradicts with Hc: px <> py *)
      admit.
    + exfalso.
      (* We have $Hc : px <> py$ and $Hc2 : tx <> ty$ *)
      (* Therefore, it is impossible to have H *)
      (* H : phase_int px .* pn_int tx = phase_int py .* pn_int ty *)
Admitted. (* An informal proof is presented instead due to the difficulty in quantumlib *)

End Prerequisites.

Section Negation.


Definition minus_id_png n : (PauliTuple n) := (NOne , id_pn n).

Notation "[-1]" := minus_id_png.

Definition neg_png n (p: PauliTuple n) : PauliTuple n :=
  match p with
  | (phase, tuple) => (mulg NOne phase, tuple)
  end.

Definition neg_p1g (p: PauliOp): PauliOp :=
  match p with
  | (phase, tuple) => (mulg NOne phase, tuple)
  end.

Definition neg_phase (p: phase): phase :=
  mulg NOne p.

Lemma neg_phase_correct:
  forall x y, phase_int x = -C1 * phase_int y <-> 
      x = mult_phase NOne y.
Proof.
  move => x y.
  split.
  {
    case x; case y; rewrite /=.
    all: try by easy.
    all: autorewrite with C_db.
    all: 
    intros H;
    inversion H;
    (* Check https://rocq-prover.org/doc/v8.15/stdlib/Coq.Reals.Reals.html *)
    (* For proving goals like ?1<>0 *)
    try (contradict H1; discrR);
    try (contradict H2; discrR).
  }
  {
    case x; case y.
    all: rewrite /=; autorewrite with C_db; try by easy.
  }
Qed. 

Lemma pstring_neg_implies: 
forall n (x y: PauliTuple n), 
  png_int x = -C1 .* png_int y -> x = mult_png (NOne, id_pn n) y.
Proof.
  move => n [px tx] [py ty].
  rewrite /= /mult_png => H. 
  Qsimpl.
  rewrite /get_phase_png get_phase_pn_id.
  rewrite mult_phase_id mult_pn_id.
  move: H.
  assert (
  forall n px (tx: PauliTupleBase n),
    phase_int px .* pn_int tx = png_int (px, tx)
  ). by easy.
  rewrite H.
  replace (phase_int px .* pn_int tx) with (png_int (px, tx)) by easy.
  replace (-C1) with (phase_int NOne) by easy.
  rewrite Mscale_assoc mult_phase_comp. 
  rewrite H.
  move => H1.
  apply png_int_injection in H1.
  elim H1 => Hp Ht.
  by subst.
Qed.

Lemma png_neg_alt:
  forall n (x y: PauliTuple n),
  png_int (mulg x y) = -C1 .* png_int (mulg y x) ->
  mulg x y = mult_png (NOne, id_pn n) (mulg y x).
Proof. 
  move => n x y H.
  by apply pstring_neg_implies in H.
Qed.



Lemma PauliOp_bicommute:
  forall x y,
  get_phase x y = get_phase y x \/
  get_phase x y = neg_phase (get_phase y x).
  (* phase_int (get_phase x y) = -C1 * phase_int (get_phase y x). *)
Proof.
  move => x y.
  case x; case y; rewrite /=.
  all: try(by left); rewrite -neg_phase_correct.
  all: try(right; lca).
Qed.

End Negation.


Lemma phase_comm n:
 forall (sx sy:phase) (pt: PauliTupleBase n),
 (* mulg cannot be inferenced here *)
 mult_png (sx, pt) (sy, pt) = mult_png (sy, pt) (sx, pt).
Proof.
  move => sx sy.
  by case sx; case sy.
Qed.

Lemma commute_png_implies n:
  forall (px py: phase) (tx ty: PauliTupleBase n),
  commute_at mult_png (px, tx) (py, ty)-> mult_pn tx ty = mult_pn ty tx /\
   get_phase_png (px, tx) (py, ty) = get_phase_png (py, ty) (px, tx).
Proof.
  rewrite /commute_at /mult_png /= => px py tx ty H.
  apply pair_inj in H.
  destruct H as [H1 H2].
  by rewrite H1 H2.
Qed.

Lemma mult_p1_comm:
  commutative mult_p1.
Proof.
  rewrite /commuteg => x y.
  by case x; case y.
Qed.

Lemma phase_mult_p1_comm:
  forall hx hy,
  get_phase hx hy = get_phase hy hx ->
  mult_p1 hx hy = mult_p1 hy hx.
Proof.
  move => x y.
  by case x; case y.
Qed.


(* A very profound theorem: *)
(* all PauliOperators are either commute or anticommute *)
(* TODO: the definition of anticommute is too loose. *)
(* find something in mathcomp to make it work *)
Theorem pstring_bicommute n:
  forall (x y: PauliTuple n), commute_at mulg x y \/ 
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
          (* by rewrite !beheadCons !theadCons mult_p1_comm. *)
          rewrite !beheadCons !theadCons /neg_phase /= phase_int_comp /=. 
          by rewrite mult_p1_comm.
    }
    (* tail anticommute *)
    case (PauliOp_bicommute hx hy) => Hhead.
    - apply png_neg_alt in H.
      rewrite /mult_png /= mult_pn_id /mulg /= /mult_png in H.
      rewrite /get_phase_png get_phase_pn_id mult_phase_id in H.
      apply pair_inj in H.
      elim H => H0 H1.
      right. 
      rewrite !get_phase_png_cons !theadCons !beheadCons.
      rewrite /get_phase_png.
      rewrite !Hhead !H0 !H1.
      rewrite phase_mult_p1_comm.
      rewrite !phase_int_comp /= Mscale_assoc !Cmult_assoc.
      remember (phase_int (get_phase hy hx)) as a.
      remember (phase_int (get_phase_pn ty tx)) as b.
      by rewrite (Cmult_comm a _).
      exact Hhead.
    - left.
      rewrite /neg_phase in Hhead.
      rewrite !get_phase_png_cons !Hhead.
      apply pstring_neg_implies in H.
      rewrite /mulg /= /mult_png in H.
      apply pair_inj in H.
      destruct H.
      rewrite H H0 mult_p1_comm.
      rewrite mult_pn_id /get_phase_png get_phase_pn_id.
      rewrite mult_phase_id !mult_phase_assoc.
      by rewrite (mult_phase_comm _  NOne) mult_phase_assoc.
    }
Qed.

End Commutativity.


Lemma applyP_plus { n: nat }:
  forall (operator: PauliTuple n) (st1 st2: Vector (2^n)),
  (applyP (st1 .+ st2) operator) = 
  (applyP st1 operator) .+ (applyP st2 operator).
Proof. move => *; by rewrite /applyP Mmult_plus_distr_l. Qed.

Lemma applyP_mscale { n: nat }:
  forall (operator: PauliTuple n) (st: Vector (2^n)) (a: C),
  (applyP (a .* st) operator) = 
  a.* (applyP st operator) .
Proof. move => *. by rewrite /applyP Mscale_mult_dist_r. Qed.

Lemma applyP_comb {n : nat }:
  forall (op1 op2: PauliTuple n) (st: Vector (2^n)),
  applyP (applyP st op1) op2 = 
  applyP st (mulg op2 op1).
Proof.
  move: (applyP_is_action n) => [_ H] op1 op2 st.
  move: (H st) => H1.
  clear H.
  rewrite /act_comp /= in H1.
  move: (H1 op1 op2) => H.
  clear H1.
  symmetry. apply H; 
  by rewrite inE.
Qed.

Lemma applyP_id {n: nat} :
  forall (st: Vector (2^n)),
  WF_Matrix st ->
  applyP st (@oneg (PauliTuple n)) = st.
Proof.
  move: (applyP_is_action n) => [H _] st.
  rewrite /act_id /= in H.
  apply H.
Qed.
