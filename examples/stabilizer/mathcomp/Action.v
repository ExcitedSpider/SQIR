(* 
This file includes the formalization of 
  - quantum group action.
  - phase negation
  - commutativity of Pauli operators
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
  forall (a b: aT), WF_Matrix x -> to x (mulg b a) = to (to x a) b.

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
Require Import P1Props.

Section QuantumActions. 

Import P1Group.
Import P1GGroup.

(* Apply a single-qubit pauli operator *)
Definition apply_1 : Vector 2 -> GenPauliOp -> Vector 2 :=
  fun psi op => (p1g_int op) × psi.

Check is_action.

Lemma mult_phase_comp: forall a b, phase_int (a) * phase_int (b) = 
  phase_int (mult_phase a b).
Proof.
  move => a b.
  all: case a; case b; lca.
Qed.

Definition aTs := [set: GenPauliOp].


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

(* Interestingly, Coq can infer all types that depend on the final one. *)
Canonical act_1 := (Action _ _ _ _ act_1_is_action).



(* Sancheck *)
Goal act_1 ∣0⟩ (% X) = ∣1⟩.
Proof.
  rewrite /= /apply_1 /=.
  lma'.
Qed.

Import PNGroup.
Import PNGGroup.

Variable (n: nat).

Definition apply_n : Vector (2^n) -> GenPauliTuple n -> Vector (2^n) :=
  fun psi op => (png_int op) × psi.

Set Bullet Behavior "Strict Subproofs".

Definition aTsn := [set: GenPauliTuple n].


Fact act_n_is_action:
  is_action _ aTsn _ apply_n.
Proof.
  rewrite /is_action /act_id.
  split.
  {
    (* identity *)
    intros x Hwf.
    (* TODO: solve dependency issue of PNProps. *)
    rewrite /act_id /apply_n id_png_int.
    by rewrite Mmult_1_l.
  }
  {
    (* compatibility *)
    intros x.
    rewrite /act_comp /apply_n /= => [[pa ta] [pb tb]] _ _ Hwf.
    induction n.
    - rewrite (tuple0 ta) (tuple0 tb) /=.
      case pa; case pb; simpl; Qsimpl.
      all: try easy.
      all: lma'.
    (* Need to find a way to do decomposition of x *)
    (* Mathematically, x can be represented by a linear combination *)
    (* of basic vectors in the Vector space *)
    (* x = Sum_i alpha_i x_i *)
    (* where { x_i } is the set of basic vectors *)
    (* But it's hard to do it in Coq *)
    - admit.
  }
Admitted. (* Need a lemma to decomposite x = Sum_i alpha_i x_i *)

Canonical act_n := (Action _ _ _ _ act_n_is_action).

(* Had to close here awardly because we don't want n to remain variable *)
End QuantumActions.

Import PNGroup.
Import PNGGroup.
Import P1GGroup.
Import P1Group.

Definition xxx: GenPauliTuple 3 := (One, [tuple of X :: X :: X :: []]).

(* sancheck *)
Goal act_n _ ∣0,0,0⟩ xxx = ∣1,1,1⟩.
Proof.
  rewrite /act_n /apply_n /=.
  Qsimpl.
  lma'.
Qed.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import PauliGroup.
Require Import SQIR.UnitaryOps.
Import P1Group.
Import P1GGroup.

Check act_1 ∣0⟩ (% X) == ∣1⟩.

Section StabDef.

Import PauliGroup.P1Group.
Import PauliGroup.P1GGroup.

Check GenPauliOp: finGroupType.

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

Import P1GGroup.

Lemma Z0_stab: stab act_1 (% Z) ∣0⟩.
by solve_stab1. Qed.

Lemma Z1_stab: stab act_1 (p1g_of NOne Z) ∣1⟩.
by solve_stab1. Qed.

Section Assumption.

Variable (aT: finGroupType).
Variable (D : {set aT}).
Variable (n: nat).

Check (action aT D n).
Variable (to: action aT D n).



End Assumption.

(* Theories about -1 * pt%g *)
Module Commutativity.

Import PNGroup.
Import PNGGroup.
Import P1Group.
Import P1GGroup.
Require Import ExtraSpecs.
From mathcomp Require Import eqtype ssrbool.

Notation PString := GenPauliTuple.

Section Prerequisites.

Lemma pair_inj:
(forall T R (a b: T) (x y: R), (a, x) = (b, y) -> a = b /\ x = y).
  {
    intros.
    by inversion H.
  }
Qed.

Lemma png_int_injection: forall n px py (tx ty: PauliTuple n),
  png_int (px, tx) = png_int (py, ty) -> px = py /\ tx = ty.
Admitted.

Lemma eq_by_contra n (a b : PString n):
  (a != b -> False) -> a = b.
Proof.
  by apply contra_not_eq.
Qed.
  
End Prerequisites.

Section Negation.


Definition minus_id_png n : (PString n) := (NOne , id_pn n).

Notation "[-1]" := minus_id_png.

Definition neg_png n (p: PString n) : PString n :=
  match p with
  | (phase, tuple) => (mulg NOne phase, tuple)
  end.

Definition neg_p1g (p: GenPauliOp): GenPauliOp :=
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
forall n (x y: PString n), 
  png_int x = -C1 .* png_int y -> x = mult_png (NOne, id_pn n) y.
Proof.
  move => n [px tx] [py ty].
  rewrite /= /mult_png => H. 
  Qsimpl.
  rewrite /get_phase_png get_phase_pn_id.
  rewrite mult_phase_id mult_pn_id.
  move: H.
  assert (
  forall n px (tx: PauliTuple n),
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
  forall n (x y: GenPauliTuple n),
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
 forall (sx sy:phase) (pt: PauliTuple n),
 (* mulg cannot be inferenced here *)
 mult_png (sx, pt) (sy, pt) = mult_png (sy, pt) (sx, pt).
Proof.
  move => sx sy.
  by case sx; case sy.
Qed.

Lemma commute_png_implies n:
  forall (px py: phase) (tx ty: PauliTuple n),
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
