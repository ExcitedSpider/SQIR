From mathcomp Require Import all_ssreflect fingroup.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".

Module PauliOneGroup.

Inductive PauliOp : Type :=
| I : PauliOp
| X : PauliOp
| Y : PauliOp
| Z : PauliOp.

(* multiplication on PauliOp *)
Definition mult_p1(a b: PauliOp): PauliOp :=
  match a, b with
  | I, p => p
  | p, I => p  
  
  | X, X => I
  | Y, Y => I 
  | Z, Z => I

  | X, Y => Z
  | Y, X => Z

  | Y, Z => X
  | Z, Y => X

  | Z, X => Y
  | X, Z => Y 
end.

(* All pauli op squares to I *)
Definition inv_p1 (op: PauliOp): PauliOp := op.


(* ID of Pauli_1 group *)
Definition id_p1 := I.

(* Already Proved Properties *)

Definition decode_EE (n: 'I_4) : PauliOp := nth I [:: I;X;Y;Z] (nat_of_ord n).
Definition encode_EE (e: PauliOp) : 'I_4 := 
  match e with
  | I => Ordinal (n:=4) (m:=0) is_true_true
  | X => Ordinal (n:=4) (m:=1) is_true_true
  | Y => Ordinal (n:=4) (m:=2) is_true_true
  | Z => Ordinal (n:=4) (m:=3) is_true_true
  end.

Lemma code_decodeEE : cancel encode_EE decode_EE.
Proof.
  by case.
Qed.

HB.instance Definition _ := Equality.copy PauliOp (can_type code_decodeEE).
HB.instance Definition _ := Finite.copy PauliOp (can_type code_decodeEE).

Lemma mult_p1_assoc: associative mult_p1.
Proof. 
  rewrite /associative.
  move => x y z.
  case: x; case: y; case: z; by [].
Qed. 


Lemma mult_p1_id: left_id id_p1 mult_p1.
Proof. 
  rewrite /left_id.
  move => x.
  by case: x.
Qed. 

Print left_inverse.

Lemma mult_p1_left_inv: left_inverse id_p1 inv_p1 mult_p1.
Proof.
  rewrite /left_inverse.
  move => x.
  by case: x.
Qed.

HB.instance Definition _ := isMulGroup.Build PauliOp
  mult_p1_assoc mult_p1_id mult_p1_left_inv.

Check PauliOp: finGroupType.

End PauliOneGroup.

Module PauliNGroup.
Import PauliOneGroup.

(* Pauli Group with fixed length n *)
Definition PauliTuple n := {tuple n of PauliOp}.

(* Multiolication on Pauli Group with fixed length n *)
Definition mult_pn {n: nat} (a b: PauliTuple n): PauliTuple n := 
  (map_tuple (fun x => (mult_p1 x.1 x.2))) (zip_tuple a b).

Definition pn_id n := [tuple of nseq n I].
(* Definition pn_id n := nseq_tuple n I. *)

Definition inv_pn {n: nat} (pt: PauliTuple n): PauliTuple n := map_tuple inv_p1 pt.

Example mult_pn_exp0:
  mult_pn [tuple X; X] [tuple X; X] == [tuple I; I].
Proof. by []. Qed.

Example mult_pn_exp1:
  mult_pn [tuple X; X] [tuple X; X] = [tuple I; I].
Proof. by apply/eqP. Qed.
(* In SSR, you need to change view to computable equality to prompt it compute  *)

Example inv_pn_exp0: 
  inv_pn [tuple X; Y; Z] = [tuple X; Y; Z].
Proof. by apply/eqP. Qed.

(* Lemma mult_pn_by_component n:
  forall xh xt yh yt,
  (@mult_pn n) [tuple of xh::xt] [tuple of yh::yt].  *)

Lemma trivial_tuples (p q: PauliTuple 0) : p = q.
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.

(* 
Shout out to
https://github.com/coq-community/bits/blob/f0b274803dc93c5799bd26473c2bcea5b43139ea/src/ssrextra/tuple.v
Thanks for their beutiful proofs for these two lemmas
zipCons and mapCons
*)
Lemma zipCons {n A B} a (aa: n.-tuple A) b (bb: n.-tuple B) :
  zip_tuple [tuple of a::aa] [tuple of b::bb] = [tuple of (a,b) :: zip_tuple aa bb].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (a,b)). Qed.

Lemma mapCons {n A B} (f: A -> B) b (p: n.-tuple A) :
  map_tuple f [tuple of b :: p] = [tuple of f b :: map_tuple f p].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (f b)). Qed.

Lemma mult_pn_assoc n: associative (@mult_pn n). 
Proof.
  unfold associative.
  induction n.
  {
    intros.
    apply trivial_tuples.
  }
  {
    intros.
    (* applies view of tupleP *)
    (* Change t: tuple n+1 to t: h::tx *)
    case : x / tupleP => hx tx.
    case : y / tupleP => hy ty.
    case : z / tupleP => hz tz.
    unfold mult_pn.
    repeat rewrite zipCons mapCons zipCons mapCons.
    remember (IHn tx ty tz) as IHxyz;
      unfold mult_pn in IHxyz; rewrite IHxyz; clear HeqIHxyz IHxyz.
    rewrite mult_p1_assoc /=.
    reflexivity.
  }
Qed.


Check tupleP.
Print tuple1_spec.

Lemma pn_idP {n: nat}: 
  pn_id n.+1 = [tuple of id_p1 :: (pn_id n)].
Proof.
  rewrite /pn_id /id_p1 /=.
  (* 
    both side seems the same
    but unable to unity
    the goal is literally
    *)
  Fail by []. 
Admitted.

Lemma mult_pn_id n: left_id (@pn_id n) (@mult_pn n).
Proof. 
  unfold left_id.
  induction n.
  1: by intros; apply trivial_tuples. 
  intros.
  case : x / tupleP => hx tx.
  rewrite pn_idP.
  move: IHn.
  rewrite /mult_pn /pn_id zipCons mapCons=> IHx.
  have IHtx := (IHx tx).
  by rewrite IHtx.
Qed.



Lemma mult_pn_left_inv n: left_inverse (@pn_id n) (@inv_pn n) (@mult_pn n).
Proof.
  unfold left_inverse.
  induction n.
  1: by intros; apply trivial_tuples.
  move => x.
  case : x / tupleP => hx tx.
  rewrite /inv_pn mapCons.
  have IHtx := (IHn tx).
  move: IHtx.
  rewrite /mult_pn zipCons mapCons => H.
  by rewrite H /= mult_p1_left_inv pn_idP.
Qed.


Variable n:nat.

HB.instance Definition _ := Finite.on (@PauliTuple n).

HB.instance Definition _ := isMulGroup.Build 
  (@PauliTuple n) (@mult_pn_assoc n) (@mult_pn_id n) (@mult_pn_left_inv n).

Check (@PauliTuple n): finGroupType.

End PauliNGroup.

(* P1 Group with phase  *)
Module P1ScaleGroup.

Import PauliOneGroup.

Inductive phase : Type :=
| One : phase   (* 1 *)
| Img : phase   (* i *)
| NOne : phase  (* -1 *)
| NImg : phase. (* -i *)

Definition decode_phase (n: 'I_4) : phase := nth One [:: One;Img;NOne;NImg] (nat_of_ord n).
Definition encode_phase (e: phase) : 'I_4 :=
  match e with
  | One => Ordinal (n:=4) (m:=0) is_true_true
  | Img => Ordinal (n:=4) (m:=1) is_true_true
  | NOne => Ordinal (n:=4) (m:=2) is_true_true
  | NImg => Ordinal (n:=4) (m:=3) is_true_true
  end.

Lemma code_decode_phase : cancel encode_phase decode_phase.
Proof.
  by case.
Qed.

HB.instance Definition _ := 
  Equality.copy phase (can_type code_decode_phase).
HB.instance Definition _ := Finite.copy phase (can_type code_decode_phase).


Definition mult_phase (a b : phase) : phase :=
  match a, b with
  | One, x => x
  | x, One => x
  | Img, Img => NOne
  | Img, NOne => NImg
  | Img, NImg => One
  | NOne, Img => NImg
  | NOne, NOne => One
  | NOne, NImg => Img
  | NImg, Img => One
  | NImg, NOne => Img
  | NImg, NImg => NOne
  end.

(* - prove phases form a group *)


Definition inv_phase (sc: phase): phase := 
match sc with
| One => One
| Img => NImg
| NOne => NOne
| NImg => Img 
end.

Definition id_phase := One.

Lemma mult_phase_assoc: associative mult_phase.
Proof.
  rewrite /associative => x y z.
  by case x; case y; case z.
Qed.
  
Lemma mult_phase_id: left_id id_phase mult_phase.
Proof.
  rewrite /left_id => x.
  by case x.
Qed.

Lemma mult_phase_left_inv: left_inverse id_phase inv_phase mult_phase.
Proof.
  rewrite /left_inverse => x.
  by case x.
Qed.

HB.instance Definition _ := isMulGroup.Build phase
  mult_phase_assoc mult_phase_id mult_phase_left_inv.

(* Define Generalized Pauli Operator as *)
(* Cartisian Product of phase and PauliOp *)
Check phase: finType.
Check PauliOp: finType.
Definition phaseSet := [set: phase].

Goal One \in phaseSet.
by rewrite in_set. Qed.

Check prod.
Locate prod.

(* for "Generalized Pauli Operator" *)
Definition GenPauliOp := prod phase PauliOp.

(* Mathcomp has provided finType structure for prod *)
(* which you can find by *) 
Search "fin" "prod".
Check Datatypes_prod__canonical__fintype_Finite.

Check GenPauliOp: finType.

(* We can also define product set *) 
Definition GenPauliOpSet := setX [set: phase] [set: PauliOp].

Lemma setx_correct: forall (gop: GenPauliOp),
  gop \in GenPauliOpSet.
Proof.
  move => gop.
  case gop => *.
  by apply /setXP.
Qed.

Definition get_phase(a b: PauliOp): phase :=
  match a, b with  
  | I, p => One
  | p, I => One
  | X, X => One
  | Y, Y => One 
  | Z, Z => One

  | X, Y => Img
  | Z, X => Img
  | Y, Z => Img

  | Z, Y => NImg
  | Y, X => NImg
  | X, Z => NImg
  end.

Definition mult_p1g (a b: GenPauliOp): GenPauliOp := 
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      mult_phase (get_phase pa pb) (mult_phase sa sb), 
      mult_p1 pa pb
    ) 
  end. 

Definition inv_p1g (a: GenPauliOp): GenPauliOp := 
  match a with
  | pair s p => (inv_phase s, inv_p1 p)
  end.

Definition id_p1g := (id_phase, id_p1).

(* Lemma mult_p1_phase_assoc: *) 
(*   associative mult_p1_phase. *)

(* get_phase px (mult_p1 py pz) = *)
(* get_phase (mult_p1 px py) pz *)

Lemma mult_p1g_assoc:
  associative mult_p1g.
Proof.
  rewrite /associative => x y z.
  case x => sx px.
  case y => sy py.
  case z => sz pz.
  rewrite /mult_p1g /=.
  repeat rewrite mult_phase_assoc mult_p1_assoc.
  apply injective_projections; rewrite /=.
  2: by []. 
  (* we first handle a few cases that can be solved without fully unfold *)
  case px, py, pz; try by rewrite /= mult_phase_assoc. 
  (* Then we do brute-force *)
  all: try by case sx, sy, sz.
Qed.

Lemma mult_p1g_id:
  left_id id_p1g mult_p1g.
Proof.
  rewrite /left_id => x.
  case x => s p.
  by rewrite /mult_p1g /=.
Qed.

Lemma mult_p1g_left_inv:
  left_inverse id_p1g inv_p1g mult_p1g.
Proof.
  rewrite /left_inverse /id_p1g /inv_p1g /mult_p1g => x.
  case x => s p.
  rewrite mult_phase_left_inv mult_p1_left_inv.
  case p;
  by rewrite /=.
Qed.

HB.instance Definition _ := Finite.on GenPauliOp.
HB.instance Definition _ := isMulGroup.Build GenPauliOp
  mult_p1g_assoc mult_p1g_id mult_p1g_left_inv.

End P1ScaleGroup.

(* 
Interprete Pauli Groups (1-qubit and n-qubit) by Robert's QuantumLib
*)
Section Interpretation.

Require Import QuantumLib.Quantum.
Import PauliOneGroup.

(* 
==========================
interpretation of group p1 
==========================
*)
Definition p1_int (p : PauliOp) : Square 2 :=
match p with
| I => Matrix.I 2 
| X => Quantum.σx
| Y => Quantum.σy
| Z => Quantum.σz
end.


(* 
==========================
interpretation of group p1g 
==========================
*)

Import P1ScaleGroup.

Definition phase_int (s: phase): C := 
  match s with
  | One => C1
  | NOne => -C1
  | Img => Ci
  | NImg => - Ci
  end.

Definition p1g_int(p: GenPauliOp): Square 2 :=
  match p with
  | pair s p => (phase_int s) .* (p1_int p)
  end.


(* 
==========================
interpretation of group pn 
==========================
*)

Import PauliNGroup.

Check Matrix.I 1.

Definition pn_reducer {m n: nat} (acc: Matrix m n) (op: PauliOp)  :=
  acc ⊗ (p1_int op).

(* Cannot Infer m and n *) 
Fail Definition pn_int {n:nat} (p: PauliTuple n): Square (2^n) := 
  (foldl pn_reducer (Matrix.I 1) p).

(* It actually does not matter if the dimension is correct... *)
Definition pn_int_alt {n:nat} (p: PauliTuple n): Square (2^n) := 
  (foldl (@pn_reducer 2 2) (Matrix.I 1) p).

Check kron_assoc.

Example pn_interpret:
pn_int_alt [X;Z;Y;I] = σx ⊗ σz ⊗ σy ⊗ Matrix.I 2.
Proof.
  rewrite /pn_int_alt /pn_reducer /=.
  by Qsimpl.
Qed.


End Interpretation.

