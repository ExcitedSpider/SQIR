From mathcomp Require Import all_ssreflect fingroup.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".

Section PauliOneGroup.

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
Definition p1_id := I.

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


Lemma mult_p1_id: left_id p1_id mult_p1.
Proof. 
  rewrite /left_id.
  move => x.
  by case: x.
Qed. 

Print left_inverse.

Lemma mult_p1_left_inv: left_inverse p1_id inv_p1 mult_p1.
Proof.
  rewrite /left_inverse.
  move => x.
  by case: x.
Qed.

HB.instance Definition _ := isMulGroup.Build PauliOp
  mult_p1_assoc mult_p1_id mult_p1_left_inv.

Check PauliOp: finGroupType.

End PauliOneGroup.

Section PauliNGroup.

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
  pn_id n.+1 = [tuple of p1_id :: (pn_id n)].
Proof.
  rewrite /pn_id /p1_id /=.
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

Section Interpretation.

End Interpretation.

