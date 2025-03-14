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
  by case: x; case: y; case: z.
Qed. 


Lemma mult_p1_id: left_id p1_id mult_p1.
Proof. 
  rewrite /left_id.
  move => x.
  by case: x.
Qed. 

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
  (map (fun x => (mult_p1 x.1 x.2))) (zip a b).

Definition pn_id n := [tuple of nseq n I].

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

Lemma mult_pn_assoc n: associative (@mult_pn n). Admitted.

Lemma mult_pn_cmpn {n: nat}:
  forall (x y: PauliTuple n.+1),
  mult_pn x y = [tuple of (mult_p1 (thead x) (thead y)) :: (mult_pn (behead x) (behead y))].
Admitted.

Lemma mult_pn_id n: left_id (@pn_id n) (@mult_pn n).
Proof. 
  unfold left_id.
  induction n.
  - intros. 
    rewrite tuple0. 
    symmetry.
    apply tuple0.
  - simpl. 
    intros x'.
    rewrite mult_pn_cmpn.
    replace (mult_p1 (thead (pn_id n.+1)) (thead x')) with (thead x'). (* A1 *)
    replace (behead_tuple (pn_id n.+1)) with ((pn_id n)). (* A2 *)
    rewrite IHn.
    simpl.
    symmetry.
    apply tuple_eta.
    (* A2 *)
    { admit. (* don't know how to prove it, need to learn ssreflect*) }
    (* A1 *)
    { by []. }
Admitted.

Lemma mult_pn_left_inv n: left_inverse (@pn_id n) (@inv_pn n) (@mult_pn n).
Proof.
  unfold left_inverse.
  induction n.
  - intros x.
    rewrite tuple0.
    symmetry. 
    apply tuple0.
  - Admitted.

Variable n:nat.

HB.instance Definition _ := Finite.on (@PauliTuple n).

HB.instance Definition _ := isMulGroup.Build 
  (@PauliTuple n) (@mult_pn_assoc n) (@mult_pn_id n) (@mult_pn_left_inv n).

Check (@PauliTuple n): finGroupType.

End PauliNGroup.
