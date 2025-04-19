From mathcomp Require Import all_ssreflect fingroup.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".



Definition t1 := [tuple 1; 2].
Definition t2 := [tuple 3; 4].

Goal [tuple of t1 ++ t2] == [tuple 1; 2; 3; 4].
Proof. by []. Qed.

Goal take 3 [tuple 1; 2; 3; 4] == [tuple 1; 2; 3].
Proof. by []. Qed.

Goal drop 1 [tuple 1; 2; 3; 4] == [tuple 2; 3; 4].
Proof. by []. Qed.

Inductive alphabet := A | B | C.
Definition decode_EE (n: 'I_3) : alphabet := nth A [:: A;B;C] (nat_of_ord n).
Definition encode_EE (e: alphabet) : 'I_3 := 
  match e with
  | A => Ordinal (n:=3) (m:=0) is_true_true
  | B => Ordinal (n:=3) (m:=1) is_true_true
  | C => Ordinal (n:=3) (m:=2) is_true_true
  end.

Lemma code_decodeEE : cancel encode_EE decode_EE.
Proof.
  by case.
Qed.

HB.instance Definition _ := Equality.copy alphabet (can_type code_decodeEE).
HB.instance Definition _ := Finite.copy alphabet (can_type code_decodeEE).
Check alphabet: finType.



Definition g := alphabet.
Variable mul: g -> g -> g.
Variable mul_id: g.
Variable mul_inv: g -> g.

Lemma thing1: associative mul.
Proof.
Admitted.

Lemma thing2: left_id mul_id mul.
Proof.
Admitted.

Lemma thing3: left_inverse mul_id mul_inv mul.
Proof.
Admitted.


Check Finite g.
HB.about Finite.
HB.instance Definition _ := Finite.on g.
HB.instance Definition _ := isMulGroup.Build g
  thing1 thing2 thing3.

Goal forall (a b: g),
  mulg a b = mul a b.
by []. Qed.


Check g: finGroupType.


Section NactionDef.

From mathcomp Require Import action.

Check is_action.
Variables (gT : finGroupType) (sT : finType).
Variables (to : {action gT &-> sT}) (n :  nat).

Definition n_act (t : n.-tuple sT) a := [tuple of map (to^~ a) t].
Print n_act.

Locate "^~".

Fact n_act_is_action : is_action setT n_act.
Proof. Admitted.

(* astab: {set ?rT} -> action ?D ?rT -> {set ?aT} *)
Check astab.

Print astab.

End NactionDef.









