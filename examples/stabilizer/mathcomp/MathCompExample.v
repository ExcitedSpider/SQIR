From mathcomp Require Import all_ssreflect fingroup finset ssrnat seq tuple.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".

Example seq_on_tuple n (t : n.-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof.
  rewrite map_rev.
  rewrite revK.
  by rewrite size_map.
Qed.


Example seq_on_tuple' n (t : n.-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. by rewrite !size_tuple. Qed.

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

Notation g := alphabet.
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


HB.instance Definition _ := Finite.on g.
HB.instance Definition _ := isMulGroup.Build g
  thing1 thing2 thing3.

Goal forall (a b: g),
  mulg a b = mul a b.
by []. Qed.


Check g: finGroupType.

Definition gen1 := generated [set (A: g); (B: g)].

Hypothesis AB_eq_C: mulg A B = C.

Goal C \in gen1.
Proof. 
  rewrite /gen1.
  move: AB_eq_C => <-.
  apply: groupM.
  apply mem_gen.
  apply set21.
  apply mem_gen.
  apply set22.
Qed.


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

From mathcomp Require Import div.

Goal 5 = 1 %[mod 2].
Proof. by apply /eqP. Qed.


Module Generator.

Variable (gT : finGroupType) (A B: gT).

Definition generator := [set A; B].

Hypothesis AB_neq : A != B.

Definition gengroup := generated generator.

Lemma generators_size_2 : #|generator| == 2.
Proof. Admitted.

Lemma ab_in_gengroup : 
  mulg A B \in gengroup.
Proof. Admitted.

End Generator.


From mathcomp Require Import all_ssreflect fingroup finset ssrnat seq tuple.

Section Generator2.

Variable (gT : finGroupType) (a b: gT).

Variable P: gT -> Prop.

Hypothesis fact_P_a : P a.
Hypothesis fact_P_b : P a.
Hypothesis lemma_P_comp: 
  forall (x y: gT), P x -> P y -> P (x * y).

Theorem p_ab_gen:
  forall (e: gT), e \in (generated [set a; b]) -> P e.
Proof.
  move => e He.
  (* This is a useful lemma according to freindly online people *)
  Check gen_prodgP.
  rewrite generated.unlock in He.
Abort.
(*  *)


End Generator2.

Definition plainSet := [set true; false].

Definition setx := [set (x, y) | x in plainSet, y in plainSet & x != y].

Lemma example_setx:
  (true, false) \in setx.
Abort.
