 (*
The formalism of Pauli Groups and their quotient groups
In quantum computing, quotied pauli groups are pauligroups without phase
Key Definitions:
- PauliBase: The 1-qubit Pauli quotient group
- phase: The phase {-1, i, -1, -i} and they forms a group
- PauliOp: The 1-qubit Pauli group
- PauliTupleBase: The n-qubit Pauli quotient group
- PauliTuple: The n-qubit Pauli group

You can use all canonical definitions in mathcomp: oneg, mulg, invg, idg

This file also contains interpretation:
f: PauliGroup n ->  Matrix 2^n
To bridge group with quantumlib 
*)
From mathcomp Require Import all_ssreflect fingroup.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".


(* 
Shout out to
https://github.com/coq-community/bits
for their tuple lemmas in this section
*)
Section TupleExtras.

Lemma beheadCons {n A} a (aa: n.-tuple A) : behead_tuple [tuple of a::aa] = aa.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma theadCons : forall {n A} (a:A) (aa: n.-tuple A), thead [tuple of a::aa] = a.
Proof. done. Qed.

Lemma zipCons {n A B} a (aa: n.-tuple A) b (bb: n.-tuple B) :
  zip_tuple [tuple of a::aa] [tuple of b::bb] = [tuple of (a,b) :: zip_tuple aa bb].
Proof.
    apply: eq_from_tnth => i.
    rewrite (tnth_nth (a, b)) /=.
    by rewrite (tnth_nth (a, b)) /=.
Qed.

Lemma mapCons {n A B} (f: A -> B) b (p: n.-tuple A) :
  map_tuple f [tuple of b :: p] = [tuple of f b :: map_tuple f p].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (f b)). Qed.

Lemma catCons {n1 n2 A} (a:A) (aa:n1.-tuple A) (bb:n2.-tuple A) :
  cat_tuple [tuple of a::aa] bb = [tuple of a::cat_tuple aa bb].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma catNil {n A} (aa:n.-tuple A) :
  cat_tuple [tuple] aa = aa.
Proof. exact: val_inj. Qed.
  
End TupleExtras. 

Module P1Group.

Inductive PauliBase : Type :=
| I : PauliBase
| X : PauliBase
| Y : PauliBase
| Z : PauliBase.

(* multiplication on PauliBase *)
Definition mult_p1(a b: PauliBase): PauliBase :=
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
Definition inv_p1 (op: PauliBase): PauliBase := op.


(* ID of Pauli_1 group *)
Definition id_p1 := I.

(* Already Proved Properties *)
Definition decode_EE (n: 'I_4) : PauliBase := nth I [:: I;X;Y;Z] (nat_of_ord n).
Definition encode_EE (e: PauliBase) : 'I_4 := 
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

HB.instance Definition _ := Equality.copy PauliBase (can_type code_decodeEE).
HB.instance Definition _ := Finite.copy PauliBase (can_type code_decodeEE).

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

HB.instance Definition _ := isMulGroup.Build PauliBase
  mult_p1_assoc mult_p1_id mult_p1_left_inv.


Check PauliBase: finGroupType.

End P1Group.

Module PNGroup.
Import P1Group.

(* Pauli Group with fixed length n *)
Definition PauliTupleBase n := {tuple n of PauliBase}.

(* Multiolication on Pauli Group with fixed length n *)
Definition mult_pn {n: nat} (a b: PauliTupleBase n): PauliTupleBase n := 
  (map_tuple (fun x => (mult_p1 x.1 x.2))) (zip_tuple a b).

Definition id_pn n := [tuple of nseq n I].
(* Definition id_pn n := nseq_tuple n I. *)

Definition inv_pn {n: nat} (pt: PauliTupleBase n): PauliTupleBase n := map_tuple inv_p1 pt.

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

Lemma trivial_tuples (p q: PauliTupleBase 0) : p = q.
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.

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
  id_pn n.+1 = [tuple of id_p1 :: (id_pn n)].
Proof.
  rewrite /id_pn /id_p1 /=.
  apply: eq_from_tnth => i;
  by rewrite !(tnth_nth I).
Qed.

Lemma mult_pn_id n: left_id (@id_pn n) (@mult_pn n).
Proof. 
  unfold left_id.
  induction n.
  1: by intros; apply trivial_tuples. 
  intros.
  case : x / tupleP => hx tx.
  rewrite pn_idP.
  move: IHn.
  rewrite /mult_pn /id_pn zipCons mapCons=> IHx.
  have IHtx := (IHx tx).
  by rewrite IHtx.
Qed.



Lemma mult_pn_left_inv n: left_inverse (@id_pn n) (@inv_pn n) (@mult_pn n).
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

Section Structure.

Variable n:nat.

HB.instance Definition _ := Finite.on (@PauliTupleBase n).

HB.instance Definition _ := isMulGroup.Build 
  (@PauliTupleBase n) (@mult_pn_assoc n) (@mult_pn_id n) (@mult_pn_left_inv n).

Check (@PauliTupleBase n): finGroupType.

End Structure.

End PNGroup.

(* P1 Group with phase  *)
Module P1GGroup.

Import P1Group.

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
(* Cartisian Product of phase and PauliBase *)
Check phase: finType.
Check PauliBase: finType.
Definition phaseSet := [set: phase].

Goal One \in phaseSet.
by rewrite in_set. Qed.

Check prod.
Locate prod.

(* for "Generalized Pauli Operator" *)
Definition PauliOp := prod phase PauliBase.

(* Mathcomp has provided finType structure for prod *)
(* which you can find by *) 
(* Search "fin" "prod". *)
Check Datatypes_prod__canonical__fintype_Finite.

Check PauliOp: finType.

(* We can also define product set *) 
Definition PauliOpSet := setX [set: phase] [set: PauliBase].

Definition p1g_of: phase -> PauliBase -> PauliOp := 
  fun p o => pair p o.

Check p1g_of One X.



Lemma setx_correct: forall (gop: PauliOp),
  gop \in PauliOpSet.
Proof.
  move => gop.
  case gop => *.
  by apply /setXP.
Qed.

Definition get_phase(a b: PauliBase): phase :=
  match a, b with  
  | I, _ => One
  | _, I => One
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

Definition mult_p1g (a b: PauliOp): PauliOp := 
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      mult_phase (get_phase pa pb) (mult_phase sa sb), 
      mult_p1 pa pb
    ) 
  end. 


Definition inv_p1g (a: PauliOp): PauliOp := 
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

HB.instance Definition _ := Finite.on PauliOp.
HB.instance Definition _ := isMulGroup.Build PauliOp
  mult_p1g_assoc mult_p1g_id mult_p1g_left_inv.

Notation "%( x ; y )" := (p1g_of x y) (at level 210).

Notation "% x" := (p1g_of One x)  (at level 210).


(* San Check by Examples *)

Goal mulg (% Y) (% X) = %(NImg; Z). 
by []. Qed.

Goal mulg (%(NImg; Y)) (% X) = %(NOne; Z). 
by []. Qed.

Goal mult_p1g (% X) (% Y) = %(Img; Z). 
by []. Qed.

Goal mult_p1g (% Z) (% Y) = %(NImg; X). 
by []. Qed.

Goal mult_p1g (% X) (% Z) = %(NImg; Y). 
by []. Qed.

End P1GGroup.

Module PNGGroup.

Import P1GGroup.
Import PNGroup.
Import P1Group.

Definition get_phase_pn {n: nat} (a b: PauliTupleBase n): phase := 
  foldl mult_phase One (
    map (fun item => get_phase item.1 item.2)  (zip_tuple a b)
  ).  

(* -1 *)
Compute get_phase_pn [tuple X;X;Y;Y] [tuple I;I;X;X].

Definition PauliTuple (n: nat) := prod phase (PauliTupleBase n).

Definition get_phase_png {n: nat} (a b: PauliTuple n): phase :=
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      mult_phase (get_phase_pn pa pb) (mult_phase sa sb)
    )
  end.

Definition mult_png {n: nat} (a b: PauliTuple n): PauliTuple n :=
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      get_phase_png a b,
      mult_pn pa pb
    ) 
end.

Definition inv_png {n}( a: PauliTuple n): PauliTuple n := 
  match a with
  | pair s p => (inv_phase s, inv_pn p)
  end.

Definition id_p1g := (id_phase, id_pn).

Lemma mult_phase_inj: 
  forall a b x y,
  a = x ->
  b = y ->
  mult_phase a b = mult_phase x y.
Proof.
  move => *.
  by subst.
Qed.

Print mult_pn.

Lemma mult_pn_cons n:
  forall (hx hy: PauliBase) (tx ty: PauliTupleBase n),
    mult_pn [tuple of hx :: tx] [tuple of hy :: ty] = 
    [tuple of mult_p1 hx hy :: mult_pn tx ty]
    .
Proof.
  rewrite /mult_pn => hx hy tx ty.
  by rewrite zipCons mapCons.
Qed.


Lemma mult_phase_comm:
  commutative mult_phase.
Proof.
  rewrite /commutative => x y.
  by case x, y.
Qed.

Lemma get_phase_pn_cons n:
  forall (hx hy: PauliBase) (tx ty: PauliTupleBase n),
  get_phase_pn [tuple of hx :: tx] [tuple of hy :: ty] = 
  mult_phase (get_phase hx hy) (get_phase_pn tx ty).
Proof.
  intros.
  rewrite /get_phase_pn  /=.
  rewrite mult_phase_comm.
  rewrite -foldl_rcons /=.
  symmetry.
  rewrite (foldl_foldr mult_phase_assoc mult_phase_comm).
  rewrite foldr_rcons mult_phase_comm.
  rewrite mult_phase_id.
  by rewrite (foldl_foldr mult_phase_assoc mult_phase_comm).
Qed.  


Lemma get_phase_png_cons {n: nat} :
  forall px py hx hy (tx ty: PauliTupleBase n),
    get_phase_png (px, [tuple of (hx :: tx)]) (py, [tuple of (hy :: ty)])
  = mult_phase (get_phase hx hy) (get_phase_png (px, tx) (py, ty)).
Proof.
  move => *.
  rewrite /get_phase_png get_phase_pn_cons.
  by rewrite !mult_phase_assoc.
Qed.


Lemma get_phase_png_assoc n:
  forall (a b c: PauliTuple n),
  get_phase_png (get_phase_png a b, mult_pn a.2 b.2) c = 
  get_phase_png a (get_phase_png b c, mult_pn b.2 c.2).
Proof.
  induction n.
  - move => [sx px] [sy py] [sz pz].
    rewrite (tuple0 px) (tuple0 py) (tuple0 pz) /=.
    rewrite /get_phase_png /=.
    by rewrite mult_phase_assoc.
  - move => [sx px] [sy py] [sz pz] /=.
    case : px / tupleP => hx tx.
    case : py / tupleP => hy ty.
    case : pz / tupleP => hz tz.
    move:  (IHn (sx, tx) (sy, ty) (sz, tz)) => IHn0.
    clear IHn.
    rewrite ?mult_pn_cons /get_phase_png ?get_phase_pn_cons.
    rewrite /get_phase_png /= in IHn0.
    (* case hx, hy, hz. *) 
    (* all: try by rewrite IHn0. *)
    rewrite -?mult_phase_assoc.  
    remember 
      (get_phase_pn (mult_pn tx ty) tz) as pt.
    rewrite (mult_phase_comm  pt).
    rewrite mult_phase_assoc.
    rewrite mult_phase_assoc.
    remember 
      ((mult_phase (get_phase (mult_p1 hx hy) hz) (get_phase hx hy))) as const.
    rewrite -mult_phase_assoc.
    rewrite (mult_phase_comm _ pt).
(* Too Tedious to continue *)
Admitted. (* Need to construct some autowrite mechanism *) 


(* Do not try to attempt this! *)
(* This is not valid *)
Lemma get_phase_png_comm n:
  forall (a b: PauliTuple n),
  get_phase_png a b <>
  get_phase_png b a.
Abort.
  

Lemma mult_png_assoc n: 
  associative (@mult_png n).
Proof.
  rewrite /associative /mult_png => x y z.
  case x => sx px.
  case y => sy py.
  case z => sz pz.
  f_equal.
  2: by rewrite mult_pn_assoc.
  by rewrite ?get_phase_png_assoc.
Qed.

Lemma get_phase_pn_id n:
  forall v,
  get_phase_pn (id_pn n) v = One.
Proof.
  move => v.
  induction n.
  by rewrite tuple0 (tuple0 v).
  case : v / tupleP => hv tv.
  rewrite pn_idP /get_phase_pn /=.
  rewrite /id_pn /get_phase_pn in IHn.
  by rewrite IHn.
Qed.

Definition id_png (n:nat) := 
  (One, id_pn n).

Lemma mult_png_id n:
  left_id (id_png n) (@mult_png n).
Proof.
  rewrite  /mult_png /left_id /= => x.
  case x => s v.
  rewrite mult_pn_id /id_png /get_phase_png.
  rewrite mult_phase_id .
  f_equal.
  by rewrite get_phase_pn_id.
Qed.

Check inv_png.

Lemma inv_pn_pres_phase n:
  forall (v: PauliTupleBase n),
  get_phase_pn (inv_pn v) v = One.
Proof.
  move => v.
  rewrite /get_phase_pn.
  induction n.
    by rewrite (tuple0) /=.
  case : v / tupleP => hv tv.
  by case hv; rewrite /= IHn.
Qed.
  

Lemma mult_png_left_inv n:
  left_inverse (id_png n) inv_png mult_png. 
Proof.
  rewrite /left_inverse /mult_png /inv_png /id_png => x.
  case x => p v.
  rewrite mult_pn_left_inv.
  f_equal.
  rewrite /get_phase_png mult_phase_left_inv.
  rewrite mult_phase_comm mult_phase_id.
  by rewrite inv_pn_pres_phase.
Qed.

Section Strcture.

Variable n: nat.

HB.instance Definition _ := Finite.on (@PauliTuple n).
HB.instance Definition _ := isMulGroup.Build
  (@PauliTuple n) (@mult_png_assoc n) (@mult_png_id n) (@mult_png_left_inv n).



End Strcture.

End PNGGroup.

Require Import QuantumLib.Quantum.
(* Make sure it is loaded *)

(* 
Interprete Pauli Groups (1-qubit and n-qubit) by Robert's QuantumLib
*)
Section Interpretation.

Import P1Group.

(* 
==========================
interpretation of group p1 
==========================
*)
Definition p1_int (p : PauliBase) : Square 2 :=
match p with
| I => Matrix.I 2 
| X => Quantum.σx
| Y => Quantum.σy
| Z => Quantum.σz
end.


(* Check action.act act_p1. *)

(* Goal (action.act act_p1 ∣0⟩ X) = ∣1⟩. *)
(* Proof. *)
(*   rewrite /= /apply_p1. *)
(*   by lma'. *)
(* Qed. *)


(* 
==========================
interpretation of group p1g 
==========================
*)

Import P1GGroup.

Definition phase_int (s: phase): C := 
  match s with
  | One => C1
  | NOne => -C1
  | Img => Ci
  | NImg => - Ci
  end.

Definition p1g_int(p: PauliOp): Square 2 :=
  match p with
  | pair s p => (phase_int s) .* (p1_int p)
  end.


(* 
==========================
interpretation of group pn 
==========================
*)

Import PNGroup.


Fixpoint pn_int {n: nat} : (n.-tuple PauliBase) -> Square (2^n) :=
  if n is n'.+1 return (n.-tuple PauliBase) ->  Square (2^n)
  then fun xs => (p1_int (thead xs)) ⊗ (pn_int (behead xs))
  else fun _ => Matrix.I 1.

Goal pn_int [tuple X; Y; Z] = σx ⊗ σy ⊗ σz.
Proof.
  rewrite /=.
  Qsimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

Definition id1_pn: PauliTupleBase 1 := [tuple I].
Lemma mult_pn_thead n:
forall (hy hx: PauliBase) (ty tx: PauliTupleBase n), 
  thead (mult_pn [tuple of hy :: ty] [tuple of hx :: tx]) = (mulg hy hx) .
Proof.
  intros.
  unfold mult_pn.
  by rewrite zipCons mapCons theadCons.
Qed.


Lemma mult_pn_behead n:
forall (hy hx: PauliBase) (ty tx: PauliTupleBase n), 
  behead_tuple (mult_pn [tuple of hy :: ty] [tuple of hx :: tx]) = (mulg ty tx) .
Proof.
  intros.
  unfold mult_pn.
  by rewrite zipCons mapCons beheadCons.
Qed.


Check kron_assoc.

Ltac pn_int_simpl :=
  Qsimpl;
  repeat rewrite kron_assoc;
  auto with wf_db.

Example pn_interpret:
pn_int [X;Z;Y;I] = σx ⊗ σz ⊗ σy ⊗ Matrix.I 2.
Proof.
  rewrite /pn_int /=.
  by pn_int_simpl.
Qed.

(* 
==========================
interpretation of group png
==========================
*)

Import PNGGroup.

Definition png_int {n:nat} (p: PauliTuple n): Square (2^n) :=
  match p with
  | (phase, tuple) => (phase_int phase) .* (pn_int tuple)
  end.

Lemma png_int_one n:
  forall (pt: PauliTupleBase n),
  pn_int pt = png_int (One, pt).
Proof.
  move => pt.
  by rewrite /png_int /= Mscale_1_l.
Qed.

Lemma phase_int_comp: forall x y,
phase_int (mult_phase x y) = phase_int x * phase_int y.
Proof.
  move => x y.
  case x; case y;
  simpl; lca.
Qed.

Print get_phase_pn.

Lemma get_phase_pn_behead n:
  forall x y (tx ty: PauliTupleBase n),
  (get_phase_pn [tuple of y :: ty] [tuple of x :: tx]) = 
    mult_phase (get_phase y x) (get_phase_pn ty tx).
Proof.
  move => x y tx ty.
  by rewrite get_phase_pn_cons.
Qed.

Lemma p1_int_Mmult: forall x y,
  p1_int y ×  p1_int x = phase_int (get_phase y x) .* p1_int (mulg y x).
Proof.
  move => x y.
  case x; case y; simpl; lma'.
Qed.


Lemma pn_int_Mmult n: forall (x y: PauliTupleBase n),
phase_int (get_phase_pn x y) .* pn_int (mult_pn x y) =
(pn_int x × pn_int y).
Proof.
  move => x y.
  induction n.
  - rewrite tuple0 (tuple0 y) /=; lma'.
  - case: x / tupleP; case : y / tupleP => x tx y ty.
    rewrite /= !theadCons !beheadCons /= .
    rewrite kron_mixed_product'; try easy.
    rewrite mult_pn_behead mult_pn_thead get_phase_pn_behead.
    rewrite phase_int_comp p1_int_Mmult -IHn.
    rewrite !Mscale_kron_dist_l !Mscale_kron_dist_r.
    by rewrite Mscale_assoc.
Qed.
    

Lemma png_int_Mmult n:
  forall (x y: PauliTuple n),
  png_int x × png_int y = png_int (mulg x y).
Proof.
  move  => [sx x] [sy y].
  rewrite /png_int /= /get_phase_png.
  rewrite !Mscale_mult_dist_r !Mscale_mult_dist_l Mscale_assoc.
  rewrite !phase_int_comp.
  rewrite -pn_int_Mmult !Mscale_assoc.
  rewrite Cmult_assoc Cmult_comm .
  by rewrite (Cmult_comm (phase_int sy)) Cmult_assoc.
Qed.

End Interpretation.


Module Export all_pauligroup.
  Export P1Group.
  Export P1GGroup.
  Export PNGroup.
  Export PNGGroup.
End all_pauligroup.