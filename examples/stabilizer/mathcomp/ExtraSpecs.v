From mathcomp Require Import fingroup.

Section commutative.

Definition commute_at {T: Type} (op: T -> T -> T) (a b: T) : Prop :=
  op a b = op b a.

Definition anticommute_at {T: Type} (op: T -> T -> T) (opp: T -> T) (a b: T) : Prop :=
  op a b = opp (op b a).
  
Definition commute {T: Type} (op: T -> T -> T) : Prop :=
  forall a b: T, commute_at op a b.

Definition anticommute {T: Type} 
  (op: T -> T -> T) (opp: T -> T) : Prop :=
forall a b: T, anticommute_at op opp a b.

Definition bicommute {T: Type}
  (op: T -> T -> T) (opp: T -> T) : Prop :=
forall a b: T, commute_at op a b \/ anticommute_at op opp a b.


Locate commute.

(* When it is mathcomp group, we can simplify the definition *)
Definition commuteg (T: finGroupType) :=
  forall (x y: T), fingroup.commute x y.

(* TODO: Define anitcommute with abelian monoid *)

End commutative.

From QuantumLib Require Import Quantum.

Section Projector.


Record Projector {n:nat} := ProjectorBuild {
  P : Square (2^n)
; is_hermitian : P† = P
; is_idempotent : P × P = P 
}.

End Projector.