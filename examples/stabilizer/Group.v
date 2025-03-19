(*
Deprecated. 
We now use mathcomp group.
Do not use. 
*)

Module Group.

Record group: Type := {
  A : Type;
  op: A -> A -> A;
  sym: A -> A;
  e: A;
  e_neutral_left : forall x:A, op e x = x;
  sym_op: forall x y z: A, op (op x y) z = op x (op y z);
  op_comm: forall x y: A, op x y = op y x
}.

End Group.


