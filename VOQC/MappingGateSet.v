Require Export UnitaryListRepresentation.

(** This gate set is use as the output of circuit mapping. It consists of
   single-qubit gates (from some other gate set), CX gates, and SWAP gates.
   We distinguish between CX and SWAP (which can be implemented using three
   CXs) to facilitate translation validation. *)

Inductive Map_Unitary (u : Set) : nat -> Set := 
  | U_U        : u -> Map_Unitary u 1 
  | U_CX       : Map_Unitary u 2
  | U_SWAP     : Map_Unitary u 2.

Arguments U_U {u}.
Arguments U_CX {u}.
Arguments U_SWAP {u}.

Module MappingGateSet (G : GateSet) <: GateSet.

Definition U := Map_Unitary (G.U 1).

Definition to_base {n dim} (u : U n) (qs : list nat) (pf : List.length qs = n) :=
  match u with
  | U_U u  => let q := List.nth O qs O in G.to_base u [q] (one_elem_list q)
  | U_CX   => @SQIR.CNOT dim (List.nth O qs O) (List.nth (S O) qs O)
  | U_SWAP => @SQIR.SWAP dim (List.nth O qs O) (List.nth (S O) qs O)
  end.

Local Transparent SQIR.CNOT SQIR.SWAP.

Lemma to_base_only_uses_qs : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n),
    @only_uses _ dim (to_base u qs pf) qs.
Proof.
  intros.
  destruct u; simpl.
  - destruct qs; inversion pf.
    destruct qs; inversion pf.
    simpl.  
    apply G.to_base_only_uses_qs.
  - constructor; apply nth_In; lia.
  - repeat constructor; apply nth_In; lia.
Qed.

Lemma to_base_WT : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n),
  @uc_well_typed _ dim (to_base u qs pf) <-> (bounded_list qs dim /\ List.NoDup qs).
Proof.
  intros n dim u s pf.
  split.
  - intro H.
    destruct u. 
    all: repeat (destruct s; simpl in *; try lia). 
    + apply G.to_base_WT in H. auto.
    + inversion H; subst.
      unfold bounded_list; split.
      intros x [Hx | [Hx | Hx]]; subst; easy.
      repeat constructor; auto.
      intro contra; destruct_In; auto.
    + inversion H; inversion H3; subst.
      unfold bounded_list; split.
      intros x [Hx | [Hx | Hx]]; subst; easy.
      repeat constructor; auto.
      intro contra; destruct_In; auto.
  - intro H.
    destruct u.
    all: repeat (destruct s; simpl in *; try lia). 
    + apply G.to_base_WT. auto.
    + destruct H as [H1 H2].
      inversion H2; subst.
      assert (n < dim)%nat.
      { apply H1. left. auto. }
      assert (n0 < dim)%nat.
      { apply H1. right. left. auto. }
      assert (n <> n0).
      { intro contra. contradict H3. left. auto. }
      constructor; auto.
    + destruct H as [H1 H2].
      inversion H2; subst.
      assert (n < dim)%nat.
      { apply H1. left. auto. }
      assert (n0 < dim)%nat.
      { apply H1. right. left. auto. }
      assert (n <> n0).
      { intro contra. contradict H3. left. auto. }
      repeat constructor; auto.
Qed.

Lemma to_base_map_commutes : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n) (f : nat -> nat) (pfm : List.length (map f qs) = n),
  @to_base _ dim u (map f qs) pfm = map_qubits f (to_base u qs pf).
Proof.
  intros n dim u qs pf f pfm.
  destruct u; simpl.
  repeat (destruct qs; simpl in *; try lia). 
  erewrite <- G.to_base_map_commutes.
  reflexivity.
  all: repeat erewrite map_nth_In; try reflexivity; lia.
Qed.

Local Opaque SQIR.CNOT SQIR.SWAP.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | U_U u1, U_U u2 => G.match_gate u1 u2
  | U_CX, U_CX | U_SWAP, U_SWAP => true
  | _, _ => false
  end.

Lemma match_gate_implies_eq : forall {n} dim (u u' : U n) (qs : list nat) (pf : List.length qs = n), 
  match_gate u u' = true -> uc_equiv (@to_base n dim u qs pf) (to_base u' qs pf).
Proof.
  intros.
  dependent destruction u; dependent destruction u'.
  all: inversion H; try reflexivity.
  apply G.match_gate_implies_eq. auto.
Qed.

End MappingGateSet.
