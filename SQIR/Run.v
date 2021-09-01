Require Import UnitarySem.
Require Import VectorStates.
(* Require Import Coq.Lists.Streams. *)

(* Parameter rng : nat -> R. *)

(* Somewhere need an axiom saying
   a <> b
   rng a ⟂ rng b *)


(* MOVE TO: Matrix.v *)
Fixpoint vec_to_list {n : nat} (v : Vector n) :=
  match n with
  | O    => nil
  | S n' => v n' O :: @vec_to_list n' v
  end.

Lemma vec_to_list_length_aux : forall m n (v : Vector n), length (@vec_to_list m v) = m.
Proof.
  intros.
  induction m; auto.
  simpl. rewrite IHm.
  reflexivity.
Qed.

Lemma vec_to_list_length : forall n (v : Vector n), length (vec_to_list v) = n.
Proof. intros. apply vec_to_list_length_aux. Qed.

(* MOVE TO: Complex.v *)
Definition Cmod2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Lemma Cmod2_ge_0 : forall c, 0 <= Cmod2 c.
Proof. intros. simpl. field_simplify. apply Rplus_le_le_0_compat; apply pow2_ge_0. Qed.

(* Choose an index in the list l based on random number r ∈ [0,1).
   
   Example: Say that the input list is l = [.2, .3, .4, .1] (which might correspond
   to the probabilities of measuring the outcomes 00, 01, 10, 11). Then this
   function will return:
    * 0 for r ∈ [0, .2)
    * 1 for r ∈ [.2, .5)
    * 2 for r ∈ [.5, .9)
    * 3 for r ∈ [.9, 1) 

   The probability of getting a particular outcome is the size of this interval.
   (See max_interval below.) *)
Fixpoint sample (l : list R) (r : R) : nat :=
  match l with
  | nil    => 0 (* error case *)
  | x :: l' => if Rle_lt_dec r x then 0 else S (sample l' (r-x))
  end.

(* Run ucom c on the zero input vector and return a list with the probabilities
   of each measurement outcome. *)
Definition run {dim} (c : base_ucom dim) : list R :=
  let v := (uc_eval c) × basis_vector (2^dim) 0 in
  map Cmod2 (vec_to_list v).

(* Run ucom c on the zero input vector and return the result of
   measuring all qubits as a nat. rnd is a random input in [0,1]. *)
Definition run_and_measure {dim} (c : base_ucom dim) (rnd : R) : nat :=
  sample (run c) rnd.

(* Probability of a particular outcome. *)
Definition pr_outcome {dim} (c : base_ucom dim) (i : nat) : R :=
  nth i (run c) 0.

(* Add adjacent elements in l within range width, resulting in a list with 
   segs elements. *)
(* TODO: Replace with a more elegant algebraic definition. *)
Fixpoint sum_width (l : list R) (width segs : nat) : list R :=
  match segs with
  | 0 => []
  | S segs' => fold_left Rplus (firstn width l) 0 :: sum_width (skipn width l) width segs'
  end.

(* Example: *)
Eval simpl in (sum_width (1 :: 3 :: 4 :: 6 :: 2 :: 1 :: 5 :: 2 :: 1 :: 5 :: 2 :: 8 :: []) 3 4).

(* Same as run_and_measure, but only measures the first n qubits. *)
Definition run_and_measure_partial (n k : nat) (c : base_ucom (n + k)) (rnd : R) : nat :=
  let l := sum_width (run c) (2^k) (2^n) in
  sample l rnd.

Definition pr_outcome_partial (n k : nat) (c : base_ucom (n + k)) (i : nat) : R := 
  let l := sum_width (run c) (2^k) (2^n) in
  nth i l 0.

(* The probability that distribution D satisifies predicate P is the 
   proportion of values for rnd such that (sample D rnd) satisifes P.
   In the simplest case, where P holds only between r1 and r2, this 
   probability is (r2 - r1). *)
(* TODO: Is there a better run-based definition? *)
(* TODO: are r1 <= r2, 0 <= r1, r2 <= 1 bounds necessary? *)
Inductive max_interval (P : R -> Prop) : R -> Prop :=
| MI: forall r1 r2, 0 <= r1 <= r2 ->
           (forall r, r1 < r < r2 -> P r) ->               
           (forall r, 0 <= r < r1 -> ~ P r) ->
           (forall r, r2 < r -> ~ P r) ->
           max_interval P (r2 - r1)%R.

Lemma max_interval_unique : forall r1 r2 P,
    max_interval P r1 ->
    max_interval P r2 ->
    r1 = r2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (total_order_T r0 r3) as [[L03 | E03] | G03]; try lra.
  2: {
    destruct (total_order_T r1 r4) as [[L14 | E14] | G14]; try lra.
    remember ((r1 + r4) / 2)%R as r14.
    assert (r1 < r14 < r4)%R by lra.
    destruct (total_order_T r0 r14) as [[L | E] | G]; try lra.
    + assert (P r14) by (apply H6; lra).
      assert (~ P r14) by (apply H4; lra).
      easy.
    + remember ((r14 + r4) / 2)%R as r144.
      assert (r14 < r144 < r4)%R by lra.
      assert (P r144) by (apply H6; lra).
      assert (~ P r144) by (apply H4; lra).
      easy.
    + assert (P r14) by (apply H6; lra).
      assert (~ P r14) by (apply H3; lra).
      easy.
  }
  destruct (total_order_T r0 r1) as [[L01 | E01] | G01].
  - destruct (total_order_T r1 r3) as [[L13 | E13] | G13].
    + remember ((r0 + r1) / 2)%R as r01.
      assert (r0 < r01 < r1)%R by lra.
      assert (P r01) by (apply H2; lra).
      assert (~ P r01) by (apply H7; lra).
      easy.
    + remember ((r0 + r1) / 2)%R as r01.
      assert (r0 < r01 < r1)%R by lra.
      assert (P r01) by (apply H2; lra).
      assert (~ P r01) by (apply H7; lra).
      easy.
    + remember ((r0 + r3) / 2)%R as r03.
      assert (r0 < r03 < r3)%R by lra.
      assert (P r03) by (apply H2; lra).
      assert (~ P r03) by (apply H7; lra).
      easy.
  - destruct (total_order_T r3 r4) as [[L34 | E34] | G34]; try lra.
    + remember ((r3 + r4) / 2)%R as r34.
      assert (r3 < r34 < r4)%R by lra.
      assert (P r34) by (apply H6; lra).
      assert (~ P r34) by (apply H4; lra).
      easy.
    + remember ((r3 + r4) / 2)%R as r43.
      assert (r4 < r43 < r3)%R by lra.
      assert (P r43) by (apply H2; lra).
      assert (~ P r43) by (apply H8; lra).
      easy.
  - destruct (total_order_T r0 r4) as [[L04 | E04] | G04].
    + remember ((r0 + r1) / 2)%R as r10.
      assert (r1 < r10 < r0)%R by lra.
      assert (P r10) by (apply H6; lra).
      assert (~ P r10) by (apply H3; lra).
      easy.
    + remember ((r0 + r1) / 2)%R as r10.
      assert (r1 < r10 < r0)%R by lra.
      assert (P r10) by (apply H6; lra).
      assert (~ P r10) by (apply H3; lra).
      easy.
    + remember ((r0 + r3) / 2)%R as r03.
      assert (r0 < r03 < r3)%R by lra.
      assert (P r03) by (apply H2; lra).
      assert (~ P r03) by (apply H8; lra).
      easy.
Qed.

Lemma max_interval_size : forall k l,
    (k < length l)%nat ->
    Forall (fun x => 0 <= x) l ->
    max_interval (fun x => sample l x = k) (nth k l 0).
Proof.
  intros.
  gen k.
  induction l; intros; simpl in H; try lia.
  inversion H0; subst.
  destruct k; simpl.
  - replace a with (a-0)%R by lra.
    econstructor; intros; try lra. 
    + destruct (Rle_lt_dec r (a - 0)); try lra; easy.
    + destruct (Rle_lt_dec r (a - 0)); try lra. easy.
  - apply lt_S_n in H.
    specialize (IHl H4 k H).
    inversion IHl.
    replace (r2 - r1)%R with ((r2 + a) - (r1 + a))%R by lra.
    constructor; intros; try lra.
    + destruct (Rle_lt_dec r a). lra.
      f_equal.
      apply H5.
      lra.
    + destruct (Rle_lt_dec r a). lia.
      intros F.
      apply (H6 (r-a)%R). lra.
      lia.
    + destruct (Rle_lt_dec r a). lia.
      intros F.
      apply (H7 (r-a)%R). lra.
      lia.
Qed.      
  
(* Connect pr_outcome and run_and_measure using max_interval. *)
Lemma pr_outcome_eq_aux : forall dim (c : base_ucom dim) n,
  (n < 2^dim)%nat ->
  max_interval (fun x : R => run_and_measure c x = n) (pr_outcome c n).
Proof.
  intros.
  apply max_interval_size.
  unfold run.
  rewrite map_length, vec_to_list_length; easy.
  unfold run.
  remember (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)) as l. clear Heql.
  apply Forall_nth; intros.
  gen l. induction i; intros.
  - destruct l. simpl in H0; lia.
    simpl. apply Cmod2_ge_0.
  - destruct l; simpl in H0; try lia.
    apply IHi.
    lia.
Qed.    

(* I prefer this definition, but it needs the uniqueness proof above. -RNR *)
Lemma pr_outcome_eq : forall dim (c : base_ucom dim) n r,
  (n < 2^dim)%nat ->
  pr_outcome c n = r <-> max_interval (fun x => run_and_measure c x = n) r.
Proof.
  split; intros.
  - rewrite <- H0.
    apply pr_outcome_eq_aux.
    easy.
  - eapply max_interval_unique.
    apply pr_outcome_eq_aux; trivial.
    easy.
Qed.

Lemma length_sum_width :
  forall m l n,
    length l = (n * m)%nat ->
    length (sum_width l n m) = m.
Proof.
  induction m; intros.
  - easy.
  - simpl. rewrite IHm. easy. rewrite skipn_length. lia.
Qed.

Lemma fold_left_Rplus :
  forall l r,
    fold_left Rplus l r = (r + fold_left Rplus l 0)%R.
Proof.
  induction l; intros.
  - simpl. lra.
  - simpl. rewrite IHl. rewrite IHl with (r := (0 + a)%R). lra.
Qed.

Lemma fold_left_firstn :
  forall n l,
    0 <= fold_left Rplus (firstn n (map Cmod2 l)) 0.
Proof.
  induction n; intros.
  - simpl. lra.
  - destruct l.
    + simpl. lra.
    + simpl. rewrite fold_left_Rplus. specialize (IHn l).
      specialize (Cmod2_ge_0 c) as G.
      lra.
Qed.

Lemma skipn_map :
  forall {A B} n (l : list A) (f : A -> B),
    skipn n (map f l) = map f (skipn n l).
Proof.
  intros A B. induction n; intros.
  - simpl. easy.
  - destruct l. simpl. easy.
    simpl. apply IHn.
Qed.
    
Lemma nth_sum_width_Cmod2 :
  forall i m l n d,
    length l = (n * m)%nat ->
    (i < m)%nat ->
    0 <= nth i (sum_width (map Cmod2 l) n m) d.
Proof.
  induction i; intros.
  - destruct m. lia.
    simpl. apply fold_left_firstn.
  - destruct m. lia.
    simpl. rewrite skipn_map.
    apply IHi. rewrite skipn_length. lia. lia.
Qed.
  
Lemma pr_outcome_partial_eq_aux : forall n k (c : base_ucom (n + k)) i,
  (i < 2^n)%nat ->
  max_interval (fun x : R => run_and_measure_partial n k c x = i) (pr_outcome_partial n k c i).
Proof.
  intros.
  remember (vec_to_list (uc_eval c × basis_vector (2 ^ (n + k)) 0)) as l.
  assert (length l = 2 ^ n * 2 ^ k)%nat by (rewrite Heql; rewrite vec_to_list_length; rewrite Nat.pow_add_r; lia).
  apply max_interval_size.
  rewrite length_sum_width. easy.
  unfold run.
  rewrite <- Heql. rewrite map_length. rewrite H0. lia.
  apply Forall_nth; intros.
  unfold run in *.
  rewrite <- Heql in *. rewrite length_sum_width in H1.
  apply nth_sum_width_Cmod2. rewrite H0. lia. lia. rewrite map_length. lia.
Qed.    

Lemma pr_outcome_partial_eq : forall n k (c : base_ucom (n + k)) i r,
  (i < 2^n)%nat ->
  pr_outcome_partial n k c i = r <-> max_interval (fun x => run_and_measure_partial n k c x = i) r.
Proof.
  split; intros.
  - rewrite <- H0.
    apply pr_outcome_partial_eq_aux.
    easy.
  - eapply max_interval_unique.
    apply pr_outcome_partial_eq_aux; trivial.
    easy.
Qed.

(* TODO: Generalize max_interval to support more types of predicates. *)

(* Using a single predicate and dividers: *)
Inductive max_interval_disjoint (P : R -> Prop) (rl rr : R) : R -> Prop :=
| MaxConsec : forall r1 r2, rl <= r1 <= r2 /\ r2 <= rr ->
            (forall r, r1 < r < r2 -> P r) ->               
            (forall r, rl <= r < r1 -> ~ P r) ->
            (forall r, r2 < r <= rr -> ~ P r) ->
            max_interval_disjoint P rl rr (r2 - r1)%R
| MaxSplit : forall rm r1 r2, rl < rm < rr -> 
                   ~ P rm ->
                   max_interval_disjoint P rl rm r1 ->
                   max_interval_disjoint P rm rr r2 ->
                   max_interval_disjoint P rl rr (r1 + r2).

(* Using a list of predicates *)
(* Doesn't imply disjointness. *)
Inductive max_interval_sum : list (R -> Prop) -> R -> Prop :=
| MaxEmpty : max_interval_sum [] 0 (* could remove this case to simplify *)
| MaxSing : forall P r, max_interval P r -> max_interval_sum [P] r 
| MaxMult : forall L P r1 r2, max_interval P r1 -> max_interval_sum L r2 ->
                         max_interval_sum (P :: L) (r1 + r2).

(* TODO: Uniqueness proofs for max_interval_disjoint and max_interval_sum *)
Lemma max_interval_disjoint_unique : forall rl rr r1 r2 P,
    max_interval_disjoint P rl rr r1 ->
    max_interval_disjoint P rl rr r2 ->
    r1 = r2.
Admitted.

Lemma max_interval_sum_unique : forall L r1 r2,
    max_interval_sum L r1 ->
    max_interval_sum L r2 ->
    r1 = r2.
Proof.
  induction L; intros. inversion H. inversion H0. easy.
  inversion H; inversion H0; subst.
  - apply max_interval_unique with a; easy.
  - inversion H9. rewrite Rplus_0_r.
    apply max_interval_unique with a; easy.
  - inversion H5. rewrite Rplus_0_r.
    apply max_interval_unique with a; easy.
  - rewrite (max_interval_unique r0 r4 a); trivial.
    rewrite (IHL r3 r5); easy.
Qed.

