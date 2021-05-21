Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
(**********************)
(** Unitary Programs **)
(**********************)
Definition var := nat.

Definition posi : Type := (var * nat).

Definition posi_eq (r1 r2 : posi) : bool := 
                match r1 with (x1,y1)
                            => match r2
                               with (x2,y2) => (x1 =? x2) && (y1 =? y2)
                               end
                end.

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Lemma mod_sum_lt :
  forall x y M,
    x < M ->
    y < M ->
    (x + y) mod M < x <-> x + y >= M.
Proof.
  intros. split; intros.
  - assert ((x + y) mod M < x + y) by lia.
    rewrite Nat.div_mod with (y := M) in H2 by lia.
    assert (0 < (x + y) / M) by nia.
    rewrite Nat.div_str_pos_iff in H3 by lia. lia.
  - rewrite Nat.mod_eq by lia.
    assert (1 <= (x + y) / M < 2).
    { split.
      apply Nat.div_le_lower_bound; lia.
      apply Nat.div_lt_upper_bound; lia.
    }
    replace (M * ((x + y) / M)) with M by nia.
    lia.
Qed.


Lemma mod_sum_lt_bool :
  forall x y M,
    x < M ->
    y < M ->
    ¬ (M <=? x + y) = (x <=? (x + y) mod M).
Proof.
  intros. bdestruct (M <=? x + y); bdestruct (x <=? (x + y) mod M); try easy.
  assert ((x + y) mod M < x) by (apply mod_sum_lt; lia). lia.
  assert (x + y >= M) by (apply mod_sum_lt; lia). lia.
Qed.

Notation "i '==?' j" := (posi_eq i j) (at level 50).


Lemma posi_eqb_eq : forall a b, a ==? b = true -> a = b.
Proof.
 intros. unfold posi_eq in H.
 destruct a. destruct b.
 apply andb_true_iff in H.
 destruct H. apply Nat.eqb_eq in H.
 apply Nat.eqb_eq in H0. subst. easy.
Qed.

Lemma posi_eqb_neq : forall a b, a ==? b = false -> a <> b.
Proof.
 intros. unfold posi_eq in H.
 destruct a. destruct b.
 apply andb_false_iff in H.
 destruct H. apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite eq1 in H. easy.
 apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite H0 in H. easy.
Qed.

Lemma posi_eq_reflect : forall r1 r2, reflect (r1 = r2) (posi_eq r1 r2). 
Proof.
  intros.
  destruct (r1 ==? r2) eqn:eq1.
  apply  ReflectT.
  apply posi_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply posi_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve posi_eq_reflect : bdestruct.


Definition rz_val : Type := (nat -> bool).

Inductive val := nval (b:bool) (r:rz_val) | hval (b1:bool) (b2:bool) (r:rz_val) | qval (rc:rz_val) (r:rz_val).

(* Update the value at one index of a boolean function. *)
Definition eupdate {S} (f : posi -> S) (i : posi) (x : S) :=
  fun j => if j ==? i then x else f j.

Lemma eupdate_index_eq {S} : forall (f : posi -> S) i b, (eupdate f i b) i = b.
Proof.
  intros. 
  unfold eupdate.
  bdestruct (i ==? i). easy.
  contradiction.
Qed.

Lemma eupdate_index_neq {S}: forall (f : posi -> S) i j b, i <> j -> (eupdate f i b) j = f j.
Proof.
  intros. 
  unfold eupdate.
  bdestruct (j ==? i).
  subst. contradiction.
  reflexivity.
Qed.

Lemma eupdate_same {S}: forall (f : posi -> S) i b,
  b = f i -> eupdate f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.

Lemma eupdate_same_1 {S}: forall (f f': posi -> S) i b b',
 f = f' -> b = b' -> eupdate f i b = eupdate f' i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.


Lemma eupdate_twice_eq {S}: forall (f : posi -> S) i b b',
  eupdate (eupdate f i b) i b' = eupdate f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.  

Lemma eupdate_twice_neq {S}: forall (f : posi -> S) i j b b',
  i <> j -> eupdate (eupdate f i b) j b' = eupdate (eupdate f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); bdestruct (x ==? j); subst; easy.
Qed.


Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).


Lemma same_eupdate : forall (f f' : posi -> val) c v, f = f' -> f[c |-> v] = f'[c |-> v].
Proof.
  intros. 
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. subst. easy.
  assumption. assumption.
Qed.

Lemma same_eupdate_1 : forall (f f' : posi -> val) c v v', f = f' -> v = v' -> f[c |-> v] = f'[c |-> v'].
Proof.
  intros. 
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. subst. easy.
  assumption. assumption.
Qed.

(* Adds an equality in the context *)
Ltac ctx e1 e2 :=
  let H := fresh "HCtx" in
  assert (e1 = e2) as H by reflexivity.

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.

(*
Ltac fb_push_n_simpl := repeat (try rewrite fb_push_n_left by lia; try rewrite fb_push_n_right by lia).
Ltac update_simpl := repeat (try rewrite update_index_neq by lia); try rewrite update_index_eq by lia.
*)
Ltac BreakIfExpression :=
  match goal with
  | [ |- context[if ?X <? ?Y then _ else _] ] => bdestruct (X <? Y); try lia
  | [ |- context[if ?X <=? ?Y then _ else _] ] => bdestruct (X <=? Y); try lia
  | [ |- context[if ?X =? ?Y then _ else _] ] => bdestruct (X =? Y); try lia
  end.

Ltac IfExpSimpl := repeat BreakIfExpression.

(* irrelavent vars. *)
Definition vars_neq (l:list var) := forall n m x y, nth_error l m = Some x ->  nth_error l n = Some y -> n <> m -> x <> y.


Inductive exp := SKIP (p:posi) | X (p:posi) | CU (p:posi) (e:exp)
        | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (p:posi) 
        | SR (q:nat) (x:var) (* a series of RZ gates for QFT mode. *)
        | SRR (q:nat) (x:var) (* a series of RRZ gates for QFT mode. *)
        | HCNOT (p1:posi) (p2:posi)
        | Seq (s1:exp) (s2:exp).

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.


Inductive sexp :=  | Lshift (x:var) | Rshift (x:var) 
                   | Rev (x:var)  (* move the positions in x to be upside-down. *)
                 (*  | Reset (x:var) *)
                   | Exp (s:exp) | SSeq (s1:sexp) (s2:sexp).

Coercion Exp : exp >-> sexp.

Notation "p1 ;; p2" := (SSeq p1 p2) (at level 49) : exp_scope.

Inductive pexp := SExp (s:sexp) | QFT (x:var) | RQFT (x:var)
               | H (x:var) | FSeq (p1:pexp) (p2:pexp).

Coercion SExp : sexp >-> pexp.

Definition Z (p:posi) := RZ 1 p.

Notation "p1 ;;; p2" := (FSeq p1 p2) (at level 48) : exp_scope.

Fixpoint inv_exp p :=
  match p with
  | SKIP a => SKIP a
  | X n => X n
  | CU n p => CU n (inv_exp p)
  | SR n x => SRR n x
  | SRR n x => SR n x
  | HCNOT p1 p2 => HCNOT p1 p2
  | Seq p1 p2 => inv_exp p2; inv_exp p1
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  end.

Fixpoint inv_sexp p :=
  match p with 
  | Exp e => Exp (inv_exp e)
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | Rev x => Rev x
  | p1 ;; p2 => inv_sexp p2 ;; inv_sexp p1
  end.

Fixpoint inv_pexp p :=
   match p with 
    | SExp s => SExp (inv_sexp s)
    | QFT x => RQFT x
    | RQFT x => QFT x
    | H x => H x
    | FSeq p1 p2 => FSeq (inv_pexp p2) (inv_pexp p1)
   end.


Fixpoint GCCX' x n size :=
  match n with
  | O | S O => X (x,n - 1)
  | S m => CU (x,size-n) (GCCX' x m size)
  end.
Definition GCCX x n := GCCX' x n n.

Fixpoint nX x n := 
   match n with 0 => X (x,0)
            | S m => X (x,m); nX x m
   end.

(* Grover diffusion operator. *)
Definition diff_half (x c:var) (n:nat) := H x ;;; H c ;;; SExp (Exp (nX x n; X (c,0))). 

Definition diff_1 (x c :var) (n:nat) :=
  diff_half x c n ;;; SExp (Exp (GCCX x n)) ;;; (inv_pexp (diff_half x c n)).

(*The second implementation of grover's diffusion operator.
  The whole circuit is a little different, and the input for the diff_2 circuit is asssumed to in Had mode. *)
Definition diff_2 (x c :var) (n:nat) :=
  H x ;;; SExp (Exp (GCCX x n)) ;;; H x.

Fixpoint is_all_true C n :=
  match n with 0 => true
           | S m => C m && is_all_true C m
  end.

Definition const_u (C :nat -> bool) (n:nat) c := if is_all_true C n then SExp (Exp (X (c,0))) else SKIP (c,0).

Fixpoint niter_prog n (c:var) (P : pexp) : pexp :=
  match n with
  | 0    => SKIP (c,0)
  | 1    => P
  | S n' => niter_prog n' c P ;;; P
  end.

Definition body (C:nat -> bool) (x c:var) (n:nat) := const_u C n c;;; diff_2 x c n.

Definition grover_e (i:nat) (C:nat -> bool) (x c:var) (n:nat) := 
        H x;;; H c ;;; SExp (Exp (Z (c,0))) ;;; niter_prog i c (body C x c n).

(** Definition of Deutsch-Jozsa program. **)

Definition deutsch_jozsa (x c:var) (n:nat) :=
  SExp (Exp (nX x n; X (c,0))) ;;; H x ;;; H c ;;; SExp (Exp (X (c,0)));;; H c ;;; H x.

Inductive type := Had | Phi (n:nat) | Nor.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).

Definition env := Env.t type.

Definition or_not_r (x y:var) (n1 n2:nat) := x <> y \/ S n1 < n2.

Inductive exp_fresh : posi -> exp -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh p (X p')
      | sr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh p (SR n x)
      | srr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh p (SRR n x)
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh p e -> exp_fresh p (CU p' e)
      | cnot_fresh : forall p p1 p2, p <> p1 -> p <> p2 -> exp_fresh p (HCNOT p1 p2)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh p (RRZ q p')
      | seq_fresh : forall p e1 e2, exp_fresh p e1 -> exp_fresh p e2 -> exp_fresh p (Seq e1 e2).

Lemma posi_eq_dec : forall x y : posi, {x = y}+{x <> y}.
Proof.
  intros. 
  bdestruct (x ==? y). left. easy. right. easy.
Qed.

Inductive exp_fwf : exp -> Prop :=
      | skip_fwf : forall p, exp_fwf (SKIP p)
      | x_fwf : forall p,  exp_fwf (X p)
      | sr_fwf : forall n x, exp_fwf (SR n x)
      | srr_fwf : forall n x, exp_fwf (SRR n x)
      | cu_fwf : forall p e, exp_fresh p e -> exp_fwf e -> exp_fwf (CU p e)
      | hcnot_fwf : forall p1 p2, p1 <> p2 -> exp_fwf (HCNOT p1 p2)
      | rz_fwf : forall p q, exp_fwf (RZ q p)
      | rrz_fwf : forall p q, exp_fwf (RRZ q p)
      | seq_fwf : forall e1 e2, exp_fwf e1 -> exp_fwf e2 -> exp_fwf (Seq e1 e2).

Inductive well_typed_exp : env -> exp -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_nor : forall env p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (X p)
    | x_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (X p)
    | cu_nor : forall env p e, Env.MapsTo (fst p) Nor env
                        ->  well_typed_exp env e -> well_typed_exp env (CU p e)
    | cnot_had : forall env p1 p2, Env.MapsTo (fst p1) Had env -> Env.MapsTo (fst p2) Had env
                         -> well_typed_exp env (HCNOT p1 p2)
    | rz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RZ q p)
    | rz_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (RZ 1 p)
    | rrz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RRZ q p)
    | rrz_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (RRZ 1 p)
    | sr_had : forall env n m x, Env.MapsTo x (Phi n) env -> m < n -> well_typed_exp env (SR m x)
    | srr_had : forall env n m x, Env.MapsTo x (Phi n) env -> m < n -> well_typed_exp env (SRR m x)
    | e_seq : forall env p1 p2, well_typed_exp env p1 
                          -> well_typed_exp env p2 -> well_typed_exp env (p1 ; p2).


Inductive well_typed_sexp : env -> sexp -> Prop :=
    | lshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_sexp env (Lshift x)
    | lshift_had : forall env x, Env.MapsTo x Had env -> well_typed_sexp env (Lshift x)
    | rshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_sexp env (Rshift x)
    | rshift_had : forall env x, Env.MapsTo x Had env -> well_typed_sexp env (Rshift x)
    | rev_nor : forall env x, Env.MapsTo x Nor env -> well_typed_sexp env (Rev x)
    | rev_had : forall env x, Env.MapsTo x Had env -> well_typed_sexp env (Rev x)
    | exp_refl : forall env e, exp_fwf e -> well_typed_exp env e -> well_typed_sexp env (Exp e)
    | se_seq : forall env e1 e2, well_typed_sexp env e1
                  -> well_typed_sexp env e2 -> well_typed_sexp env (e1 ;; e2).


Inductive well_typed_pexp (aenv: var -> nat) : env -> pexp -> env -> Prop :=
    | sexp_refl : forall env e, well_typed_sexp env e -> well_typed_pexp aenv env (SExp e) env
    | qft_nor :  forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x (Phi (aenv x)) env)
                   -> well_typed_pexp aenv env (QFT x) env'
    | rqft_phi :  forall env env' x, Env.MapsTo x (Phi (aenv x)) env -> Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_pexp aenv env (RQFT x) env'
    | h_nor : forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x Had env) ->  
                  well_typed_pexp aenv env (H x) env'
    | h_had : forall env env' x, Env.MapsTo x Had env -> Env.Equal env' (Env.add x Nor env) ->  
                                   well_typed_pexp aenv env (H x) env'
    | fe_seq : forall env env' env'' e1 e2, well_typed_pexp aenv env e1 env' -> 
                 well_typed_pexp aenv env' e2 env'' -> well_typed_pexp aenv env (e1 ;;; e2) env''.


Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)
    | right_had: forall b1 b2 r, r 0 = false -> right_mode_val Had (hval b1 b2 r)
    | right_phi: forall n rc r, right_mode_val (Phi n) (qval rc r).

(*
Definition right_mode_vals (f:posi -> val) (x:var) (t:type) : Prop :=
    forall i, right_mode_val t (f (x,i)).
*)

(*
Inductive right_mode_pexp : env -> (posi -> val) -> pexp -> env -> Prop :=
    | qft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
             well_typed_pexp env (QFT a) env' -> right_mode_pexp env f (QFT a) env'
    | rqft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t -> 
                        well_typed_pexp env (RQFT a) env' -> right_mode_pexp env f (RQFT a) env'
    | h_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
                     well_typed_pexp env (H a) env' -> right_mode_pexp env f (H a) env'
    | sexp_right : forall env f e, right_mode_sexp env f e -> right_mode_pexp env f (SExp e) env
    | pseq_right : forall env env' env'' f e1 e2, right_mode_pexp env f e1 env'
                     -> right_mode_pexp env' f e2 env'' -> right_mode_pexp env f (e1 ;;; e2) env''.
*)
(*
Inductive right_mode_exp : env -> (posi -> val) -> exp -> Prop :=
    | skip_right : forall env f, forall p, right_mode_exp env f (SKIP p)
    | x_right : forall env f a b t, Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (X (a,b))
    | cu_right : forall env f a b t e, Env.MapsTo a t env -> right_mode_val t (f (a,b))
                      -> right_mode_exp env f e -> right_mode_exp env f (CU (a,b) e)
    | rz_right : forall env f a b t q,  Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (RZ q (a,b))
    | rrz_right : forall env f a b t q,  Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (RRZ q (a,b))
    | seq_right : forall env f e1 e2, right_mode_exp env f e1 -> right_mode_exp env f e2 -> right_mode_exp env f (e1 ; e2).

Inductive right_mode_sexp : env -> (posi -> val) -> sexp -> Prop :=
    | lshift_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Lshift a) 
    | rshift_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Rshift a)
    | rev_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Rev a)
    | exp_right : forall env f e, right_mode_exp env f e -> right_mode_sexp env f (Exp e)
    | sseq_right : forall env f e1 e2, right_mode_sexp env f e1 -> right_mode_sexp env f e2 -> right_mode_sexp env f (e1 ;; e2).


Inductive right_mode_pexp : env -> (posi -> val) -> pexp -> env -> Prop :=
    | qft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
             well_typed_pexp env (QFT a) env' -> right_mode_pexp env f (QFT a) env'
    | rqft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t -> 
                        well_typed_pexp env (RQFT a) env' -> right_mode_pexp env f (RQFT a) env'
    | h_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
                     well_typed_pexp env (H a) env' -> right_mode_pexp env f (H a) env'
    | sexp_right : forall env f e, right_mode_sexp env f e -> right_mode_pexp env f (SExp e) env
    | pseq_right : forall env env' env'' f e1 e2, right_mode_pexp env f e1 env'
                     -> right_mode_pexp env' f e2 env'' -> right_mode_pexp env f (e1 ;;; e2) env''.
*)
Lemma mapsto_always_same : forall k v1 v2 s,
           @Env.MapsTo (type) k v1 s ->
            @Env.MapsTo (type) k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply Env.find_1 in H0.
     apply Env.find_1 in H1.
     rewrite H0 in H1.
     injection H1.
     easy.
Qed.

Lemma find_add : forall k v m,
        @Env.find (type) k (Env.add k v m) = Some v.
Proof.
      intros.
      apply Env.find_1.
      apply Env.add_1.
      easy.
Qed.

Lemma mapsto_add1 : forall k v1 v2 s,
        @Env.MapsTo (type) k v1 (Env.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply Env.find_1 in H0.
      rewrite find_add in H0.
      inversion H0.
      reflexivity.
Qed.

Lemma mapsto_equal : forall k v s1 s2,
   @Env.MapsTo type k v s1 ->
   Env.Equal s1 s2 ->
   Env.MapsTo k v s2.
Proof.
      intros.
      unfold Env.Equal in H1.
      apply Env.find_2. rewrite <- H1.
      apply Env.find_1.
      assumption.
Qed.

(*
Lemma right_mode_cu : forall env f x i e, well_typed_exp env (CU (x,i) e)
                          -> right_mode_exp env f (CU (x,i) e) -> (exists b r, (f (x,i)) = nval b r).
Proof.
  intros. inv H0. inv H1. apply (mapsto_always_same x Nor t env0) in H8. subst.
  inv H9. exists b. exists r. easy.
  assumption.
Qed.
*)


(* Here we defined the specification of carry value for each bit. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Definition allfalse := fun (_:nat) => false.

Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Lemma fb_push_right:
  forall n b f, 0 < n -> fb_push b f n = f (n-1).
Proof.
  intros. induction n. lia.
  simpl. assert ((n - 0) = n) by lia.
  rewrite H1. reflexivity.
Qed.




(* fb_push_n is the n repeatation of fb_push.
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).
*)

(* A function to compile positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* A function to compile N to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition nat2fb n := N2fb (N.of_nat n).

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

Fixpoint carry b n f g :=
  match n with
  | 0 => b
  | S n' => let c := carry b n' f g in
           let a := f n' in
           let b := g n' in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_1 : forall b f g, carry b 1 f g = majb (f 0) (g 0) b.
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_n : forall n b f g, carry b (S n) f g = majb (f n) (g n) (carry b n f g).
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_sym :
  forall b n f g,
    carry b n f g = carry b n g f.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. btauto.
Qed.

Lemma carry_false_0_l: forall n f, 
    carry false n allfalse f = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_false_0_r: forall n f, 
    carry false n f allfalse = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_fbpush :
  forall n a ax ay fx fy,
    carry a (S n) (fb_push ax fx) (fb_push ay fy) = carry (majb a ax ay) n fx fy.
Proof.
  induction n; intros.
  simpl. unfold majb. btauto.
  remember (S n) as Sn. simpl. rewrite IHn. unfold fb_push. subst.
  simpl. easy.
Qed.

Lemma carry_succ :
  forall m p,
    carry true m (pos2fb p) allfalse = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  induction m; intros. simpl. destruct p; reflexivity.
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  Local Opaque fb_push carry.
  destruct p; simpl.
  rewrite carry_fbpush; unfold majb; simpl. rewrite IHm. reflexivity.
  rewrite carry_fbpush; unfold majb; simpl. rewrite carry_false_0_r. Local Transparent fb_push. simpl. btauto.
  rewrite carry_fbpush; unfold majb; simpl. Local Transparent carry. destruct m; reflexivity.
Qed.

Lemma carry_succ' :
  forall m p,
    carry true m allfalse (pos2fb p) = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  intros. rewrite carry_sym. apply carry_succ.
Qed.

Lemma carry_succ0 :
  forall m, carry true m allfalse allfalse = pos2fb xH m.
Proof.
  induction m. easy. 
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  rewrite carry_fbpush. unfold majb. simpl. rewrite carry_false_0_l. easy.
Qed.

Lemma carry_add_pos_eq :
  forall m b p q,
    carry b m (pos2fb p) (pos2fb q) ⊕ (pos2fb p) m ⊕ (pos2fb q) m = pos2fb (add_c b p q) m.
Proof.
  induction m; intros. simpl. destruct p, q, b; reflexivity.
  Local Opaque carry.
  destruct p, q, b; simpl; rewrite carry_fbpush; 
    try (rewrite IHm; reflexivity);
    try (unfold majb; simpl; 
         try rewrite carry_succ; try rewrite carry_succ'; 
         try rewrite carry_succ0; try rewrite carry_false_0_l;
         try rewrite carry_false_0_r;
         unfold allfalse; try btauto; try (destruct m; reflexivity)).
Qed.

Lemma carry_add_eq_carry0 :
  forall m x y,
    carry false m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y)) m.
Proof.
  intros.
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_false_0_l. easy.
  rewrite carry_false_0_l. btauto.
  rewrite carry_false_0_r. btauto.
  apply carry_add_pos_eq.
Qed.

Lemma carry_add_eq_carry1 :
  forall m x y,
    carry true m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y + 1)) m.
Proof.
  intros. 
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_succ0. destruct m; easy.
  rewrite carry_succ'. replace (q + 1)%positive with (Pos.succ q) by lia. btauto.
  rewrite carry_succ. replace (p + 1)%positive with (Pos.succ p) by lia. btauto.
  rewrite carry_add_pos_eq. unfold add_c. rewrite Pos.add_carry_spec.
  replace (p + q + 1)%positive with (Pos.succ (p + q)) by lia. easy.
Qed.

Definition fbxor f g := fun (i : nat) => f i ⊕ g i.

Definition msma i b f g := fun (x : nat) => if (x <? i) then 
        (carry b (S x) f g ⊕ (f (S x))) else (if (x =? i) then carry b (S x) f g else f x).

Definition msmb i (b : bool) f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else g x.

Definition msmc i b f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else (carry b x f g ⊕ f x ⊕ g x).

Definition sumfb b f g := fun (x : nat) => carry b x f g ⊕ f x ⊕ g x.

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.

Lemma sumfb_correct_carry0 :
  forall x y,
    sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
Proof.
  intros. unfold nat2fb. rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma sumfb_correct_carry1 :
  forall x y,
    sumfb true (nat2fb x) (nat2fb y) = nat2fb (x + y + 1).
Proof.
  intros. unfold nat2fb. do 2 rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry1. easy.
Qed.

Lemma sumfb_correct_N_carry0 :
  forall x y,
    sumfb false (N2fb x) (N2fb y) = N2fb (x + y).
Proof.
  intros. apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma pos2fb_Postestbit :
  forall n i,
    (pos2fb n) i = Pos.testbit n (N.of_nat i).
Proof.
  induction n; intros.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. easy.
Qed.

Lemma N2fb_Ntestbit :
  forall n i,
    (N2fb n) i = N.testbit n (N.of_nat i).
Proof.
  intros. destruct n. easy.
  simpl. apply pos2fb_Postestbit.
Qed.

Lemma Z2N_Nat2Z_Nat2N :
  forall x,
    Z.to_N (Z.of_nat x) = N.of_nat x.
Proof.
  destruct x; easy.
Qed.

Lemma Nofnat_mod :
  forall x y,
    y <> 0 ->
    N.of_nat (x mod y) = ((N.of_nat x) mod (N.of_nat y))%N.
Proof.
  intros. specialize (Zdiv.mod_Zmod x y H0) as G.
  repeat rewrite <- Z2N_Nat2Z_Nat2N. rewrite G. rewrite Z2N.inj_mod; lia.
Qed.

Lemma Nofnat_pow :
  forall x y,
    N.of_nat (x ^ y) = ((N.of_nat x) ^ (N.of_nat y))%N.
Proof.
  intros. induction y. easy.
  Local Opaque N.pow. replace (N.of_nat (S y)) with ((N.of_nat y) + 1)%N by lia.
 simpl. rewrite N.pow_add_r. rewrite N.pow_1_r. rewrite Nnat.Nat2N.inj_mul. rewrite IHy. lia.
Qed.

Lemma negatem_Nlnot :
  forall (n : nat) (x : N) i,
    negatem n (N2fb x) i = N.testbit (N.lnot x (N.of_nat n)) (N.of_nat i).
Proof.
  intros. unfold negatem. rewrite N2fb_Ntestbit. symmetry.
  bdestruct (i <? n). apply N.lnot_spec_low. lia.
  apply N.lnot_spec_high. lia.
Qed.

Lemma negatem_arith :
  forall n x,
    x < 2^n ->
    negatem n (nat2fb x) = nat2fb (2^n - 1 - x).
Proof.
  intros. unfold nat2fb. apply functional_extensionality; intro i.
  rewrite negatem_Nlnot. rewrite N2fb_Ntestbit.
  do 2 rewrite Nnat.Nat2N.inj_sub. rewrite Nofnat_pow. simpl.
  bdestruct (x =? 0). subst. simpl. rewrite N.ones_equiv. rewrite N.pred_sub. rewrite N.sub_0_r. easy.
  rewrite N.lnot_sub_low. rewrite N.ones_equiv. rewrite N.pred_sub. easy.
  apply N.log2_lt_pow2. assert (0 < x) by lia. lia.
  replace 2%N with (N.of_nat 2) by lia. rewrite <- Nofnat_pow. lia.
Qed.


(* Here, we define the addto / addto_n functions for angle rotation. *)
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev {A} n (f : nat -> A) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.

Lemma fbrev'_fbrev :
  forall n f,
    0 < n ->
    fbrev n f = fbrev' ((n - 1) / 2) n f.
Proof.
  intros. unfold fbrev, fbrev'. apply functional_extensionality; intro.
  assert ((n - 1) / 2 < n) by (apply Nat.div_lt_upper_bound; lia).
  assert (2 * ((n - 1) / 2) <= n - 1) by (apply Nat.mul_div_le; easy).
  assert (n - 1 - (n - 1) / 2 <= (n - 1) / 2 + 1).
  { assert (n - 1 <= 2 * ((n - 1) / 2) + 1).
    { assert (2 <> 0) by easy.
      specialize (Nat.mul_succ_div_gt (n - 1) 2 H3) as G.
      lia.
    }
    lia.
  }
  IfExpSimpl; easy.
Qed.

Lemma allfalse_0 : forall n, cut_n allfalse n = nat2fb 0.
Proof.
  intros. unfold nat2fb. simpl.
  unfold cut_n.
  apply functional_extensionality; intro.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma f_num_aux_0: forall n f x, cut_n f n = nat2fb x 
                -> f n = false -> cut_n f (S n) = nat2fb x.
Proof.
  intros.
  rewrite <- H0.
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? n).
  bdestruct (x0 <? S n).
  easy.
  lia.
  bdestruct (x0 <? S n).
  assert (x0 = n) by lia.
  subst. rewrite H1. easy.
  easy.
Qed.

Definition twoton_fun (n:nat) := fun i => if i <? n then false else if i=? n then true else false.


Definition times_two_spec (f:nat -> bool) :=  fun i => if i =? 0 then false else f (i-1).

(* Showing the times_two spec is correct. *)

Lemma nat2fb_even_0:
  forall x, nat2fb (2 * x) 0 = false.
Proof.
  intros.
  unfold nat2fb.
  rewrite Nat2N.inj_double.
  unfold N.double.
  destruct (N.of_nat x).
  unfold N2fb,allfalse.
  reflexivity.
  unfold N2fb.
  simpl.
  reflexivity.
Qed.

Lemma pos2fb_times_two_eq:
  forall p x, x <> 0 -> pos2fb p (x - 1) = pos2fb p~0 x.
Proof.
  intros.
  induction p.
  simpl.
  assert ((fb_push false (fb_push true (pos2fb p))) x = (fb_push true (pos2fb p)) (x - 1)).
  rewrite fb_push_right.
  reflexivity. lia.
  rewrite H1.
  reflexivity.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
Qed.

Lemma times_two_correct:
   forall x, (times_two_spec (nat2fb x)) = (nat2fb (2*x)).
Proof.
  intros.
  unfold times_two_spec.
  apply functional_extensionality; intros.
  unfold nat2fb.
  bdestruct (x0 =? 0).
  rewrite H0.
  specialize (nat2fb_even_0 x) as H3.
  unfold nat2fb in H3.
  rewrite H3.
  reflexivity.
  rewrite Nat2N.inj_double.
  unfold N.double,N2fb.
  destruct (N.of_nat x).
  unfold allfalse.
  reflexivity.
  rewrite pos2fb_times_two_eq.
  reflexivity. lia.
Qed.


Lemma f_twoton_eq : forall n, twoton_fun n = nat2fb (2^n).
Proof.
  intros.
  induction n.
  simpl.
  unfold twoton_fun.
  apply functional_extensionality.
  intros. 
  IfExpSimpl.
  unfold fb_push. destruct x. easy. lia.
  unfold fb_push. destruct x. lia. easy.
  assert ((2 ^ S n) = 2 * (2^n)). simpl. lia.
  rewrite H0.
  rewrite <- times_two_correct.
  rewrite <- IHn.
  unfold twoton_fun,times_two_spec.
  apply functional_extensionality; intros.
  bdestruct (x =? 0).
  subst.
  bdestruct (0 <? S n).
  easy. lia.
  bdestruct (x <? S n).
  bdestruct (x - 1 <? n).
  easy. lia.
  bdestruct (x =? S n).
  bdestruct (x - 1 <? n). lia.
  bdestruct (x - 1 =? n). easy.
  lia.
  bdestruct (x-1<? n). easy.
  bdestruct (x-1 =? n). lia.
  easy.
Qed.

Local Transparent carry.

Lemma carry_cut_n_false : forall i n f, carry false i (cut_n f n) (twoton_fun n) = false.
Proof.
  intros.
  induction i.
  simpl. easy.
  simpl. rewrite IHi.
  unfold cut_n,twoton_fun.
  IfExpSimpl. btauto.
  simpl.
  btauto.
  simpl. easy.
Qed.

Lemma carry_lt_same : forall m n f g h b, m < n -> (forall i, i < n -> f i = g i)
                          -> carry b m f h = carry b m g h.
Proof.
 induction m; intros; simpl. easy.
 rewrite H1. rewrite (IHm n) with (g:= g); try lia. easy.
 easy. lia.
Qed.

Lemma carry_lt_same_1 : forall m n f g h h' b, m < n -> (forall i, i < n -> f i = g i)
                 -> (forall i, i < n -> h i = h' i) -> carry b m f h = carry b m g h'.
Proof.
 induction m; intros; simpl. easy.
 rewrite H1. rewrite H2. rewrite (IHm n) with (g:= g) (h' := h'); try lia. easy.
 easy. easy. lia. lia.
Qed.

Local Opaque carry.

Lemma sumfb_cut_n : forall n f, f n = true -> sumfb false (cut_n f n) (twoton_fun n)  = cut_n f (S n).
Proof.
  intros.
  unfold sumfb.
  apply functional_extensionality; intros.
  rewrite carry_cut_n_false.
  unfold cut_n, twoton_fun.
  IfExpSimpl. btauto.
  subst. rewrite H0. simpl.  easy.
  simpl. easy.
Qed.

Lemma f_num_aux_1: forall n f x, cut_n f n = nat2fb x -> f n = true 
                  -> cut_n f (S n) = nat2fb (x + 2^n).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  rewrite <- H0.
  rewrite <- f_twoton_eq.
  rewrite sumfb_cut_n.
  easy. easy.
Qed.

Lemma f_num_0 : forall f n, (exists x, cut_n f n = nat2fb x).
Proof.
  intros.
  induction n.
  exists 0.
  rewrite <- (allfalse_0 0).
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x <? 0).
  inv H0. easy.
  destruct (bool_dec (f n) true).
  destruct IHn.
  exists (x + 2^n).
  rewrite (f_num_aux_1 n f x).
  easy. easy. easy.
  destruct IHn.
  exists x. rewrite (f_num_aux_0 n f x).
  easy. easy.
  apply not_true_is_false in n0. easy.
Qed.

Lemma f_num_small : forall f n x, cut_n f n = nat2fb x -> x < 2^n.
Proof.
  intros.
Admitted.

Definition addto (r : nat -> bool) (n:nat) : nat -> bool := fun i => if i <? n 
                    then (cut_n (fbrev n (sumfb false (cut_n (fbrev n r) n) (nat2fb 1))) n) i else r i.

Definition addto_n (r:nat -> bool) n := fun i => if i <? n
                        then (cut_n (fbrev n (sumfb false 
                  (cut_n (fbrev n r) n) (sumfb false (nat2fb 1) (negatem n (nat2fb 1))))) n) i else r i.

Lemma addto_n_0 : forall r, addto_n r 0 = r.
Proof.
  intros.
  unfold addto_n.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma addto_0 : forall r, addto r 0 = r.
Proof.
  intros.
  unfold addto.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma cut_n_fbrev_flip : forall n f, cut_n (fbrev n f) n = fbrev n (cut_n f n).
Proof.
  intros.
  unfold cut_n, fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  easy. lia. easy.
Qed.

Lemma cut_n_if_cut : forall n f g, cut_n (fun i => if i <? n then f i else g i) n = cut_n f n.
Proof.
  intros.
  unfold cut_n.
  apply functional_extensionality; intros.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma fbrev_twice_same {A}: forall n f, @fbrev A n (fbrev n f) = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  assert ((n - 1 - (n - 1 - x)) = x) by lia.
  rewrite H2. easy.
  lia. easy.
Qed.

Lemma cut_n_mod : forall n x, cut_n (nat2fb x) n = (nat2fb (x mod 2^n)).
Proof.
  intros.
  unfold nat2fb.
Admitted.

Lemma add_to_r_same : forall q r, addto (addto_n r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto_n.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite negatem_arith.
  rewrite sumfb_correct_carry0.
  assert (1 < 2 ^ (S n)).
  apply Nat.pow_gt_1. lia. lia.
  assert ((1 + (2 ^ S n - 1 - 1)) = 2^ S n -1) by lia.
  rewrite H2.
  rewrite H0.
  rewrite sumfb_correct_carry0.
  unfold addto.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb
                          (x + (2 ^ S n - 1))))
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb
                         (x + (2 ^ S n - 1)))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  rewrite sumfb_correct_carry0.
  assert (((x + (2 ^ S n - 1)) mod 2 ^ S n + 1) = ((x + (2 ^ S n - 1)) mod 2 ^ S n + (1 mod 2^ S n))).
  assert (1 mod 2^ S n = 1).
  rewrite Nat.mod_small. easy. easy.
  rewrite H3. easy.
  rewrite H3.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert ((x + (2 ^ S n - 1) + 1) = x + 2 ^ S n) by lia.
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  assert (x mod 2 ^ S n = x).
  rewrite Nat.mod_small. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
  rewrite H5.
  rewrite plus_0_r.
  rewrite H5.
  rewrite <- H0.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  apply Nat.pow_gt_1. lia. lia.
Qed.

Lemma add_to_same : forall q r, addto_n (addto r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite H0.
  rewrite sumfb_correct_carry0.
  unfold addto_n.
  rewrite negatem_arith.
  rewrite sumfb_correct_carry0.
  assert (1 < 2 ^ (S n)).
  apply Nat.pow_gt_1. lia. lia.
  assert ((1 + (2 ^ S n - 1 - 1)) = 2^ S n -1) by lia.
  rewrite H2.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb (x + 1))) 
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb (x+1))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  assert ((2 ^ S n - 1) = (2 ^ S n - 1) mod (2^ S n)).
  rewrite Nat.mod_small by lia.
  easy.
  rewrite H3.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert ((x + 1 + (2 ^ S n - 1))  = x + 2 ^ S n) by lia.
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite <- H0.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
  apply Nat.pow_gt_1. lia. lia.
Qed.


Lemma posi_neq_f : forall (p p' : posi), p <> p' -> fst p <> fst p' \/ snd p <> snd p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 bdestruct (v =? v0).
 subst. right.
 intros R. subst. contradiction.
 bdestruct (n =? n0).
 subst.
 left.
 intros R. subst. contradiction.
 left. lia.
Qed.

Lemma posi_neq_b : forall (p p' : posi), fst p <> fst p' \/ snd p <> snd p' -> p <> p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 intros R. inv R.
 destruct H0.
 lia.
 lia.
Qed.


(* helper functions/lemmas for NOR states. *)
Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Lemma nor_mode_nval : forall f x, nor_mode f x -> (exists r, f x = nval true r \/ f x = nval false r).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H0.
  exists r.
  destruct b. left. easy. right. easy.
Qed.

Lemma neq_sym {A} : forall (x y: A), x <> y -> y <> x.
Proof.
 intros. intros R.
 subst. contradiction.
Qed.

Lemma nor_mode_up : forall f x y v, x <> y -> nor_mode f x -> nor_mode (f[y |-> v]) x.
Proof.
  intros. unfold nor_mode in *.
  assert ((f [y |-> v]) x = (f x)).
  rewrite eupdate_index_neq. reflexivity. apply neq_sym. assumption.
  rewrite H2.
  destruct (f x); inv H1. easy.
Qed.



Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | a => false end.

Lemma get_cua_eq : forall f x v, nor_mode f x -> get_cua ((f[x |-> put_cu (f x) v]) x) = v.
Proof.
  intros.
  unfold get_cua.
  rewrite eupdate_index_eq.
  unfold put_cu.
  unfold nor_mode in H0.
  destruct (f x). easy. inv H0. inv H0.
Qed.

Lemma double_put_cu : forall (f:posi -> val) x v v', put_cu (put_cu (f x) v) v' = put_cu (f x) v'.
Proof.
  intros.
  unfold put_cu.
  destruct (f x). easy. easy. easy.
Qed.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Lemma get_cus_cua : forall n f x m, m < n -> get_cus n f x m = get_cua (f (x,m)).
Proof.
  intros.
  unfold get_cus,get_cua.
  bdestruct (m <? n).
  destruct (f (x,n)). easy. easy. easy.
  lia.
Qed.

Definition put_cus (f:posi -> val) (x:var) (g:nat -> bool) (n:nat) : (posi -> val) :=
     fun a => if fst a =? x then if snd a <? n then put_cu (f a) (g (snd a)) else f a else f a.

Lemma cus_get_neq : forall (f:posi -> val) (x y :var) g n i, 
              x <> y -> get_cua ((put_cus f y g n) (x,i)) = get_cua (f (x,i)).
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? y).
 lia. easy.
Qed.

Lemma put_cus_out : forall (f:posi -> val) (x y :var) g n i, 
              n <= i -> ((put_cus f y g n) (x,i)) = (f (x,i)).
Proof. 
  intros.
  unfold put_cus.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n). lia.
  easy. easy.
Qed.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Lemma nor_mode_cus_eq: forall f x g n y i, 
       nor_mode f (y,i) -> nor_mode (put_cus f x g n) (y,i).
Proof.
  intros. unfold nor_mode in *.
  unfold put_cus.
  simpl.
  bdestruct (y =? x).
  bdestruct (i <? n).
  destruct (f (y, i)).
  unfold put_cu. easy.
  inv H0. inv H0.
  apply H0. apply H0.
Qed.

Lemma cus_get_eq : forall (f:posi -> val) (x :var) g n i, 
              i < n -> nor_modes f x n -> get_cua ((put_cus f x g n) (x,i)) = g i.
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n).
 unfold put_cu.
 specialize (H1 i H3). unfold nor_mode in *.
 destruct (f (x, i)) eqn:eq1. easy.
 inv H1. inv H1.
 lia. lia.
Qed.

Lemma put_cus_eq : forall (f:posi -> val) (x:var) g n i, 
          i < n -> (put_cus f x g n) (x,i) = put_cu (f (x,i)) (g i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n). easy. lia. lia.
Qed.

Lemma put_cus_neq : forall (f:posi -> val) (x y:var) g n i, 
              x <> y -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x). lia. easy.
Qed.

Lemma put_cus_neq_1 : forall (f:posi -> val) (x:var) g n c, 
              x <> fst c -> (put_cus f x g n) c = f c.
Proof.
 intros.
 destruct c. apply put_cus_neq.
 simpl in H0. assumption.
Qed.

Lemma put_cus_neq_2 : forall (f:posi -> val) (x y:var) g n i, 
           n <= i -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n). lia. easy.
 easy.
Qed.

Lemma put_cu_cus : forall (f:posi -> val) x y g i n v, put_cu (put_cus f y g n (x,i)) v = put_cu (f (x,i)) v.
Proof.
  intros.
  unfold put_cus,put_cu.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n).
  destruct (f (x,i)). easy. easy. easy. easy. easy.
Qed.


Lemma nor_mode_up_1 : forall f x v, nor_mode f x -> nor_mode (f[x |-> put_cu (f x) v]) x.
Proof.
  intros.
  unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu.
  destruct (f x).
  easy. inv H0. inv H0.
Qed.


Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
                | S m => if M m then X (x,m) ; init_v m x M else init_v m x M
      end.

Lemma nor_mode_ups : forall f f' x v, f x = f' x -> nor_mode f x ->
                                    nor_mode (f[x |-> put_cu (f' x) v]) x.
Proof.
  intros. unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu. rewrite <- H0.
  destruct (f x); inv H1. easy.
Qed.

Lemma nor_mode_get : forall f x, nor_mode f x -> (exists b, get_cua (f x) = b).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H0.
  exists b. unfold get_cua. reflexivity.
Qed.



Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | hval b1 b2 r => Some b1
                 | _ => None
    end.

(*
Lemma get_cu_good : forall tenv f p e, well_typed_exp tenv (CU p e) 
            -> right_mode_exp tenv f (CU p e) -> (exists b, get_cu (f p) = Some b).
Proof.
  intros. 
  unfold get_cu.
  inv H0. inv H1. 
  apply (mapsto_always_same a Nor t tenv) in H8. subst.
  inv H9.
  exists b0. easy. easy.
Qed.
*)

Lemma put_get_cu : forall f x, nor_mode f x -> put_cu (f x) (get_cua (f x)) = f x.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H0. destruct (f x); inv H0.
 reflexivity.
Qed.

Lemma get_put_cu : forall f x v, nor_mode f x -> get_cua (put_cu (f x) v) = v.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H0. destruct (f x); inv H0.
 reflexivity.
Qed.

(*
Definition vxor (a b:val) := (get_cua a) ⊕ (get_cua b).

Definition vand (a b:val) := (get_cua a) && (get_cua b).

Notation "p1 '[⊕]' p2" := (vxor p1 p2) (at level 50) : exp_scope.

Notation "p1 '[&&]' p2" := (vand p1 p2) (at level 50) : exp_scope.

Lemma vxor_l_t : forall r b, vxor (nval true r) b = (¬ (get_cua b)).
Proof.
  intros. unfold vxor. unfold get_cua. destruct b.
  btauto. btauto. btauto.
Qed.

Lemma vxor_l_f : forall r b, vxor (nval false r) b = ((get_cua b)).
Proof.
  intros. unfold vxor. unfold get_cua. destruct b.
  btauto. btauto. btauto.
Qed.
*)

Lemma xorb_andb_distr_l : forall x y z, (x ⊕ y) && z = (x && z) ⊕ (y && z).
Proof.
 intros. btauto.
Qed.

Lemma xorb_andb_distr_r : forall x y z, z && (x ⊕ y) = (z && x) ⊕ (z && y).
Proof.
 intros. btauto.
Qed.


Ltac bt_simpl := repeat (try rewrite xorb_false_r; try rewrite xorb_false_l;
            try rewrite xorb_true_r; try rewrite xorb_true_r; 
            try rewrite andb_false_r; try rewrite andb_false_l;
            try rewrite andb_true_r; try rewrite andb_true_l;
            try rewrite xorb_andb_distr_l; try rewrite xorb_andb_distr_r;
            try rewrite andb_diag).



Lemma get_cua_t : forall b r, get_cua (nval b r) = b.
Proof.
 intros. unfold get_cua. reflexivity.
Qed.

(* Proofs of types and syntax. *)
Ltac nor_sym := try (apply neq_sym; assumption) ; try assumption.


Lemma iner_neq : forall (x y:var) (a b:nat), x <> y -> (x,a) <> (y,b).
Proof.
  intros. intros R.
  inv R. contradiction.
Qed.

Lemma iner_neq_1 : forall (x:var) (c:posi) a, x <> fst c -> (x,a) <> c.
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Lemma iner_neq_2 : forall (x:var) (c:posi) a, x <> fst c -> c <> (x,a).
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Ltac tuple_eq := intros R; inv R; lia.

Ltac iner_p := try nor_sym; try tuple_eq ; try (apply iner_neq ; assumption)
           ; try (apply iner_neq_1 ; assumption) ; try (apply iner_neq_2 ; assumption).


Lemma eupdates_twice_neq : forall f x g n c v, x <> fst c 
           -> (put_cus f x g n)[c |-> v] = put_cus (f[c |-> v]) x g n.
Proof.
  intros. unfold put_cus.
  apply functional_extensionality.
  intros.
  bdestruct (x0 ==? c).
  subst.
  rewrite eupdate_index_eq.
  bdestruct (fst c =? x).
  subst. contradiction.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  bdestruct (fst x0 =? x).
  rewrite eupdate_index_neq.
  easy. nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy. nor_sym.
Qed.


(*A function to get the rotation angle of a state. *)
Definition get_r (v:val) :=
   match v with nval x r => r
              | qval rc r => rc
              | hval x y r => r
   end.

Lemma get_r_put_same : forall (f:posi -> val) x y g n i,
      get_r (put_cus f x g n (y,i)) = get_r (f (y,i)).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n).
 unfold put_cu.
 destruct (f (y, i)).
 unfold get_r. easy. easy. easy. easy. easy.
Qed.

Lemma put_cu_mid_eq : forall (f g:posi -> val) a v, 
              nor_mode f a -> nor_mode g a -> get_r (f a) = get_r (g a) -> (put_cu (f a) v) = (put_cu (g a) v).
Proof.
 intros.
 unfold put_cu. unfold nor_mode in *.
 destruct (f a). destruct (g a).
 unfold get_r in H2. subst.
 easy. inv H1. inv H1.
 inv H0. inv H0.
Qed.

Lemma put_cus_twice_neq : forall (f:posi -> val) (x y:var) g1 g2 n, 
              x <> y -> (put_cus (put_cus f x g1 n) y g2 n)
                          = (put_cus (put_cus f y g2 n) x g1 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? y).
 bdestruct (v =? x). lia. easy.
 easy.
Qed.


Lemma put_cu_twice_eq : forall (f:posi -> val) (x:var) v1 v2 i, 
        put_cu (put_cu (f (x,i)) v1) v2 = put_cu (f (x,i)) v2.
Proof.
  intros. unfold put_cu.
  destruct (f (x, i)). easy. easy. easy.
Qed.

Lemma put_cu_twice_eq_1 : forall (f:posi -> val) c v1 v2, 
        put_cu (put_cu (f c) v1) v2 = put_cu (f c) v2.
Proof.
  intros. unfold put_cu.
  destruct (f c). easy. easy. easy.
Qed.


Lemma put_cus_twice_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
              (put_cus (put_cus f x g1 n) x g2 n)
                          = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite put_cu_twice_eq. easy.
 easy.
 easy.
Qed.

Lemma put_cus_sem_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
           (forall m, m < n -> g1 m = g2 m) -> 
                 (put_cus f x g1 n) = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite H0. easy.
 lia. easy. easy. 
Qed.


(* Defining program semantic functions. *)
Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  if b then nval b (r_rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (r_rotate r q)
     end.

Fixpoint srr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (srr_rotate' st x m size)[(x,m) |-> times_r_rotate (st (x,m)) (size - m)]
   end.
Definition srr_rotate st x n := srr_rotate' st x (S n) (S n).


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
                  | a => a
     end.

Fixpoint lshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,0) |-> f(x,size)]
             | S m => ((lshift' m size f x)[ (x,n) |-> f(x,m)])
   end.
Definition lshift (f:posi -> val) (x:var) (n:nat) := lshift' (n-1) (n-1) f x.

Fixpoint rshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,size) |-> f(x,0)]
             | S m => ((rshift' m size f x)[(x,m) |-> f (x,n)])
   end.
Definition rshift (f:posi -> val) (x:var) (n:nat) := rshift' (n-1) (n-1) f x.

(*
Inductive varType := SType (n1:nat) (n2:nat).

Definition inter_env (enva: var -> nat) (x:var) :=
             match  (enva x) with SType n1 n2 => n1 + n2 end.
*)

Definition hexchange (v1:val) (v2:val) :=
  match v1 with hval b1 b2 r1 => 
    match v2 with hval b3 b4 r2 => if eqb b3 b4 then v1 else hval b1 (¬ b2) r1
                | _ => v1
    end
             | _ => v1
  end.

(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (e:exp) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | HCNOT p1 p2 => (st[p1 |-> (hexchange (st p1) (st p2))])
              | CU p e' => if get_cua (st p) then exp_sem e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | SR n x => sr_rotate st x n (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n
              | e1 ; e2 => exp_sem e2 (exp_sem e1 st)
    end.

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun (a: var * nat) =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.


Lemma x_nor_sem : forall f x v, nor_mode f x -> put_cu (f x) (¬ (get_cua (f x))) = v ->
                            exp_sem (X x) f = (f[x |-> v]).
Proof.
 intros.
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 unfold get_cua in H1. rewrite H0 in H1. 
 unfold put_cu in H1. subst. 
 assert ((exchange (f x)) = nval (¬ true) x0).
 unfold exchange. rewrite H0. reflexivity.
 rewrite <- H1. simpl. easy.
 unfold get_cua in H1. rewrite H0 in H1.
 unfold put_cu in H1. subst.
 assert ((exchange (f x)) = nval (¬ false) x0).
 unfold exchange. rewrite H0.
 reflexivity. 
 rewrite <- H1. simpl. easy. 
Qed.

Lemma lshift'_irrelevant :
   forall n size f x p, fst p <> x -> lshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHn.
  easy.
  apply iner_neq_1. lia.
Qed.


Lemma rshift'_irrelevant :
   forall n size f x p, fst p <> x -> rshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  intros. simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  intros. simpl.
  rewrite eupdate_index_neq.
  rewrite IHn. easy.
  apply iner_neq_1. lia.
Qed.

Lemma sr_rotate'_ge : 
   forall n size f x p, n <= snd p -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H0. lia.
 intros R. inv R. lia.
Qed.

Lemma sr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        sr_rotate' f (fst p) n size p = times_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma sr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma srr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        srr_rotate' f (fst p) n size p = times_r_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma srr_rotate'_ge : 
   forall n size f x p, n <= snd p -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H0. lia.
 intros R. inv R. lia.
Qed.

Lemma srr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma efresh_exp_sem_irrelevant :
  forall e p f,
    exp_fresh p e ->
    exp_sem e f p = f p.
Proof.
  induction e;intros.
  subst. simpl. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl.
  destruct (get_cua (f p)).
  eapply IHe. inv H0. assumption. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  inv H0.
  destruct H3.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try easy.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_ge; try easy. lia.
  inv H0.
  destruct H3.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try easy.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_ge; try easy. lia.
  inv H0. simpl.
  rewrite eupdate_index_neq by iner_p. easy.
  inv H0. simpl.
  apply (IHe1) with (f := f) in H4.
  apply (IHe2) with (f := (exp_sem e1 f)) in H5.
  rewrite H5. rewrite H4. easy.
Qed.


Lemma two_cu_same : forall f p e1 e2, get_cua (f p) = true ->
                     exp_fwf (CU p e1) -> exp_sem (e1 ; e2) f = exp_sem (CU p e1; CU p e2) f. 
Proof.
  intros.
  inv H1.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite (efresh_exp_sem_irrelevant e1 p f) by assumption.
  destruct (get_cua (f p)). easy.
  inv eq1. inv H0.
Qed.

Definition right_mode_env (aenv: var -> nat) (env: env) (st: posi -> val)
            := forall t p, snd p < aenv (fst p) -> Env.MapsTo (fst p) t env -> right_mode_val t (st p).

Lemma well_typed_right_mode_exp : forall e aenv env f, well_typed_exp env e
          -> right_mode_env aenv env f -> right_mode_env aenv env (exp_sem e f).
Proof.
  induction e; intros; simpl.
  easy. 
  unfold right_mode_env in *. intros. 
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  inv H0. destruct p0.
  destruct (f (v,n)) eqn:eq1. 
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.
  rewrite <- H3 in *. constructor.
  apply H1 in H6.
  rewrite eq1 in *. inv H6. easy.
  apply H1 in H6.
  rewrite eq1 in H6. inv H6. easy.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.
  rewrite <- H3 in *.
  apply H1 in H6.
  destruct (f p0) eqn:eq1. inv H6. constructor. inv H6. easy. inv H6. easy.
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  inv H0.
  destruct (get_cua (f p)). apply IHe. easy. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  inv H0. simpl in H3.
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.  
  rewrite <- H3 in *.
  apply H1 in H6. inv H6.
  destruct b. constructor. constructor. easy.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.  
  rewrite <- H3 in *.
  apply H1 in H6. inv H6. constructor. easy. easy.
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  inv H0. simpl in H3.
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.  
  rewrite <- H3 in *.
  apply H1 in H6. inv H6.
  destruct b. constructor. constructor. easy.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.  
  rewrite <- H3 in *.
  apply H1 in H6. inv H6. constructor. easy. easy.
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  inv H0. unfold sr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? q).
  rewrite sr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi n)) in H3; try easy.
  rewrite <- H3 in *.
  apply H1 in H7. inv H7. constructor. lia.
  rewrite sr_rotate'_ge; try lia.
  apply H1 ; try easy.
  rewrite sr_rotate'_irrelevant.
  apply H1; try easy. lia.
  unfold right_mode_env in *.
  intros.
  inv H0. unfold srr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? q).
  rewrite srr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi n)) in H3; try easy.
  rewrite <- H3 in *.
  apply H1 in H7. inv H7. constructor. lia.
  rewrite srr_rotate'_ge; try lia.
  apply H1 ; try easy.
  rewrite srr_rotate'_irrelevant.
  apply H1; try easy. lia.
  unfold right_mode_env in *.
  intros.
  inv H0.
  bdestruct (p ==? p1). subst.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.
  rewrite <- H3.
  rewrite eupdate_index_eq.
  unfold hexchange.
  apply H1 in H7.
  inv H7.
  destruct (f p2). constructor. easy.
  destruct (eqb b0 b3). constructor. easy.
  constructor. easy.
  constructor. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H1. easy. easy.
  inv H0.
  specialize (IHe1 aenv env0 f H5 H1).
  specialize (IHe2 aenv env0 (exp_sem e1 f) H6 IHe1).
  easy.
Qed.


(* This is the semantics for shifting/virtual qubit states. *)
Fixpoint sexp_sem (env: var -> nat) (e:sexp) (st: posi -> val) : (posi -> val) :=
   match e with | Lshift x => (lshift st x (env x))
                | Rshift x => (rshift st x (env x))
                | Rev x => (reverse st x (env x))
              | Exp e => exp_sem e st
              | e1 ;; e2 => sexp_sem env e2 (sexp_sem env e1 st)
    end.


Lemma lshift'_0 : forall m n f x, m <= n -> lshift' m n f x (x,0) = f (x,n).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq by tuple_eq.
 rewrite IHm. easy. lia.
Qed.

Lemma lshift'_gt : forall i m n f x, m < i -> lshift' m n f x (x,i) = f (x,i).
Proof.
  intros.
  induction m.
  simpl.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm.
  easy. lia.
  tuple_eq.
Qed.

Lemma lshift'_le : forall i m n f x, S i <= m <= n  -> lshift' m n f x (x,S i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros. inv H0. inv H1.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_0 : forall m n f x, m <= n -> rshift' m n f x (x,n) = f (x,0).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHm. easy. lia.
 tuple_eq.
Qed.

Lemma rshift'_gt : forall i m n f x, m <= n < i -> rshift' m n f x (x,i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  intros.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_le : forall i m n f x, i < m <= n  -> rshift' m n f x (x,i) = f (x,S i).
Proof.
  induction m.
  simpl.
  intros. inv H0. inv H1.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma well_typed_right_mode_sexp : forall e aenv tenv f, well_typed_sexp tenv e
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv (sexp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  unfold right_mode_env in *. intros.
  unfold lshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  destruct n.
  rewrite lshift'_0 by lia.
  apply H1. simpl in *. lia. easy.
  rewrite lshift'_le by lia. apply H1. simpl in *. lia. easy.
  rewrite lshift'_irrelevant by iner_p.
  apply H1. simpl in *. easy. easy.
  unfold right_mode_env in *. intros.
  unfold rshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  bdestruct (n <? (aenv v - 1)).
  rewrite rshift'_le by lia. apply H1. simpl in *. lia. easy.
  bdestruct (n =? (aenv v - 1)).
  subst.
  rewrite rshift'_0 by lia. apply H1. simpl in *. lia. easy. lia.
  rewrite rshift'_irrelevant by iner_p. apply H1. simpl in *. lia. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in H2.
  unfold reverse. simpl.
  bdestruct (v =? x). bdestruct (n <? aenv x). simpl.
  subst. apply H1. simpl in *. lia. easy.
  simpl in *. apply H1. easy. easy.
  simpl in *. apply H1. easy. easy.
  apply well_typed_right_mode_exp.
  inv H0. easy. easy.
  inv H0.
  specialize (IHe1 aenv tenv f H5 H1).
  specialize (IHe2 aenv tenv (sexp_sem aenv e1 f) H6 IHe1).
  easy.
Qed.

(* This is the semantics for switching qubit representation states. *)
Definition h_case (v : val) :=
    match v with nval b r => if r 0 then hval false b (rotate r 1) else hval true (¬ b) r
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1)
               | hval false false r => nval false (rotate r 1)
               | a => a
    end.

Lemma fbrev_1_same {A}: forall f, @fbrev A 1 f = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality. intros.
  bdestruct (x<?1).
  assert (1 - 1 - x = x) by lia.
  rewrite H1. easy. easy. 
Qed.
 
Lemma cut_n_1_1: forall (r:rz_val), r 0 = true -> cut_n r 1 = nat2fb 1.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H0. easy.
  unfold nat2fb. simpl. 
  rewrite fb_push_right. easy. lia.
Qed.

Lemma cut_n_1_0: forall (r:rz_val), r 0 = false -> cut_n r 1 = nat2fb 0.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H0. easy.
  unfold nat2fb. simpl. easy.
Qed.



Lemma rotate_twice_same_1 : forall r, (rotate (rotate r 1) 1) = r.
Proof.
  intros. unfold rotate.
  unfold addto.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert ( x = 0) by lia. subst.
  repeat rewrite fbrev_1_same.
  destruct (r 0) eqn:eq1.
  specialize (cut_n_1_1 r eq1) as eq2.
  rewrite eq2.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  assert (((1 + 1) mod 2 ^ 1) = 0).
  assert ((1 + 1) = 2) by lia. rewrite H1.
  rewrite Nat.pow_1_r. rewrite Nat.mod_same. easy. lia.
  rewrite H1.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia.
  unfold nat2fb. simpl. easy.
  rewrite (cut_n_1_0 r eq1).
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  assert ((1 + 1) = 2) by lia. rewrite H1.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia.
  unfold nat2fb. easy.
  easy.
Qed.

Lemma rotate_1_0: forall r, r 0 = false -> rotate r 1 0 = true.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_0 r H0). 
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia. easy. lia.
Qed.

Lemma rotate_1_1: forall r, r 0 = true -> rotate r 1 0 = false.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_1 r H0). 
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia. easy. lia.
Qed.

Lemma h_case_twice_same : 
   forall t v, right_mode_val t v -> h_case (h_case v) = v.
Proof.
  intros. unfold h_case.
  destruct v.
  destruct (r 0) eqn:eq1.
  destruct b.
  rewrite rotate_twice_same_1. easy.
  rewrite rotate_twice_same_1. easy.
  destruct b. simpl. easy. simpl. easy.
  inv H0.
  destruct b1.
  destruct b2. rewrite H3. simpl. easy.
  rewrite H3. simpl. easy.
  destruct b2.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  easy.
Qed.

Lemma hexchange_twice_same :
  forall v1 v2, hexchange (hexchange v1 v2) v2 = v1.
Proof.
  intros.
  unfold hexchange.
  destruct v1 eqn:eq1. easy.
  destruct v2 eqn:eq2. easy.
  destruct (eqb b0 b3) eqn:eq3. easy.
  assert ((¬ (¬ b2)) = b2) by btauto. rewrite H0. easy.
  easy. easy.
Qed.

Fixpoint h_sem (f:posi -> val) (x:var) (n : nat) := 
    match n with 0 => f
              | S m => (h_sem f x m)[(x,m) |-> h_case (f (x,m))]
    end.

Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (f:nat -> bool) :=
   match v with nval b r => qval r f
              | a => a
   end.

Definition lshift_fun (f:nat -> bool) (n:nat) := fun i => f (i+n).


Fixpoint assign_r (f:posi -> val) (x:var) (r : nat -> bool) (n:nat) := 
    match n with 0 => f
              | S m => (assign_r f x r m)[(x,m) |-> up_qft (f (x,m)) (lshift_fun r m)]
    end.

Definition turn_qft (st : posi -> val) (x:var) (rmax : nat) := 
       assign_r st x (get_cus rmax st x) rmax.


Fixpoint assign_seq (f:posi -> val) (x:var) (vals : nat -> bool) (n:nat) := 
   match n with 0 => f
              | S m => (assign_seq f x vals m)[(x,m) |-> nval (vals m) (get_r (f (x,m)))]
   end.

Definition get_r_qft (f:posi -> val) (x:var) :=
      match f (x,0) with qval rc g => g
                      | _ => allfalse
      end.

Definition turn_rqft (st : posi -> val) (x:var) (rmax : nat) := assign_seq st x (get_r_qft st x) rmax.

(* Here, we define the addto / addto_n functions for angle rotation. 
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev {A} n (f : nat -> A) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.
*)

Fixpoint prog_sem (env:var -> nat) (e:pexp) (st:posi-> val) : (posi -> val) :=
    match e with SExp e => sexp_sem env e st
               | H x => h_sem st x (env x)
               | QFT x => turn_qft st x (env x)
               | RQFT x => turn_rqft st x (env x)
               | e1 ;;; e2 => prog_sem env e2 (prog_sem env e1 st)
    end.

Lemma assign_r_right_mode : forall n i size f x r, i < n <= size -> 
       (forall i, i < size -> right_mode_val Nor (f (x,i))) ->
       right_mode_val (Phi size) (assign_r f x r n (x,i)).
Proof.
  induction n; intros; simpl. inv H0. inv H2.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  unfold up_qft.
  specialize (H1 n).
  assert (n < size) by lia. apply H1 in H2. inv H2.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma assign_r_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_r f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy. 
Qed.

Lemma assign_seq_right_mode : forall n i f x r, i < n -> 
       right_mode_val Nor (assign_seq f x r n (x,i)).
Proof.
  induction n; intros; simpl.
  inv H0.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia.
Qed.

Lemma assign_seq_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_seq f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma h_sem_right_mode_nor : forall n i f x, i < n -> 
       right_mode_val Nor (f (x,i)) ->
       right_mode_val Had (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case. destruct (r 0) eqn:eq1; constructor.
  rewrite rotate_1_1; try easy. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor.
Qed.


Lemma h_sem_right_mode_had : forall n i f x, i < n -> 
       right_mode_val Had (f (x,i)) ->
       right_mode_val Nor (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case.
  destruct b1. destruct b2; constructor.
  destruct b2; constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor. easy.
Qed.

Lemma h_sem_right_mode_out : forall n t f x v i, v <> x -> 
       right_mode_val t (f (v,i)) ->
       right_mode_val t(h_sem f x n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma well_typed_right_mode_pexp : forall e aenv tenv tenv' f, well_typed_pexp aenv tenv e tenv'
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv' (prog_sem aenv e f).
Proof.
  induction e; intros; simpl.
  apply well_typed_right_mode_sexp. inv H0. easy. inv H0. easy. 
  inv H0. unfold turn_qft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v (Phi (aenv v)) tenv)) in H2; try easy.
  apply mapsto_add1 in H2. subst.
  apply assign_r_right_mode. lia.
  intros. apply H1. easy. easy.
  apply assign_r_right_mode_out; try lia.
  apply H1. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H2; try easy.
  apply Env.add_3 in H2; try lia. easy.
  inv H0. unfold turn_rqft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Nor tenv)) in H2; try easy.
  apply mapsto_add1 in H2. subst.
  apply assign_seq_right_mode. lia.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H2; try easy.
  apply Env.add_3 in H2; try lia.
  apply assign_seq_right_mode_out; try lia.
  apply H1. easy. easy.
  inv H0.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Had tenv)) in H2; try easy.
  apply mapsto_add1 in H2. subst.
  apply h_sem_right_mode_nor. lia. apply H1. easy. easy.
  apply mapsto_equal with (s2 := (Env.add x Had tenv)) in H2; try easy.
  apply Env.add_3 in H2; try lia.
  apply h_sem_right_mode_out. lia. apply H1. easy. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Nor tenv)) in H2; try easy.
  apply mapsto_add1 in H2. subst.
  apply h_sem_right_mode_had. lia. apply H1; easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H2; try easy.
  apply Env.add_3 in H2; try lia.
  apply h_sem_right_mode_out. lia. apply H1; easy.
  inv H0.
  specialize (IHe1 aenv tenv env' f H5 H1).
  specialize (IHe2 aenv env' tenv' (prog_sem aenv e1 f) H7 IHe1).
  easy.
Qed.

Lemma rev_twice_same : forall f st x, reverse (reverse st x (f x)) x (f x) = st.
Proof.
  intros. unfold reverse.
  apply functional_extensionality.
  intros.
  destruct x0. simpl.
  bdestruct (v =? x).
  subst.
  bdestruct ((n <? f x)).
  simpl.
  bdestruct ((x =? x)).
  bdestruct (( f x - 1 - n <? f x)).
  simpl.
  assert ( f x - 1 - ( f x - 1 - n)= n) by lia.
  rewrite H3. easy.
  simpl. lia.
  lia. simpl. easy.
  simpl. easy.
Qed.

(*
  The following defines the inverse function of a given RCIRplus circuit. 
*)

Lemma inv_exp_involutive :
  forall p,
    inv_exp (inv_exp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma inv_sexp_involutive :
  forall p,
    inv_sexp (inv_sexp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite inv_exp_involutive. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma inv_pexp_involutive :
  forall p,
    inv_pexp (inv_pexp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite inv_sexp_involutive. easy.
  - rewrite IHp1, IHp2. easy.
Qed.


Lemma fresh_inv_exp :
  forall p e,
    exp_fresh p e ->
    exp_fresh p (inv_exp e).
Proof.
  intros. induction H0; simpl; try constructor; try assumption.
Qed.

Lemma fwf_inv_exp :
  forall p,
    exp_fwf p ->
    exp_fwf (inv_exp p).
Proof.
  intros. induction H0; simpl; try constructor; try assumption.
  apply fresh_inv_exp. assumption.
Qed.

Lemma typed_inv_exp :
  forall tenv p,
    well_typed_exp tenv p ->
    well_typed_exp tenv (inv_exp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0. constructor. assumption.
  apply IHp. assumption.
  inv H0. constructor. assumption.
  apply rrz_had. assumption.
  inv H0. constructor. assumption.
  apply rz_had. assumption.
  inv H0. eapply srr_had. apply H4. easy.
  inv H0. eapply sr_had. apply H4. easy.
  inv H0. constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.

Lemma typed_inv_sexp :
  forall tenv p,
    well_typed_sexp tenv p ->
    well_typed_sexp tenv (inv_sexp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0. constructor. easy.
  apply rshift_had. apply H3.
  inv H0. constructor. easy.
  apply lshift_had. easy.
  inv H0.
  constructor. apply fwf_inv_exp. easy.
  apply typed_inv_exp. easy.
  inv H0.
  constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.

Lemma exchange_twice_same :
   forall (f: posi -> val) p, exchange (exchange (f p)) = f p.
Proof.
  intros. unfold exchange.
  destruct (f p) eqn:eq1.
  assert ((¬ (¬ b)) = b) by btauto.
  rewrite H0. easy.
  easy.
  easy.
Qed.   


Lemma rotate_r_same : forall r q, (rotate (r_rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_r_same.
  easy.
Qed.

Lemma rotate_same : forall r q, (r_rotate (rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_same.
  easy.
Qed.


Lemma times_rotate_r_same: forall r q, times_rotate (times_r_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b.
  rewrite rotate_r_same.
  easy. easy.
  assert ((¬ (¬ b2)) = b2) by btauto.
  rewrite H0. easy.
  rewrite rotate_r_same.
  easy.
Qed.

Lemma times_rotate_same: forall r q, times_r_rotate (times_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b. 
  rewrite rotate_same.
  easy. easy.
  assert ((¬ (¬ b2)) = b2) by btauto.
  rewrite H0. easy.
  rewrite rotate_same.
  easy.
Qed.


Lemma lr_shift_same : forall n f x, 
                 lshift ((rshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? 0). subst.
  rewrite lshift'_0.
  rewrite rshift'_0. easy. easy. easy.
  destruct n0. lia.
  bdestruct (S n0 <=? n-1).
  rewrite lshift'_le.
  rewrite rshift'_le.
  easy. lia. lia.
  rewrite lshift'_gt.
  rewrite rshift'_gt. easy.
  lia. lia.
  rewrite lshift'_irrelevant.
  rewrite rshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

Lemma rl_shift_same : forall n f x,
                 rshift ((lshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? n-1). subst.
  rewrite rshift'_0.
  rewrite lshift'_0. easy. easy. easy.
  bdestruct (n0 <? n-1).
  rewrite rshift'_le.
  rewrite lshift'_le.
  easy. lia. lia.
  rewrite rshift'_gt.
  rewrite lshift'_gt. easy.
  lia. lia.
  rewrite rshift'_irrelevant.
  rewrite lshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

Lemma h_sem_gt : forall m n f x v,
      m <= n -> 
       h_sem (f[(x,n) |-> v]) x m = (h_sem f x m)[(x,n) |-> v].
Proof.
  induction m; intros.
  simpl. easy.
  simpl.
  rewrite eupdate_twice_neq by iner_p.
  rewrite IHm by lia.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma had_twice_same : forall n f x t, 
     (forall i, i < n -> right_mode_val t (f (x,i))) ->
    h_sem (h_sem f x n) x n = f.
Proof.
  induction n; intros.
  simpl. easy.
  simpl.
  rewrite h_sem_gt by lia.
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite h_case_twice_same with (t := t).
  rewrite IHn with (t := t).
  rewrite eupdate_same. easy. easy.
  intros. apply H0. lia. apply H0. lia.
Qed.

Lemma sr_rotate_up : forall m n f x size v, m <= n -> 
     sr_rotate' (f[(x,n) |-> v]) x m size = (sr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma sr_rotate_rotate: forall f x n size, sr_rotate' (srr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite sr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_r_same. easy.
Qed.

Lemma srr_rotate_up : forall m n f x size v, m <= n -> 
     srr_rotate' (f[(x,n) |-> v]) x m size = (srr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma srr_rotate_rotate: forall f x n size, srr_rotate' (sr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite srr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_same. easy.
Qed.

Lemma exp_sem_assoc : forall f e1 e2 e3, 
               exp_sem (e1 ; e2 ; e3) f = exp_sem (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Lemma inv_exp_correct :
  forall tenv aenv e f,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_env aenv tenv f ->
    exp_sem (inv_exp e; e) f = f.
Proof.
  induction e; intros.
  - simpl. easy.
  - simpl.
    remember (f [p |-> exchange (f p)]) as f'.
    assert (f = f'[p |-> exchange (f' p)]).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    rewrite exchange_twice_same.
    rewrite eupdate_same. easy. easy.
    rewrite H3. easy.
  - specialize (typed_inv_exp tenv (CU p e) H1) as eq1. simpl in eq1.
    assert (inv_exp (CU p e) = CU p (inv_exp e)). simpl. easy.
    rewrite H3.
    destruct (get_cua (f p)) eqn:eq3.
    rewrite <- two_cu_same.
    apply IHe. inv H0. assumption.
    inv H1. assumption. assumption.
    assumption. rewrite <- H3.
    apply fwf_inv_exp. assumption.
    simpl. rewrite eq3. rewrite eq3. easy.
  - simpl.
    assert ((f [p |-> times_r_rotate (f p) q])
                  [p |-> times_rotate ((f [p |-> times_r_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_r_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H3. easy.
  - simpl.
    assert ((f [p |-> times_rotate (f p) q])
                  [p |-> times_r_rotate ((f [p |-> times_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H3. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite sr_rotate_rotate. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite srr_rotate_rotate. easy.
  - simpl.
    rewrite eupdate_twice_eq.
    rewrite eupdate_same. easy.
    rewrite eupdate_index_eq.
    inv H0. rewrite eupdate_index_neq by easy.
    rewrite hexchange_twice_same. easy.
 - assert (inv_exp (e1; e2) = inv_exp e2; inv_exp e1). simpl. easy.
   rewrite H3.
   rewrite exp_sem_assoc.
   assert (exp_sem (inv_exp e2; (inv_exp e1; (e1; e2))) f 
             = exp_sem (inv_exp e1 ; (e1 ; e2)) (exp_sem (inv_exp e2) f)).
   simpl. easy.
   rewrite H4.
   rewrite <- exp_sem_assoc.
   assert ( forall f', exp_sem ((inv_exp e1; e1); e2) f' = exp_sem e2 (exp_sem ((inv_exp e1; e1)) f')).
   intros. simpl. easy.
   rewrite H5.
   rewrite IHe1.
   assert (exp_sem e2 (exp_sem (inv_exp e2) f) = exp_sem (inv_exp e2 ; e2) f).
   simpl. easy.
   rewrite H6.
   rewrite IHe2. easy.
   inv H0. easy.
   inv H1. easy. easy.
   inv H0. easy.
   inv H1. easy.
   eapply well_typed_right_mode_exp.
   apply typed_inv_exp. inv H1. easy. easy.
Qed.

Lemma map_find_add : forall x v env, @Env.find (type) x (Env.add x v env) = Some v.
Proof.
  intros.
  apply Env.find_1.
  apply Env.add_1. easy.
Qed.

Lemma map_find_neq : forall x y v env, x <> y -> @Env.find (type) x (Env.add y v env) = Env.find x env.
Proof.
  intros.
  destruct (Env.find (elt:=type) x env0) eqn:eq1.
  apply Env.find_1. apply Env.add_2. lia. 
  apply Env.find_2 in eq1. easy.
  destruct (Env.find (elt:=type) x (Env.add y v env0)) eqn:eq2.
  apply Env.find_2 in eq2. apply Env.add_3 in eq2.
  apply Env.find_1 in eq2. rewrite eq1 in eq2. inv eq2. lia.
  easy.
Qed.


Lemma typed_inv_pexp :
  forall p aenv tenv tenv',
    well_typed_pexp aenv tenv p tenv' ->
    well_typed_pexp aenv tenv' (inv_pexp p) tenv.
Proof.
  induction p; intros; simpl; try assumption.
  simpl. inv H0.
  apply sexp_refl.
  apply typed_inv_sexp. easy.
  inv H0.
  econstructor.
  apply mapsto_equal with (s1 := (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0.
  econstructor.
  apply mapsto_equal with (s1 := (Env.add x Nor tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0.
  apply h_had.
  apply mapsto_equal with (s1 := (Env.add x Had tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  constructor.
  apply mapsto_equal with (s1 := (Env.add x Nor tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0.
  econstructor.
  specialize (IHp2 aenv env' tenv').
  apply IHp2. assumption.
  apply IHp1. easy.
Qed.

Lemma inv_exp_correct_rev :
  forall aenv tenv e f,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_env aenv tenv f ->
    exp_sem (e; inv_exp e) f = f.
Proof.
  intros. apply fwf_inv_exp in H0.
  assert ((e; inv_exp e) = inv_exp (inv_exp e) ; inv_exp e).
  rewrite inv_exp_involutive. easy.
  rewrite H3.
  apply (inv_exp_correct tenv aenv). assumption.
  apply typed_inv_exp. assumption.
  assumption.
Qed.

Lemma sexp_sem_assoc : forall env f e1 e2 e3, 
               sexp_sem env (e1 ;; e2 ;; e3) f = sexp_sem env (e1 ;; (e2 ;; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Lemma inv_sexp_correct :
  forall tenv aenv e f,
    well_typed_sexp tenv e -> right_mode_env aenv tenv f ->
    sexp_sem aenv (inv_sexp e ;; e) f = f.
Proof.
  induction e; intros.
 - simpl.
   rewrite lr_shift_same. easy.
 - simpl.
   rewrite rl_shift_same. easy.
 - simpl.
   rewrite rev_twice_same. easy.
  - simpl. inv H0.
    specialize (inv_exp_correct tenv aenv s f H3 H5 H1) as eq1.
    simpl in eq1. easy.
 - assert (inv_sexp (e1;; e2) = inv_sexp e2;; inv_sexp e1). simpl. easy.
   rewrite H2.
   rewrite sexp_sem_assoc.
   assert (sexp_sem aenv (inv_sexp e2;; (inv_sexp e1;; (e1;; e2))) f
             = sexp_sem aenv (inv_sexp e1 ;; (e1 ;; e2)) (sexp_sem aenv (inv_sexp e2) f)).
   simpl. easy.
   rewrite H3.
   rewrite <- sexp_sem_assoc.
   assert ( forall f', sexp_sem aenv ((inv_sexp e1;; e1);; e2) f' = sexp_sem aenv e2 (sexp_sem aenv ((inv_sexp e1;; e1)) f')).
   intros. simpl. easy.
   rewrite H4.
   rewrite IHe1.
   assert (sexp_sem aenv e2 (sexp_sem aenv (inv_sexp e2) f) = sexp_sem aenv (inv_sexp e2 ;; e2) f).
   simpl. easy.
   rewrite H5.
   rewrite IHe2. easy.
   inv H0. easy.
   easy.
   inv H0. easy.
   apply well_typed_right_mode_sexp.
   apply typed_inv_sexp. inv H0. easy. easy.
Qed.

Lemma inv_sexp_correct_rev :
  forall tenv aenv e f,
    well_typed_sexp tenv e -> right_mode_env aenv tenv f ->
    sexp_sem aenv (e;; inv_sexp e) f = f.
Proof.
  intros.
  assert ((e;; inv_sexp e) = inv_sexp (inv_sexp e) ;; inv_sexp e).
  rewrite inv_sexp_involutive. easy.
  rewrite H2.
  apply (inv_sexp_correct tenv).
  apply typed_inv_sexp. easy.
  easy.
Qed.

Lemma pexp_sem_assoc : forall env f e1 e2 e3, 
               prog_sem env (e1 ;;; e2 ;;; e3) f = prog_sem env (e1 ;;; (e2 ;;; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Lemma assign_r_angle_same : forall n i f x r, i < n -> nor_modes f x n ->
              get_r ((assign_r f x r n) (x,i)) = get_r (f (x,i)).
Proof.
  induction n; intros; simpl.
  easy.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  unfold up_qft.
  unfold nor_modes in H1. unfold nor_mode in H1.
  specialize (H1 n H0). 
  destruct (f (x,n)). unfold get_r. easy. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn. easy. lia.
  unfold nor_modes in *. intros. apply H1. lia.
Qed.

Lemma assign_seq_covers : forall m n i f x g h, i < m <= n ->
            nor_modes f x n -> h i = get_cua (f (x,i)) ->
            assign_seq (assign_r f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_r_angle_same; try easy.
 rewrite H2. 
 unfold nor_modes in H1.
 assert (m < n) by lia.
 specialize (H1 m H3). unfold nor_mode in H1.
 destruct (f (x,m)). unfold get_cua,get_r. easy. lia. lia.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma assign_seq_ge : forall n i f x h, n <= i -> assign_seq f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_seq_out : forall n p f x h, fst p <> x -> assign_seq f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma qft_start_nor_modes : forall aenv tenv tenv' x f, well_typed_pexp aenv tenv (QFT x) tenv'
        -> right_mode_env aenv tenv f -> nor_modes f x (aenv x).
Proof.
  intros. inv H0. unfold right_mode_env in H1.
  unfold nor_modes. intros.
  specialize (H1 Nor (x,i)). simpl in H1. 
  specialize (H1 H0 H3). inv H1.
  unfold nor_mode. rewrite <- H2. easy.
Qed.

Lemma assign_r_same_0 : forall n size f x h, 0 < n <= size
          -> nor_modes f x size -> (assign_r f x h n (x,0)) = qval (get_r (f (x,0))) h.
Proof.
  induction n; intros; simpl.
  lia.
  bdestruct (n =? 0). subst.
  rewrite eupdate_index_eq.
  unfold nor_modes in H1.
  assert (0 < size) by lia.
  specialize (H1 0 H2). unfold nor_mode in H1.
  unfold lshift_fun.
  unfold up_qft.
  destruct (f (x,0)). unfold get_r.
  assert ((fun i : nat => h (i + 0)) = h).
  apply functional_extensionality.
  intros. rewrite plus_0_r. easy. rewrite H3. easy. lia. lia. 
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn with (size := size); try easy. lia.
Qed.

Lemma assign_r_ge : forall n i f x h, n <= i -> assign_r f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_out : forall n p f x h, fst p <> x -> assign_r f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Definition phi_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with qval rc r => True | _ => False end.

Definition phi_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> phi_mode f (x,i).

Definition get_snd_r (f:posi -> val) (p:posi) :=
    match (f p) with qval rc r => r | _ => allfalse end.

Lemma assign_seq_lt : forall n i f x h, i < n -> assign_seq f x h n (x,i) = nval (h i) (get_r (f (x,i))).
Proof.
 induction n; intros; simpl.
 easy.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. 
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_covers : forall m n i f x g h, i < m <= n ->
            phi_modes f x n -> lshift_fun h i  = get_snd_r f (x,i) ->
            assign_r (assign_seq f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_seq_lt; try lia.
 unfold up_qft.
 unfold phi_modes in H1.
 specialize (H1 m).
 assert (m < n) by lia. apply H1 in H3.
 unfold phi_mode in H3.
 unfold get_snd_r in H2.
 destruct (f (x,m)). lia. lia.
 rewrite <- H2.
 unfold get_r. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma rqft_start_phi_modes : forall aenv tenv tenv' x f, well_typed_pexp aenv tenv (RQFT x) tenv'
        -> right_mode_env aenv tenv f -> phi_modes f x (aenv x).
Proof.
  intros. inv H0. unfold right_mode_env in H1.
  unfold phi_modes. intros.
  specialize (H1 (Phi (aenv x)) (x,i)). simpl in H1. 
  specialize (H1 H0 H3). inv H1.
  unfold phi_mode. rewrite <- H6. easy.
Qed.

Lemma sr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       sr_rotate' f x n size (x,i) = times_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma srr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       srr_rotate' f x n size (x,i) = times_r_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Definition qft_uniform (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x, Env.MapsTo x (Phi (aenv x)) tenv -> 
             (forall i, i < aenv x -> get_snd_r f (x,i) = (lshift_fun (get_r_qft f x) i)).

Lemma addto_shift_same : forall r n size x, n < size -> addto (fun i => r (i+n)) (size - n) x = addto r size (x + n).
Proof.
  intros. unfold addto.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H3.
  unfold sumfb.
  bdestruct (size - n - 1 - x <? size - n).
  bdestruct (size - n - 1 - x <? size).
  assert ((size - n - 1 - (size - n - 1 - x) + n) = (size - 1 - (size - n - 1 - x))) by lia.
  rewrite H6.
  rewrite carry_lt_same with (n:= size - n) (g := (fun i : nat =>
    if i <? size
    then if i <? size then r (size - 1 - i) else r i
    else allfalse i)); try lia. easy.
  intros.
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert (size - n - 1 - i + n = size - 1 - i) by lia. rewrite H10. easy.
  1-5:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma sumfb_lt_same : forall m n f g h h' b, m < n -> (forall i, i < n -> f i = g i)
               -> (forall i, i < n -> h i = h' i) -> sumfb b f h m = sumfb b g h' m.
Proof.
 intros. unfold sumfb.
 rewrite  carry_lt_same_1 with (n:= n) (g:=g) (h' := h'); try lia.
 rewrite H1 by lia. rewrite H2 by lia. easy.
 easy. easy.
Qed.


Lemma addto_n_shift_same : forall r n size x, n < size -> addto_n (fun i => r (i+n)) (size - n) x = addto_n r size (x + n).
Proof.
  intros. unfold addto_n.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H3.
  rewrite sumfb_lt_same with (n:= size - n) (g:= (fun i : nat =>
   if i <? size
   then if i <? size then r (size - 1 - i) else r i
   else allfalse i)) (h' := (sumfb false (nat2fb 1) (negatem size (nat2fb 1)))); try lia. easy.
  intros. 
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert ((size - n - 1 - i + n) = (size - 1 - i)) by lia. rewrite H7. easy. lia. lia.
  intros.
  rewrite sumfb_lt_same with (n:= size - n) (g := nat2fb 1)
    (h' := (negatem size (nat2fb 1))). easy. lia.
  intros. easy.
  intros. unfold negatem.
  bdestruct (i0 <? size - n).
  bdestruct (i0 <? size). easy.
  1-3:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma qft_uniform_sr_rotate : forall n i size f x, i < n <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (sr_rotate' f x n size) (x, i) = lshift_fun (get_r_qft (sr_rotate' f x n size) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite sr_rotate'_lt_1.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia. lia.
 destruct (f (x,0)). lia. lia.
 subst. unfold rotate.
 rewrite addto_shift_same; try lia.
 assert ((size - 0)  = size) by lia. rewrite H2. easy. lia.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.

Lemma qft_uniform_srr_rotate : forall n i size f x, i < n <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (srr_rotate' f x n size) (x, i) = lshift_fun (get_r_qft (srr_rotate' f x n size) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite srr_rotate'_lt_1.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_r_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia. lia.
 destruct (f (x,0)). lia. lia.
 subst. unfold r_rotate.
 rewrite addto_n_shift_same; try lia.
 assert ((size - 0)  = size) by lia. rewrite H2. easy. lia.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.

Lemma sr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (sr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma sr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (sr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (srr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (srr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma qft_uniform_exp_trans : 
    forall e f aenv tenv, qft_uniform aenv tenv f -> well_typed_exp tenv e
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv (exp_sem e f).
Proof.
  induction e; intros; simpl.
  easy.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  destruct (get_cua (f p)) eqn:eq1.
  apply IHe; try easy. easy.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  unfold sr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_sr_rotate. easy. lia.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  unfold right_mode_env in H2.
  unfold phi_modes. intros.
  specialize (H2 (Phi (aenv x0)) (x0,i0)).
  simpl in H2. assert (i0 < aenv x0) by lia.
  apply H2 in H5; try easy.
  inv H5. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H5 in *. rewrite <- H10. lia.
  rewrite H0; try easy.
  rewrite sr_rotate'_get_snd_r_ge; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  rewrite sr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)).
  apply H2 in H6.
  inv H6.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H1 in *. rewrite <- H8.
  unfold times_rotate, rotate,addto.
  bdestruct (x + i <? S q - 0). lia. easy. simpl. lia.
  rewrite sr_rotate'_get_snd_r_out; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  rewrite sr_rotate'_irrelevant; try lia. easy.
  iner_p.
  inv H1.
  unfold qft_uniform in *. intros.
  unfold srr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_srr_rotate. easy. lia.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  unfold right_mode_env in H2.
  unfold phi_modes. intros.
  specialize (H2 (Phi (aenv x0)) (x0,i0)).
  simpl in H2. assert (i0 < aenv x0) by lia.
  apply H2 in H5; try easy.
  inv H5. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H5 in *. rewrite <- H10. lia.
  rewrite H0; try easy.
  rewrite srr_rotate'_get_snd_r_ge; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  rewrite srr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)).
  apply H2 in H6.
  inv H6.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H1 in *. rewrite <- H8.
  unfold times_r_rotate, r_rotate,addto_n.
  bdestruct (x + i <? S q - 0). lia. easy. simpl. lia.
  rewrite srr_rotate'_get_snd_r_out; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  rewrite srr_rotate'_irrelevant; try lia. easy.
  iner_p.
  inv H1.
  unfold qft_uniform in *. intros.
  bdestruct (p1 ==? (x,i)). subst.
  simpl in H6.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_snd_r in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  destruct p1.
  bdestruct (v =? x). subst. simpl in *.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_r_qft.
  rewrite eupdate_index_neq by iner_p. easy.
  inv H1.
  specialize (IHe1 f aenv tenv H0 H6 H2).
  apply well_typed_right_mode_exp with (e := e1) in H2; try easy.
  specialize (IHe2 (exp_sem e1 f) aenv tenv IHe1). apply IHe2; try easy.
Qed.

Lemma qft_uniform_sexp_trans : 
    forall e f aenv tenv, qft_uniform aenv tenv f -> well_typed_sexp tenv e
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv (sexp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  assert (get_snd_r (lshift f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,lshift. rewrite lshift'_irrelevant. easy. easy.
  rewrite H6. rewrite H0.
  assert ((get_r_qft (lshift f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,lshift.
  rewrite lshift'_irrelevant. easy. easy.
  rewrite H7. easy. 1-2:easy.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r, rshift,get_r_qft.
  repeat rewrite rshift'_irrelevant; try easy.
  unfold get_snd_r,get_r_qft in H0.
  rewrite H0. 1-3:easy.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r,reverse,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl.
  rewrite H0. 1-3:easy.
  apply qft_uniform_exp_trans; try easy. inv H1. easy.
  inv H1. specialize (IHe1 f aenv tenv H0 H6 H2).
  apply IHe2; try easy.
  apply well_typed_right_mode_sexp; easy.
Qed.

Lemma assign_seq_out_1 : forall n f h x y i, x <> y -> assign_seq f x h n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma h_sem_out : forall n f x y i, x <> y -> h_sem f x n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy.
Qed.

Lemma assign_r_lt : forall n f x r i, i < n -> assign_r f x r n (x,i) = up_qft (f (x,i)) (lshift_fun r i).
Proof.
 induction n; intros; simpl.
 lia.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma lshift_fun_0 : forall f, lshift_fun f 0 = f.
Proof.
  intros. apply functional_extensionality. intros.
  unfold lshift_fun. rewrite plus_0_r. easy.
Qed.

Lemma qft_uniform_pexp_trans : 
    forall e f aenv tenv tenv', qft_uniform aenv tenv f -> well_typed_pexp aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv' (prog_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H1.
  apply qft_uniform_sexp_trans; try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_qft,get_snd_r.
  rewrite assign_r_lt; try lia.
  unfold get_r_qft.
  rewrite assign_r_lt; try lia.
  unfold up_qft.
  unfold right_mode_env in H2. 
  specialize (H2 Nor (x,i)) as eq1. simpl in eq1. 
  specialize (H2 Nor (x,0)) as eq2. simpl in eq2.
  assert (0 < aenv x) by lia.
  specialize (eq1 H3 H4). specialize (eq2 H5 H4).
  inv eq1. inv eq2.
  rewrite lshift_fun_0. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H1; try easy.
  apply Env.add_3 in H1 ; try lia. 
  assert (get_snd_r (turn_qft f x (aenv x)) (x0, i) = get_snd_r f (x0, i)).
  unfold get_snd_r,turn_qft.
  rewrite assign_r_out; try easy. rewrite H7.
  rewrite H0; try easy.
  unfold get_r_qft,turn_qft.
  rewrite assign_r_out; try easy.
  unfold qft_uniform in *. intros.
  inv H1.
  bdestruct (x =? x0). subst.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H8; try easy.
  apply mapsto_add1 in H8. inv H8.
  unfold turn_rqft.
  unfold get_snd_r in *.
  rewrite assign_seq_out_1.
  rewrite H0; try easy.
  unfold get_r_qft.
  destruct (f (x, 0)) eqn:eq1.
  rewrite assign_seq_out_1 by lia. easy.
  rewrite assign_seq_out_1 by lia. easy.
  rewrite assign_seq_out_1 by lia. easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3.
  apply Env.add_3 in H3. easy. lia. easy. lia.
  unfold qft_uniform in *. intros.
  bdestruct (x =? x0). subst.
  inv H1.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H8; try easy.
  apply mapsto_add1 in H8. inv H8.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H8; try easy.
  apply mapsto_add1 in H8. inv H8.
  unfold get_snd_r in *.
  rewrite h_sem_out by easy. rewrite H0; try easy.
  unfold get_r_qft.
  rewrite h_sem_out by easy. easy.
  inv H1.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply Env.add_3 in H9. easy. lia.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply Env.add_3 in H9. easy. lia.
  inv H1. specialize (IHe1 f aenv tenv env' H0 H6 H2).
  apply IHe2 with (tenv := env'); try easy.
  eapply well_typed_right_mode_pexp. apply H6. easy.
Qed.

Lemma get_r_qft_lshift : forall f x m n, m < n -> (forall i, n <= i -> get_r_qft f x i = false) ->
            (forall i, n - m <= i -> lshift_fun (get_r_qft f x) m i = false).
Proof.
  intros.
  unfold lshift_fun.
  apply H1. lia.
Qed. 

Definition qft_gt (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x, Env.MapsTo x (Phi (aenv x)) tenv -> (forall i, 0 < (aenv x) <= i -> get_r_qft f x i = false).

Lemma qft_gt_exp_trans : 
    forall e f aenv tenv, qft_gt aenv tenv f -> well_typed_exp tenv e
            -> right_mode_env aenv tenv f -> qft_gt aenv tenv (exp_sem e f).
Proof.
  induction e; intros; simpl.
  easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. simpl in H7.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  destruct (get_cua (f p)). apply IHe; try easy. easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. simpl in H7.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. simpl in H7.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H7. inv H7. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (x =? x0). subst.
  unfold sr_rotate.
  rewrite sr_rotate'_lt_1; try lia.
  inv H1.
  apply mapsto_always_same with (v1 := (Phi (aenv x0))) in H8. inv H8.
  specialize (H0 x0 H3 i H4).
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)). simpl in H2.
  apply H2 in H3; try lia. inv H3.
  unfold times_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H1 in *.
  rewrite <- H6 in *. unfold rotate,addto.
  bdestruct (i <? S q - 0). lia. easy. easy.
  unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try easy.
  rewrite H0; try easy. simpl. lia.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (x =? x0). subst.
  unfold srr_rotate.
  rewrite srr_rotate'_lt_1; try lia.
  inv H1.
  apply mapsto_always_same with (v1 := (Phi (aenv x0))) in H8. inv H8.
  specialize (H0 x0 H3 i H4).
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)). simpl in H2.
  apply H2 in H3; try lia. inv H3.
  unfold times_r_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H1 in *.
  rewrite <- H6 in *. unfold r_rotate,addto_n.
  bdestruct (i <? S q - 0). lia. easy. easy.
  unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try easy.
  rewrite H0; try easy. simpl. lia.
  unfold qft_gt in *. intros.
  inv H1. destruct p1.
  simpl in H8. bdestruct (x =? v). subst.
  apply mapsto_always_same with (v1 := (Phi (aenv v))) in H8. inv H8. easy.
  unfold get_r_qft in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  specialize (IHe1 f aenv tenv H0 H6 H2).
  apply IHe2 ; try easy.
  apply well_typed_right_mode_exp; easy.
Qed.

Lemma qft_gt_sexp_trans : 
    forall e f aenv tenv, qft_gt aenv tenv f -> well_typed_sexp tenv e
            -> right_mode_env aenv tenv f -> qft_gt aenv tenv (sexp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_r_qft in *.
  unfold lshift. rewrite lshift'_irrelevant by iner_p.
  rewrite H0 ; try easy.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_r_qft in *.
  unfold rshift. rewrite rshift'_irrelevant by iner_p.
  rewrite H0 ; try easy.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply mapsto_always_same with (v2:=Had) in H3; try easy.
  unfold get_snd_r,reverse,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl.
  rewrite H0. 1-3:easy.
  apply qft_gt_exp_trans; try easy. inv H1. easy.
  inv H1. specialize (IHe1 f aenv tenv H0 H6 H2).
  apply IHe2; try easy.
  apply well_typed_right_mode_sexp; easy.
Qed.

Lemma qft_gt_pexp_trans : 
    forall e f aenv tenv tenv', qft_gt aenv tenv f -> well_typed_pexp aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> qft_gt aenv tenv' (prog_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H1.
  apply qft_gt_sexp_trans; try easy.
  inv H1.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_qft,get_r_qft in *.
  rewrite assign_r_lt; try lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold right_mode_env in H2. specialize (H2 Nor (x,0)).
  simpl in H2. destruct H3. apply H2 in H3; try easy.
  inv H3. unfold get_cus. bdestruct (i <? aenv x). lia. easy.
  unfold get_r_qft,turn_qft in *.
  rewrite assign_r_out.
  rewrite H0; try easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H1; try easy.
  apply Env.add_3 in H1. easy. lia. iner_p.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply mapsto_always_same with (v2:=Nor) in H3; try easy.
  apply Env.add_1. easy.
  unfold turn_rqft,get_r_qft in *.
  unfold right_mode_env in H2.
  inv H1.
  destruct H4.
  destruct (f (x, 0)) eqn:eq1.
  rewrite assign_seq_out.
  rewrite H0; try easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3. easy. lia. iner_p.
  rewrite assign_seq_out.
  rewrite H0; try easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3. easy. lia. iner_p.
  rewrite assign_seq_out.
  rewrite H0; try easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3. easy. lia. iner_p.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  inv H1.
  apply mapsto_equal with (k := x) (v:= (Phi (aenv x))) in H8; try easy.
  apply mapsto_add1 in H8. inv H8.
  apply mapsto_equal with (k := x) (v:= (Phi (aenv x))) in H8; try easy.
  apply mapsto_add1 in H8. inv H8.
  unfold get_r_qft in *.
  rewrite h_sem_out by lia. rewrite H0; try easy.
  inv H1.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply Env.add_3 in H9. easy. lia.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply Env.add_3 in H9. easy. lia.
  inv H1. specialize (IHe1 f aenv tenv env' H0 H6 H2).
  apply IHe2 with (tenv := env'); try easy.
  eapply well_typed_right_mode_pexp. apply H6. easy.
Qed.

Lemma inv_pexp_correct_rev :
  forall e tenv tenv' aenv f,
    well_typed_pexp aenv tenv e tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> prog_sem aenv (e;;; inv_pexp e) f = f.
Proof. 
  induction e; intros.
 - simpl. inv H0.
    specialize (inv_sexp_correct_rev tenv' aenv s f H6 H1) as eq1.
    simpl in eq1. easy.
 - simpl. unfold turn_qft,turn_rqft.
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? aenv v).
   rewrite assign_seq_covers; try easy.
   eapply qft_start_nor_modes. apply H0. easy.
   unfold get_r_qft.
   rewrite assign_r_same_0 with (size := (aenv v)); try lia.
   rewrite get_cus_cua. easy. lia.
   eapply qft_start_nor_modes. apply H0. easy.
   rewrite assign_seq_ge by lia.
   rewrite assign_r_ge by lia. easy.
   rewrite assign_seq_out by iner_p.
   rewrite assign_r_out by iner_p. easy.
 - simpl. unfold turn_qft,turn_rqft.
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? aenv v).
   rewrite assign_r_covers; try easy.
   eapply rqft_start_phi_modes. apply H0. easy.
   unfold qft_uniform in H2.
   inv H0. rewrite H2; try easy.
   unfold qft_gt in H3. 
   assert ((get_cus (aenv v) (assign_seq f v (get_r_qft f v) (aenv v)) v)
           = (get_r_qft f v)).
   apply functional_extensionality. intros.
   bdestruct (x <? aenv v).
   rewrite get_cus_cua; try lia.
   rewrite assign_seq_lt; try lia.
   unfold get_cua. easy.
   unfold get_cus. bdestruct (x <? aenv v). lia.
   rewrite H3; try easy. lia.
   rewrite H0. easy.
   rewrite assign_r_ge; try lia.
   rewrite assign_seq_ge; try lia. easy.
   rewrite assign_r_out by iner_p.
   rewrite assign_seq_out by iner_p. easy.
 - simpl.
   inv H0.
   rewrite had_twice_same with (t := Nor). easy. intros. 
   unfold right_mode_env in H1. apply H1. easy. easy.
   rewrite had_twice_same with (t := Had). easy. intros. 
   unfold right_mode_env in H1. apply H1. easy. easy.
 - assert (inv_pexp (e1;;; e2) = inv_pexp e2;;; inv_pexp e1). simpl. easy.
   rewrite H4.
   rewrite pexp_sem_assoc.
   assert (prog_sem aenv (e1;;; (e2;;; (inv_pexp e2;;; inv_pexp e1))) f
             = prog_sem aenv (e2 ;;; (inv_pexp e2 ;;; inv_pexp e1)) (prog_sem aenv (e1) f)).
   simpl. easy.
   rewrite H5.
   rewrite <- pexp_sem_assoc.
   assert ( forall f', prog_sem aenv ((e2;;; inv_pexp e2);;; inv_pexp e1) f'
            = prog_sem aenv (inv_pexp e1) (prog_sem aenv ((e2;;; inv_pexp e2)) f')).
   intros. simpl. easy.
   rewrite H6.
   inv H0.
   rewrite (IHe2 env' tenv').
   assert (prog_sem aenv (inv_pexp e1) (prog_sem aenv e1 f) = prog_sem aenv (e1 ;;; inv_pexp e1) f).
   simpl. easy.
   rewrite H0.
   rewrite (IHe1 tenv env'). easy. easy. easy. easy. easy. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv). easy. easy.
   apply qft_uniform_pexp_trans with (tenv := tenv); try easy.
   apply qft_gt_pexp_trans with (tenv := tenv) ; try easy.
Qed.

Lemma inv_pexp_correct :
  forall e tenv tenv' aenv f,
    well_typed_pexp aenv tenv e tenv' -> right_mode_env aenv tenv' f ->
    qft_uniform aenv tenv' f -> qft_gt aenv tenv' f ->
    prog_sem aenv (inv_pexp e ;;; e) f = f.
Proof. 
  intros.
  assert ((inv_pexp e;;; e) = (inv_pexp e;;; inv_pexp (inv_pexp e))).
  rewrite inv_pexp_involutive. easy.
  rewrite H4.
  assert (well_typed_pexp aenv tenv' (inv_pexp e) tenv).
  apply typed_inv_pexp. easy.
  apply (inv_pexp_correct_rev (inv_pexp e) tenv' tenv aenv f H5 H1).
  1-2:easy.
Qed.


Lemma exp_sem_same_out:
   forall e f g1 g2, exp_sem e f = g1 -> exp_sem e f = g2 -> g1 = g2.
Proof.
 intros e.
 induction e;simpl; intros; subst; try easy.
Qed.

Lemma inv_exp_reverse :
  forall (tenv:env) (aenv: var -> nat) e f g,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_env aenv tenv f ->
    exp_sem e f = g ->
    exp_sem (inv_exp e) g = f.
Proof.
  intros. specialize (inv_exp_correct_rev aenv tenv e f H0 H1 H2) as G.
  simpl in G.
  subst. easy.
Qed.


Ltac nor_mode_simpl := repeat (try (apply nor_mode_up ; iner_p); try apply nor_mode_cus_eq; try easy). 

Lemma right_mode_val_cus_same : 
   forall f t p x g n, right_mode_val t (f p)
    -> right_mode_val t (put_cus f x g n p).
Proof.
  intros. unfold put_cus.
  destruct p.
  simpl. 
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  unfold put_cu.
  destruct (f (x,n0)). inv H0. constructor.
  inv H0. constructor. easy.
  inv H0.  constructor. easy. easy.
Qed.

Lemma right_mode_exp_put_cus_same :
    forall aenv tenv f x g n,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  unfold put_cus.
  destruct p. simpl in *.
  bdestruct (v=?x). bdestruct (n0 <? n).
  specialize (H0 t (v,n0)). simpl in H0.
  apply H0 in H1; try easy.
  unfold put_cu.
  destruct (f (v,n0)). inv H1. constructor.
  easy. easy. apply H0; try easy.
  apply H0; try easy.
Qed.

Lemma right_mode_exp_up_same_1 :
    forall aenv tenv f f' c b,
     nor_mode f c -> nor_mode f' c ->
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f' c) b]).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  bdestruct (p ==? c).
  subst. rewrite eupdate_index_eq.
  unfold nor_mode in *.
  destruct (f' c).
  unfold put_cu.
  apply H2 in H4. inv H4. rewrite <- H7 in *. constructor.
  rewrite <- H5 in *. lia. rewrite <- H7 in *. lia. easy.
  lia. lia.
  rewrite eupdate_index_neq by iner_p. apply H2; try easy.
Qed.

Lemma put_cus_update_flip : forall n f g x c v, fst c <> x -> put_cus (f[c |-> v]) x g n = (put_cus f x g n)[c |-> v].
Proof.
  intros.
  apply functional_extensionality; intro.
  bdestruct (c ==? x0). subst. rewrite eupdate_index_eq.
  destruct x0. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  destruct x0.
  bdestruct (v0 =? x). subst. bdestruct (n0 <? n). 
  rewrite put_cus_eq by iner_p.
  rewrite put_cus_eq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_out by lia.
  rewrite put_cus_out by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma right_mode_exp_up_same :
    forall aenv tenv f c b,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f c) b]).
Proof.
  intros.
  unfold right_mode_env in *.
  intros.
  bdestruct (c ==? p). subst.
  rewrite eupdate_index_eq.
  apply (H0 t) in H1; try easy.
  destruct (f p). unfold put_cu. inv H1. constructor.
  unfold put_cu. easy.
  unfold put_cu. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H0; try easy.
Qed.

Ltac right_simpl := repeat (try apply right_mode_exp_put_cus_same; try apply right_mode_exp_up_same;
                 (try (apply right_mode_exp_up_same_1; nor_mode_simpl)); try easy).

(*  Compilation to bcom. *)
(* Controlled rotation cascade on n qubits. *)

(* States that is useful in compiling RCIR+ to SQIR. *)
Definition id_fun := fun (i:nat) => i.

Definition adj_offset (index:nat) (offset:nat) (size:nat) :=
    (index + offset) mod size.

Definition rz_ang (n:nat) : R := ((2%R * PI)%R / 2%R^n).

Definition rrz_ang (n:nat) : R := ((2%R * PI)%R - ((2%R * PI)%R / 2%R^n)).

Definition vars := nat -> (nat * nat * (nat -> nat) * (nat -> nat)).

Definition start (vs :vars) (x:var) := fst (fst (fst (vs x))).

Definition vsize (vs:vars) (x:var) := snd (fst (fst (vs x))).

Definition vmap (vs:vars) (x:var) := snd (fst (vs x)).

Definition avmap (vs:vars) (x:var) := snd (vs x).

Definition find_pos (f : vars) (p:posi) :=
      let (a,b) := p in start f a + (vmap f a b).

(* Compilinng input variables to a format that will be used on RCIR+. *)


Fixpoint compile_var' (l: list (var * nat)) (dim:nat) :=
   match l with [] => fun _ => (0,0,id_fun,id_fun)
              | (x,n):: l' => fun i => if x =? i
                           then (dim,n,id_fun,id_fun) else (compile_var' l' (dim + n)) i
   end.

Definition compile_var l := compile_var' l 0.

Fixpoint get_dim (l: list (var * nat)) :=
   match l with [] => 0
             | (x,n) :: l' => n + get_dim l'
   end.


Inductive vars_WF : (list (var * nat)) -> Prop :=
    vars_WF_empty : vars_WF (List.nil)
    | vars_WF_many : forall x y xl, 0 < y -> vars_WF xl -> vars_WF ((x,y)::xl).

Fixpoint avars (l: list (var * nat)) (dim:nat) : (nat -> posi) :=
    match l with [] => fun i => (dim,dim)
              | (x,n):: l' => fun i => if (dim <? i) && (i - dim <? n) then (x, i - dim)
                                       else avars l' (dim + n) i
    end.
       
(*                                                                            
Lemma vs_bij : forall l dim vs avs, dim = get_dim l ->
            vs = compile_var' l 0 -> vars_WF l -> avs = avars l 0 ->
         (forall x y, y < vsize vs x -> 
              (forall i, i < dim -> avs (find_pos vs (x,y)) = (x,y))).
Proof.
  intros. subst.
  induction l. simpl in H5. lia.
  simpl.
  destruct a eqn:eq1.
Admitted.
*)

Lemma compile_var'_WF : forall l dim p vs, vs = compile_var' l dim
              -> snd p < vsize vs (fst p) -> find_pos vs p < dim + get_dim l.
Proof.
 induction l; intros; simpl in *.
 rewrite H0 in H1. unfold vsize in H1. simpl in H1. lia.
 destruct a eqn:eq1.
 destruct p eqn:eq2.
 simpl in *. subst.
 unfold start,vsize,vmap. unfold vsize in H1.
 bdestruct (v =? v0). subst. simpl in *.
 unfold id_fun. lia.
 remember (compile_var' l (dim + n)) as vs'.
 assert (snd (fst (fst (vs' v0))) = vsize vs' v0) by easy.
 rewrite H2 in H1.
 specialize (IHl (dim + n) (v0,n0) vs' Heqvs' H1).
 subst.
 unfold find_pos,start,vmap in IHl. lia.
Qed.

Lemma compile_var_WF : forall l p vs, vs = compile_var l
              -> snd p < vsize vs (fst p) -> find_pos vs p < get_dim l.
Proof.
  intros. unfold compile_var.
  specialize (compile_var'_WF l 0 p vs H0 H1) as eq1. lia.
Qed.
(*
Definition inter_num (size:nat) (t : varType) :=
   match t with NType => size
              | SType => size+1
   end.
*)


(* the compilation state properties with lemmas. *)
Definition vars_start_diff (vs: vars) :=
        forall x y,  x <> y -> start vs x <> start vs y.

Definition weak_finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n -> f x < n)%nat /\ 
  (exists g, (forall y, y < n -> g y < n)%nat /\
        (forall x, (x < n)%nat -> g (f x) = x) /\ 
        (forall y, (y < n)%nat -> f (g y) = y)).

Definition vars_finite_bij (vs:vars) :=
   forall x,  weak_finite_bijection (vsize vs x) (vmap vs x).

Definition vars_sparse (vs:vars) :=
   forall x y, x <> y -> (forall i j, i < vsize vs x -> j < vsize vs y -> start vs x + i <> start vs y + j).

Lemma finite_bij_lt : forall vs, vars_finite_bij vs 
         -> (forall x i, i < vsize vs x -> vmap vs x i < vsize vs x).
Proof.
  intros. unfold vars_finite_bij in H0.
  unfold weak_finite_bijection in H0.
  destruct (H0 x).
  apply H2. easy.
Qed.

Lemma finite_bij_inj : forall vs x, vars_finite_bij vs 
         -> (forall i j, i < vsize vs x -> j < vsize vs x -> i <> j -> vmap vs x i <> vmap vs x j).
Proof.
  intros. unfold vars_finite_bij in H0.
  unfold weak_finite_bijection in H0.
  destruct (H0 x).
  destruct H5. destruct H5. destruct H6.
  specialize (H6 i H1) as eq1.
  specialize (H6 j H2) as eq2.
  intros R.
  rewrite R in eq1. rewrite eq1 in eq2. subst. contradiction.
Qed.



(* Compiled RCIR+ circuit well-formedness. *)
Inductive exp_WF : vars -> exp -> Prop :=
      | skip_wf : forall vs p, snd p < vsize vs (fst p) -> exp_WF vs (SKIP p)
      | x_wf : forall vs p, snd p < vsize vs (fst p) -> exp_WF vs (X p)
      | cu_wf : forall vs p e, snd p < vsize vs (fst p) -> exp_WF vs e -> exp_WF vs (CU p e)
      | hcnot_wf : forall vs p1 p2, snd p1 < vsize vs (fst p1)
                              -> snd p2 < vsize vs (fst p2) -> exp_WF vs (HCNOT p1 p2)
      | rz_wf : forall vs p q, snd p < vsize vs (fst p) -> exp_WF vs (RZ q p)
      | rrz_wf : forall vs p q, snd p < vsize vs (fst p) -> exp_WF vs (RRZ q p)
      | sr_wf : forall vs n x, S n < vsize vs x -> exp_WF vs (SR n x)
      | ssr_wf : forall vs n x, S n < vsize vs x -> exp_WF vs (SRR n x)       
      | seq_wf : forall vs e1 e2, exp_WF vs e1 -> exp_WF vs e2 -> exp_WF vs (Seq e1 e2).


Inductive exp_rmax : nat -> exp -> Prop :=
      | skip_rmax : forall rs p, exp_rmax rs (SKIP p)
      | x_rmax : forall rs p, exp_rmax rs (X p)
      | hcnot_rmax : forall rs p1 p2, exp_rmax rs (HCNOT p1 p2)
      | cu_rmax : forall vs p e, exp_rmax vs e -> exp_rmax vs (CU p e)
      | rz_rmax : forall rs p q, q < rs -> exp_rmax rs (RZ q p)
      | rrz_rmax : forall rs p q, q < rs -> exp_rmax rs (RRZ q p)
      | sr_rmax : forall rs n x, S n < rs -> exp_rmax rs (SR n x)
      | srr_rmax : forall rs n x, S n < rs -> exp_rmax rs (SRR n x)
      | seq_rmax : forall rs e1 e2, exp_rmax rs e1 -> exp_rmax rs e2 -> exp_rmax rs (Seq e1 e2).


Fixpoint gen_sr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_sr_gate' f dim x m size) (SQIR.Rz (rz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_sr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_sr_gate' f dim x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_srr_gate' f dim x m size) (SQIR.Rz (rrz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_srr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_srr_gate' f dim x (S n) (S n).

Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) : base_ucom dim :=
  match exp with SKIP p => SQIR.ID (find_pos f p)
              | X p => SQIR.X (find_pos f p)
              | RZ q p => SQIR.Rz (rz_ang q) (find_pos f p)
              | RRZ q p => SQIR.Rz (rrz_ang q) (find_pos f p)
              | SR n x => gen_sr_gate f dim x n
              | SRR n x => gen_srr_gate f dim x n
              | HCNOT p1 p2 => SQIR.CNOT (find_pos f p1) (find_pos f p2)
              | CU p1 (X p2) => SQIR.CNOT (find_pos f p1) (find_pos f p2)
              | CU p e1 => control (find_pos f p) (trans_exp f dim e1)
              | e1 ; e2 => SQIR.useq (trans_exp f dim e1) (trans_exp f dim e2)
  end.

Definition exp_com_WF (vs:vars) (dim:nat) :=
    forall p, snd p < vsize vs (fst p) -> find_pos vs p < dim.

Definition exp_com_gt (vs:vars) (avs: nat -> posi) (dim:nat) :=
    forall i, i >= dim -> vsize vs (fst (avs i)) = 0.

Fixpoint turn_angle (rval : nat -> bool) (n : nat) : R :=
  match n with 0 => (0:R)
            | S m => ((1/ (2^(Nat.b2n(rval m))))%R + turn_angle rval m)%R
  end.

Definition z_phase (b:bool) : R := if b then 1%R else (-1)%R.

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp ((turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
             | hval b1 b2 r => Cexp ((turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)
             | qval q r => Cexp ((turn_angle q r_max)) .* (∣0⟩ .+ (Cexp ((turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

Definition trans_state (avs : nat -> posi) (rmax : nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) rmax.

Lemma WF_trans_state : forall avs r f i, WF_Matrix (trans_state avs r f i).
Proof.
  intros. unfold trans_state. auto with wf_db.
Qed.

Hint Resolve WF_trans_state : wf_db.

Lemma trans_exp_cu : forall vs dim p e, 
       (exists p1, e = X p1 /\ 
             trans_exp vs dim (CU p e) = SQIR.CNOT (find_pos vs p) (find_pos vs p1))
    \/ (trans_exp vs dim (CU p e) = ((control (find_pos vs p) (trans_exp vs dim e)))).
Proof.
  intros.
  simpl in *.
  destruct e. right. easy.
  left.
  exists p0. easy.
  right. easy.
  right. easy. right. easy. right. easy.
  right. easy. right. easy. right. easy.
Qed.

Lemma find_pos_prop : forall vs p1 p2, vars_start_diff vs -> vars_finite_bij vs ->
            vars_sparse vs ->
            snd p1 < vsize vs (fst p1) -> snd p2 < vsize vs (fst p2) ->
            p1 <> p2 -> find_pos vs p1 <> find_pos vs p2.
Proof.
  intros.
  unfold find_pos,vars_start_diff in *.
  destruct p1. destruct p2.
  simpl in *.
  destruct (vs v) eqn:eq1.
  destruct (vs v0) eqn:eq2.
  destruct p. destruct p0.
  bdestruct (v =? v0).
  subst.
  assert (n <> n0). intros R. subst. contradiction.
  rewrite eq1 in eq2.
  inv eq2.
  specialize (finite_bij_inj vs v0 H1) as eq3.
  specialize (eq3 n n0 H3 H4 H6) as eq4. lia.
  specialize (H2 v v0 H6).
  apply H2.
  apply finite_bij_lt;  assumption.
  apply finite_bij_lt;  assumption.
Qed.

Lemma trans_state_update : forall dim (vs:vars) (avs: nat -> posi) rmax f (p:posi) v,
      (snd p < vsize vs (fst p)) ->
     (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
     (forall i, i < dim -> find_pos vs (avs i) = i) ->
    (forall x , x < dim -> (trans_state avs rmax (f [p |-> v]))  x
            = update (trans_state avs rmax f) (find_pos vs p) (compile_val v rmax) x).
Proof.
  intros.
  unfold trans_state.
  bdestruct (x =? (find_pos vs p)).
  subst.
  rewrite H1 by assumption.
  rewrite eupdate_index_eq.
  rewrite update_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite update_index_neq. easy. lia.
  intros R. subst. rewrite H2 in H4. lia. lia.
Qed.



Local Transparent SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma vkron_fun_gt : forall i m (f : nat -> Vector 2) v, i <= m -> vkron i (update f m v) = vkron i f.
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma vkron_shift_gt : forall i m j (f : nat -> Vector 2) v, j < m ->
                vkron i (shift (update f j v) m) = vkron i (shift f m).
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  assert (shift (update f j v) m i = shift f m i).
  unfold shift.
  rewrite update_index_neq. easy. lia.
  rewrite H1. easy.
Qed.


Lemma vkron_split_up : forall n i (f : nat -> Vector 2) v,
  (forall j, WF_Matrix (f j)) -> WF_Matrix v ->
(*  (forall j, j < n -> WF_Matrix (f j)) -> Maybe necessary? *)
  i < n ->
  vkron n (update f i v) = (vkron i f) ⊗ v ⊗ (vkron (n - (i + 1)) (shift f (i + 1))).
Proof.
  intros.
  rewrite (vkron_split n i).
  rewrite vkron_fun_gt by lia.
  assert ((n - 1 - i) = n - (i + 1)) by lia. rewrite H3.
  rewrite vkron_shift_gt.
  rewrite update_index_eq. easy. lia.
  intros.
  bdestruct (i =? j). subst.
  rewrite update_index_eq. assumption.
  rewrite update_index_neq.
  apply H0. lia. lia.
Qed.



Lemma denote_ID_1 : forall dim n, n < dim -> uc_eval (ID n) = I (2 ^ dim).
Proof.
  intros.
  rewrite denote_ID. unfold pad.
  bdestruct (n+1<=? dim).
  gridify. easy. lia.
Qed.

Lemma vkron_X : forall (n i : nat) (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.X i)) × (vkron n f) 
      = vkron i f ⊗ (σx × (f i)) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H1 H0). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma vkron_Rz : forall (n i : nat) q (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.Rz q i)) × (vkron n f) 
      = vkron i f ⊗ (phase_shift q × f i) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H1 H0). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Definition size_env (vs : vars):= fun i => vsize vs i.

Lemma is_fresh_sr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H4 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H4 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
Qed.


Lemma is_fresh_sr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma is_fresh_srr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H4 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H4 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
Qed.

Lemma is_fresh_srr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma fresh_is_fresh :
  forall p e vs (dim:nat),
    exp_fresh p e -> exp_WF vs e ->
    snd p < vsize vs (fst p) ->
    vars_start_diff vs -> vars_finite_bij vs ->
    vars_sparse vs ->
      @is_fresh _ dim (find_pos vs p) ((trans_exp vs dim e)).
Proof.
  intros.
  remember (find_pos vs p) as q.
  generalize dependent vs.
  induction e; intros.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  specialize (trans_exp_cu vs dim p0 e) as eq1.
  destruct eq1. destruct H6. destruct H6.
  subst. rewrite H7.
  apply fresh_app2.
  inv H0. inv H1. inv H12.
  apply find_pos_prop; try assumption.
  apply find_pos_prop; try assumption.
  inv H1. inv H11. assumption.
  inv H0. inv H11. assumption.
  rewrite H6. rewrite Heqq.
  inv H1. inv H0.
  apply fresh_control.
  split.
  apply find_pos_prop; try assumption. 
  apply IHe; try assumption. easy.
  subst. inv H0. inv H1.
  simpl.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H0. inv H1.
  simpl.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H0. inv H1.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H8. lia.
  specialize (is_fresh_sr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_sr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. easy. easy.
  subst. inv H0. inv H1.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H8. lia.
  specialize (is_fresh_srr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_srr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. easy. easy.
  simpl.
  apply fresh_app2.
  inv H0. inv H1.
  apply find_pos_prop; try assumption. subst.
  apply find_pos_prop; try assumption.
  inv H1. easy.
  inv H0. easy.
  simpl.
  apply fresh_seq; try assumption.
  inv H1. inv H0.
  apply IHe1; try assumption. easy.
  inv H1. inv H0.
  apply IHe2; try assumption. easy. 
Qed.

Lemma gen_sr_gate_uc_well_typed : forall n size x dim vs, n <= size ->
     n < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_sr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H2.
  specialize (H2 (x,0)). apply H2. iner_p.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H2 (x,n)). apply H2. simpl. lia.
Qed.

Lemma gen_srr_gate_uc_well_typed : forall n size x dim vs, n <= size ->
     n < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_srr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H2.
  specialize (H2 (x,0)). apply H2. iner_p.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H2 (x,n)). apply H2. simpl. lia.
Qed.

Lemma trans_exp_uc_well_typed : forall e dim vs,     
     vars_start_diff vs -> vars_finite_bij vs ->
       vars_sparse vs -> exp_fwf e -> exp_WF vs e ->
            exp_com_WF vs dim ->  @uc_well_typed _ dim (((trans_exp vs dim e))).
Proof.
  induction e; intros.
  simpl. inv H4. constructor. apply H5. easy. 
  simpl. inv H4. constructor. apply H5. easy. 
  specialize (trans_exp_cu vs dim p e) as eq1.
  destruct eq1. destruct H6. destruct H6. subst. simpl.
  inv H4. constructor. apply H5. easy. 
  apply H5. inv H11. assumption.
  inv H3. inv H8.
  inv H11.
  apply find_pos_prop; try assumption.
  rewrite H6. 
  apply uc_well_typed_control.
  inv H3. inv H4. split.
  apply H5. easy.
  split.
  apply fresh_is_fresh; try assumption.
  apply IHe; try assumption.
  inv H4.
  simpl. constructor.
  apply H5. easy.
  inv H4.
  simpl. constructor.
  apply H5. easy.
  simpl. unfold gen_sr_gate.
  apply gen_sr_gate_uc_well_typed; try easy.
  inv H4. easy.
  simpl. unfold gen_srr_gate.
  apply gen_srr_gate_uc_well_typed; try easy.
  inv H4. easy.
  simpl. inv H4.
  constructor. apply H5. easy.
  apply H5. easy.
  apply find_pos_prop; try assumption.
  inv H3. easy.
  simpl.
  inv H3. inv H4.
  constructor.
  apply IHe1; try easy.
  apply IHe2; try easy.
Qed.

Lemma two_n_kron_n: forall {m p} n i (A : Matrix m p),
  WF_Matrix A -> (i + n) ⨂ A = (n ⨂ A) ⊗ (i ⨂ A).
Proof.
  intros.
  induction n.
  simpl.
  Msimpl. rewrite plus_0_r.
  reflexivity.
  rewrite kron_n_assoc by assumption.
  restore_dims.
  rewrite kron_assoc.
  rewrite <- IHn.
  assert ((m ^ n * m ^ i) = m ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H1. clear H1.
  assert ((p ^ n * p ^ i) = p ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H1. clear H1.
  rewrite <- kron_n_assoc by assumption.
  assert ((i + S n) =  S (i + n)) by lia.
  rewrite H1. easy.
  assumption.
  auto with wf_db.
  auto with wf_db.
Qed.

Lemma uc_cnot_control : forall (n i j : nat),
  i < n -> j < n -> i <> j ->
  (@uc_eval n (SQIR.CNOT i j)) = (uc_eval (control i (SQIR.X j))).
Proof.
  intros.
  rewrite control_correct.
  autorewrite with eval_db.
  bdestruct ( i <? j).
  assert ((i + (1 + (j - i - 1) + 1)) = j + 1) by lia.
  rewrite H4. 
  bdestruct (j + 1 <=? n).
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  rewrite kron_plus_distr_r.
  rewrite kron_assoc.
  rewrite kron_assoc.
  assert ((I 2 ⊗ I (2 ^ (n - (j + 1)))) = I (2^ S (n - (j + 1)))).
  rewrite <- kron_n_I.
  rewrite <- kron_n_assoc.
  rewrite kron_n_I. easy.
  auto with wf_db.
  rewrite H7.
  rewrite kron_assoc.
  assert ((I (2 ^ (j - i - 1)) ⊗ I (2 ^ S (n - (j + 1)))) = I (2 ^ (n - (i + 1)))).
  Check @kron_n_I.
  Check two_n_kron_n.
  rewrite <- kron_n_I.
  rewrite <- kron_n_I.
  rewrite <- two_n_kron_n.
  rewrite kron_n_I.
  assert ((S (n - (j + 1)) + (j - i - 1)) = (n - (i + 1))) by lia.
  rewrite H8. easy. 
  auto with wf_db.
  restore_dims.
  rewrite H8.
  gridify. easy.
  1-9:auto with wf_db.
  lia. lia.
  bdestruct (j <? i).
  assert (j + (1 + (i - j - 1) + 1) = i + 1) by lia.
  rewrite H5. 
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  bdestruct (j + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  gridify. easy. lia. lia. lia.
  constructor. easy.
  constructor. easy.
Qed.

Lemma vkron_proj_eq : forall f q n r b,
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> 
  proj q n b × (vkron n f) = vkron n f.
Proof.
  intros f q n r b ? ? ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. 
  do 2 (apply f_equal2; try reflexivity). 
  rewrite H2. destruct b; solve_matrix.
Qed.

Lemma vkron_proj_neq : forall f q n r b b',
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> b <> b' ->
  proj q n b' × (vkron n f) = Zero.
Proof.
  intros f q n r b b' ? ? H ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. rewrite H.
  destruct b. destruct b'. contradiction. lma.
  destruct b'.  lma. contradiction.
Qed.


Local Opaque SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma trans_exp_cu_eval : forall vs dim p e, 
          vars_start_diff vs -> vars_finite_bij vs -> vars_sparse vs ->
                 exp_fwf (CU p e) ->
                 exp_WF vs (CU p e) -> exp_com_WF vs dim ->
                 (uc_eval ( (trans_exp vs dim (CU p e)))) = 
                    (uc_eval (control (find_pos vs p) ( (trans_exp vs dim e)))).
Proof.
  intros.
  specialize (trans_exp_cu vs dim p e) as eq1.
  destruct eq1.
  destruct H6. destruct H6. subst.
  simpl.
  rewrite uc_cnot_control. easy.
  inv H4. apply H5. easy.
  inv H4. inv H11. apply H5. easy.
  inv H3. inv H9. inv H4. inv H12. 
  apply find_pos_prop; try assumption.
  rewrite H6. easy.
Qed.

Lemma turn_angle_add_same : forall n r q, q < n -> (turn_angle r n + rz_ang q)%R = (turn_angle (rotate r q) n)%R.
Proof.

Admitted.

Lemma turn_angle_add_r_same : forall n r q, q < n -> (turn_angle r n + rrz_ang q)%R = (turn_angle (r_rotate r q) n)%R.
Proof.

Admitted.

Lemma Z_0_bit : σz × ∣0⟩ = ∣0⟩.
Proof.
  solve_matrix.
Qed.

Lemma Z_1_bit : σz × ∣1⟩ = (-1)%R .* ∣1⟩.
Proof.
  solve_matrix.
Qed.

Lemma rz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H5 by assumption.
      apply (H3 (Phi size)) in H1; try easy. inv H1. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H1.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H6.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_same. easy. easy.
Qed.

Lemma rrz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_r_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H5 by assumption.
      apply (H3 (Phi size)) in H1; try easy. inv H1. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H1.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H6.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_r_same. easy. easy.
Qed.

Lemma gen_sr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize ->
    exp_com_WF vs dim -> n < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_sr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (sr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((sr_rotate' f x n size) [(x, n)
                      |-> times_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (sr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  Check rz_ang_trans_sem.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (sr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite sr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite sr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_rotate. constructor.
  rewrite sr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite sr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.

Lemma gen_srr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize ->
    exp_com_WF vs dim -> n < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_srr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (srr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((srr_rotate' f x n size) [(x, n)
                      |-> times_r_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (srr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_r_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rrz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (srr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite srr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite srr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_r_rotate. constructor.
  rewrite srr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite srr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.

Lemma trans_exp_sem :
  forall dim e f tenv rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    exp_fwf e ->
    exp_WF vs e ->
    exp_com_WF vs dim ->
    well_typed_exp tenv e ->
    right_mode_env (size_env vs) tenv f ->
         (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
         (forall i, i < dim -> find_pos vs (avs i) = i) ->
         (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))) ->
    exp_rmax rmax e ->
    dim > 0 ->
    (uc_eval ((trans_exp vs dim e))) × (vkron dim (trans_state avs rmax f)) 
                =  vkron dim (trans_state avs rmax (exp_sem e f)).
Proof.
  intros dim e. induction e; intros.
  - simpl. rewrite denote_ID_1. Msimpl. easy.
    apply H5. inv H4. easy.
  - simpl.
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p |-> exchange (f p)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (exchange (f p)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p))
                 = compile_val (exchange (f p)) rmax).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. unfold right_mode_env in H7.
      apply (H7 Nor) in H16. inv H16.
      unfold exchange. 
      unfold compile_val.
      distribute_scale.
      destruct b. simpl.
      autorewrite with ket_db. easy.
      simpl.
      autorewrite with ket_db. easy. easy.
      apply (H7 Had) in H16.
      inv H16. 
      unfold exchange.
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db.
      rewrite Mplus_comm. easy. easy.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - rewrite trans_exp_cu_eval by assumption.
    rewrite control_correct.
    simpl. 
    assert (exists r', (trans_state avs rmax f) (find_pos vs p) = r' .* (ket (Nat.b2n (get_cua (f p))))).
    inv H3. inv H4.
    unfold trans_state. 
    rewrite H8 by assumption.
    inv H6. apply (H7 Nor) in H17; try easy. inv H17.
    unfold compile_val,get_cua.
    exists (Cexp (turn_angle r rmax)). easy.
    destruct H13.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    specialize (IHe f tenv rmax vs avs).
    inv H3. inv H4. inv H6. apply (H7 Nor) in H18 as eq1.
    rewrite IHe; try easy.
    destruct (get_cua (f p)) eqn:eq2.
    erewrite vkron_proj_neq.
    rewrite vkron_proj_eq with (r := x).
    Msimpl. easy. auto with wf_db. apply H5. easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite H8; try easy.
    auto with wf_db.
    apply H5; easy. rewrite H13. reflexivity. easy.
    rewrite vkron_proj_eq with (r := x).
    rewrite vkron_proj_neq with (r := x) (b := false). Msimpl. easy.
    auto with wf_db.
    apply H5. easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite H8; try easy. easy.
    auto with wf_db.
    apply H5; easy. rewrite H13. reflexivity. inv H11. easy.
    easy.
    apply fresh_is_fresh; try easy.
    inv H3. easy. inv H4. easy. inv H4. easy.
    apply trans_exp_uc_well_typed; try easy. inv H3. easy. inv H4. easy.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. apply (H7 Nor) in H16; try easy. inv H16. 
      unfold times_rotate. destruct b.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H11. rewrite turn_angle_add_same. easy. easy.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy.
      apply (H7 Had) in H16. inv H16. 
      unfold compile_val,times_rotate. unfold rz_ang,z_phase.
      assert ((2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H14.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H16. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H16. Msimpl. easy. easy.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_r_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_r_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_r_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. apply (H7 Nor) in H16.
      inv H16.
      unfold times_r_rotate. destruct b. 
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H11. rewrite turn_angle_add_r_same. easy. easy.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy. easy.
      apply (H7 Had) in H16. inv H16.
      unfold compile_val,times_r_rotate. unfold rrz_ang,z_phase.
      assert ((2 * PI - 2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H14.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H16. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H16. Msimpl. easy. easy.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - Local Opaque gen_sr_gate. simpl.
    Local Transparent gen_sr_gate. unfold gen_sr_gate,sr_rotate.
    inv H6. inv H4. inv H3. inv H11.
    rewrite gen_sr_gate_eval with (asize := n) (tenv := tenv); try easy.
  - Local Opaque gen_srr_gate. simpl.
    Local Transparent gen_srr_gate. unfold gen_srr_gate,srr_rotate.
    inv H6. inv H4. inv H3. inv H11.
    rewrite gen_srr_gate_eval with (asize := n) (tenv := tenv); try easy.
  - simpl. inv H3. inv H4.
    rewrite uc_cnot_control; try easy.
    rewrite control_correct. inv H6.
    apply (H7 Had) in H16 as eq1.
    apply (H7 Had) in H17 as eq2. inv eq1. inv eq2.
    unfold hexchange.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    assert ((uc_eval (SQIR.X (find_pos vs p2))
      × vkron dim (trans_state avs rmax f))
      = (vkron dim (trans_state avs rmax (f[p2 |-> exchange (f p2)])))).
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p2 |-> exchange (f p2)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p2) (compile_val (exchange (f p2)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). easy. assumption. assumption. lia.
    rewrite H19.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p2))
                 = compile_val (exchange (f p2)) rmax).
    { unfold trans_state.
      rewrite H8 by assumption.
      unfold exchange.
      rewrite <- H6. 
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db. rewrite Mplus_comm. easy.
      }
    rewrite H20. easy.
    auto with wf_db.
    auto with wf_db.
    apply H5. assumption.
    apply H5. assumption.
    auto with wf_db.
    rewrite H19. clear H19.
    destruct (eqb b0 b3) eqn:eq1.
    apply Bool.eqb_prop in eq1.
    rewrite <- H6. unfold exchange. subst.
    rewrite H6. rewrite H3.
    rewrite eupdate_same by easy.
    rewrite eupdate_same by easy.
    rewrite <- Mmult_plus_distr_r.
    rewrite Mplus_comm.
    rewrite proj_sum.
    Msimpl. easy.
    apply H5. easy.
    apply eqb_false_iff in eq1.
    rewrite <- H6. unfold exchange.
    rewrite (vkron_split dim (find_pos vs p1)).
    assert (trans_state avs rmax f (find_pos vs p1) = Cexp ((turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val. rewrite H8; try easy. rewrite <- H3. easy.
    rewrite H19.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim false)
            (vkron (find_pos vs p1) (trans_state avs rmax f) ⊗ ∣1⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift (trans_state avs rmax f) (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣1⟩ = ket (Nat.b2n true)). autorewrite with ket_db. simpl. easy. rewrite H20.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H20. clear H20. Msimpl.
    rewrite (vkron_split dim (find_pos vs p1) (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))).
    assert (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]) (find_pos vs p1) = Cexp ((turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val. rewrite H8; try easy.
    rewrite eupdate_index_neq by iner_p. rewrite <- H3. easy.
    rewrite H20. clear H20.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim true)
            (vkron (find_pos vs p1)
                (trans_state avs rmax (f [p2 |-> hval b3 b0 r0])) ⊗ ∣0⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift
                     (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))
                     (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣0⟩ = ket (Nat.b2n false)). autorewrite with ket_db. simpl. easy. rewrite H20.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H20. clear H20. Msimpl.

    admit.
    auto with wf_db.
    apply H5. easy.
    auto with wf_db.
    apply H5. easy.
    1-2:easy.
    assert (SQIR.X (find_pos vs p2) = trans_exp vs dim (X p2)) by easy.
    rewrite H3.
    apply fresh_is_fresh; try easy. constructor. easy. constructor. easy.
    assert (SQIR.X (find_pos vs p2) = trans_exp vs dim (X p2)) by easy. rewrite H3.
    apply trans_exp_uc_well_typed; try easy. constructor. constructor. easy.
    apply H5. easy. apply H5. easy.
    apply find_pos_prop; try easy.
  - simpl. inv H3. inv H4. inv H6. inv H11.
    rewrite Mmult_assoc. rewrite (IHe1 f tenv); try easy.
    rewrite (IHe2 (exp_sem e1 f) tenv); try easy.
    apply well_typed_right_mode_exp; try easy.
Admitted.


Definition shift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then f ((i + offset) mod size) else f i.

Definition ashift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then (((f i) + offset) mod size) else f i.

Lemma shift_fun_back : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, ashift_fun f off size (shift_fun g (size - off) size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct (g ((i + (size - off)) mod size) <? size).
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((i + (size - off) + off) = i + size) by lia.
  rewrite H9.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  assert (g ((i + (size - off)) mod size) < size).
  apply H2.
  apply Nat.mod_bound_pos. lia. lia. lia.
  apply H3 in H7.
  bdestruct (g i <? size). lia.
  rewrite H4. easy.
Qed.

Lemma shift_fun_back_1 : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, shift_fun f (size-off) size (ashift_fun g off size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct ((g i + off) mod size <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((g i + off + (size - off)) = g i + size) by lia.
  rewrite H9.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite H4. easy. apply H2. easy.
  assert ((g i + off) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia.
  bdestruct (g i <? size).
  apply H3 in H7. lia.
  rewrite H4. easy.
Qed.

Definition afbrev (f:nat -> nat) (size:nat) :=
         fun (x : nat) => if (x <? size) then size - 1 - f x else f x.


Lemma fbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H4. lia.
  assert (size - 1 - i < size) by lia.
  apply H2 in H8. lia.
  bdestruct (g i <? size ).
  apply H3 in H6. lia. 
  rewrite H4. easy.
Qed.


Lemma afbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H2 in H6. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H9. rewrite H4. easy. lia. 
  bdestruct (g i <? size ).
  apply H3 in H6. lia. 
  rewrite H4. easy.
Qed.

Definition trans_lshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, 
               shift_fun g (size - 1) size,ashift_fun ag 1 size) else f i
     end.

Definition trans_rshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size,
                              shift_fun g 1 size,ashift_fun ag (size - 1) size) else f i
     end.


Definition vars_anti_same (vs:vars) :=
     forall x, (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x) /\
     (forall i, i < vsize vs x -> avmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x) /\
     (forall i, vmap vs x (avmap vs x i) = i) /\ (forall i, avmap vs x (vmap vs x i) = i).

Definition lshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x  <? vsize f x)
                                       then (x, avmap (trans_lshift f x) x (i - start f x)) else avs i).

Definition rshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rshift f x) x (i - start f x)) else avs i).

Definition trans_rev (f: vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, fbrev size g,afbrev ag size) else f i
     end.

Definition rev_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rev f x) x (i - start f x)) else avs i).

Fixpoint trans_sexp (f : vars) (dim:nat) (exp:sexp) (avs: nat -> posi) :
  (base_ucom dim * vars  * (nat -> posi)) :=
  match exp with Lshift x => (SQIR.ID (find_pos f (x,0)), trans_lshift f x, 
                              lshift_avs dim f avs x)

              | Rshift x => (SQIR.ID (find_pos f (x,0)),trans_rshift f x, rshift_avs dim f avs x)

              | Rev x => (SQIR.ID (find_pos f (x,0)),trans_rev f x,rev_avs dim f avs x)
              | Exp e => (trans_exp f dim e, f,avs)
              | e1 ;; e2 => match trans_sexp f dim e1 avs with (e1',f',avs') =>
                               match trans_sexp f' dim e2 avs' with (e2',f'',avs'')
                                          => (SQIR.useq e1' e2', f'',avs'')  end end
  end.


Definition avs_prop (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i < dim -> (start vs (fst (avs i)) <= i /\ i - start vs (fst (avs i))  < vsize vs (fst (avs i))
              /\ avmap vs (fst (avs i)) (i - start vs (fst (avs i))) = snd (avs i)).
(*
Definition avs_prop_gt (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i >= dim -> i - start vs (fst (avs i))  >= vsize vs (fst (avs i))
     /\ avs (find_pos vs n) = n.
*)
(* This defines when avs i and avs j will be the same. *)
Lemma var_not_over_lap : forall (p1 p2:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p2 < vsize vs (fst p2))
       ->  fst p1 <> fst p2 ->
       start vs (fst p1) > find_pos vs p2 \/ find_pos vs p2 - start vs (fst p1) >= vsize vs (fst p1).
Proof.
  intros. unfold vars_sparse in H0. 
  bdestruct (start vs (fst p1) <=? find_pos vs p2).
  right.
  specialize (H0 (fst p1) (fst p2) H3).
  unfold find_pos in *. destruct p2. destruct p1. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs v0 <? vsize vs v0).
  unfold vars_anti_same in H1.
  destruct (H1 v). apply H6 in H2.
  specialize (H0 (start vs v + vmap vs v n - start vs v0) (vmap vs v n) H5 H2).
  assert (start vs v0 + (start vs v + vmap vs v n - start vs v0) = start vs v + vmap vs v n) by lia.
  rewrite H8 in H0. lia. assumption.
  left. assumption.
Qed.

Lemma var_not_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       ->  fst p <> x ->
       start vs x > find_pos vs p \/ find_pos vs p - start vs x >= vsize vs x.
Proof.
  intros. unfold vars_sparse in H0. 
  bdestruct (start vs x <=? find_pos vs p).
  right.
  specialize (H0 (fst p) x H3).
  unfold find_pos in *. destruct p. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs x <? vsize vs x).
  unfold vars_anti_same in H1.
  destruct (H1 v). apply H6 in H2.
  specialize (H0 (vmap vs v n) (start vs v + vmap vs v n - start vs x) H2 H5).
  assert (start vs x + (start vs v + vmap vs v n - start vs x) = start vs v + vmap vs v n) by lia.
  rewrite H8 in H0. lia. assumption.
  left. assumption.
Qed.

Lemma var_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       -> start vs x <= find_pos vs p  -> find_pos vs p - start vs x < vsize vs x
          -> fst p = x.
Proof.
  intros.
  bdestruct (fst p =? x). easy.
  specialize (var_not_over_lap_1 x p vs H0 H1 H2 H5) as eq1.
  destruct eq1. lia. lia.
Qed.


Lemma var_over_lap_exists : forall (x:var) (n:nat) (vs:vars), 
       vars_anti_same vs -> start vs x <= n -> n - start vs x < vsize vs x
       -> exists p, find_pos vs (x,p) = n.
Proof.
  intros. unfold find_pos.
  unfold vars_anti_same in H0. specialize (H0 x).
  destruct H0 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  exists (avmap vs x (n - start vs x)).
  rewrite X5. lia.
Qed.

Lemma vs_avs_bij_l : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs -> vars_sparse vs ->
           exp_com_WF vs dim -> (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i).
Proof.
  intros. 
  bdestruct (avs (find_pos vs i) ==? i). easy.
  unfold avs_prop in H0.
  specialize (H0 (find_pos vs i)).
  assert (find_pos vs i < dim ).
  apply H3. easy.
  specialize (H0 H6).
  bdestruct (avs (find_pos vs i) ==? i). easy.
  destruct (avs (find_pos vs i)) eqn:eq1. destruct i eqn:eq2.
  bdestruct (v =? v0). subst.
  assert (n <> n0). intros R. subst. contradiction.
  destruct H0 as [V1 [ V2 V3]]. simpl in V3.
  assert ((start vs v0 + vmap vs v0 n0 - start vs v0) = vmap vs v0 n0) by lia. rewrite H0 in V3.
  unfold vars_anti_same in H1.
  destruct (H1 v0) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite X6 in V3. subst. lia.
  specialize (var_not_over_lap (avs (find_pos vs (v0, n0))) (v0, n0) vs H2 H1 H4) as eq3.
  rewrite eq1 in eq3. simpl in eq3.
  apply eq3 in H8.
  destruct H8. destruct H0.
  unfold find_pos in H0. simpl in H0. lia.
  destruct H0 as [V1 [V2 V3]].
  unfold find_pos in V2. simpl in V2. lia.
Qed.

Lemma vs_avs_bij_r : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
           (forall i, i < dim -> find_pos vs (avs i) = i).
Proof.
  intros. 
  bdestruct (find_pos vs (avs i) =? i). easy.
  unfold avs_prop in H0.
  specialize (H0 i H2).
  unfold find_pos in H3.
  destruct (avs i) eqn:eq1. simpl in H0.
  destruct H0 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (vmap vs v (avmap vs v (i - start vs v)) = vmap vs v n).
  rewrite V3. easy.
  rewrite X5 in H0.
  rewrite <- H0 in H3. lia. 
Qed.


Lemma vs_avs_size : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
             (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))).
Proof.
  intros. 
  unfold avs_prop in H0.
  specialize (H0 i H2).
  destruct H0 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 (fst (avs i))) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  apply X3. easy.
Qed.


Inductive sexp_WF : vars -> nat -> sexp -> Prop :=
      | lshift_wf : forall vs rs x, 0 < vsize vs x -> sexp_WF vs rs (Lshift x)
      | rshift_wf : forall vs rs x, 0 < vsize vs x -> sexp_WF vs rs (Rshift x)
      | rev_wf : forall vs rs x, 0 < vsize vs x -> sexp_WF vs rs (Rev x)
      | exp_wf : forall vs rs e, exp_WF vs e -> exp_rmax rs e -> sexp_WF vs rs (Exp e)
      | sseq_wf : forall vs rs e1 e2, sexp_WF vs rs e1 -> sexp_WF vs rs e2 -> sexp_WF vs rs (SSeq e1 e2).




Lemma lshift_avs_lshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (lshift_avs dim vs avs x) rmax (lshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold lshift_avs,trans_lshift. 
  destruct (vs x) eqn:eq1.
  destruct p. destruct p.
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold lshift.
  unfold start,vsize. rewrite eq1. simpl.
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  destruct (avs x0) eqn:eq2. simpl in H10. subst.
  unfold ashift_fun.
  bdestruct (x0 - n1 <? n2).
  unfold avs_prop in H2.
  specialize (H2 x0 H6). rewrite eq2 in H2. simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  unfold avmap,start in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3.
  bdestruct (n3 =? n2 -1 ). rewrite H2.
  assert ((n2 - 1 + 1) = n2) by lia.
  rewrite H11.
  rewrite Nat.mod_same by lia.
  rewrite lshift'_0 by lia. easy.
  unfold start,vsize in V2. rewrite eq1 in V2. simpl in V2. 
  specialize (X3 (x0 - n1)).
  unfold vsize,avmap in X3. rewrite eq1 in X3. simpl in X3.
  apply X3 in V2. rewrite V3 in V2.
  rewrite Nat.mod_small by lia.
  assert (n3 + 1 = S n3) by lia. rewrite H11.
  rewrite lshift'_le by lia. easy.
  unfold start,vsize in H8. rewrite eq1 in H8. simpl in H8. lia. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H9 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  simpl.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  apply H4 in H6.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H6. lia.
  simpl.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
Qed.

Lemma rshift_avs_rshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (rshift_avs dim vs avs x) rmax (rshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rshift_avs,trans_rshift. 
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold ashift_fun,vsize. rewrite eq1. simpl.
  unfold vsize in H8. rewrite eq1 in H8. simpl in H8.
  specialize (H2 x0 H6) as eq2.
  bdestruct (x0 - start vs x <? size).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. unfold vsize. rewrite eq1. simpl. lia.
  unfold rshift.
  destruct (avs x0) eqn:eq3. simpl in H11. subst. simpl in *.
  destruct eq2 as [V1 [V2 V3]].
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. 
  destruct n eqn:eq4. rewrite plus_0_l.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_0 by lia. easy.
  assert ( (S n0 + (size - 1)) = n0 + size) by lia. rewrite H11.
  rewrite Nat.add_mod by lia.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  rewrite V3 in V2.
  rewrite (Nat.mod_small n0) by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_le by lia. easy. lia. lia.
  simpl.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  bdestruct (fst (avs x0) =? x).
  rewrite H9 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by lia. easy.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
  apply H4 in H6.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H6. lia.
  simpl.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
Qed.

Lemma rev_avs_rev_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> trans_state avs rmax f
                   = trans_state (rev_avs dim vs avs x) rmax (reverse f x (vsize vs x)).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rev_avs,reverse,trans_rev,afbrev. 
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  unfold avmap. bdestruct (x =? x). simpl.
  bdestruct ( x0 - start vs x <? size).
  bdestruct (size - 1 - ag (x0 - start vs x) <? vsize vs x).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia. 
  unfold avs_prop in H2. specialize (H2 x0 H6).
  rewrite H12 in H2. simpl in H2. 
  destruct H2 as [V1 [V2 V3]].
  unfold vsize. rewrite eq1. simpl.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  assert (size - 1 - (size - 1 -
      ag (x0 - start vs x)) = ag (x0 - start vs x)) by lia.
  rewrite H2.
  destruct (avs x0). simpl in H12. subst.
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. easy. unfold vsize in H11. rewrite eq1 in H11. simpl in H11. lia.
  unfold vsize in H8. rewrite eq1 in H8. simpl in H8. lia. lia.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H2 x0 H6). rewrite H9 in H2. 
  destruct H2 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H2 x0 H6). rewrite H8 in H2. 
  destruct H2 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  apply H4 in H6.
  bdestruct ((fst (avs x0) =? x)).
  rewrite H7 in H6. lia.
  simpl. easy.
Qed.

Lemma vsize_vs_same: forall e dim vs vs' avs p,
         vs' = (snd (fst (trans_sexp vs dim e avs))) -> vsize vs' p = vsize vs p.
Proof.
 induction e; intros;subst; try easy.
 simpl.
 unfold trans_lshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_sexp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma size_env_vs_same : forall vs vs' e dim avs,
         vs' = (snd (fst (trans_sexp vs dim e avs))) -> size_env vs' = size_env vs.
Proof.
 intros. unfold size_env.
  apply functional_extensionality.
  intros.
  erewrite vsize_vs_same. reflexivity. apply H0.
Qed.

Lemma start_vs_same: forall e dim vs vs' avs p, vs' = (snd (fst (trans_sexp vs dim e avs))) -> start vs' p = start vs p.
Proof.
 induction e; intros;subst; try easy.
 simpl.
 unfold trans_lshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_sexp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma vars_start_diff_vs_same : forall vs vs' e dim avs, vs' = (snd (fst (trans_sexp vs dim e avs)))
                    -> vars_start_diff vs -> vars_start_diff vs'.
Proof.
  intros.
  unfold vars_start_diff in *.
  intros.
  rewrite (start_vs_same e dim vs vs' avs).
  rewrite (start_vs_same e dim vs vs' avs).
  apply H1. easy. easy. easy.
Qed.



Lemma shift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> shift_fun g off size i < size). 
Proof.
  intros. unfold shift_fun.
  bdestruct (i <? size).
  apply H0. apply Nat.mod_bound_pos. 
  lia. lia. lia.
Qed.

Lemma fbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> fbrev size g i < size). 
Proof.
  intros. unfold fbrev.
  bdestruct (i <? size).
  apply H0. lia. 
  lia.
Qed.

Lemma vars_fun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_sexp vs dim e avs)))
          -> (forall i, i < vsize vs x -> vmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> vmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 (n2 - 1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (fbrev_lt n0 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in H0. subst. apply H1. easy.
  subst. simpl.
  destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_sexp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_sexp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> vmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.


Lemma ashift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> ashift_fun g off size i < size). 
Proof.
  intros. unfold ashift_fun.
  bdestruct (i <? size).
  apply Nat.mod_bound_pos. 
  lia. lia. apply H0. lia.
Qed.


Lemma afbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> afbrev g size i < size). 
Proof.
  intros. unfold afbrev.
  bdestruct (i <? size). lia. lia.
Qed.


Lemma vars_afun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_sexp vs dim e avs)))
          -> (forall i, i < vsize vs x -> avmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> avmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n (n2-1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (afbrev_lt n n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  subst. simpl. apply H1. easy.
  subst. simpl.
  destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_sexp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_sexp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> avmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma shift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> g (f x) = x) ->
           (forall x, x < size -> ashift_fun g (size - off) size (shift_fun f off size x) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct (f ((x + size) mod size) <? size).
  assert ((size - size) = 0) by lia. rewrite H7.
  rewrite plus_0_r.
  rewrite H3.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small) by lia.
  easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (off =? 0). subst.
  assert (size - 0 = size) by lia. rewrite H7.
  rewrite plus_0_r.
  bdestruct (f (x mod size) <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite H3.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H3. 
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (f ((x + off) mod size) <? size).
  rewrite H3.
  assert (size - off < size) by lia.
  rewrite <- (Nat.mod_small (size - off) size) by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((x + off + (size - off)) = x + size) by lia.
  rewrite H10.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  assert (f ((x + off) mod size) < size).
  apply H1. 
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma ashift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
           (forall x, x < size -> (shift_fun f off size (ashift_fun g (size - off) size x)) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct ((g x + (size - size)) mod size <? size).
  assert ((size - size) = 0) by lia. rewrite H7.
  rewrite plus_0_r.
  rewrite (Nat.mod_small (g x)).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H3. easy. easy.
  apply H2. easy. apply H2. easy.
  assert ((g x + (size - size)) mod size < size). 
  apply Nat.mod_bound_pos. lia. lia.
  lia.
  bdestruct ((g x + (size - off)) mod size <? size).
  rewrite <- (Nat.mod_small off size) by lia.
  rewrite <- Nat.add_mod by lia.
  rewrite (Nat.mod_small off) by lia.
  assert ((g x + (size - off) + off) = g x + size) by lia.
  rewrite H8.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H3. easy. easy. apply H2. lia.
  assert ((g x + (size - off)) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma afbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H2. lia. lia.
  assert (size - 1 - i < size) by lia.
  apply H1 in H6. lia. lia.
Qed.

Lemma fbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H1. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H7. rewrite H2. lia. lia. lia. lia.
Qed.

Definition exists_fun_bij (vs:vars) (x:var) := exists g : nat -> nat,
  (forall y : nat, y < vsize vs x -> g y < vsize vs x) /\
  (forall x0 : nat,
   x0 < vsize vs x -> g (vmap vs x x0) = x0) /\
  (forall y : nat, y < vsize vs x -> vmap vs x (g y) = y).

Lemma trans_same_bij:  forall e dim vs vs' avs x, 
    (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) ->
      vs' = (snd (fst (trans_sexp vs dim e avs)))
       -> 0 < vsize vs x ->
       exists_fun_bij vs x -> exists_fun_bij vs' x.
Proof.
  induction e; intros; subst.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Lshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_lshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g 1 n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g 1 n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert (n2 - 1 <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  specialize (shift_fun_twice n0 g (n2 - 1) n2 H3 H0 Ht Hf x1) as eq2.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (n2 - (n2 -1) = 1) by lia. rewrite H4 in eq2.
  rewrite eq2. easy. assumption. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert ((n2 - 1) <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g (n2 - 1) n2 H3 H0 Ht Hb) as eq2.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. 
  assert ((n2 - (n2 - 1)) = 1) by lia. rewrite H4 in eq2.
  rewrite eq2. easy. easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g (n2 - 1) n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g (n2 - 1) n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (1 <= n2) by lia.
  specialize (shift_fun_twice n0 g 1 n2 H3 H0 Ht Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (1 <= n2) by lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g 1 n2 H3 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rev x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rev.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (afbrev g n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check afbrev_lt.
  specialize (afbrev_lt g n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  Check afbrev_back_lt.
  specialize (afbrev_back_lt g n0 n2 Ht H0 Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  Check fbrev_back_lt.
  specialize (fbrev_back_lt n0 g n2 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- simpl in *. easy.
- simpl in *.
  destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *.
  assert (v = (snd (fst (trans_sexp vs dim e1 avs)))).
  rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1 H2 H3).
  assert ((forall i : nat, i < vsize v x -> vmap v x i < vsize v x) ).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs).
  rewrite (vsize_vs_same e1 dim vs v avs) in H4.
  apply (vars_fun_lt e1 dim) with (avs := avs). easy. apply H0. easy. easy. easy.
  assert (v0 = snd (fst (trans_sexp v dim e2 p0))).
  rewrite eq2. easy.
  assert (0 < vsize v x).
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). easy. rewrite eq1. easy.
  specialize (IHe2 dim v v0 p0 x H4 H5 H6 IHe1). easy.
Qed.

Lemma vars_finite_bij_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_sexp vs dim e avs)))
                    -> vars_finite_bij vs -> vars_finite_bij vs'.
Proof.
  intros. unfold vars_finite_bij in *.
  intros.
  unfold weak_finite_bijection in *.
  split.
  intros. specialize (H1 x).
  destruct H1.
  rewrite (vsize_vs_same e dim vs vs' avs).
  apply (vars_fun_lt e dim vs vs' avs). assumption. easy.
  rewrite <- (vsize_vs_same e dim vs vs' avs). easy. easy. easy.
  specialize (H1 x). destruct H1.
  bdestruct (vsize vs x =? 0).
  assert (vsize vs' x = 0).
  rewrite (vsize_vs_same e dim vs vs' avs). easy. easy.
  destruct H2. exists x0.
  split. intros. lia.
  split. intros. lia.
  intros. lia.
  assert (0 < vsize vs x) by lia.
  specialize (trans_same_bij e dim vs vs' avs x H1 H0 H4 H2) as eq1. easy.
Qed.

Lemma vars_sparse_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_sexp vs dim e avs)))
                    -> vars_sparse vs -> vars_sparse vs'.
Proof.
  intros.
  unfold vars_sparse in *.
  intros.
  repeat rewrite (start_vs_same e dim vs vs' avs) by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H3 by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H4 by easy.
  apply H1; easy.
Qed.

Lemma vars_fun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_sexp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> vmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold fbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  subst. simpl. apply H1.  easy.
  subst. simpl.
  destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_sexp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_sexp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> vmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_afun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_sexp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> avmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold afbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  subst. simpl. apply H1. easy.
  subst. simpl.
  destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_sexp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_sexp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> avmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_vs_anti_bij :
    forall e dim vs vs' avs x, vs' = (snd (fst (trans_sexp vs dim e avs))) ->
     (forall i : nat, i < vsize vs x -> vmap vs x i < vsize vs x) ->
     (forall i : nat, i >= vsize vs x -> vmap vs x i >= vsize vs x) ->
    (forall i : nat, i < vsize vs x -> avmap vs x i < vsize vs x) ->
       (forall i : nat, i >= vsize vs x -> avmap vs x i >= vsize vs x) ->
      (forall i : nat, vmap vs x (avmap vs x i) = i) -> 
       (forall i : nat, avmap vs x (vmap vs x i) = i) ->
      (forall i : nat, vmap vs' x (avmap vs' x i) = i) /\ (forall i : nat, avmap vs' x (vmap vs' x i) = i).
Proof.
 induction e; intros.
-
 subst. simpl. split. intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H4. rewrite eq1 in H4. simpl in H4.
 apply H4 in H7. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
 intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H2. rewrite eq1 in H2. simpl in H2.
 apply H2 in H7. lia.
 unfold vmap,avmap in H6. rewrite eq1 in H6. simpl in H6.
 rewrite H6. easy.
 unfold vmap,avmap in H6.
 rewrite H6. easy.
- subst. simpl.
 split. intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (shift_fun n0 1 n2 (ashift_fun n (n2 - 1) n2 i) 
           = shift_fun n0 (n2 - (n2 - 1)) n2 (ashift_fun n (n2 - 1) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H7. easy.
 rewrite H7.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H4. rewrite eq1 in H4. simpl in H4.
 apply H4 in H7. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
 intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (ashift_fun n (n2 - 1) n2 (shift_fun n0 1 n2 i) 
           = ashift_fun n (n2 - 1) n2 (shift_fun n0 (n2 - (n2 -1)) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H7. easy.
 rewrite H7.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H2. rewrite eq1 in H2. simpl in H2.
 apply H2 in H7. lia.
 unfold vmap,avmap in H6. rewrite eq1 in H6. simpl in H6.
 rewrite H6. easy.
 unfold vmap,avmap in H6.
 rewrite H6. easy.
-
 subst. simpl. split. intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite afbrev_back ; try easy.
 unfold vmap,avmap in H5. rewrite H5. easy.
 intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite fbrev_back ; try easy.
 unfold vmap,avmap in H6. rewrite H6. easy.
- split. subst. simpl. easy. subst. simpl. easy.
-
 subst. simpl.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p. simpl.
 specialize (IHe1 dim vs v avs x).
 rewrite eq1 in IHe1.
 assert (v = snd (fst (b, v, p0))) by easy.
 specialize (IHe1 H0 H1 H2 H3 H4 H5 H6).
 specialize (IHe2 dim v v0 p0 x).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H7. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy. easy. easy.
Qed.

Lemma vars_anti_vs_same: forall e dim vs vs' avs, vs' = (snd (fst (trans_sexp vs dim e avs)))
                    -> vars_anti_same vs -> vars_anti_same vs'.
Proof.
  intros.
  unfold vars_anti_same in *.
  intro x. specialize (H1 x).
  destruct H1.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_lt e dim vs vs' avs). easy. assumption.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_ge e dim vs) with (avs := avs) ; easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_lt e dim vs vs' avs). easy. easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_ge e dim vs vs' avs) ; easy.
  destruct H2 as [H2 [H3 [H4 [H5 H6]]]].
  specialize (vars_vs_anti_bij e dim vs vs' avs x H0 H1 H2 H3 H4 H5 H6) as eq1.
  destruct eq1. easy.
Qed.


Lemma wf_vs_same: forall e1 e2 avs dim vs vs', exp_WF vs e1 -> 
                vs' = (snd (fst (trans_sexp vs dim e2 avs))) -> exp_WF vs' e1.
Proof.
  intros.
  induction H0. constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  apply IHexp_WF. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  apply IHexp_WF1. easy.
  apply IHexp_WF2. easy.
Qed.

Lemma swf_vs_same: forall e1 e2 rmax avs dim vs vs', sexp_WF vs rmax e1 -> 
                vs' = (snd (fst (trans_sexp vs dim e2 avs))) -> sexp_WF vs' rmax e1.
Proof.
  intros.
  induction H0. constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor. eapply wf_vs_same. apply H0. apply H1. easy.
  constructor.
  apply IHsexp_WF1. easy.
  apply IHsexp_WF2. easy.
Qed.


Lemma exists_same_vs_var : forall e dim x n avs vs vs', vs' = (snd (fst (trans_sexp vs dim e avs)))->
                  n < vsize vs x -> 
                 (exists n', n' < vsize vs x /\ find_pos vs' (x,n) = find_pos vs (x,n')).
Proof.
 induction e; intros.
- 
 specialize (start_vs_same (Lshift x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_lshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + (n3 - 1)) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia. lia.
 exists n. 
 rewrite H0. simpl.
 unfold trans_lshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
-
 specialize (start_vs_same (Rshift x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + 1) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia.
 exists n. 
 rewrite eq3. simpl. easy.
 exists n.
 split. easy.
 rewrite H0. simpl.
 unfold trans_rshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- 
 specialize (start_vs_same (Rev x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rev in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold fbrev.
 bdestruct (n <? n3).
 exists ((n3 - 1 - n)).
 split. lia. easy. lia. lia. 
 exists n.
 split. easy.
 rewrite H0. simpl.
 unfold trans_rev,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- rewrite H0. simpl. exists n. easy.
- 
 simpl in H0.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_sexp v dim e2 p0 ) eqn:eq2. destruct p.
 simpl in H0. subst.
 specialize (IHe2 dim x n p0 v v0).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H0. destruct H0. destruct H0.
 specialize (IHe1 dim x x0 avs vs v).
 rewrite eq1 in IHe1. assert (v = snd (fst (b, v, p0))) by easy.
 apply IHe1 in H3. destruct H3.
 destruct H3.
 exists x1.
 split. assumption. 
 rewrite H2. easy.
 erewrite <- vsize_vs_same.
 apply H0. rewrite eq1. easy.
 erewrite vsize_vs_same.
 apply H1.
 rewrite eq1. easy.
Qed.

Lemma exp_com_WF_vs_same : forall e dim avs vs vs', vs' = (snd (fst (trans_sexp vs dim e avs)))
          -> exp_com_WF vs dim -> exp_com_WF vs' dim.
Proof.
 induction e; intros.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Lshift x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Rshift x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Rev x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 rewrite H0. simpl. easy.
 simpl in H0.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p.
 simpl in H0.
 specialize (IHe1 dim avs vs v).
 specialize (IHe2 dim p0 v v0).
 subst.
 apply IHe2. rewrite eq2. easy.
 apply IHe1. rewrite eq1. easy.
 assumption. 
Qed.

Lemma exp_com_gt_vs_same :
    forall e dim vs vs' avs avs', vs' = (snd (fst (trans_sexp vs dim e avs)))
      -> avs' = snd (trans_sexp vs dim e avs)
          -> exp_com_gt vs avs dim -> exp_com_gt vs' avs' dim.
Proof.
 induction e; intros.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Lshift x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold lshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rshift x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold rshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rev x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold rev_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 rewrite H1. rewrite H0. simpl. easy.
 rewrite H0. rewrite H1. simpl in *.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p.
 simpl in *.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 apply IHe1 in H2.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy. rewrite eq2. easy.
 1-3:easy.
Qed.

Lemma avs_prop_vs_same : forall e dim vs vs' avs avs', vs' = (snd (fst (trans_sexp vs dim e avs)))
      -> avs' = snd (trans_sexp vs dim e avs) -> vars_anti_same vs -> vars_sparse vs
          -> avs_prop vs avs dim -> avs_prop vs' avs' dim.
Proof.
 induction e; intros.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_lshift,lshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_lshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rshift,rshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_rshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rev,rev_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_rev.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
- subst. simpl. easy.
-
 subst. simpl.
 destruct (trans_sexp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_sexp v dim e2 p0) eqn:eq2. destruct p.
 simpl.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 assert (v = v) by easy. assert (p0 = p0) by easy.
 specialize (IHe1 H0 H1 H2 H3 H4).
 apply (vars_anti_vs_same e1 dim vs v avs) in H2.
 apply (vars_sparse_vs_same e1 dim vs v avs) in H3.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy.
 rewrite eq2. easy. easy. easy. easy. rewrite eq1. easy.
 rewrite eq1. easy.
Qed.

Lemma trans_sexp_sem :
  forall dim (e:sexp) f env rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    sexp_WF vs rmax e ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_sexp env e ->
    right_mode_env (size_env vs) env f ->
    avs_prop vs avs dim ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_sexp vs dim e avs)))) × (vkron dim (trans_state avs rmax f)) 
         = vkron dim (trans_state (snd (trans_sexp vs dim e avs)) rmax (sexp_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros; simpl.
  - rewrite denote_ID_1. Msimpl. unfold size_env. 
    rewrite <- lshift_avs_lshift_same; try easy.
    inv H4. easy. unfold exp_com_WF,find_pos in H5.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H4. easy.
  - rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rshift_avs_rshift_same; try easy.
    inv H4. easy. unfold exp_com_WF,find_pos in H5.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H4. easy.
  - rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rev_avs_rev_same; try easy.
    inv H4. easy. unfold exp_com_WF,find_pos in H5.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H4. easy.
  - erewrite trans_exp_sem. easy. 1-3:assumption. inv H7.  easy. inv H4. easy. easy.
    inv H7. apply H14. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    apply vs_avs_size with (dim := dim); try easy.
    inv H4. easy. easy.
  - simpl. inv H4. inv H7.
    destruct (trans_sexp vs dim e1 avs) as [p avs'] eqn:eq1.
    destruct p as [e1' vs']. 
    destruct (trans_sexp vs' dim e2 avs') as [p avs''] eqn:eq2.
    destruct p as [e2' vs'']. simpl.
    specialize (IHe1 f env0 rmax vs avs H0 H1 H2 H3 H15 H5 H6 H13 H8 H9 H10).
    rewrite eq1 in IHe1. simpl in IHe1.
    rewrite Mmult_assoc. rewrite IHe1.
    specialize (IHe2 (sexp_sem (size_env vs) e1 f) env0 rmax vs' avs').
    rewrite eq2 in IHe2. simpl in IHe2.
    rewrite IHe2; try assumption.
    erewrite (size_env_vs_same vs vs'). easy.
    rewrite eq1. easy.
    eapply vars_start_diff_vs_same. rewrite eq1. easy. easy.
    eapply vars_finite_bij_vs_same. rewrite eq1. easy. assumption.
    eapply vars_sparse_vs_same. rewrite eq1. easy. easy.
    eapply vars_anti_vs_same. rewrite eq1. easy. easy.
    eapply swf_vs_same. apply H16. rewrite eq1. easy.
    eapply exp_com_WF_vs_same. rewrite eq1. easy. easy.
    eapply exp_com_gt_vs_same. rewrite eq1. easy. rewrite eq1. easy. easy.
    rewrite (size_env_vs_same vs vs' e1 dim avs).
    apply well_typed_right_mode_sexp; try easy. rewrite eq1. easy.
    eapply avs_prop_vs_same. rewrite eq1. easy. rewrite eq1. easy.
    easy. easy. easy.
Qed.

(* generalized Controlled rotation cascade on n qubits. *)

(* SQIR.Rz (rz_ang q) (find_pos f p) *)

Fixpoint controlled_rotations_gen (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (controlled_rotations_gen f dim x m i)
                 (control (find_pos f (x,m+i)) (SQIR.Rz (rz_ang n) (find_pos f (x,i))))
  end.

(* generalized Quantum Fourier transform on n qubits. 
   We use the definition below (with cast and map_qubits) for proof convenience.
   For a more standard functional definition of QFT see Quipper:
   https://www.mathstat.dal.ca/~selinger/quipper/doc/src/Quipper/Libraries/QFT.html *)

Fixpoint QFT_gen (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (find_pos f (x,0))
  | S m => SQIR.useq (SQIR.H (find_pos f (x,m))) (SQIR.useq (controlled_rotations_gen f dim x (size-m) m)
            (QFT_gen f dim x m size))
  end.

Definition trans_qft (f:vars) (dim:nat) (x:var) : base_ucom dim :=
          QFT_gen f dim x (vsize f x) (vsize f x).

Fixpoint controlled_rotations_gen_r (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (control (find_pos f (x,m+i)) (SQIR.Rz (rrz_ang n) (find_pos f (x,i))))
                  (controlled_rotations_gen_r f dim x m i)
  end.

Fixpoint QFT_gen_r (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (find_pos f (x,0))
  | S m => SQIR.useq (controlled_rotations_gen_r f dim x (size-m) m)
            (SQIR.useq (SQIR.H (find_pos f (x,m))) (QFT_gen_r f dim x m size))
  end.

Definition trans_rqft (f:vars) (dim:nat) (x:var) : base_ucom dim :=
          QFT_gen_r f dim x (vsize f x) (vsize f x).

Fixpoint nH (f : vars) (dim:nat) (x:var) (n:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (SQIR.H (find_pos f (x,m))) (nH f dim x m)
     end.

Definition trans_h (f : vars) (dim:nat) (x:var) : base_ucom dim := nH f dim x (vsize f x).
        

(*
Inductive pexp := SExp (s:sexp) | QFT (x:var) | RQFT (x:var)
               | H (x:var) | FSeq (p1:pexp) (p2:pexp).
(f : vars) (dim:nat) (exp:sexp) (avs: nat -> posi) :
*)

Fixpoint trans_pexp (vs:vars) (dim:nat) (exp:pexp) (avs: nat -> posi) :=
     match exp with SExp s => (trans_sexp vs dim s avs)
                 | QFT x => (trans_qft vs dim x, vs, avs)
                 | RQFT x => (trans_rqft vs dim x, vs, avs)
                 | H x => (trans_h vs dim x, vs, avs)
                 | FSeq e1 e2 =>  
                         match trans_pexp vs dim e1 avs with (e1',vs',avs') => 
                             match trans_pexp vs' dim e2 avs' with (e2',vs'',avs'') => 
                                        (SQIR.useq e1' e2', vs'', avs'')
                             end
                            end
     end.


Inductive pexp_WF : vars -> nat -> pexp -> Prop :=
      | qft_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (QFT x)
      | rqft_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (RQFT x)
      | h_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (H x)
      | sexp_wf : forall vs rs e, sexp_WF vs rs e -> pexp_WF vs rs (SExp e)
      | fseq_wf : forall vs rs e1 e2, pexp_WF vs rs e1 -> pexp_WF vs rs e2 -> pexp_WF vs rs (FSeq e1 e2).

Lemma trans_pexp_sem :
  forall dim (e:pexp) f env env' rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    pexp_WF vs rmax e ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_pexp (size_env vs) env e env' ->
    right_mode_env (size_env vs) env f ->
    avs_prop vs avs dim ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_pexp vs dim e avs)))) × (vkron dim (trans_state avs rmax f)) 
         = vkron dim (trans_state (snd (trans_pexp vs dim e avs)) rmax (prog_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros; simpl.
Admitted.

(* Definition of the adder and the modmult in the language. *)
Definition CNOT (x y : posi) := CU x (X y).
Definition SWAP (x y : posi) := if (x ==? y) then (SKIP x) else (CNOT x y; CNOT y x; CNOT x y).
Definition CCX (x y z : posi) := CU x (CNOT y z).

Lemma cnot_fwf : forall x y, x<> y -> exp_fwf (CNOT x y).
Proof.
  intros.
  unfold CNOT. constructor.
  constructor. easy.
  constructor.
Qed.

Lemma swap_fwf : forall x y, exp_fwf (SWAP x y).
Proof.
  intros.
  unfold SWAP.
  bdestruct (x ==? y).
  constructor.
  constructor.
  constructor. apply cnot_fwf. easy.
  apply cnot_fwf. nor_sym.
  constructor. constructor. easy.
  constructor.
Qed.

Lemma ccx_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (CCX x y z).
Proof.
  intros.
  unfold CCX.
  constructor. constructor. easy.
  constructor. nor_sym.
  constructor. constructor.
  easy.
  constructor.
Qed.


(* Proofs of semantics. *)
Lemma cnot_sem : forall f x y, nor_mode f x -> nor_mode f y -> 
              exp_sem (CNOT x y) f = (f[y |-> put_cu (f y) (get_cua (f x) ⊕ get_cua (f y))]).
Proof.
 intros.
 unfold CNOT.
 assert (eq1 := H0).
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 simpl.
 destruct (get_cua (f x)).
 bt_simpl.
 unfold exchange.
 destruct (f y) eqn:eq2.
 simpl. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 destruct (f y) eqn:eq2.
 simpl. destruct b.
 rewrite <- eq2. rewrite eupdate_same. easy.
 easy.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 simpl.
 assert (get_cua (f x) = false). unfold get_cua. rewrite H0. easy.
 rewrite H2.
 destruct (f y) eqn:eq2.
 simpl. destruct b.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
Qed.

Lemma cnot_nor : forall f x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> exp_sem (CNOT x y) f = (f[y |-> v]).
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma cnot_nor_1 : forall f f' x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> f[y|-> v] = f'
           -> exp_sem (CNOT x y) f = f'.
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma ccx_sem : forall f x y z, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                    exp_sem (CCX x y z) f = (f[z |-> put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x)))]).
Proof.
 intros. 
 assert (eq1 := H0).
 unfold CCX. apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 simpl. rewrite H0. simpl.
 destruct (f z) eqn:eq2.
 unfold exchange.
 simpl.
 destruct (get_cua (f y)) eqn:eq3.
 simpl. easy.
 simpl. rewrite eupdate_same. easy. rewrite eq2.
 bt_simpl. easy.
 unfold nor_mode in H2.
 rewrite eq2 in H2. inv H2.
 unfold nor_mode in H2.
 rewrite eq2 in H2. inv H2.
 simpl.
 rewrite H0. simpl. bt_simpl.
 rewrite put_get_cu. rewrite eupdate_same. easy. easy. assumption.
Qed.

Lemma ccx_nor : forall f f' x y z v, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                       put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x))) = v ->
                       f = f' ->
                    exp_sem (CCX x y z) f = (f'[z |-> v]).
Proof.
 intros. subst. apply ccx_sem. 1 - 6: assumption. 
Qed.

Local Opaque CNOT. Local Opaque CCX.

(* modmult adder based on QFT. *)
Fixpoint rz_adder (x:var) (n:nat) (M: nat -> bool) :=
    match n with 0 => (SKIP (x,0))
               | S m => (if M m then SR m x else SKIP (x,m)) ; rz_adder x m M
    end.

Check phi_modes.

Check cut_n.

Lemma rz_adder_sem : forall n f x M, phi_modes f x n ->
                   get_r_qft (exp_sem (rz_adder x n M) f) x
                    = cut_n (fbrev n (sumfb false (fbrev n (get_r_qft f x)) (fbrev n M))) n.
Proof.
  intros.
Admitted.

Definition one_cu_adder (x:var) (n:nat) (c3:posi) (M:nat -> bool) := CU c3 (rz_adder x n M).

(* assuming the input is in qft stage. *)
Definition rz_modadder (x:var) (n:nat) (y c: posi) (a:nat -> bool) (N:nat -> bool) :=
    (SExp (Exp (one_cu_adder x n y a ; rz_adder x n N))) ;;; RQFT x ;;; (SExp (Exp (CNOT (x,n-1) c))) ;;; QFT x
          ;;; (SExp (Exp (one_cu_adder x n c N ; one_cu_adder x n y a)));;;
     RQFT x ;;; (SExp (Exp (X (x,n-1) ; CNOT (x,n-1) c; X (x,n-1))));;; QFT x;;; SExp (Exp (one_cu_adder x n y a)).

(* Mod adder. [x][0] -> [x][ax%N] having the a and N as constant. *)
Fixpoint rz_modmult' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (a:nat -> bool) (N:nat -> bool) :=
     match n with 0 => SExp (Exp (SKIP (x,0)))
               | S m => rz_modadder x size (y,m) c a N ;;; rz_modmult' y x m size c a N
     end.
Definition rz_modmult_half (y:var) (x:var) (n:nat) (c:posi) (a:nat -> bool) (N:nat -> bool) :=
                 QFT x ;;; rz_modmult' y x n n c a N ;;; RQFT x.

Definition rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (C:nat -> bool) (Cinv : nat -> bool) (N:nat -> bool) :=
                 rz_modmult_half y x n c C N ;;; inv_pexp (rz_modmult_half y x n c Cinv N).




(* modmult adder based on classical circuits. *)
Definition MAJ a b c := CNOT c b ; CNOT c a ; CCX a b c.
Definition UMA a b c := CCX a b c ; CNOT c a ; CNOT a b.

Lemma maj_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (MAJ x y z).
Proof.
  intros.
  unfold MAJ.
  constructor.
  constructor. 
  apply cnot_fwf. nor_sym.
  apply cnot_fwf. easy.
  apply ccx_fwf; easy. 
Qed.

(*
Lemma maj_well_typed : forall f tenv x y z, nor_mode f x -> nor_mode f y -> nor_mode f z
            -> right_mode_exp tenv f (MAJ x y z) -> well_typed_exp tenv (MAJ x y z).
Proof.
  intros.
  unfold MAJ in *. inv H3. inv H8.
  constructor.
  constructor. eapply cnot_well_typed. apply H2. easy. easy.
  eapply cnot_well_typed. apply H2. easy. easy.
  eapply ccx_well_typed. apply H0. easy. easy. easy.
Qed.
*)

Lemma uma_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (UMA x y z).
Proof.
  intros.
  unfold UMA.
  constructor.
  constructor. 
  apply ccx_fwf; easy. 
  apply cnot_fwf. easy.
  apply cnot_fwf. easy.
Qed.

Lemma MAJ_correct :
  forall a b c f,
    nor_mode f a -> nor_mode f b -> nor_mode f c ->
    a <> b -> b <> c -> a <> c ->
    exp_sem (MAJ c b a) f = (((f[a |-> put_cu (f a) (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])
                              [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])
                              [c |-> put_cu (f c) (get_cua (f c) ⊕ (get_cua (f a)))]).
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
Proof.
  intros ? ? ? ? HNa HNb HNc Hab' Hbc' Hac'.
  unfold MAJ.
  simpl.
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite ccx_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f a)
   ⊕ (get_cua (f a) ⊕ get_cua (f b) && get_cua (f a) ⊕ get_cua (f c)))
    = (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))).
  unfold majb. btauto.
  rewrite H1. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  rewrite eupdate_twice_neq by nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  1-3:nor_sym. 1-2:assumption.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
Qed.

Lemma UMA_correct_partial :
  forall a b c f' fa fb fc,
    nor_mode f' a -> nor_mode f' b -> nor_mode f' c ->
    a <> b -> b <> c -> a <> c ->
    get_cua (f' a) = majb fa fb fc ->
    get_cua (f' b) = (fb ⊕ fa) -> get_cua (f' c) = (fc ⊕ fa) ->
    exp_sem (UMA c b a) f' = (((f'[a |-> put_cu (f' a) fa])
                  [b |-> put_cu (f' b) (fa ⊕ fb ⊕ fc)])[c |-> put_cu (f' c) fc]).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  unfold majb. intros.
  unfold UMA.
  simpl.
  rewrite ccx_sem by (try assumption; try nor_sym).
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (x ==? c).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert (((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c)) = fc).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H9. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c))
   ⊕ get_cua (f' b)) = ((fa ⊕ fb) ⊕ fc)).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H10. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) = fa).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H11. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up_1.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
Qed.

Local Transparent CNOT. Local Transparent CCX.

(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [x][y] and produce [x][(x+y) % 2 ^ n] *)
Fixpoint MAJseq' n x y c : exp :=
  match n with
  | 0 => MAJ c (y,0) (x,0)
  | S m => MAJseq' m x y c; MAJ (x, m) (y, n) (x, n)
  end.
Definition MAJseq n x y c := MAJseq' (n - 1) x y c.

Lemma majseq'_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (MAJseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply maj_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply IHn.
  apply maj_fwf.
  1-3:iner_p.
Qed.

Lemma majseq_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (MAJseq n x y c).
Proof.
  intros. unfold MAJseq.
  apply majseq'_fwf; assumption.
Qed.

Fixpoint UMAseq' n x y c : exp :=
  match n with
  | 0 => UMA c (y,0) (x,0)
  | S m => UMA (x, m) (y,n) (x, n); UMAseq' m x y c
  end.
Definition UMAseq n x y c := UMAseq' (n - 1) x y c.

Lemma umaseq'_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (UMAseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply uma_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply uma_fwf.   1-3:iner_p.
  apply IHn.
Qed.

Lemma umaseq_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (UMAseq n x y c).
Proof.
  intros. unfold UMAseq.
  apply umaseq'_fwf; assumption.
Qed.

(*
Lemma umaseq'_well_typed : forall m n tenv f x y c, m < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c
            -> right_mode_exp tenv f (UMAseq' m x y c)  -> well_typed_exp tenv (UMAseq' m x y c).
Proof.
  intros.
  induction m; simpl.
  eapply uma_well_typed. apply H3. apply H2. lia. apply H1. lia.
  simpl in H4. easy.
  simpl in H4. inv H4.
  constructor. 
  eapply uma_well_typed. apply H1. lia. apply H2. lia. apply H1. lia. easy.
  apply IHm. lia. easy.
Qed.

Lemma umaseq_well_typed : forall n tenv f x y c, 0 < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c
            -> right_mode_exp tenv f (UMAseq n x y c)  -> well_typed_exp tenv (UMAseq n x y c).
Proof.
  intros. unfold UMAseq in *.
  apply (umaseq'_well_typed (n-1) n tenv f); try assumption. lia.
Qed.
*)

Definition adder01 n x y c: exp := MAJseq n x y c; UMAseq n x y c.

Lemma adder_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (adder01 n x y c).
Proof.
  intros. unfold adder01. constructor.
  apply majseq_fwf; assumption.
  apply umaseq_fwf; assumption.
Qed.


Lemma msm_eq1 :
  forall n i c f g,
    S i < n ->
    msma i c f g i ⊕ msma i c f g (S i) = msma (S i) c f g i.
Proof.
  intros. unfold msma. IfExpSimpl. easy.
Qed.

Lemma msm_eq2 :
  forall n i c f g,
    S i < n ->
    msmb i c f g (S i) ⊕ msma i c f g (S i) = msmb (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl. btauto.
Qed.
       

Lemma msm_eq3 :
  forall n i c f g,
    S i < n ->
    majb (msma i c f g (S i)) (msmb i c f g (S i)) (msma i c f g i) = msma (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl.
  simpl. unfold majb. easy.
Qed.

Definition var_prop (f:var -> nat) (x y c : var) (n:nat) : Prop :=
      n <= (f x) /\  n <= f y /\ f c = 1.



Lemma msmb_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msmb (S i) b f g) n = (put_cus st x
             (msmb i b f g) n)[(x,S i) |-> put_cu (st (x,S i)) (msmb i b f g (S i) ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  bdestruct (x =? v).
  subst.
  unfold put_cus. simpl.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (v =? v).
  bdestruct (S i <? n).
  assert ((msmb (S i) b f g (S i)) = (msmb i b f g (S i) ⊕ msma i b f g (S i))).
  erewrite msm_eq2. easy. apply H0.
  rewrite H3. easy. lia. lia.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? v).
  bdestruct (n0 <? n).
  unfold msmb.
  bdestruct (n0 <=? S i).
  bdestruct (n0 <=? i).
  easy. lia.
  bdestruct (n0 <=? i). lia. easy.
  easy. easy. intros R. inv R. lia.
  rewrite put_cus_neq. rewrite eupdate_index_neq.
  rewrite put_cus_neq. easy. assumption.
  intros R. inv R. lia. lia.
Qed.

Lemma msma_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msma (S i) b f g) n = ((put_cus st x
             (msma i b f g) n)[(x,S i) |-> put_cu (st (x,S i))
                          (majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i))])
                      [(x,i) |-> put_cu (st (x,i)) (msma i b f g i ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  unfold put_cus. simpl.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? i). subst.
  rewrite eupdate_index_eq.
  bdestruct (i <? n).
  unfold put_cu.
  destruct (st (x, i)).
  assert ((msma (S i) b f g i)  = (msma i b f g i ⊕ msma i b f g (S i))).
  erewrite <- msm_eq1. easy. apply H0.
  rewrite H2. easy. easy. easy.
  lia.
  rewrite eupdate_index_neq.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (S i <? n).
  unfold put_cu.
  destruct (st (x, S i)).
  assert ((msma (S i) b f g (S i))  = majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i)).
  erewrite <- msm_eq3. easy. apply H2.
  rewrite H3. easy. easy. easy. lia.
  rewrite eupdate_index_neq.
  simpl.
  bdestruct (n0 <? n).
  bdestruct (x =? x).
  assert ((msma (S i) b f g n0) = (msma i b f g n0)).
  unfold msma.
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i).
  easy. lia.
  bdestruct (n0 =? S i).
  lia.
  bdestruct (n0 <? i). lia.
  bdestruct (n0 =? i). lia.
  easy.
  rewrite H5. easy.
  lia.
  bdestruct (x =? x). easy. easy.
  intros R. inv R. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? x). lia.
  easy.
  apply iner_neq. lia.
  apply iner_neq. lia.
Qed.

Lemma msma_0 : forall f x b g n, 0 < n -> nor_modes f x n -> put_cus f x (msma 0 b (get_cus n f x) g) n =
                     f[(x,0) |-> put_cu (f (x,0)) (carry b (S 0) (get_cus n f x) g)].
Proof.
  intros.
  unfold put_cus, msma.
  apply functional_extensionality.
  intros.
  destruct x0. simpl in *.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 =? 0).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H1. lia. lia.
  intros R. inv R. contradiction.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Lemma msmb_0 : forall S f b y n, 0 < n -> nor_modes S y n -> put_cus S y (msmb 0 b f (get_cus n S y)) n =
                     S[(y,0) |-> put_cu (S (y,0)) (f 0 ⊕ (get_cua (S (y,0))))].
Proof.
  intros.
  unfold put_cus, msmb.
  apply functional_extensionality.
  intros.
  destruct x. simpl in *.
  bdestruct (v =? y). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 <=? 0).
  inv H3.
  rewrite eupdate_index_eq.
  rewrite get_cus_cua. easy. lia.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H1. lia. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Local Opaque MAJ. Local Opaque UMA.

Lemma MAJseq'_correct :
  forall i n S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem (MAJseq' i x y c) S = 
     (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmb i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros.
  - simpl. rewrite MAJ_correct.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by assumption.
    rewrite put_cus_neq_1 by assumption.
    rewrite eupdate_index_eq. easy.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    rewrite put_cus_neq by assumption.
    unfold msmb.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <=? 0).
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia.
    rewrite xorb_comm. easy.
    lia.
    bdestruct (n0 <=? 0). lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H3. easy.
    rewrite put_cus_out by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    bdestruct (v =? x). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_1 by nor_sym.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    unfold msma.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <? 0). lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite carry_1.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia. easy.
    bdestruct (n0 <? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_get_cu. easy.
    apply H2. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_out by nor_sym.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    apply H2. lia.
    apply H3. lia.
    assumption.
    tuple_eq. destruct c. simpl in *.
    tuple_eq. destruct c. simpl in *. tuple_eq.
  - simpl. rewrite (IHi n).
    rewrite MAJ_correct.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    apply functional_extensionality.
    intros.
    destruct x0.
    bdestruct (n0 <? n). 
    bdestruct (v =? x). subst.
    bdestruct (n0 =? i).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite <- (msm_eq1 n).
    rewrite put_cu_twice_eq.
    easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i).
    subst. rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite (put_cus_eq (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])).
    rewrite (msm_eq3 n).
    rewrite put_cu_twice_eq.
    rewrite put_cus_eq by lia. easy.
    lia. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i).
    easy. lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (v =? y). subst.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite (msm_eq2 n). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmb.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia.
    bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia. easy. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H2. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H2. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    tuple_eq. tuple_eq. tuple_eq.
    lia. lia.
    unfold nor_modes. intros.
    apply H2. lia.
    unfold nor_modes. intros.
    apply H3. lia.
    apply H4. lia. lia. lia.
Qed.

Local Transparent carry.

Lemma UMAseq'_correct :
  forall i n S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem (UMAseq' i x y c) (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) = 
         (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros. 
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) 0) (fb := (get_cus n S y) 0)
                   (fc := carry (get_cua (S c)) 0 (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    simpl. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite eupdate_index_eq.
    rewrite put_cu_twice_eq_1.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by lia.
    rewrite put_get_cu. easy.  assumption.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_eq.
    unfold sumfb. simpl.
    assert (((get_cus n S x 0 ⊕ get_cus n S y 0) ⊕ get_cua (S c)) 
          = ((get_cua (S c) ⊕ get_cus n S x 0) ⊕ get_cus n S y 0)) by btauto.
    rewrite H10. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold sumfb.
    unfold msmc.
    bdestruct (n0 <=? 0). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_cus_neq_2 by lia. easy.
    bdestruct (v =? x).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_eq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H2. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by nor_sym.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct ( n0 <? 0). lia.
    bdestruct (n0 =? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H2. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym. easy.
    destruct c. simpl in *. tuple_eq.
    destruct c. simpl in *. tuple_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H3. lia.
    destruct c.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up_1. apply H4. apply iner_neq. assumption.
    apply iner_neq_1; assumption.
    apply iner_neq_1; assumption.
    rewrite put_cus_neq by lia.
    rewrite cus_get_eq.
    unfold msma.
    bdestruct (0 <? 0). lia.
    bdestruct (0 =? 0). 
    rewrite carry_1.
    unfold carry. easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    rewrite cus_get_eq.
    unfold msmc.
    bdestruct (0 <=? 0).
    rewrite xorb_comm. easy.
    lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H3. lia.
    rewrite put_cus_neq_1 by lia.
    rewrite put_cus_neq_1 by lia.
    rewrite get_cua_eq.
    simpl. rewrite get_cus_cua. easy. lia.
    assumption.
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) (Datatypes.S i)) (fb := (get_cus n S y) (Datatypes.S i))
                   (fc := carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite <- (IHi n).
    assert (((((put_cus
        (put_cus
           (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
           (msma (Datatypes.S i) (get_cua (S c)) 
              (get_cus n S x) (get_cus n S y)) n) y
        (msmc (Datatypes.S i) (get_cua (S c)) (get_cus n S x)
           (get_cus n S y)) n) [(x, Datatypes.S i)
     |-> S (x, Datatypes.S i)]) [(y, Datatypes.S i)
    |-> put_cu (S (y, Datatypes.S i))
          ((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
           ⊕ carry (get_cua (S c)) (Datatypes.S i) 
               (get_cus n S x) (get_cus n S y))]) [
   (x, i)
   |-> put_cu (S (x, i))
         (carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x)
            (get_cus n S y))])
     = (put_cus
     (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])
        x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) y
     (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)).
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_eq. easy.
    1-3:apply iner_neq_1; lia.
    destruct x0.
    bdestruct (n0 <? n).
    bdestruct (v =? x). subst.
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (i <? i). lia.
    bdestruct (i =? i). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? Datatypes.S i).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (Datatypes.S i <? i). lia.
    bdestruct (Datatypes.S i =? i). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H2. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i). easy. lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    bdestruct (v =? y). subst.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msmc.
    bdestruct (Datatypes.S i <=? i). lia.
    assert (((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
       ⊕ carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y))
     = ((carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)
    ⊕ get_cus n S x (Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))).
    rewrite <- (get_cus_cua n). btauto. lia.
    rewrite H12. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmc.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia. bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    easy.
    rewrite H8. rewrite IHi. easy.
    lia. lia.
    1-7:easy.
    lia.
    1-6:easy.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply neq_sym.
    apply iner_neq_1.
    assumption.
    apply H2. lia.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    1-3:tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (Datatypes.S i <? Datatypes.S i). lia.
    bdestruct (Datatypes.S i =? Datatypes.S i).
    unfold majb.
    simpl. btauto. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msmc.
    bdestruct (Datatypes.S i <=? Datatypes.S i).
    btauto.
    lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (i <? Datatypes.S i). easy. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
Qed.

(* adder correctness proofs. *)
Lemma adder01_correct_fb :
  forall n S x y c,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem (adder01 n x y c) S = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  intros. unfold adder01. unfold MAJseq, UMAseq.
  simpl.
  rewrite MAJseq'_correct with (n := n). 
  assert (forall S', put_cus S' y (msmb (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n = put_cus S' y (msmc (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n).
  intros. apply put_cus_sem_eq. intros.
  unfold msmb,msmc.
  bdestruct (m <=? n - 1). easy. lia.
  rewrite H7.
  apply UMAseq'_correct. assumption. lia. 1 - 6: assumption.
  apply H0. lia. 1 - 6 : assumption.
Qed.
(*
Lemma adder01_nor_fb :
  forall n env S S' x y c,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    S' = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) ->
    exp_sem env S (adder01 n x y c) S'.
Proof.
  intros.
  subst. apply adder01_correct_fb. 1-7:assumption.
Qed.

Check put_cus.
*)
Definition reg_push (f : posi -> val)  (x : var) (v:nat) (n : nat) : posi -> val := put_cus f x (nat2fb v) n.


Lemma reg_push_exceed :
  forall n x v f,
    reg_push f x v n = reg_push f x (v mod 2^n) n.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  apply put_cus_sem_eq. intros.
  rewrite Nofnat_mod. 2: apply Nat.pow_nonzero; lia.
  rewrite Nofnat_pow. simpl.
  do 2 rewrite N2fb_Ntestbit. rewrite N.mod_pow2_bits_low. easy. lia.
Qed.

Lemma get_cus_put_neq :
   forall f x y g n, x <> y -> get_cus n (put_cus f x g n) y = get_cus n f y.
Proof.
  intros. unfold get_cus,put_cus.
  apply functional_extensionality. intros.
  simpl.
  bdestruct ( y =? x). lia.
  destruct (f (y, x0)). easy. easy. easy.
Qed.


Lemma pos2fb_bound : forall n p m , (Pos.to_nat p) < 2 ^ n -> n <= m -> pos2fb p m = false.
Proof.
intros n p.
induction p.
intros. simpl.
Admitted.

Lemma N2fb_bound :
    forall n x m, x < 2 ^ n -> n <= m -> (nat2fb x) m = false.
Proof.
 intros.
 unfold nat2fb.
 unfold N2fb.
 destruct (N.of_nat x) eqn:eq.
 unfold allfalse. reflexivity.
 eapply (pos2fb_bound n). lia. lia.
Qed.

Check put_cus.

Lemma put_get_cus_eq :
   forall f x n, nor_modes f x n -> (put_cus f x (get_cus n f x) n) = f.
Proof.
  intros.
  unfold put_cus,get_cus,put_cu.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  subst.
  unfold nor_modes in H0.
  specialize (H0 n0 H2) as eq1. unfold nor_mode in eq1.
  destruct (f (x,n0)). easy. inv eq1. inv eq1.
  easy. easy.
Qed.


Lemma get_cus_put_eq :
   forall f x v n, v < 2^n -> nor_modes f x n -> get_cus n (put_cus f x (nat2fb v) n) x = (nat2fb v).
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n).
  simpl.
  unfold nor_modes in H0.
  assert (nor_mode (put_cus f x (nat2fb v) n) (x, x0)).
  apply nor_mode_cus_eq. apply H1. easy.
  unfold nor_mode in H3.
  destruct (put_cus f x ((nat2fb v)) n (x, x0)) eqn:eq2.
  unfold put_cus in eq2. simpl in eq2.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu in eq2.
  assert (nor_mode f (x,x0)).
  apply H1. easy.
  unfold nor_mode in H6.
  destruct (f (x, x0)). inv eq2. easy. inv H6. inv H6. lia. lia.
  inv H3. inv H3.
  unfold allfalse.
  rewrite (N2fb_bound n). easy. assumption. lia.
Qed.

(* The following two lemmas show the correctness of the adder implementation based on MAJ;UMA circuit. 
   The usage of the adder is based on the carry0 lemma. *)
Lemma adder01_correct_carry0 :
  forall n (S S' S'' : posi -> val) x y c v1 v2,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y (v1+v2) n ->
    exp_sem (adder01 n x y c) S' = S''.
Proof.
  intros. unfold reg_push in *. rewrite adder01_correct_fb; try assumption.
  subst. destruct c. simpl in *. rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq. 
  rewrite get_put_cu by easy.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry0.
  rewrite put_cus_twice_eq. easy. easy.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H2. easy. easy.
  unfold nor_modes. intros. apply nor_mode_up. iner_p.
  apply H1. easy. subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. easy. subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H2. easy. subst.
  destruct c.
  repeat apply nor_mode_cus_eq.
  apply nor_mode_up_1. easy.
Qed.

Lemma adder01_correct_carry1 :
  forall n (S S' S'' : posi -> val) x y c v1 v2,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y (v1+v2+1) n ->
    exp_sem (adder01 n x y c) S'  = S''.
Proof.
  intros. unfold reg_push in *. rewrite adder01_correct_fb; try assumption.
  subst. destruct c. simpl in *. rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq. 
  rewrite get_put_cu by easy.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry1.
  rewrite put_cus_twice_eq. easy. easy.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H2. lia. easy.
  unfold nor_modes. intros. 
  apply nor_mode_up. iner_p. apply H1. easy.
  subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. easy. 
  subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H2. easy. 
  subst.
  destruct c.
  repeat apply nor_mode_cus_eq.
  apply nor_mode_up_1. easy.
Qed.

Local Opaque adder01.
(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0 i x : exp :=
  match i with
  | 0 => SKIP (x,0)
  | S i' => negator0 i' x; X (x, i')
  end.

Lemma negator0_fwf : forall n x, exp_fwf (negator0 n x).
Proof.
  intros. induction n;simpl.
  constructor. constructor. easy. constructor.
Qed.


Lemma negatem_put_get : forall i n f x, S i <= n ->
       put_cus f x (negatem (S i) (get_cus n f x)) n =
              (put_cus f x (negatem i (get_cus n f x)) n)[(x,i) |-> put_cu (f (x,i)) (¬ (get_cua (f (x,i))))].
Proof.
  intros.
  unfold negatem.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (x =? v).
  bdestruct (n0 =? i).
  subst.
  rewrite eupdate_index_eq.
  unfold put_cus. simpl.
  bdestruct (v =? v).
  bdestruct (i <? n).
  bdestruct (i <? S i).
  rewrite get_cus_cua. easy. lia.
  lia. lia. lia.
  rewrite eupdate_index_neq.
  unfold put_cus. simpl.
  bdestruct (v =? x).
  bdestruct (n0 <? n).
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i). easy.
  lia.
  bdestruct (n0 <? i). lia. easy.
  easy. easy.
  intros R. inv R. lia.
  rewrite put_cus_neq.
  rewrite eupdate_index_neq.
  rewrite put_cus_neq.
  easy. 
  lia.
  intros R. inv R. lia. lia.
Qed.

Lemma negator0_correct :
  forall i n f x,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    exp_sem (negator0 i x) f = (put_cus f x (negatem i (get_cus n f x)) n).
Proof.
 induction i; intros.
 simpl.
 assert ((negatem 0 (get_cus n f x)) = get_cus n f x).
  apply functional_extensionality. intros.
 unfold negatem. bdestruct (x0 <? 0).
 lia. easy.
 rewrite H3.
 rewrite put_get_cus_eq. constructor. assumption.
 simpl. 
 rewrite (IHi n) ; try lia; try easy.
 rewrite negatem_put_get.
 assert (exchange (put_cus f x (negatem i (get_cus n f x)) n (x, i)) = 
            put_cu (f (x, i)) (¬ (get_cua (f (x, i))))).
 unfold negatem. simpl.
 unfold put_cus. simpl. bdestruct (x=?x).
 bdestruct (i<?n). bdestruct (i <? i). lia.
 assert (nor_mode f (x,i)).
 apply H2. easy.
 unfold nor_mode in H6. destruct (f (x,i)) eqn:eq1.
 rewrite get_cus_cua.
 unfold exchange,put_cu,get_cua. rewrite eq1. easy. lia. lia. lia. lia. lia.
 rewrite H3. easy. lia.
Qed.

(*
Lemma negator0_nor :
  forall i n env f f' x,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    f' = (put_cus f x (negatem i (get_cus n f x)) n) ->
    exp_sem env f (negator0 i x) f'.
Proof.
 intros. subst. apply negator0_correct. 1 - 3: assumption.
Qed.
*)
(* The correctness represents the actual effect of flip all bits for the number x.
   The effect is to make the x number positions to store the value  2^n - 1 - x. *)
Lemma negator0_sem :
  forall n x v f,
    0 < n ->
    v < 2^n -> nor_modes f x n ->
    exp_sem (negator0 n x) (reg_push f x v n) = reg_push f x (2^n - 1 - v) n.
Proof.
  intros. unfold reg_push in *.
  rewrite (negator0_correct n n); try assumption.
  rewrite put_cus_twice_eq.
  rewrite get_cus_put_eq; try easy.
  rewrite negatem_arith ; try easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply H2. lia.
Qed.

(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)
Local Opaque CNOT. Local Opaque CCX.

Definition highbit n x c2 := X (x,n-1) ; X c2 ; CNOT (x,n-1) c2 ; X c2; X (x,n-1).

Definition highb01 n x y c1 c2: exp := MAJseq n x y c1; highbit n x c2 ; inv_exp (MAJseq n x y c1).

Definition no_equal (x y:var) (c1 c2 : posi) : Prop := x <> y /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> fst c1 /\ y <> fst c2 /\ fst c1 <> fst c2.

Lemma highbit_fwf : forall n x c2, fst c2 <> x -> exp_fwf(highbit n x c2).
Proof.
 intros. repeat constructor.
 apply cnot_fwf. destruct c2. iner_p.
Qed.

Lemma highb01_fwf : forall n x y c1 c2, no_equal x y c1 c2 -> exp_fwf (highb01 n x y c1 c2).
Proof.
  intros. unfold no_equal in H0.  destruct H0 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  constructor. constructor.
  apply majseq_fwf; try assumption.
  apply highbit_fwf; try iner_p.
  apply fwf_inv_exp.
  apply majseq_fwf; try assumption.
Qed.

Lemma get_cus_up : forall n f x c v, fst c <> x -> get_cus n (f[c |-> v]) x = get_cus n f x.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? n). destruct c. simpl in *. rewrite eupdate_index_neq by iner_p.
  easy. easy.
Qed.

Lemma exp_sem_seq : forall e1 e2 f, exp_sem (e1 ; e2) f = exp_sem e2 (exp_sem e1 f).
Proof.
intros. simpl. easy.
Qed.

Lemma exp_sem_x : forall p f, exp_sem (X p) f = (f[p |-> exchange (f p)]).
Proof.
intros. simpl. easy.
Qed.

Lemma put_cu_exchange : forall (f : posi -> val) p v, nor_mode f p ->  put_cu (exchange (f p)) v = put_cu (f p) v.
Proof.
 intros. unfold exchange. unfold nor_mode in H0.
 destruct (f p) eqn:eq1. simpl. easy. lia. lia.
Qed.

Lemma highbit_correct :
  forall n f x c2,
    0 < n -> fst c2 <> x -> nor_mode f c2 -> nor_modes f x n -> get_cua (f c2) = false ->
    exp_sem (highbit n x c2) f = f[c2 |-> put_cu (f c2) ((majb true false (get_cus n f x (n-1))) ⊕ true)].
Proof.
 intros. unfold highbit. repeat rewrite exp_sem_seq.
 rewrite exp_sem_x with (f:=f). rewrite exp_sem_x with (f := (f [(x, n - 1) |-> exchange (f (x, n - 1))])).
 destruct c2.
 rewrite eupdate_index_neq by iner_p.
 rewrite cnot_sem.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p. 
 rewrite eupdate_index_eq.
 rewrite eupdate_twice_eq.
 rewrite put_cu_exchange by easy.
 assert (get_cua (exchange (f (v, n0))) = true).
 unfold get_cua in H4. unfold nor_mode in H2.
 unfold get_cua,exchange.
 destruct (f (v, n0)) eqn:eq1. subst. easy. lia. lia.
 rewrite H5.
 unfold majb. bt_simpl.
 rewrite exp_sem_x with (p := (v, n0)) by easy.
 rewrite eupdate_twice_eq by easy.
 rewrite eupdate_index_eq.
 rewrite exp_sem_x by easy.
 rewrite eupdate_twice_neq by iner_p.
 rewrite eupdate_twice_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_eq.
 rewrite exchange_twice_same.
 apply eupdate_same_1.
 rewrite eupdate_same. easy. easy.
 unfold nor_modes in H3. specialize (H3 (n-1)).
 assert (n - 1 < n) by lia. specialize (H3 H6).
 unfold nor_mode in H2.
 unfold nor_mode in H3.
 unfold exchange.
 rewrite get_cus_cua.
 destruct (f (x, n - 1)) eqn:eq1. simpl.
 unfold put_cu. destruct (f (v, n0)) eqn:eq2.
 assert ((¬ (¬ (¬ b))) = (¬ b)) by btauto. rewrite H7. easy. lia. lia. lia. lia. easy.
 apply nor_mode_up. iner_p.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_modes in H3. assert (n -1 < n) by lia.
 specialize (H3 (n-1) H5). unfold nor_mode in H3.
 unfold exchange.
 destruct (f (x, n - 1)) eqn:eq1. easy. lia. lia.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_mode in H2.
 unfold exchange.
 destruct (f (v, n0)) eqn:eq1. easy. lia. lia.
Qed.


Local Opaque highbit.

Lemma highb01_correct :
  forall n aenv tenv f x y c1 c2,
    0 < n -> no_equal x y c1 c2 ->
    nor_mode f c2 -> nor_mode f c1 -> nor_modes f x n -> nor_modes f y n -> 
    get_cua (f c2) = false -> well_typed_exp tenv (MAJseq n x y c1) -> right_mode_env aenv tenv f ->
    exp_sem (highb01 n x y c1 c2) f =
      f[c2 |-> put_cu (f c2) ((majb true false (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))) ⊕ true)].
Proof.
  intros.
  unfold highb01. unfold no_equal in H1.
  destruct H1 as [V1 [V2 [V3 [V4 [V5 V6]]]]].
  destruct c1. destruct c2.
  simpl. unfold MAJseq. rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  rewrite highbit_correct; try lia.
  rewrite put_cu_cus. rewrite put_cu_cus.
  rewrite get_cus_cua by lia.
  rewrite put_cus_neq by lia.
  rewrite cus_get_eq; try lia.
  rewrite eupdate_index_neq by iner_p.
  erewrite inv_exp_reverse. easy.
  apply majseq'_fwf ; try easy. apply H7.
  apply right_mode_exp_up_same. apply H8.
  rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite get_cus_up by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_update_flip by iner_p.
  rewrite put_cus_update_flip by iner_p.
  apply eupdate_same_1. easy.
  unfold msma. bdestruct (n - 1 <? n - 1). lia.
  bdestruct (n - 1 =? n - 1).
  assert ((S (n - 1)) = n) by lia. rewrite H10. easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H4. easy.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H5. easy.
  apply nor_mode_up ; iner_p. 
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H4. easy.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H4. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Local Opaque highb01.

(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n x y c1 c2 := (X c1; negator0 n x); highb01 n x y c1 c2; inv_exp (X c1; negator0 n x).

Lemma negations_aux :
  forall n x c v S v' r,
    0 < n -> fst c <> x ->
    v < 2^n ->
    v' = nval false r -> nor_modes S x n ->
    exp_sem (X c; negator0 n x) (reg_push (S[c |-> v']) x v n) 
           = (reg_push (S[c |-> nval true r]) x (2^n - 1 - v) n).
Proof.
  intros; subst. simpl.
  assert (((reg_push (S [c |-> nval false r]) x v n) [c
   |-> exchange (reg_push (S [c |-> nval false r]) x v n c)]) 
        = reg_push (S [c |-> nval true r]) x v n).
  unfold reg_push.
  rewrite <- put_cus_update_flip by easy.
  rewrite eupdate_twice_eq. 
  destruct c. simpl in *.
  rewrite put_cus_neq by lia.
  rewrite eupdate_index_eq.
  unfold exchange. simpl. easy.
  rewrite H3.
  rewrite (negator0_sem n) ; try easy.
  unfold nor_modes. intros.
  apply nor_mode_up. destruct c. iner_p. apply H4. easy.
Qed.

Lemma pow2_predn :
  forall n x,
    x < 2^(n-1) -> x < 2^n.
Proof.
  intros. destruct n. simpl in *. lia.
  simpl in *. rewrite Nat.sub_0_r in H0. lia.
Qed.

Lemma Ntestbit_lt_pow2n :
  forall x n,
    (x < 2^n)%N ->
    N.testbit x n = false.
Proof.
  intros. apply N.mod_small in H0. rewrite <- H0. apply N.mod_pow2_bits_high. lia.
Qed.

Lemma Ntestbit_in_pow2n_pow2Sn :
  forall x n,
    (2^n <= x < 2^(N.succ n))%N ->
    N.testbit x n = true.
Proof.
  intros. assert (N.log2 x = n) by (apply N.log2_unique; lia).
  rewrite <- H1. apply N.bit_log2.
  assert (2^n <> 0)%N by (apply N.pow_nonzero; easy).
  lia.
Qed.

Lemma carry_leb_equiv_true :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x <= y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = true.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H2. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_in_pow2n_pow2Sn. btauto.
  split.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  rewrite <- Nnat.Nat2N.inj_succ.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^(S n)) with (2^n + 2^n) by (simpl; lia).
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv_false :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x > y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = false.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. btauto.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = (x <=? y).
Proof.
  intros. bdestruct (x <=? y). apply carry_leb_equiv_true; easy. apply carry_leb_equiv_false; easy.
Qed.

Lemma pow2_low_bit_false : forall n i, i < n -> nat2fb (2^n) i = false.
Proof.
 intros. unfold nat2fb.
 rewrite N2fb_Ntestbit.
 assert (N.of_nat i < N.of_nat n)%N.
 lia.
 specialize (N.mul_pow2_bits_low 1 (N.of_nat n) (N.of_nat i) H1) as eq1.
 assert (1 * 2 ^ N.of_nat n = 2 ^ N.of_nat n)%N by lia.
 rewrite H2 in eq1.
 assert (2%N = (N.of_nat 2)) by easy. rewrite H3 in eq1.
 rewrite Nofnat_pow.
 rewrite eq1. easy.
Qed.

Lemma carry_false_lt: forall n f g,
    (forall i, i <= n -> g i = false) -> 
    carry false n f g = false.
Proof.
  induction n;intros.
  simpl. easy.
  simpl.
  rewrite IHn.
  rewrite H0 by lia. btauto.
  intros. rewrite H0. easy. lia.
Qed.

Lemma low_bit_same : forall n x, 0 < n -> x < 2^n -> 
    (forall i, i < n -> nat2fb (x + 2^n) i = nat2fb x i).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  unfold sumfb.
  rewrite pow2_low_bit_false by easy. bt_simpl.
  rewrite carry_false_lt. btauto.
  intros.
  apply pow2_low_bit_false. lia.
Qed.

Lemma carry_low_bit_same : forall m b n x g, m <= n -> 0 < n -> x < 2^n -> 
    carry b m (nat2fb (x + 2^n)) g = carry b m (nat2fb x) g.
Proof.
  induction m;intros. simpl. easy.
  simpl.
  rewrite IHm by lia.
  rewrite low_bit_same by lia. easy.
Qed.


Lemma majb_carry_s_eq : forall n x y, 0 < n -> x < 2^n -> y < 2^n ->
      majb true false (carry true n (nat2fb (2^n - 1 - x)) (nat2fb y)) 
       = carry true (S n) (nat2fb ((2^n - 1 - x) + 2^n)) (nat2fb y).
Proof.
  intros. simpl. unfold majb.
  assert (nat2fb (2 ^ n - 1 - x + 2 ^ n) n = true).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_in_pow2n_pow2Sn. easy.
  split. 
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nnat.Nat2N.inj_succ. 
  rewrite <- Nofnat_pow.
  rewrite Nat.pow_succ_r. lia. lia.
  rewrite H3.
  assert (nat2fb y n = false).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n. easy.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  rewrite H4. rewrite carry_low_bit_same. easy.
  easy. lia. lia.
Qed.

Lemma reg_push_update_flip : forall n f g x c v, fst c <> x 
         -> reg_push (f[c |-> v]) x g n = (reg_push f x g n)[c |-> v].
Proof.
  intros. unfold reg_push.
  rewrite put_cus_update_flip. easy. lia.
Qed.

Lemma reg_push_twice_neq : forall (f:posi -> val) (x y:var) g1 g2 n, 
              x <> y -> (reg_push (reg_push f x g1 n) y g2 n)
                          = (reg_push (reg_push f y g2 n) x g1 n).
Proof.
 intros. unfold reg_push. rewrite put_cus_twice_neq. easy. lia.
Qed.


Lemma comparator01_fwf : forall n x y c1 c2, no_equal x y c1 c2 ->
               exp_fwf (comparator01 n x y c1 c2).
Proof.
  intros. unfold comparator01.
  constructor. constructor. constructor. constructor.
  apply negator0_fwf. 
  apply highb01_fwf. easy.
  apply fwf_inv_exp.
  constructor. constructor. apply negator0_fwf. 
Qed.

Lemma comparator01_correct :
  forall tenv aenv n x y c1 c2 v1 v2 f f' f'',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    f' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (¬(v1 <=? v2))]) x v1 n) y v2 n ->
    exp_sem (comparator01 n x y c1 c2) f' = f''.
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. subst.
  unfold no_equal in *.
  destruct H3 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  destruct c1. destruct c2.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_twice_neq by easy.
  rewrite reg_push_update_flip by iner_p.
  assert (exists b r, f (v, n0) = nval b r).
  unfold nor_mode in H6. destruct (f (v, n0)). exists b. exists r. easy. lia. lia.
  destruct H3. destruct H3.
  rewrite negations_aux with (r := x1); try easy.
  unfold reg_push.
  rewrite highb01_correct with (tenv := tenv) (aenv := aenv); try easy.
  assert (put_cus
  (put_cus
     ((f [(v, n0) |-> put_cu (f (v, n0)) false]) [
      (v0, n1) |-> put_cu (f (v0, n1)) (¬(v1 <=? v2))]) x 
     (nat2fb v1) n) y (nat2fb v2) n
      = (reg_push
    ((reg_push
     (f[
      (v0, n1) |-> put_cu (f (v0, n1)) (¬(v1 <=? v2))]) y v2 n)[(v, n0) |-> put_cu (f (v, n0)) false]) x v1 n)).
  unfold reg_push.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_twice_neq by lia. 
  rewrite put_cus_update_flip by iner_p. easy. 
  rewrite H12. clear H12.
  erewrite inv_exp_reverse. easy.
  constructor. constructor. apply negator0_fwf.
  constructor. apply H9. easy. 
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. apply H11.
  Check negations_aux.
  rewrite negations_aux with (r := x1); try easy.
  repeat rewrite cus_get_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_cus_put_eq; try lia.
  rewrite get_cus_put_neq; try lia.
  rewrite <- put_cus_update_flip with (f := (f [(v0, n1) |-> put_cu (f (v0, n1)) false])).
  rewrite get_cus_put_eq; try lia.
  assert ((get_cua (nval true x1)) = true). unfold get_cua. easy.
  rewrite H12.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H13 in eq2. clear H13.
  assert ((n + 1) = S n) by lia.
  rewrite H13 in eq2. clear H13. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H13 in eq2. rewrite eq2.
  rewrite put_cu_cus.
  rewrite put_cu_cus.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite double_put_cu.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_twice_eq.
  rewrite put_cus_update_flip by iner_p.
  bt_simpl. unfold reg_push. easy.
  1-7:lia. 
  unfold nor_modes. intros.
  repeat apply nor_mode_up ; iner_p. apply H5. easy.
  iner_p.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H4. easy. iner_p.
  rewrite H3. unfold put_cu. easy.
  unfold reg_push.
  unfold nor_modes. intros. apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  apply H4. easy.
  apply nor_mode_cus_eq. apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up_1; iner_p.
  apply nor_mode_cus_eq.
  unfold nor_mode. rewrite eupdate_index_eq. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H4. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H5. easy.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu. easy. apply H7.
  apply right_mode_exp_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H3. easy. rewrite H12.
  apply right_mode_exp_up_same_1.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy. iner_p.
  rewrite H3. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H4. easy.
Qed.

Local Opaque comparator01.

(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition subtractor01 n x y c1:= (X c1; negator0 n x); adder01 n x y c1; inv_exp (X c1; negator0 n x).

(* The correctness proof of the subtractor. *)
Lemma subtractor01_correct :
  forall tenv aenv n x y c1 v1 v2 f f' f'',
    0 < n ->
    v1 < 2^n ->
    v2 < 2^n ->     x <> y -> x <> fst c1 -> y <> fst c1 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    f' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y (v2 + 2^n - v1) n ->
    exp_sem (subtractor01 n x y c1) f' = f''.
Proof.
  intros.
  unfold subtractor01. remember (X c1; negator0 n x) as negations. simpl. subst.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  destruct (f c1) eqn:eq2.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  assert (nval true r = put_cu (f c1) true).
  rewrite eq2. easy. rewrite H13. 
  Check adder01_correct_carry1.
  rewrite adder01_correct_carry1 with (S0 := f) (v1 := (2 ^ n - 1 - v1)) (v2:=v2)
       (S'' := reg_push (reg_push (f [c1 |-> put_cu (f c1) true])
              x (2 ^ n - 1 - v1) n) y ((2 ^ n - 1 - v1) + v2 + 1) n); try easy.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  erewrite inv_exp_reverse. unfold put_cu. easy.
  constructor. constructor. apply negator0_fwf.
  constructor. apply H10. easy.
  unfold reg_push.
  repeat apply right_mode_exp_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H14.
  apply right_mode_exp_up_same. apply H12.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- H13.
  assert ((2 ^ n - 1 - v1 + v2 + 1) = (v2 + 2 ^ n - v1)) by lia.
  rewrite H14. easy.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply H6. easy. lia.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply H6. easy.
  unfold nor_mode in H8. rewrite eq2 in H8. lia.
  unfold nor_mode in H8. rewrite eq2 in H8. lia.
Qed.

Local Opaque subtractor01.

Definition no_equal_5 (x y M:var) (c1 c2 : posi) : Prop := x <> y /\ x <> M /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> M /\ y <> fst c1 /\ y <> fst c2 /\ M <> fst c1 /\ M <> fst c2 /\ fst c1 <> fst c2.


(* The implementation of a modulo adder. It takes [M][x][y], and then produces the result of [M][x+y % M][y]. 
   The modulo operation is not reversible. It will flip the high-bit to be the comparator factor.
   To flip the high-bit to zero, we use the inverse circuit of the comparator in the modulo adder to
   flip the high-bit back to zero.*)
Definition modadder21 n x y M c1 c2 := adder01 n y x c1 ; (*  adding y to x *)
                                       comparator01 n M x c1 c2; (* compare M < x + y (in position x) *)
                                       X c2 ; CU c2 (subtractor01 n M x c1) ; (* doing -M + x to x, then flip c2. *)
                                       inv_exp(comparator01 n y x c1 c2). (* compare M with x+y % M to clean c2. *)

Lemma adder01_sem_carry0 :
  forall n (f f' : posi -> val) x y c v1 v2,
    0 < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n -> get_r (f c) = get_r (f' c) -> nor_mode f' c ->
    exp_sem (adder01 n x y c) (reg_push (reg_push (f[c |-> put_cu (f' c) false]) x v1 n) y v2 n)
               = reg_push (reg_push (f[c |-> put_cu (f' c) false]) x v1 n) y (v1+v2) n.
Proof.
  intros.
  specialize (adder01_correct_carry0 n f ( reg_push
        (reg_push (f [c |-> put_cu (f c) false]) x v1 n) y v2
        n) (reg_push (reg_push (f [c |-> put_cu (f c) false]) x v1 n) y
  (v1 + v2) n) x y c v1 v2 H0 H1 H2 H3 H4 H5 H6 H7 H8) as eq1.
  unfold put_cu in *.
  unfold get_r in H9.
  unfold nor_mode in H3. unfold nor_mode in H10.
  destruct (f c) eqn:eq2.
  destruct (f' c) eqn:eq3. subst.
  rewrite eq1. easy. easy. easy. lia. lia. lia. lia.
Qed.

Lemma comparator01_sem :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_r (f c1) = get_r (f' c1) -> nor_mode f' c1
     -> get_r (f c2) = get_r (f' c2) -> nor_mode f' c2 ->
    exp_sem (comparator01 n x y c1 c2) (reg_push (reg_push 
          ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) false]) x v1 n) y v2 n)
      = (reg_push (reg_push ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) (¬(v1 <=? v2))]) x v1 n) y v2 n).
Proof.
  intros.
  specialize (comparator01_correct tenv aenv n x y c1 c2 v1 v2 f
  (reg_push
     (reg_push
        ((f [c1 |-> put_cu (f c1) false]) [c2
         |-> put_cu (f c2) false]) x v1 n) y v2 n)
    (reg_push
  (reg_push
     ((f [c1 |-> put_cu (f c1) false]) [c2
      |-> put_cu (f c2) (¬ (v1 <=? v2))]) x v1 n) y v2 n) H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10) as eq1.
  unfold put_cu in *. unfold get_r in H12. unfold get_r in H14.
  unfold nor_mode in H6. unfold nor_mode in H7.
  destruct (f c1) eqn:eq2.  destruct (f c2) eqn:eq3.
  unfold nor_mode in H13. unfold nor_mode in H15.
  destruct (f' c1) eqn:eq4.  destruct (f' c2) eqn:eq5. subst.
  rewrite eq1. 1-12:easy.
Qed.

Lemma subtractor01_sem :
  forall tenv aenv n x y c1 v1 v2 f f',
    0 < n ->
    v1 < 2^n ->
    v2 < 2^n ->  x <> y -> x <> fst c1 -> y <> fst c1 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_r (f c1) = get_r (f' c1) -> nor_mode f' c1 ->
    exp_sem (subtractor01 n x y c1) (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y v2 n) 
     = (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y (v2 + 2^n - v1) n).
Proof.
  intros.
  specialize (subtractor01_correct tenv aenv n x y c1 v1 v2 f
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y v2 n)
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y
        (v2 + 2 ^ n - v1) n) H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as eq1.
  unfold put_cu,get_r in *.
  unfold nor_mode in H8. unfold nor_mode in H14.
  destruct (f c1) eqn:eq2. destruct (f' c1) eqn:eq4.
  subst. rewrite eq1. 1-4:easy.
  1-4:lia.
Qed.

(* The correctness statement of the modulo adder. *)
Lemma modadder21_correct :
  forall tenv aenv n x y M c1 c2 v1 v2 vM f,
    0 < n -> v1 < vM -> v2 < vM -> vM < 2^(n-1) -> no_equal_5 x y M c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_modes f M n -> nor_mode f c1 -> nor_mode f c2
     -> well_typed_exp tenv (modadder21 n x y M c1 c2) -> right_mode_env aenv tenv f ->
    exp_sem (modadder21 n x y M c1 c2) 
      (reg_push (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x v1 n)
    = (reg_push (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x ((v1 + v2) mod vM) n).
Proof.
  intros.
  assert (v1 + v2 < 2^n).
  { replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
    destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
  assert (vM < 2^n).
  { apply pow2_predn. easy.
  }
  assert (v1 <2^(n-1)) by lia.
  assert (v2 <2^(n-1)) by lia.
  unfold modadder21. remember (CU c2 (subtractor01 n M x c1)) as csub01.
  remember (X c2) as csub02. simpl. subst.
  unfold no_equal_5 in H4.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  destruct c1 as [c1 cp1]. destruct c2 as [c2 cp2].
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite adder01_sem_carry0 ; (try lia ; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq with (x:=M) by lia.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite comparator01_sem with (tenv := tenv) (aenv := aenv); (try lia; try easy).
  rewrite exp_sem_x.
  assert (exchange
            (reg_push
               (reg_push
                  (((reg_push f y v2 n) [(c1, cp1)
                    |-> put_cu (f (c1, cp1)) false]) [
                   (c2, cp2)
                   |-> put_cu (f (c2, cp2)) (¬ (vM <=? v2 + v1))])
                  M vM n) x (v2 + v1) n (c2, cp2))
        = put_cu (f (c2, cp2)) (vM <=? v2 + v1)).
  unfold reg_push.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq.
  unfold exchange. unfold put_cu.
  unfold nor_mode in H9. destruct (f (c2, cp2)) eqn:eq1.
  assert ((¬ (¬ (vM <=? v2 + v1))) = (vM <=? v2 + v1)) by btauto. rewrite H4. easy. lia. lia.
  rewrite H4. clear H4. simpl.
  rewrite eupdate_index_eq. rewrite get_put_cu by easy.
  bdestruct (vM <=? v2 + v1). simpl.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite eupdate_twice_eq.
  rewrite eupdate_twice_neq by iner_p.
  rewrite subtractor01_sem with (tenv:= tenv) (aenv:=aenv); (try lia; try easy).
  erewrite inv_exp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_fwf. unfold no_equal. split. lia. easy.
  unfold modadder21 in H10. inv H10. 
  apply typed_inv_exp in H20. rewrite inv_exp_involutive in H20. apply H20.
  unfold reg_push. 
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1.
  apply nor_mode_up ; try iner_p. apply nor_mode_cus_eq. easy. easy.
  apply right_mode_exp_up_same_1. apply nor_mode_cus_eq. easy. easy.
  apply right_mode_exp_put_cus_same. apply H11.
  rewrite comparator01_sem with (tenv := tenv) (aenv:=aenv); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq with (x:=M) by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  clear H5 H6 H7 H8 H9 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 H10 H11 H12 H13 H14 H15.
  rewrite plus_comm.
  rewrite <- mod_sum_lt_bool by lia. rewrite plus_comm.
  rewrite plus_comm in H4.
  assert (v1 + v2 + 2 ^ n - vM = v1 + v2 - vM + 2^n) by lia.
  rewrite H5.
  rewrite reg_push_exceed with (v:= v1 + v2 - vM + 2 ^ n).
  assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
  rewrite <- Nat.add_mod_idemp_r with (a := v1 + v2 - vM) by easy.
  rewrite Nat.mod_same by easy.
  rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
  rewrite Nat.mod_eq by lia.
  assert (v1 + v2 < 2 * vM) by lia.
  assert ((v1 + v2) / vM < 2) by (apply Nat.div_lt_upper_bound; lia).
  assert (1 <= (v1 + v2) / vM) by (apply Nat.div_le_lower_bound; lia).
  assert ((v1 + v2) / vM = 1) by lia.
  replace (v1 + v2 - vM * ((v1 + v2) / vM)) with (v1 + v2 - vM) by lia.
  bdestruct (vM <=? v1 + v2). simpl. easy. lia.
  assert ((v1 + v2) mod vM < vM).
  apply Nat.mod_upper_bound. lia. lia.
  unfold no_equal. split. lia. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H6. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H5. easy.
  nor_mode_simpl. nor_mode_simpl.
  right_simpl. right_simpl. right_simpl.
  Local Transparent adder01 subtractor01 comparator01.
  inv H10. inv H19. inv H18. inv H19. inv H18. easy.
  inv H10. inv H19. inv H21. inv H22. inv H21. inv H22. easy.
  inv H10. inv H20. inv H18. rewrite inv_exp_involutive in H22. easy.
  unfold reg_push. apply right_mode_exp_put_cus_same. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H7. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H5. easy. nor_mode_simpl.
  right_simpl. right_simpl. right_simpl.
  inv H10. inv H19. inv H21. inv H22. inv H21. inv H24. easy.
  inv H10. inv H19. inv H21. inv H22. inv H21. inv H22. easy.
  inv H10. inv H19. inv H18. inv H19. inv H23. inv H19. inv H23. easy.
  unfold reg_push. apply right_mode_exp_up_same_1.
  nor_mode_simpl. apply H9.
  apply right_mode_exp_put_cus_same. easy.
  unfold reg_push. rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p. easy.
  erewrite inv_exp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_fwf. unfold no_equal. split. lia. easy.
  Local Opaque comparator01.
  inv H10.
  apply typed_inv_exp in H20. rewrite inv_exp_involutive in H20. apply H20.
  unfold reg_push.
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_put_cus_same. apply H11.
  rewrite comparator01_sem with (tenv := tenv) (aenv:=aenv); (try lia; try easy).
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := x) by iner_p.
  rewrite eupdate_twice_eq.
  rewrite reg_push_update_flip with (x:=M) by iner_p.
  rewrite reg_push_twice_neq with (x:=y) (y:=M) by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite plus_comm.
  rewrite <- mod_sum_lt_bool by lia.
  bdestruct (vM <=? v2 + v1). lia. simpl.
  rewrite Nat.mod_small by lia. easy.
  assert ((v1 + v2) mod vM < vM).
  apply Nat.mod_upper_bound. lia. lia.
  unfold no_equal. split. lia. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H6. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H5. lia.
  nor_mode_simpl. nor_mode_simpl.
  Local Transparent comparator01.
  inv H10. inv H19. inv H18. inv H19. inv H18. easy.
  inv H10. inv H19. inv H18. inv H19. inv H23. inv H19. inv H23. easy.
  inv H10. inv H20. inv H18. rewrite inv_exp_involutive in H22. easy.
  right_simpl. 
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold no_equal. split. lia. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H7. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H5. lia.
  1-2:nor_mode_simpl. 
  inv H10. inv H18. inv H20. inv H21. inv H20. inv H23. easy.
  inv H10. inv H19. inv H17. easy.
  inv H10. inv H18. inv H20. inv H21. inv H20. inv H21. easy.
  right_simpl.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H6. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H5. lia.
  nor_mode_simpl.
  unfold reg_push. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Definition doubler1 y := Rshift y.

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation. *)
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x;; Exp (comparator01 n x M c1 c2; CU c2 (subtractor01 n M x c1)).

(* The following implements the modulo adder for all bit positions in the
   binary boolean function of C. 
   For every bit in C, we do the two items:
   we first to double the factor (originally 2^(i-1) * x %M, now 2^i * x %M).
   Then, we see if we need to add the factor result to the sum of C*x%M
   based on if the i-th bit of C is zero or not.
modadder21 n x y M c1 c2
[M][x][0][0] -> [M][2^i * x % M][C^i*x % M][0]
 *)
(* A function to compile positive to a bool function. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)

(* A function to compile a natural number to a bool function. *)

Fixpoint modsummer' i n M x y c1 c2 s (fC : nat -> bool) :=
  match i with
  | 0 => if (fC 0) then Exp (adder01 n x y c1) else Exp (SKIP (x,0))
  | S i' =>  modsummer' i' n M x y c1 c2 s fC;; moddoubler01 n x M c1 c2;; 
          Exp (SWAP c2 (s,i));;
        (if (fC i) then Exp (modadder21 n y x M c1 c2) else Exp (SKIP (x,i)))
  end.
Definition modsummer n M x y c1 c2 s C := modsummer' (n - 1) n M x y c1 c2 s (nat2fb C).

(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n M x y c1 c2 s C := modsummer n M x y c1 c2 s C;; (inv_sexp (modsummer n M x y c1 c2 s 0)).

Definition modmult_full C Cinv n M x y c1 c2 s := modmult_half n M x y c1 c2 s C;; inv_sexp (modmult_half n M x y c1 c2 s Cinv).

Definition modmult M C Cinv n x y z s c1 c2 := Exp (init_v n z M);; modmult_full C Cinv n z x y c1 c2 s;; inv_sexp (Exp (init_v n z M)).

Definition modmult_rev M C Cinv n x y z s c1 c2 := Rev x;; modmult M C Cinv n x y z s c1 c2;; Rev x.


(* The definition of QSSA. *)

Definition fvar := nat.

(*  a type for const values that cannot appear in a quantum circuit,
   and register values that can appear in a guantum circuit. *)
Inductive atype := C : nat -> atype | Q : nat -> atype.


Definition aty_eq  (t1 t2:atype) : bool := 
   match t1 with C n => match t2 with C m => n =? m
                            | _ => false
                        end
               | Q n => match t2 with Q m => n =? m
                           | _ => false
                        end
   end.

Notation "i '=a=' j" := (aty_eq i j) (at level 50).

Lemma aty_eqb_eq : forall a b, a =a= b = true -> a = b.
Proof.
 intros. unfold aty_eq in H0.
 destruct a. destruct b.
 apply Nat.eqb_eq in H0. subst. easy.
 inv H0.
 destruct b. inv H0.
 apply Nat.eqb_eq in H0. subst. easy.
Qed.

Lemma aty_eqb_neq : forall a b, a =a= b = false -> a <> b.
Proof.
 intros. unfold aty_eq in H0.
 destruct a. destruct b.
 apply Nat.eqb_neq in H0.
 intros R. inv R. contradiction.
 intros R. inv R.
 destruct b. 
 intros R. inv R.
 apply Nat.eqb_neq in H0.
 intros R. inv R. contradiction.
Qed.

Lemma aty_eq_reflect : forall r1 r2, reflect (r1 = r2) (aty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =a= r2) eqn:eq1.
  apply  ReflectT.
  apply aty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply aty_eqb_neq in eq1.
  assumption. 
Qed.

Inductive btype := Nat : btype | Flt : btype.

Definition bty_eq (t1 t2:btype) : bool := match (t1,t2) with (Nat,Nat) => true
                                                           | (Flt,Flt) => true
                                                            | _ => false
                                          end.

Notation "i '=b=' j" := (bty_eq i j) (at level 50).


Lemma bty_eqb_eq : forall a b, a =b= b = true -> a = b.
Proof.
 intros. unfold bty_eq in H0.
 destruct a. destruct b.
 easy. inv H0.
 destruct b. inv H0. easy.
Qed.

Lemma bty_eqb_neq : forall a b, a =b= b = false -> a <> b.
Proof.
 intros. unfold bty_eq in H0.
 destruct a. destruct b. inv H0. easy.
 destruct b. easy. inv H0.
Qed.

Lemma bty_eq_reflect : forall r1 r2, reflect (r1 = r2) (bty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =b= r2) eqn:eq1.
  apply  ReflectT.
  apply bty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply bty_eqb_neq in eq1.
  assumption. 
Qed.

Definition typ :Type := (atype * btype).

Definition ty_eq (t1 t2:typ) : bool :=
   match t1 with (a1,b1) => match t2 with (a2,b2) => aty_eq a1 a2 && bty_eq b1 b2 end end.

Notation "i '=t=' j" := (ty_eq i j) (at level 50).

Lemma ty_eqb_eq : forall a b, a =t= b = true -> a = b.
Proof.
 intros. unfold ty_eq in H0.
 destruct a. destruct b.
 apply andb_true_iff in H0. destruct H0.
 apply aty_eqb_eq in H0. apply bty_eqb_eq in H1.
 subst. easy.
Qed.

Lemma ty_eqb_neq : forall a b, a =t= b = false -> a <> b.
Proof.
 intros. unfold ty_eq in H0.
 destruct a. destruct b.
 apply andb_false_iff in H0. destruct H0.
 apply aty_eqb_neq in H0. intros R. inv R. contradiction.
 apply bty_eqb_neq in H0. intros R. inv R. contradiction.
Qed.

Lemma ty_eq_reflect : forall r1 r2, reflect (r1 = r2) (ty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =t= r2) eqn:eq1.
  apply  ReflectT.
  apply ty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply ty_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve aty_eq_reflect bty_eq_reflect ty_eq_reflect : bdestruct.


Inductive factor := Var (v:var)
                 | Num (v:nat) (n:nat) (t:btype). (*a value is represented as a bool binary. *)

Inductive flag := QFTA | Classic.

(* the SSA form is to restrict non-loop instructions. x = y op z, 
    where we compute y op z and then we store the value into x, so if x is freshly defined, then x = y op z. 
    if one wants to use instructions in a loop, then use the qadd/qsub/qmul. *)
Inductive iexp := eplus (f:flag) (x : factor) (y: factor)
      | eminus (f:flag) (x:factor) (y:factor)
      | emult (f:flag) (x:factor) (y:factor)
      | ediv (f:flag) (x:factor) (y:factor)
      | emod (f:flag) (x:factor) (y:factor)
      | eload (v:var).

Inductive comexp := clt (f:flag) (x:factor) (y:factor)
                  | ceq (f:flag) (x:factor) (y:factor).

(* qadd/qsub/qmul has the property as x = y op x, which is corresponding to
   [y][x] -> [y][y op x] structure. *)
Inductive qexp := inst (v:var) (n:nat) (t:btype) (e:iexp)
                | qadd (f:flag) (v:factor) (x:var)
                | qsub (f:flag) (v:factor) (x:var)
                | qmul (f:flag) (v:factor) (x:var)
                | call (f:fvar) (l:list var)
                | qif (c:comexp) (e1:qexp) (e2:qexp)
                | qwhile (c:comexp) (e:qexp)
                | ret (l:list var)
                | qseq (q1:qexp) (q2:qexp).

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Definition func : Type := (fvar * qexp * list (nat * btype)).
    (* a function is a fun name, a starting block label, and a list of blocks. *)

Definition prog : Type := (nat * nat * nat * list (var * nat) * list func). 
   (* a program is a nat representing the stack size and number of loop limit in a while loop. a nat number 
    indicating the number of denominator for each fixed-pointer number, and a list of global vars, and a list of functions. *)


(* Define the well-formedness of exp. It is SSA + variable-dominance, as well as type match. *)
(* The following relation defines the SSA + variable dominance for expressions and instructions. *)
Inductive ssa_factor : list var -> factor -> Prop :=
   | ssa_jfactor : forall r x, In x r -> ssa_factor r (Var x)
   | ssa_cfactor_num : forall r n m t, ssa_factor r (Num n m t).

Inductive ssa_exp : list var -> iexp -> Prop := 
  | eplus_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eplus f x y)
  | eminus_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eminus f x y)
  | emult_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emult f x y)
  | ediv_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (ediv f x y)
  | emod_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emod f x y)
  | eload_ssa : forall r x, In x r -> ssa_exp r (eload x).

Inductive ssa_comexp : list var -> comexp -> Prop :=
     | ssa_clt : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_comexp r (clt f x y)
     | ssa_ceq : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_comexp r (ceq f x y).

Inductive ssa_inst : list var -> qexp -> list var -> Prop :=
   | ssa_assign : forall r x n t e, ~ In x r -> ssa_exp r e -> ssa_inst r (inst x n t e) (x::r)
   | ssa_add : forall r f x y, ssa_factor r x -> In y r -> ssa_inst r (qadd f x y) r
   | ssa_sub : forall r f x y, ssa_factor r x -> In y r -> ssa_inst r (qsub f x y) r
   | ssa_mul : forall r f x y, ssa_factor r x -> In y r -> ssa_inst r (qmul f x y) r
   | ssa_if : forall r r' r'' c e1 e2, ssa_comexp r c ->
                 ssa_inst r e1 r' -> ssa_inst r' e2 r'' -> ssa_inst r (qif c e1 e2) r''
   | ssa_while : forall r r' c e, ssa_comexp r c -> ssa_inst r e r' -> ssa_inst r (qwhile c e) r'
   | ssa_ret : forall r l, (forall a , In a l -> In a r) -> ssa_inst r (ret l) r
   | ssa_call : forall r f l, (forall a, In a l -> In a r) -> ssa_inst r (call f l) r
   | ssa_seq : forall r r' r'' e1 e2, ssa_inst r e1 r' -> ssa_inst r' e2 r'' -> ssa_inst r (qseq e1 e2) r''.

Inductive ssa_funs : list var -> list func -> list var -> Prop :=
   ssa_fun_empty : forall r, ssa_funs r [] r
  | ssa_fun_many : forall r r' r'' f e fs l, ssa_inst r e r' -> ssa_funs r' fs r'' -> ssa_funs r ((f,e,l)::fs) r''.


Inductive ssa_prog : prog -> Prop :=
  | ssa_top : forall n m i l l' fs, ssa_funs (fst (split l)) fs l' -> ssa_prog (n,m,i,l,fs).


(* The following relation defines the type system for expressions and instructions and functions. *)
Module BEnv := FMapList.Make Nat_as_OT.

Definition benv := BEnv.t typ.

Definition empty_benv := @BEnv.empty typ.

Module FTEnv := FMapList.Make Nat_as_OT.

Definition ftmenv := FTEnv.t (func).

Definition type_up_zero (t : atype) : Prop := 
   match t with (C n) => (0 < n)%nat
              | (Q n) => (0 < n)%nat
   end.

Definition asubtype (t1 t2: atype) : bool :=
   if aty_eq t1 t2 then true else
           (match t1 with C n => match t2 with Q m => n =? m
                                             | _ => false
                                 end
                         | _ => false
            end).

Inductive subtype : typ -> typ -> Prop :=
   subtype_ref : forall t, subtype t t
  | subtype_cq : forall n b, subtype (C n, b) (Q n, b).

Inductive type_factor (benv:benv) : typ -> factor -> Prop :=
     type_fac_var : forall t' t x, BEnv.MapsTo x t' benv -> subtype t' t -> type_factor benv t (Var x)
   | type_fac_nat : forall n m t' t, subtype (C m,t') t -> type_factor benv t (Num n m t').

Definition mat_cq (a:atype) (n:nat) : Prop :=
   match a with Q m => (n = m)
              | C m => (n = m)
   end.

Inductive type_iexp (gs:list var) (benv:benv) : typ -> iexp -> Prop :=
   type_plus:  forall t f x y, type_factor benv t x -> type_factor benv t y -> type_iexp gs benv t (eplus f x y)
  | type_minus:  forall t f x y, type_factor benv t x -> type_factor benv t y -> type_iexp gs benv t (eminus f x y)
  | type_mult:  forall a b f x y, type_factor benv (a,b) x -> type_factor benv (a,Nat) y -> type_iexp gs benv (a,b) (emult f x y)
  | type_div:  forall a n b f x y, type_factor benv (a,b) x -> mat_cq a n
                              -> type_factor benv (C n,Nat) y -> type_iexp gs benv (a,b) (ediv f x y)
  | type_mod:  forall a n b f x y, type_factor benv (a,b) x -> mat_cq a n
                                -> type_factor benv (C n,Nat) y -> type_iexp gs benv (a,b) (emod f x y)
  | type_load : forall n b t x, In x gs -> BEnv.MapsTo x (Q n, b) benv -> t = (Q n,b) -> type_iexp gs benv t (eload x).


Inductive type_cexp (gs:list var) (benv:benv) : typ -> comexp -> Prop :=
   type_clt : forall c n b f x y, type_factor benv (c n,b) x -> 
                     type_factor benv (c n,b) y -> type_cexp gs benv (c 1,b) (clt f x y)
  |  type_ceq : forall c n b f x y, type_factor benv (c n,b) x ->
                     type_factor benv (c n,b) y -> type_cexp gs benv (c 1,b) (ceq f x y).

Inductive type_qexp_h (fm:ftmenv) (fs:list var) (gs:list var): benv -> qexp -> Prop :=
 | htype_qadd : forall benv t f x y, type_factor benv t x -> BEnv.MapsTo y t benv -> type_qexp_h fm fs gs benv (qadd f x y)
 | htype_qsub : forall benv t f x y, type_factor benv t x ->  BEnv.MapsTo y t benv -> type_qexp_h fm fs gs benv (qsub f x y)
 | htype_qmul : forall benv a b f x y, type_factor benv (a,Nat) x ->  BEnv.MapsTo y (a,b) benv -> type_qexp_h fm fs gs benv (qmul f x y)
 | htype_call : forall benv f, In f fs -> type_qexp_h fm fs gs benv (call f)
 | htype_if : forall benv t ce e1 e2, type_cexp gs benv t ce -> type_qexp_h fm fs gs benv e1 ->
                     type_qexp_h fm fs gs benv e2 ->  type_qexp_h fm fs gs benv (qif ce e1 e2)
 | htype_while : forall benv t ce e, type_cexp gs benv t ce ->
                            type_qexp_h fm fs gs benv e -> type_qexp_h fm fs gs benv (qwhile ce e)
 | htype_ret : forall benv l, (forall x, In x l -> ~ In x gs) -> type_qexp_h fm fs gs benv (ret l)
 | htype_qseq : forall benv e1 e2, type_qexp_h fm fs gs benv e1 ->
                              type_qexp_h fm fs gs benv e2 -> type_qexp_h fm fs gs benv (qseq e1 e2).


Inductive type_qexp (fs:list var) (gs:list var): benv -> qexp -> benv -> Prop :=
   type_inst_cq: forall benv benv' c x n t e, type_iexp gs benv (c n,t) e -> ~ In x gs
                  -> BEnv.Equal benv' (BEnv.add x (c n,t) benv) -> type_qexp fs gs benv (inst x n t e) benv'
 | type_qadd : forall benv t f x y, type_factor benv t x -> BEnv.MapsTo y t benv -> type_qexp fs gs benv (qadd f x y) benv
 | type_qsub : forall benv t f x y, type_factor benv t x -> BEnv.MapsTo y t benv -> type_qexp fs gs benv (qsub f x y) benv
 | type_qmul : forall benv a b f x y, type_factor benv (a,Nat) x -> BEnv.MapsTo y (a,b) benv -> type_qexp fs gs benv (qmul f x y) benv
 | type_call : forall benv f, In f fs -> type_qexp fs gs benv (call f) benv
 | type_if : forall benv benv' benv'' t ce e1 e2, type_cexp gs benv t ce -> type_qexp fs gs benv e1 benv' ->
                     type_qexp fs gs benv' e2 benv'' ->  type_qexp fs gs benv (qif ce e1 e2) benv''
 | type_while : forall benv t ce e, type_cexp gs benv t ce ->
                            type_qexp_h fs gs benv e -> type_qexp fs gs benv (qwhile ce e) benv
 | type_ret : forall benv l, (forall x, In x l -> ~ In x gs) -> type_qexp fs gs benv (ret l) benv
 | type_qseq : forall benv benv' benv'' e1 e2, type_qexp fs gs benv e1 benv' ->
              type_qexp fs gs benv' e2 benv'' -> type_qexp fs gs benv (qseq e1 e2) benv''.

Inductive type_funs (gs:list var): benv -> list var -> list func -> list var -> Prop :=
   type_fun_empty : forall benv fs, type_funs gs benv fs [] fs
 | type_fun_many : forall benv benv' fs fs' f e l, ~ In f fs -> type_qexp fs gs benv e benv'
                -> type_funs gs benv fs l fs' -> type_funs gs benv fs ((f,e)::l) (f::fs').

Inductive gen_benv : benv -> list (var * nat) -> benv -> Prop := 
    gen_benv_empty : forall benv, gen_benv benv [] benv
  | gen_benv_many : forall benv benv' x n l, gen_benv benv l benv' -> gen_benv benv ((x,n)::l) (BEnv.add x (Q n,Nat) benv').

Inductive type_prog : prog -> Prop :=
  type_prog_t : forall n m i l fl benv fs, m <= n -> gen_benv empty_benv l benv ->
              type_funs (fst (split l)) benv [] fl fs -> type_prog (n,m,i,l,fl).



(*The semantics of QLLVM. *)

Module Reg := FMapList.Make Nat_as_OT.

Definition reg := Reg.t nat.

Module FEnv := FMapList.Make Nat_as_OT.

Definition fmenv := FEnv.t (func * benv).


Inductive sem_factor : reg -> factor -> nat -> Prop :=
   | sem_factor_var : forall r x n, Reg.MapsTo x n r -> sem_factor r (Var x) n
   | sem_factor_num : forall r m n t, sem_factor r (Num n m t) (n mod (2^m)).

Definition get_n (t:typ) := match t with (Q n,t) => n | (C n,t) => n end.

Inductive sem_iexp (M: fmenv) : reg -> typ -> iexp -> nat -> Prop :=
   | sem_eplus : forall r f x y n1 n2 t, sem_factor r x n1 -> sem_factor r y n2 ->
                           sem_iexp M r t (eplus f x y) ((n1+n2) mod (2^(get_n t)))
   | sem_eminus : forall r f x y n1 n2 t, sem_factor r x n1 -> sem_factor r y n2 ->
                           sem_iexp M r t (eminus f x y) (if n1 <? n2 then 2^(get_n t) + n2 - n1 else n1 - n2)
   | sem_emult : forall r f x y n1 n2 t, sem_factor r x n1 -> sem_factor r y n2 ->
                           sem_iexp M r t (emult f x y) ((n1*n2) mod (2^(get_n t))) 
   | sem_ediv : forall r f x y n1 n2 t, sem_factor r x n1 -> sem_factor r y n2 ->
                           sem_iexp M r t (ediv f x y) (n1/n2) 
   | sem_emod : forall r f x y n1 n2 t, sem_factor r x n1 -> sem_factor r y n2 ->
                           sem_iexp M r t (ediv f x y) (n1 mod n2) 
   | sem_eload : forall r x t v, Reg.MapsTo x v r -> sem_iexp M r t (eload x) (v mod (2^(get_n t))).

Inductive sem_cexp (M:fmenv) (benv:benv) : reg -> comexp -> bool -> Prop :=
    | sem_clt : forall r f x y t n1 n2, sem_factor r x n1 -> sem_factor r y n2 ->
                     type_factor benv t x -> type_factor benv t y ->
                           sem_cexp M benv r (clt f x y) ((n1 mod (2^(get_n t))) <? (n2 mod (2^ get_n t)))
    | sem_ceq : forall r f x y t n1 n2, sem_factor r x n1 -> sem_factor r y n2 ->
                     type_factor benv t x -> type_factor benv t y ->
                           sem_cexp M benv r (ceq f x y) ((n1 mod (2^(get_n t))) =? (n2 mod (2^ get_n t))).

Inductive sem_qexp (M: fmenv) (benv:benv) : reg -> qexp -> reg -> Prop :=
   | sem_inst : forall r x m e bt t n, BEnv.MapsTo x t benv -> sem_iexp M r t e n 
                 -> sem_qexp M benv r (inst x m bt e) (Reg.add x n r)
   | sem_qadd : forall r f x y t n1 n2, sem_factor r x n1 -> Reg.MapsTo y n2 r -> BEnv.MapsTo y t benv
                -> sem_qexp M benv r (qadd f x y) (Reg.add y ((n1 mod (2^(get_n t)))+(n2 mod (2^(get_n t))) mod (get_n t)) r)
   | sem_qsub : forall r f x y t n1 n2, sem_factor r x n1 -> Reg.MapsTo y n2 r -> BEnv.MapsTo y t benv
                -> sem_qexp M benv r (qadd f x y) (Reg.add y (if (n1 mod (2^(get_n t))) <? (n2 mod (2^(get_n t)))
                        then 2^(get_n t) + (n2 mod (2^(get_n t))) - (n1 mod (2^(get_n t)))
                 else (n1 mod (2^(get_n t))) - (n2 mod (2^(get_n t)))) r)
   | sem_times : forall r f x y t n1 n2, sem_factor r x n1 -> Reg.MapsTo y n2 r -> BEnv.MapsTo y t benv
                -> sem_qexp M benv r (qmul f x y) (Reg.add y ((n1 mod (2^(get_n t)))*(n2 mod (2^(get_n t))) mod (get_n t)) r)
   | sem_call :  forall r f x y t n1 n2, FEnv.MapsTo f (e,benv') -> 
                         sem_qexp M benv' r e r' -> 
                -> sem_qexp M benv r (call f) (Reg.add y ((n1 mod (2^(get_n t)))*(n2 mod (2^(get_n t))) mod (get_n t)) r)

with sem_func (M:fmenv) (benv:benv) (endr :reg) : qexp -> Prop :=
   sem_fun_rule : forall e r r', sem_qexp M benv r e r' -> sem_func M benv endr e.




Inductive comexp := clt (f:flag) (x:factor) (y:factor)
                  | ceq (f:flag) (x:factor) (y:factor).

(* qadd/qsub/qmul has the property as x = y op x, which is corresponding to
   [y][x] -> [y][y op x] structure. *)
Inductive qexp := inst (v:var) (n:nat) (t:btype) (e:iexp)
                | qadd (f:flag) (v:factor) (x:var)
                | qsub (f:flag) (v:factor) (x:var)
                | qmul (f:flag) (v:factor) (x:var)
                | call (f:fvar)
                | qif (c:comexp) (e1:qexp) (e2:qexp)
                | qwhile (c:comexp) (e:qexp)
                | ret (l:list (var * var))
                | qseq (q1:qexp) (q2:qexp).


Inductive comexp := clt (f:flag) (x:factor) (y:factor)
                  | ceq (f:flag) (x:factor) (y:factor).

(* qadd/qsub/qmul has the property as x = y op x, which is corresponding to
   [y][x] -> [y][y op x] structure. *)
Inductive qexp := inst (v:var) (n:nat) (t:btype) (e:iexp)
                | qadd (f:flag) (v:factor) (x:factor)
                | qsub (f:flag) (v:factor) (x:factor)
                | qmul (f:flag) (v:factor) (x:factor)
                | call (f:fvar)
                | qif (c:comexp) (e1:qexp) (e2:qexp)
                | qwhile (c:comexp) (e:qexp)
                | ret (l:list (var * var))
                | qseq (q1:qexp) (q2:qexp).




(*
Definition x := 1.

Definition y := 2.

Definition z := 3.

Definition s := 4.

Definition c1 := 5.

Definition c2 := 6.

Definition csplit (p : exp) :=
  match p with
  | SKIP => SKIP
  | X n => X n
  | RZ q p => RZ q p
  | RRZ q p => RRZ q p
  | Lshift x => Lshift x
  | Rshift x => Rshift x
  | CU n (p1; p2) => CU n p1; CU n p2
  | CU n p => CU n p
  | p1; p2 => p1; p2
  end.

Fixpoint csplit_pexp (p : pexp) :=
  match p with
  | Exp s => Exp (csplit s)
  | FSeq e1 e2 => FSeq (csplit_pexp e1) (csplit_pexp e2)
  | p => p
  end.

Fixpoint bcelim p :=
  match p with
  | SKIP => SKIP
  | X q => X q
  | RZ q p => RZ q p
  | RRZ q p => RRZ q p
  | Lshift x => Lshift x
  | Rshift x => Rshift x
  | CU q p => match bcelim p with
                 | SKIP => SKIP
                 | p' => CU q p'
                 end
  | Seq p1 p2 => match bcelim p1, bcelim p2 with
                  | SKIP, p2' => p2'
                  | p1', SKIP => p1'
                  | p1', p2' => Seq p1' p2'
                  end
  end.

Fixpoint bcelim_pexp p :=
   match p with 
     | Exp s => Exp (bcelim s)
     | FSeq e1 e2 => match bcelim_pexp e1, bcelim_pexp e2 with
                           |  Exp SKIP, e2' => e2'
                           | e1', Exp SKIP => e1'
                           | e1',e2' => e1' ;; e2'
                     end
     | e => e
   end.

Definition modmult_vars (n:nat) := cons (x,n,SType) (cons (y,n,NType) (cons (z,n,NType)
                               (cons (s,n,NType) (cons (c1,1,NType) (cons (c2,1,NType) []))))).

Definition modmult_var_fun (n:nat) := compile_var (modmult_vars n).

Definition modmult_sqir M C Cinv n := trans_pexp (modmult_var_fun n)
            (get_dim (modmult_vars n)) (csplit_pexp (bcelim_pexp(modmult_rev (nat2fb M) C Cinv n x y z s (c1,0) (c2,0)))).

Definition f_modmult_circuit a ainv N n := fun i => modmult_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.

Definition rz_mod_vars (n:nat) := cons (x,n,NType) (cons (y,n,NType) (cons (c1,1,NType) [])).

Definition rz_var_fun (n:nat) := compile_var (rz_mod_vars n).

Definition rz_mod_sqir M C Cinv n := trans_pexp (rz_var_fun n)
            (get_dim (rz_mod_vars n)) (csplit_pexp (bcelim_pexp (rz_modmult_full x y n (c1,0) (nat2fb C) (nat2fb Cinv) (nat2fb M)))).

Definition rz_f_modmult_circuit a ainv N n := fun i => 
                            rz_mod_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.

*)
