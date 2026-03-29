(* ========================================================================= *)
(*  L1_DoublyStochastic.v                                                    *)
(*                                                                           *)
(*  L1 (no site privileged) -> uniform stationary -> doubly stochastic.      *)
(*                                                                           *)
(*  E/R/R: Elements = matrix entries; Roles = row/col stochastic;            *)
(*         Rules = stationary condition pi*T = pi.                           *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Matrix as function ---- *)
Definition Mat := nat -> nat -> Q.

(* ---- Row and column sums via fold_left ---- *)
Definition row_sum (T : Mat) (N : nat) (i : nat) : Q :=
  fold_left (fun acc j => acc + T i j) (seq 0 N) 0.

Definition col_sum (T : Mat) (N : nat) (j : nat) : Q :=
  fold_left (fun acc i => acc + T i j) (seq 0 N) 0.

(* ---- Stochasticity predicates ---- *)
Definition row_stochastic (T : Mat) (N : nat) : Prop :=
  forall i, (i < N)%nat -> row_sum T N i == 1.

Definition col_stochastic (T : Mat) (N : nat) : Prop :=
  forall j, (j < N)%nat -> col_sum T N j == 1.

Definition doubly_stochastic (T : Mat) (N : nat) : Prop :=
  row_stochastic T N /\ col_stochastic T N.

(* ---- Uniform distribution ---- *)
Definition uniform (N : nat) (i : nat) : Q := 1 / inject_Z (Z.of_nat N).

(* ---- Stationary condition: pi * T = pi ---- *)
Definition is_stationary (pi : nat -> Q) (T : Mat) (N : nat) : Prop :=
  forall j, (j < N)%nat ->
    fold_left (fun acc i => acc + pi i * T i j) (seq 0 N) 0 == pi j.

(* ======================================================================= *)
(*  Fold helpers                                                            *)
(* ======================================================================= *)

(* Scalar factoring out of fold_left *)
Lemma fold_left_scalar :
  forall (f : nat -> Q) (c : Q) (n : nat),
    fold_left (fun acc i => acc + c * f i) (seq 0 n) 0 ==
    c * fold_left (fun acc i => acc + f i) (seq 0 n) 0.
Proof.
  intros f c n.
  enough (H : forall m k init1 init2,
    init1 == c * init2 ->
    fold_left (fun acc i => acc + c * f i) (seq k m) init1 ==
    c * fold_left (fun acc i => acc + f i) (seq k m) init2).
  { apply H. ring. }
  induction m as [|m IH]; intros k init1 init2 Hinit; simpl.
  - exact Hinit.
  - apply IH. rewrite Hinit. ring.
Qed.

(* Cancellation: c * x == c * y with c <> 0 implies x == y *)
Lemma Qmult_cancel_l : forall c x y : Q,
  ~ c == 0 -> c * x == c * y -> x == y.
Proof.
  intros c x y Hc H.
  assert (Hic : /c * (c * x) == /c * (c * y)).
  { rewrite H. reflexivity. }
  setoid_rewrite Qmult_assoc in Hic.
  assert (Hcr : c * /c == 1) by (apply Qmult_inv_r; exact Hc).
  assert (Hcl : /c * c == 1).
  { setoid_rewrite Qmult_comm. exact Hcr. }
  setoid_rewrite Hcl in Hic.
  lra.
Qed.

(* ======================================================================= *)
(*  MAIN THEOREM (general N > 0)                                            *)
(*  row_stochastic + uniform stationary -> col_stochastic                   *)
(* ======================================================================= *)

Theorem L1_doubly_stochastic : forall (T : Mat) (N : nat),
  (N > 0)%nat ->
  row_stochastic T N ->
  is_stationary (uniform N) T N ->
  col_stochastic T N.
Proof.
  intros T N HN Hrow Hstat j Hj.
  specialize (Hstat j Hj).
  unfold uniform in Hstat.
  unfold col_sum.
  rewrite fold_left_scalar in Hstat.
  apply Qmult_cancel_l with (1 / inject_Z (Z.of_nat N)).
  - intro Habs.
    assert (Hpos : 0 < inject_Z (Z.of_nat N)).
    { unfold Qlt. simpl. lia. }
    assert (Hpos2 : 0 < 1 / inject_Z (Z.of_nat N)).
    { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hpos. }
    lra.
  - setoid_rewrite Qmult_1_r. exact Hstat.
Qed.

(* ---- Corollary: combined doubly_stochastic statement ---- *)
Theorem L1_implies_DS : forall (T : Mat) (N : nat),
  (N > 0)%nat ->
  row_stochastic T N ->
  is_stationary (uniform N) T N ->
  doubly_stochastic T N.
Proof.
  intros T N HN Hrow Hstat.
  split.
  - exact Hrow.
  - exact (L1_doubly_stochastic T N HN Hrow Hstat).
Qed.

(* ======================================================================= *)
(*  Concrete N=2 and N=3 corollaries                                        *)
(* ======================================================================= *)

Lemma L1_doubly_stochastic_2 : forall T : Mat,
  row_stochastic T 2 ->
  is_stationary (uniform 2) T 2 ->
  col_stochastic T 2.
Proof.
  intros T Hrow Hstat.
  exact (L1_doubly_stochastic T 2 ltac:(lia) Hrow Hstat).
Qed.

Lemma L1_doubly_stochastic_3 : forall T : Mat,
  row_stochastic T 3 ->
  is_stationary (uniform 3) T 3 ->
  col_stochastic T 3.
Proof.
  intros T Hrow Hstat.
  exact (L1_doubly_stochastic T 3 ltac:(lia) Hrow Hstat).
Qed.

(* ======================================================================= *)
(*  Concrete examples: 2x2 complete graph                                   *)
(* ======================================================================= *)

Definition T_2x2 (i j : nat) : Q := 1#2.

Lemma T_2x2_row_stochastic : row_stochastic T_2x2 2.
Proof.
  intros i Hi. unfold row_sum, T_2x2. simpl. ring.
Qed.

Lemma T_2x2_uniform_stationary : is_stationary (uniform 2) T_2x2 2.
Proof.
  intros j Hj. unfold uniform, T_2x2. simpl. ring.
Qed.

Lemma T_2x2_col_stochastic : col_stochastic T_2x2 2.
Proof.
  intros j Hj. unfold col_sum, T_2x2. simpl. ring.
Qed.

Lemma T_2x2_doubly_stochastic : doubly_stochastic T_2x2 2.
Proof.
  split; [exact T_2x2_row_stochastic | exact T_2x2_col_stochastic].
Qed.

Corollary L1_implies_DS_2x2 : doubly_stochastic T_2x2 2.
Proof.
  apply L1_implies_DS; [lia | exact T_2x2_row_stochastic | exact T_2x2_uniform_stationary].
Qed.

(* ======================================================================= *)
(*  Concrete examples: 3x3 complete graph                                   *)
(* ======================================================================= *)

Definition T_3x3 (i j : nat) : Q := 1#3.

Lemma T_3x3_row_stochastic : row_stochastic T_3x3 3.
Proof.
  intros i Hi. unfold row_sum, T_3x3. simpl. ring.
Qed.

Lemma T_3x3_uniform_stationary : is_stationary (uniform 3) T_3x3 3.
Proof.
  intros j Hj. unfold uniform, T_3x3. simpl. ring.
Qed.

Lemma T_3x3_col_stochastic : col_stochastic T_3x3 3.
Proof.
  intros j Hj. unfold col_sum, T_3x3. simpl. ring.
Qed.

Lemma T_3x3_doubly_stochastic : doubly_stochastic T_3x3 3.
Proof.
  split; [exact T_3x3_row_stochastic | exact T_3x3_col_stochastic].
Qed.

Corollary L1_implies_DS_3x3 : doubly_stochastic T_3x3 3.
Proof.
  apply L1_implies_DS; [lia | exact T_3x3_row_stochastic | exact T_3x3_uniform_stationary].
Qed.

(* ======================================================================= *)
(*  Symmetric 2x2: [[a, 1-a],[1-a, a]]                                     *)
(* ======================================================================= *)

Definition T_sym (a : Q) (i j : nat) : Q :=
  match i, j with
  | O, O => a
  | O, S O => 1 - a
  | S O, O => 1 - a
  | S O, S O => a
  | _, _ => 0
  end.

Lemma T_sym_row_stochastic : forall a, row_stochastic (T_sym a) 2.
Proof.
  intros a i Hi. unfold row_sum. simpl.
  destruct i as [|[|n]]; simpl; try ring; lia.
Qed.

Lemma T_sym_uniform_stationary : forall a,
  is_stationary (uniform 2) (T_sym a) 2.
Proof.
  intros a j Hj. unfold uniform. simpl.
  destruct j as [|[|n]]; simpl; try ring; lia.
Qed.

Lemma T_sym_col_stochastic : forall a, col_stochastic (T_sym a) 2.
Proof.
  intros a j Hj. unfold col_sum. simpl.
  destruct j as [|[|n]]; simpl; try ring; lia.
Qed.

Lemma T_sym_doubly_stochastic : forall a, doubly_stochastic (T_sym a) 2.
Proof.
  intro a. split; [exact (T_sym_row_stochastic a) | exact (T_sym_col_stochastic a)].
Qed.

(* ======================================================================= *)
(*  Counterexample: asymmetric [[9/10, 1/10],[3/10, 7/10]]                 *)
(* ======================================================================= *)

Definition T_asym (i j : nat) : Q :=
  match i, j with
  | O, O => 9#10
  | O, S O => 1#10
  | S O, O => 3#10
  | S O, S O => 7#10
  | _, _ => 0
  end.

Lemma T_asym_row_stochastic : row_stochastic T_asym 2.
Proof.
  intros i Hi. unfold row_sum, T_asym. simpl.
  destruct i as [|[|n]]; simpl; try ring; lia.
Qed.

Lemma T_asym_not_col_stochastic : ~ col_stochastic T_asym 2.
Proof.
  intro H. specialize (H 0%nat ltac:(lia)).
  unfold col_sum, T_asym in H. simpl in H.
  lra.
Qed.
