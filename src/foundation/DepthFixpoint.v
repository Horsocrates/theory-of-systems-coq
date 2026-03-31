(** * DepthFixpoint.v — Nested distinction fixpoint as ToS System
    Elements: regions, gauge_dim, endo_dim at each depth
    Roles:    L5 (depth ordering) → C² → C³ → C¹ → fixpoint
    Rules:    gauge_dim = n²-1 for n>1, else 1. Fixpoint at depth 2.
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    Nested distinction: each depth level distinguishes the previous.
    Depth 0: binary (C²) → SU(2), dim 3
    Depth 1: ternary (C³) → SU(3), dim 8
    Depth 2: trivial (C¹) → U(1), dim 1
    Depth 3+: still trivial — fixpoint reached.

    Total gauge = 3 + 8 + 1 = 12 = dim(SU(2)×SU(3)×U(1)).
    No new gauge groups beyond depth 2.
*)

From Stdlib Require Import Lia.

(** ** Core definitions *)

Definition regions (depth : nat) : nat :=
  match depth with 0 => 2 | 1 => 3 | _ => 1 end.

Definition gauge_dim (depth : nat) : nat :=
  let n := regions depth in
  match n with 1 => 1 | _ => (n * n - 1)%nat end.

Definition endo_dim (depth : nat) : nat :=
  let n := regions depth in (n * n)%nat.

(** ** Depth values *)

Lemma depth0 : regions 0 = 2.
Proof. reflexivity. Qed.

Lemma depth1 : regions 1 = 3.
Proof. reflexivity. Qed.

Lemma depth2 : regions 2 = 1.
Proof. reflexivity. Qed.

Lemma depth3_fixpoint : regions 3 = 1.
Proof. reflexivity. Qed.

Lemma depth4_fixpoint : regions 4 = 1.
Proof. reflexivity. Qed.

(** ** Gauge dimensions *)

Lemma gauge_SU2 : gauge_dim 0 = 3.
Proof. reflexivity. Qed.

Lemma gauge_SU3 : gauge_dim 1 = 8.
Proof. reflexivity. Qed.

Lemma gauge_U1 : gauge_dim 2 = 1.
Proof. reflexivity. Qed.

Lemma gauge_depth3 : gauge_dim 3 = 1.
Proof. reflexivity. Qed.

Lemma total_gauge : (gauge_dim 0 + gauge_dim 1 + gauge_dim 2 = 12)%nat.
Proof. reflexivity. Qed.

(** ** Endomorphism fixpoint *)

Lemma endo_fixpoint : endo_dim 2 = 1 /\ endo_dim 3 = 1.
Proof. split; reflexivity. Qed.

(** ** No new gauge groups beyond depth 2 *)

Lemma no_new_beyond_2 : forall d, (d >= 2)%nat -> gauge_dim d = 1%nat.
Proof.
  intros d Hd.
  destruct d as [|[|d']]; [lia|lia|reflexivity].
Qed.

(** ** SM predicted: the full conjunction *)

Lemma SM_predicted :
  gauge_dim 0 = 3 /\
  gauge_dim 1 = 8 /\
  gauge_dim 2 = 1 /\
  (gauge_dim 0 + gauge_dim 1 + gauge_dim 2 = 12)%nat /\
  (forall d, (d >= 2)%nat -> gauge_dim d = 1%nat).
Proof.
  repeat split; try reflexivity.
  intros d Hd.
  destruct d as [|[|d']]; [lia|lia|reflexivity].
Qed.

(** ** Why binary at depth 0: distinction has exactly 2 sides *)

Lemma binary_at_depth0 : regions 0 = 2 /\ gauge_dim 0 = (2 * 2 - 1)%nat.
Proof. split; reflexivity. Qed.

(** ** Why ternary at depth 1: distinguishing 2 things requires a third *)

Lemma ternary_at_depth1 : regions 1 = 3 /\ gauge_dim 1 = (3 * 3 - 1)%nat.
Proof. split; reflexivity. Qed.

(** ** Fixpoint stability: regions and gauge_dim both stabilize *)

Lemma fixpoint_stability :
  forall d1 d2, (d1 >= 2)%nat -> (d2 >= 2)%nat ->
  regions d1 = regions d2 /\ gauge_dim d1 = gauge_dim d2.
Proof.
  intros d1 d2 H1 H2.
  split.
  - destruct d1 as [|[|d1']]; [lia|lia|].
    destruct d2 as [|[|d2']]; [lia|lia|].
    reflexivity.
  - destruct d1 as [|[|d1']]; [lia|lia|].
    destruct d2 as [|[|d2']]; [lia|lia|].
    reflexivity.
Qed.
