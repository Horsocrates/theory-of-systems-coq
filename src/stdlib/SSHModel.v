(** * SSHModel.v — Su-Schrieffer-Heeger Model
    Elements: Hopping parameters v (intra) and w (inter), winding number
    Roles:    SSH topological classification: v < w → topological
    Rules:    ssh_topological v w = (v < w); edge states when topological
    Status:   Stdlib — Six Directions Phase 2, Section F6
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Bool.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: SSH TOPOLOGICAL CLASSIFICATION                             *)
(*  v = intracell hopping, w = intercell hopping                      *)
(*  Topological phase: v < w (winding number = 1)                     *)
(*  Trivial phase: v > w (winding number = 0)                         *)
(* ================================================================== *)

Definition ssh_topological (v w : Q) : bool :=
  match Qnum (w - v) with
  | Zpos _ => true
  | _ => false
  end.

Lemma ssh_topo_half_one : ssh_topological (1#2) 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ssh_trivial_one_half : ssh_topological 1 (1#2) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma ssh_critical_equal : ssh_topological 1 1 = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART II: SSH GAP                                                    *)
(*  gap = 2|v - w|; closes at v = w (phase transition)                *)
(* ================================================================== *)

Definition ssh_gap (v w : Q) : Q := 2 * Qabs (v - w).

Lemma ssh_gap_half_one : ssh_gap (1#2) 1 == 1.
Proof.
  unfold ssh_gap.
  assert (H : (1#2) - 1 == -(1#2)) by ring.
  rewrite H. unfold Qabs. simpl. ring.
Qed.

Lemma ssh_gap_one_half : ssh_gap 1 (1#2) == 1.
Proof.
  unfold ssh_gap.
  assert (H : 1 - (1#2) == 1#2) by ring.
  rewrite H. unfold Qabs. simpl. ring.
Qed.

Lemma ssh_gap_closes : ssh_gap 1 1 == 0.
Proof.
  unfold ssh_gap.
  assert (H : 1 - 1 == 0) by ring.
  rewrite H. unfold Qabs. simpl. ring.
Qed.

(* ================================================================== *)
(*  PART III: WINDING NUMBER                                            *)
(*  winding = 1 if topological, 0 otherwise                          *)
(* ================================================================== *)

Definition winding_number (v w : Q) : nat :=
  if ssh_topological v w then 1%nat else 0%nat.

Lemma winding_topo : winding_number (1#2) 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma winding_trivial : winding_number 1 (1#2) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: SSH AS CLASSICAL-QUANTUM TRANSITION                       *)
(*  SSH = M(epsilon) — the measurement process                        *)
(*  v > w: classical (trivial), v < w: quantum (topological)         *)
(* ================================================================== *)

Lemma ssh_gap_symmetric :
  ssh_gap (1#2) 1 == ssh_gap 1 (1#2).
Proof.
  assert (H1 : ssh_gap (1#2) 1 == 1) by exact ssh_gap_half_one.
  assert (H2 : ssh_gap 1 (1#2) == 1) by exact ssh_gap_one_half.
  rewrite H1, H2. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem ssh_model_synthesis :
  ssh_topological (1#2) 1 = true /\
  ssh_topological 1 (1#2) = false /\
  ssh_gap (1#2) 1 == 1 /\
  ssh_gap 1 1 == 0 /\
  winding_number (1#2) 1 = 1%nat.
Proof.
  split; [exact ssh_topo_half_one|].
  split; [exact ssh_trivial_one_half|].
  split; [exact ssh_gap_half_one|].
  split; [exact ssh_gap_closes|].
  exact winding_topo.
Qed.
