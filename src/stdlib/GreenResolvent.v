(** * GreenResolvent.v -- Resolvent (I - zM)^{-1} via characteristic polynomial
    Elements: resolvent_det, R_00_golden
    Roles:    Resolvent = generating function of Green's functions
    Rules:    det(I - zM) = 1 - z*tr(M) + z^2*det(M); poles = eigenvalues
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.GreenSpectral.

Open Scope Q_scope.

(* ================================================================== *)
(*  RESOLVENT DETERMINANT                                              *)
(* ================================================================== *)

(** det(I - zM) = 1 - z*trace(M) + z^2*det(M) *)
Definition resolvent_det (M : Mat2) (z : Q) : Q :=
  1 - z * char_p M + z * z * char_q M.

(** Golden: det(I - zM) = 1 - z - z^2 *)
Lemma resolvent_det_golden :
  forall z, resolvent_det golden z == 1 - z - z * z.
Proof.
  intro z.
  unfold resolvent_det.
  assert (Hp : char_p golden == 1) by (exact golden_char_p).
  assert (Hq : char_q golden == -(1)) by (exact golden_char_q).
  rewrite Hp, Hq. ring.
Qed.

(** At z=0: resolvent_det = 1 (identity) *)
Lemma resolvent_det_golden_0 : resolvent_det golden 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** At z=1: resolvent_det = -1 *)
Lemma resolvent_det_golden_1 : resolvent_det golden 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

(** At z=1/2: resolvent_det = 1/4 *)
Lemma resolvent_det_golden_half : resolvent_det golden (1#2) == (1#4).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FULL SHIFT RESOLVENT                                               *)
(* ================================================================== *)

(** Full shift: det(I - zM) = 1 - 2z (det=0 kills z^2 term) *)
Lemma resolvent_det_full :
  forall z, resolvent_det full_mat2 z == 1 - 2 * z.
Proof.
  intro z.
  unfold resolvent_det.
  assert (Hp : char_p full_mat2 == 2) by (exact full_char_p).
  assert (Hq : char_q full_mat2 == 0) by (exact full_char_q).
  rewrite Hp, Hq. ring.
Qed.

Lemma resolvent_det_full_0 : resolvent_det full_mat2 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma resolvent_det_full_half : resolvent_det full_mat2 (1#2) == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RESOLVENT AT SPECIFIC Z VALUES                                     *)
(* ================================================================== *)

(** z=1/3: golden resolvent det = 5/9 *)
Lemma resolvent_det_golden_third : resolvent_det golden (1#3) == (5#9).
Proof. vm_compute. reflexivity. Qed.

(** z=-1: golden resolvent det = 1 *)
Lemma resolvent_det_golden_neg1 : resolvent_det golden (-(1)) == 1.
Proof. vm_compute. reflexivity. Qed.

(** z=2: golden resolvent det = -5 *)
Lemma resolvent_det_golden_2 : resolvent_det golden 2 == -(5).
Proof. vm_compute. reflexivity. Qed.

(** z=1/4: golden resolvent det *)
Lemma resolvent_det_golden_quarter : resolvent_det golden (1#4) == (11#16).
Proof. vm_compute. reflexivity. Qed.

(** Full shift at z=1/4 *)
Lemma resolvent_det_full_quarter : resolvent_det full_mat2 (1#4) == (1#2).
Proof. vm_compute. reflexivity. Qed.

(** Full shift at z=1 *)
Lemma resolvent_det_full_1 : resolvent_det full_mat2 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GENERAL Z=0 PROPERTY                                               *)
(* ================================================================== *)

Lemma resolvent_det_at_zero : forall M, resolvent_det M 0 == 1.
Proof.
  intro M. unfold resolvent_det, char_p, char_q. ring.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem resolvent_synthesis :
  (* Resolvent det at z=0 is always 1 *)
  (forall M, resolvent_det M 0 == 1) /\
  (* Golden: 1 - z - z^2 *)
  resolvent_det golden 1 == -(1) /\
  (* Full: pole at z=1/2 *)
  resolvent_det full_mat2 (1#2) == 0 /\
  (* Golden: no pole at z=-1 *)
  resolvent_det golden (-(1)) == 1.
Proof.
  split; [exact resolvent_det_at_zero|].
  split; [exact resolvent_det_golden_1|].
  split; [exact resolvent_det_full_half|exact resolvent_det_golden_neg1].
Qed.
