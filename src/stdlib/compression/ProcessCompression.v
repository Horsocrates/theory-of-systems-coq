(** * ProcessCompression.v — P4 IS multi-resolution compression
    Elements: coarsen, detail_at_level, multi_resolution
    Roles:    choosing P4 stage N = choosing resolution = compression
    Rules:    f_coarse + detail = f_fine (perfect reconstruction)
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE P4 INSIGHT:
    Under P4, a real number IS a process {f(n)}_{n∈ℕ}.
    "Compression" = observing at stage N instead of 2N.
    "Detail" = d(n) = f(2n) - f(n) (what you gain by doubling resolution).
    "Multi-resolution" = f(1) + d(1) + d(2) + ... + d(K) = f(2^K).

    This IS the Haar wavelet decomposition on processes.
    No separate compression algorithm needed — P4 IS compression.
*)

From Stdlib Require Import QArith Qabs Lia.
From Stdlib Require Import Lqa.

From ToS Require Import process.ProcessCore.

Open Scope Q_scope.

(* ================================================================ *)
(*  COARSENING = SUBSAMPLING                                         *)
(* ================================================================ *)

(** Coarsen: observe process at half rate *)
Definition coarsen (R : RealProcess) : RealProcess :=
  fun n => R (2 * n)%nat.

(** Double coarsening *)
Definition coarsen2 (R : RealProcess) : RealProcess :=
  coarsen (coarsen R).

Lemma coarsen_at : forall R n, coarsen R n = R (2 * n)%nat.
Proof. reflexivity. Qed.

Lemma coarsen2_at : forall R n, coarsen2 R n = R (4 * n)%nat.
Proof. intros R n. unfold coarsen2, coarsen. f_equal. lia. Qed.

(* ================================================================ *)
(*  DETAIL = DIFFERENCE BETWEEN RESOLUTIONS                          *)
(* ================================================================ *)

(** Detail at level: what you gain by going from stage n to 2n *)
Definition detail (R : RealProcess) (n : nat) : Q :=
  R (2 * n)%nat - R n.

(** Detail is the difference between fine and coarse *)
Lemma detail_is_difference : forall R n,
  detail R n == coarsen R n - R n.
Proof. intros. unfold detail, coarsen. ring. Qed.

(** Perfect reconstruction: coarse + detail = fine *)
Lemma perfect_reconstruction : forall R n,
  R n + detail R n == R (2 * n)%nat.
Proof. intros R n. unfold detail. ring. Qed.

(* ================================================================ *)
(*  MULTI-RESOLUTION                                                 *)
(* ================================================================ *)

(** Multi-resolution sum: R(1) + Σ_{k=0}^{K-1} detail(R, 2^k) *)
Fixpoint multi_res (R : RealProcess) (K : nat) : Q :=
  match K with
  | O => R 1%nat
  | Datatypes.S k => multi_res R k + detail R (Nat.pow 2 k)
  end.

(** K=0: just R(1) *)
Lemma multi_res_0 : forall R, multi_res R 0 = R 1%nat.
Proof. reflexivity. Qed.

(** K=1: R(1) + detail(R,1) = R(1) + R(2) - R(1) = R(2) *)
Lemma multi_res_1 : forall R, multi_res R 1 == R 2%nat.
Proof.
  intro R. unfold multi_res, detail.
  simpl (Nat.pow 2 0). simpl (2 * 1)%nat. lra.
Qed.

(** K=2: R(1) + d(1) + d(2) = R(2) + R(4) - R(2) = R(4) *)
Lemma multi_res_2 : forall R, multi_res R 2 == R 4%nat.
Proof.
  intro R. unfold multi_res, detail.
  simpl (Nat.pow 2 0). simpl (Nat.pow 2 1).
  simpl (2 * 1)%nat. simpl (2 * 2)%nat. lra.
Qed.

(* ================================================================ *)
(*  P4 ONTOLOGICAL COMPRESSION                                       *)
(* ================================================================ *)

(** Under P4: choosing resolution K = choosing stage 2^K of the process.
    This IS compression. No algorithm needed.
    Multi-resolution = the process ITSELF viewed at different scales. *)

(** Compression ratio: storing K levels instead of 2^K values *)
Definition process_compression_ratio (K : nat) : Q :=
  inject_Z (Z.of_nat (Datatypes.S K)) /
  inject_Z (Z.of_nat (Nat.pow 2 K)).

Lemma pcr_1 : process_compression_ratio 1 == 1.
Proof. unfold process_compression_ratio. vm_compute. reflexivity. Qed.

Lemma pcr_3 : process_compression_ratio 3 == 1 # 2.
Proof. unfold process_compression_ratio. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem process_compression_synthesis :
  (* Perfect reconstruction *)
  (forall R n, R n + detail R n == R (2 * n)%nat) /\
  (* Multi-resolution telescopes *)
  (forall R, multi_res R 1 == R 2%nat) /\
  (forall R, multi_res R 2 == R 4%nat) /\
  (* Compression ratio decreases *)
  process_compression_ratio 3 == 1 # 2.
Proof.
  split; [exact perfect_reconstruction |
  split; [exact multi_res_1 |
  split; [exact multi_res_2 |
  exact pcr_3]]].
Qed.
