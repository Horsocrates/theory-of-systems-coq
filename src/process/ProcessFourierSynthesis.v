(** * ProcessFourierSynthesis.v — Synthesis of the Walsh–Fourier cluster (Part VII):
      the rational Fourier transform is orthogonal, energy-preserving, invertible,
      and compresses within its energy

    Elements: ±1 matrix `had`; transform op_apply; inner product seq_inner; sums over ℚ
    Roles:    each file is a role in the Walsh–Fourier picture; this file composes them
    Rules:    orthogonality (HᵀH=N·I) → energy (‖Hf‖²=N‖f‖²) → invertibility (H(Hf)=N·f)
              → compression (captured ≤ ‖Hf‖²)

    Ties the Part VII cluster (ProcessWalshHadamard, ProcessFourierON,
    ProcessFourierCompression) into one constructive picture and verifies the bricks
    co-compile. Three bridges: the Walsh transform is (1) orthogonal AND
    energy-preserving, (2) invertible (Fourier inversion up to 1/N), (3) compresses
    within its energy (captured energy of any K coefficients ≤ ‖Hf‖²). All 0 axioms.

    HONEST FRONTIER (shared): the unitary 1/√N normalisation (rational only for N a
    square), the complex DFT (roots of unity, i), and the continuous Fourier transform
    need transcendentals — role-limits.

    ============ E/R/R разбор ============
      Rules (L5): ортогональность→энергия→обратимость→сжатие; три моста.
      Roles (L4): каждый файл = роль; синтез = роль-композиция.
      Elements  : общий субстрат `had`, op_apply, seq_inner над ℚ (L1+P4).
    ДИАГНОСТИКА: кластер процессно-конечен, 0 акс; 1/√N, комплексный DFT — роль-предел.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessCompactSpectral.    (* seq_inner *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessWalshHadamard.       (* had, pow2, hadamard_orthogonal *)
From ToS Require Import process.ProcessFourierON.           (* walsh_HH, parseval_walsh *)
From ToS Require Import process.ProcessFourierCompression.  (* captured, walsh_captured_le_energy *)

Open Scope Q_scope.

(** Bridge 1: the Walsh transform is orthogonal AND energy-preserving. *)
Theorem walsh_orthogonal_and_plancherel : forall k,
  (forall i i', (i < pow2 k)%nat -> (i' < pow2 k)%nat ->
     q_sum (fun j => had k i j * had k i' j) (pow2 k)
     == (if Nat.eqb i i' then inject_Z (Z.of_nat (pow2 k)) else 0))
  /\ (forall f,
     seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k)
     == inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k)).
Proof.
  intro k. split.
  - exact (hadamard_orthogonal k).
  - exact (parseval_walsh k).
Qed.

(** Bridge 2: the Walsh transform is invertible (applying it twice rescales by N). *)
Theorem walsh_invertible : forall k f m,
  (m < pow2 k)%nat ->
  op_apply (had k) (op_apply (had k) f (pow2 k)) (pow2 k) m
  == inject_Z (Z.of_nat (pow2 k)) * f m.
Proof. exact walsh_HH. Qed.

(** Bridge 3: compression keeps energy within the transform's total energy ‖Hf‖². *)
Theorem walsh_compression_within_energy : forall k f K,
  (K <= pow2 k)%nat ->
  captured (op_apply (had k) f (pow2 k)) K
  <= seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k).
Proof.
  intros k f K HK.
  rewrite (parseval_walsh k f).
  exact (walsh_captured_le_energy k f K HK).
Qed.

Print Assumptions walsh_orthogonal_and_plancherel.
Print Assumptions walsh_compression_within_energy.
