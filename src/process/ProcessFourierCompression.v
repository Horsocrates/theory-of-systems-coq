(** * ProcessFourierCompression.v — Compression as spectral truncation: the error
      is the dropped energy, controlled by Parseval (Part VII)

    Elements: rational coefficients c_i; finite sums Σ_{i<K}, Σ_{K≤i<N}; K ≤ N
    Roles:    c_i = coefficient (spectrum); E(K) = captured energy; tail = error;
              Parseval = energy balance
    Rules:    E(K) = Σ_{i<K} c_i² is monotone in K; E(N) = E(K) + Σ_{K≤i<N} c_i²
              (captured + dropped); tail ≥ 0 ⟹ E(K) ≤ E(N); for Walsh E(N) = N‖f‖²

    Compression keeps the first K (significant) coefficients and drops the rest. The
    dropped energy is EXACTLY the tail Σ_{K≤i<N} c_i² (the residual-norm split), so the
    captured energy E(K) is monotone in K and bounded by the total; for the Walsh
    transform the total is N‖f‖² (Plancherel), so the truncation error is controlled by
    Parseval. All exact over ℚ, 0 axioms.

    HONEST FRONTIER: the CHOICE of which K coefficients are "significant" (sorting by
    magnitude), rate–distortion, and the continuous signal are the applied/process layer.

    ============ E/R/R разбор ============
      Rules (L5): E(K) монотонна; E(N)=E(K)+хвост; хвост≥0 ⟹ E(K)≤E(N); Уолш E(N)=N‖f‖².
      Roles (L4): c_i=роль-коэффициент; E(K)=захваченная энергия; хвост=ошибка; Парсеваль=баланс.
      Elements  : рациональные c_i, конечные суммы Σ_{i<K},Σ_{K≤i<N}, K≤N (L1+P4).
    ДИАГНОСТИКА: ошибка усечения — точный факт (0 акс); выбор значимых K и сигнал — прикладное.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessWalshHadamard.   (* q_sum_split, had, pow2 *)
From ToS Require Import process.ProcessFourierON.       (* parseval_walsh *)

Open Scope Q_scope.

(** Captured energy of the first K coefficients: E(K) = Σ_{i<K} c_i². *)
Definition captured (c : nat -> Q) (K : nat) : Q := q_sum (fun i => c i * c i) K.

(** One more coefficient adds its (nonnegative) energy. *)
Lemma captured_step : forall c K, captured c (S K) == captured c K + c K * c K.
Proof. intros c K. unfold captured. cbn [q_sum]. ring. Qed.

(** Captured energy is monotone in the number of kept coefficients. *)
Lemma captured_mono : forall (c : nat -> Q) (K K' : nat),
  (K <= K')%nat -> captured c K <= captured c K'.
Proof.
  intros c K K' Hle. unfold captured.
  replace K' with (K + (K' - K))%nat by lia.
  rewrite q_sum_split. cbn beta.
  assert (Htail : 0 <= q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (K' - K)%nat)
    by (apply q_sum_nonneg; intro i; apply q_sq_nonneg).
  lra.
Qed.

(** Energy balance: total = captured + dropped tail. *)
Lemma truncation_error_eq : forall (c : nat -> Q) (K N : nat),
  (K <= N)%nat ->
  captured c N == captured c K + q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat.
Proof.
  intros c K N Hle. unfold captured.
  assert (HN : N = (K + (N - K))%nat) by lia.
  rewrite HN at 1. rewrite q_sum_split. cbn beta. reflexivity.
Qed.

(** The dropped energy (truncation error) is nonnegative. *)
Lemma truncation_error_nonneg : forall (c : nat -> Q) (K N : nat),
  0 <= q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat.
Proof. intros. apply q_sum_nonneg. intro i. apply q_sq_nonneg. Qed.

(* ===================================================================== *)
(*  Walsh compression: captured energy of any K coefficients ≤ N‖f‖².      *)
(* ===================================================================== *)

Theorem walsh_captured_le_energy : forall k f K,
  (K <= pow2 k)%nat ->
  captured (op_apply (had k) f (pow2 k)) K
  <= inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k).
Proof.
  intros k f K HK.
  apply Qle_trans with (captured (op_apply (had k) f (pow2 k)) (pow2 k)).
  - apply captured_mono. exact HK.
  - unfold captured.
    change (q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i)
                  (pow2 k))
      with (seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k)).
    rewrite (parseval_walsh k f). apply Qle_refl.
Qed.

(* Concrete energy balance for N = 4: c = (3,4,1,1), captured(2)=25, tail=2, total=27. *)
Example compression_4_example :
  let c := fun i => if Nat.eqb i 0%nat then 3
                    else if Nat.eqb i 1%nat then 4
                    else 1 in
  captured c 4%nat == captured c 2%nat + q_sum (fun i => c (2 + i)%nat * c (2 + i)%nat) 2%nat.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions walsh_captured_le_energy.
