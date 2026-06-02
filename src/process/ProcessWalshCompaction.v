(** * ProcessWalshCompaction.v — Exact energy compaction for band-limited signals
      (Part VII, Batch 3 / proposal F, minimal version)

    Elements: rational spectrum c_i; finite sums; K ≤ N
    Roles:    c_i = transform coefficient; tail = dropped energy; "band-limited" = role
    Rules:    if the spectrum is supported on the first K coefficients (c_i = 0 for
              K ≤ i < N), then the tail energy is zero — K coefficients capture ALL energy

    The minimal, honest compaction statement (per the GPT plan review): NOT a "best
    K-term" theorem (that needs a sorting/selection layer — the noted P4 boundary), but
    the exact fact that a band-limited signal (spectrum living in the first K Walsh modes)
    is reconstructed by its first K coefficients with ZERO tail energy. Over ℚ, 0 axioms.

    HONEST FRONTIER: choosing WHICH K coefficients are most significant (sorting by
    magnitude) is the best-K-term problem, requiring a comparison/selection layer; the
    first-K truncation proved here is the exact, sorting-free core.

    ============ E/R/R разбор ============
      Rules (L5): спектр на первых K (c_i=0 при K≤i<N) ⟹ хвост=0 ⟹ K коэф. ловят всю энергию.
      Roles (L4): c_i=роль-коэффициент; хвост=роль-ошибка; band-limited=роль сигнала.
      Elements  : рациональные c_i, конечные суммы, K≤N (L1+P4).
    ДИАГНОСТИКА: первые-K усечение — точно над ℚ (0 акс); best-K-term по величине = слой
    сортировки (P4-граница, не строим).

    STATUS: 1 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.     (* q_sum_zero *)
From ToS Require Import process.ProcessL2BesselGeneral.   (* q_sum_ext_bounded *)
From ToS Require Import process.ProcessFourierCompression. (* captured, truncation_error_eq *)

Open Scope Q_scope.

(** Exact compaction: a band-limited spectrum has zero tail, so the first K
    coefficients capture the full energy. *)
Theorem walsh_compaction : forall (c : nat -> Q) (K N : nat),
  (K <= N)%nat ->
  (forall i, (K <= i < N)%nat -> c i == 0) ->
  captured c N == captured c K.
Proof.
  intros c K N HK Hzero.
  rewrite (truncation_error_eq c K N HK).
  assert (Htail : q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat == 0).
  { transitivity (q_sum (fun _ : nat => 0) (N - K)%nat).
    - apply q_sum_ext_bounded. intros i Hi.
      assert (Hz : c (K + i)%nat == 0) by (apply Hzero; lia).
      rewrite Hz. ring.
    - apply q_sum_zero. }
  rewrite Htail. ring.
Qed.

(* Concrete: a 2-mode spectrum on N=4, c = (5,7,0,0); captured(4) = captured(2). *)
Example compaction_4_example :
  let c := fun i => if Nat.eqb i 0%nat then 5
                    else if Nat.eqb i 1%nat then 7 else 0 in
  captured c 4%nat == captured c 2%nat.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions walsh_compaction.
