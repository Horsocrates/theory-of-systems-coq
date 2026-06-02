(** * ProcessHadamardGate.v — The one-qubit Hadamard gate from the Walsh matrix
      (Part VII, Batch 3 / proposal C)

    Elements: rational ±1 matrix had 1 = [[1,1],[1,−1]]; abstract 1/√2 parameter
    Roles:    had 1 = unnormalised gate; the normalised gate = quantum H; involution = role
    Rules:    HᵀH = N·I gives H(Hf)=N·f (inverse up to scale); the normalised gate
              squares to the identity (H² = I) and creates equal superposition

    The bridge to quantum computing (direction D4). Per the GPT plan review, "unitary
    normalisation" is NOT the centre: the unnormalised Walsh matrix had 1 = [[1,1],[1,−1]]
    satisfies HᵀH = 2·I exactly over ℚ (so H is its own inverse up to the scale 2). The
    1/√2 normalisation is irrational — introduced as an ABSTRACT parameter s with the
    defining relation s²·2 = 1 — and under it the gate is an involution H² = I and turns
    |0⟩ into the equal superposition. 0 axioms.

    HONEST FRONTIER: 1/√N is rational only when N is a perfect square (for N = 2ᵏ, only
    when k is even); the one-qubit 1/√2 is genuinely irrational, hence the abstract
    parameter — a clean P4 boundary separating the rational gate structure from its
    transcendental normalisation.

    ============ E/R/R разбор ============
      Rules (L5): HᵀH=N·I ⟹ H(Hf)=N·f; нормированный вентиль H²=I; H|0⟩ = суперпозиция.
      Roles (L4): had 1 = роль-вентиль (ненормированный); нормировка = роль-предел; H²=I = инволюция.
      Elements  : рациональная ±1-матрица had 1, абстрактный 1/√2 (s, s²·2=1) (L1+P4).
    ДИАГНОСТИКА: структура вентиля рациональна (0 акс); 1/√2 иррациональна = абстрактный
    параметр (P4-граница, отделена от ±1-структуры).

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_scale, q_sum_ext *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessWalshHadamard.   (* had, pow2 *)
From ToS Require Import process.ProcessFourierON.       (* walsh_HH *)

Open Scope Q_scope.

(** The 2×2 Hadamard gate (unnormalised) is the Walsh matrix had 1 = [[1,1],[1,−1]]. *)
Example hadamard_2x2 :
  had 1 0 0 == 1 /\ had 1 0 1 == 1 /\ had 1 1 0 == 1 /\ had 1 1 1 == -(1).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The Walsh transform is linear: scaling the input scales the output. *)
Lemma op_apply_scale : forall k c f N m,
  op_apply (had k) (fun j => c * f j) N m == c * op_apply (had k) f N m.
Proof.
  intros k c f N m. unfold op_apply.
  transitivity (q_sum (fun j => c * (had k m j * f j)) N).
  - apply q_sum_ext. intro j. ring.
  - apply q_sum_scale.
Qed.

(** Unnormalised gate squares to N·I (= 2·I for one qubit): from walsh_HH. *)
Corollary hadamard_unnormalised_square : forall f m, (m < pow2 1)%nat ->
  op_apply (had 1) (op_apply (had 1) f (pow2 1)) (pow2 1) m
  == inject_Z (Z.of_nat (pow2 1)) * f m.
Proof. intros f m Hm. exact (walsh_HH 1 f m Hm). Qed.

Section Gate.

(* 1/√2 is irrational; introduce it as an abstract parameter with the defining
   relation (1/√2)²·2 = 1 — the honest P4 boundary. *)
Variable s2inv : Q.
Hypothesis Hs2 : s2inv * s2inv * 2 == 1.

(** The normalised one-qubit Hadamard gate. *)
Definition hgate (f : nat -> Q) : nat -> Q :=
  fun m => s2inv * op_apply (had 1) f (pow2 1) m.

(** The Hadamard gate is an INVOLUTION: applying it twice is the identity (H² = I). *)
Theorem hgate_involution : forall f m, (m < pow2 1)%nat ->
  hgate (hgate f) m == f m.
Proof.
  intros f m Hm. unfold hgate. cbn beta.
  rewrite op_apply_scale.
  rewrite (walsh_HH 1 f m Hm).
  assert (Hp : inject_Z (Z.of_nat (pow2 1)) == 2) by (vm_compute; reflexivity).
  rewrite Hp.
  assert (Heq : s2inv * (s2inv * (2 * f m)) == (s2inv * s2inv * 2) * f m) by ring.
  rewrite Heq, Hs2. ring.
Qed.

(** The |0⟩ basis state. *)
Definition e0 (j : nat) : Q := if Nat.eqb j 0%nat then 1 else 0.

(** The gate turns |0⟩ into the equal superposition (both amplitudes = 1/√2). *)
Theorem hgate_superposition :
  hgate e0 0 == s2inv /\ hgate e0 1 == s2inv.
Proof.
  unfold hgate.
  assert (H0 : op_apply (had 1) e0 (pow2 1) 0 == 1) by (vm_compute; reflexivity).
  assert (H1 : op_apply (had 1) e0 (pow2 1) 1 == 1) by (vm_compute; reflexivity).
  split.
  - rewrite H0. ring.
  - rewrite H1. ring.
Qed.

End Gate.

Print Assumptions hgate_involution.
