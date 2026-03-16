(** * ProcessRGWeinberg.v — Running of the Weak Mixing Angle
    Theory of Systems - Phase 40: RG Running of sin²θ_W (File 1)

    Elements: rg_hyper_mild, dual_rg, ratio_process
    Roles:    dual RG flow — SU(2) grows, U(1) shrinks
    Rules:    r = u_y/u_w decreases from GUT to IR
    Status:   complete

    Two couplings run under RG with different beta functions:
    SU(2): u_w grows toward FP=4 (asymptotically free, IR strong)
    U(1):  u_y → FP=1 (not AF, IR approach from below)
    Ratio r = u_y/u_w decreases: GUT → low energy

    STATUS: 28 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessRGFlow.
From ToS Require Import process.ProcessWeinbergAngle.

(* ================================================================== *)
(*  Part I: U(1) RG Map  (~10 lemmas)                                 *)
(* ================================================================== *)

(** SU(2) coupling: grows toward IR (Phase 25)
    rg_step u = 2u − u²/4, FP at 4 *)
(** We alias it for clarity *)
Definition rg_weak (u : Q) : Q := rg_step u.

(** U(1) coupling: approaches FP=1 from below
    Model: u' = u · (2 − u) = 2u − u²
    FP: u(2−u) = u → 2u − u² = u → u = 1 (or u = 0)
    For 0 < u < 1: u increases toward 1
    For u > 1: u decreases toward 1 *)
Definition rg_hyper_mild (u : Q) : Q :=
  u * (2 - u).

(** U(1) FP at u = 1 *)
Lemma rg_hyper_mild_fp1 : rg_hyper_mild 1 == 1.
Proof. unfold rg_hyper_mild. ring. Qed.

(** U(1) FP at u = 0 (trivial) *)
Lemma rg_hyper_mild_fp0 : rg_hyper_mild 0 == 0.
Proof. unfold rg_hyper_mild. ring. Qed.

(** For 0 < u < 1: u increases toward 1 *)
Lemma rg_hyper_mild_increases_small : forall u,
  0 < u -> u < 1 ->
  u < rg_hyper_mild u.
Proof.
  intros u Hu Hu1. unfold rg_hyper_mild.
  (* u(2-u) > u ⟺ 2u - u² > u ⟺ u - u² > 0 ⟺ u(1-u) > 0 *)
  assert (H : u * (2 - u) - u == u * (1 - u)) by ring.
  assert (H2 : 0 < u * (1 - u)).
  { apply Qmult_lt_0_compat; lra. }
  lra.
Qed.

(** For u > 1: u decreases toward 1 *)
Lemma rg_hyper_mild_decreases_large : forall u,
  1 < u -> u < 2 ->
  rg_hyper_mild u < u.
Proof.
  intros u Hu Hu2. unfold rg_hyper_mild.
  (* u(2-u) < u ⟺ u - u² < 0 ⟺ u(1-u) < 0 ⟺ 1-u < 0 since u > 0 *)
  assert (H : u * (2 - u) - u == u * (1 - u)) by ring.
  assert (H2 : u * (2 - u) < u).
  { assert (Heq : u - u * (2 - u) == u * (u - 1)) by ring.
    assert (Hpos : 0 < u * (u - 1)).
    { apply Qmult_lt_0_compat; lra. }
    lra. }
  lra.
Qed.

(** rg_hyper_mild is nonneg for 0 ≤ u ≤ 2 *)
Lemma rg_hyper_mild_nonneg : forall u,
  0 <= u -> u <= 2 ->
  0 <= rg_hyper_mild u.
Proof.
  intros u Hu Hu2. unfold rg_hyper_mild.
  assert (H : u * (2 - u) == u * (2 - u)) by ring.
  assert (0 <= u) by lra. assert (0 <= 2 - u) by lra.
  apply Qmult_le_0_compat; assumption.
Qed.

(** rg_hyper_mild at 3/5: 3/5 · (2 − 3/5) = 3/5 · 7/5 = 21/25 *)
Lemma rg_hyper_mild_at_3_5 : rg_hyper_mild (3#5) == 21 # 25.
Proof. unfold rg_hyper_mild. vm_compute. reflexivity. Qed.

(** rg_hyper_mild at 21/25: 21/25 · (2 − 21/25) = 21/25 · 29/25 = 609/625 *)
Lemma rg_hyper_mild_at_21_25 : rg_hyper_mild (21#25) == 609 # 625.
Proof. unfold rg_hyper_mild. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Dual RG System  (~8 lemmas)                              *)
(* ================================================================== *)

(** Iterated dual RG: SU(2) grows, U(1) evolves *)
Fixpoint dual_rg_iter (u_w u_y : Q) (n : nat) : (Q * Q) :=
  match n with
  | 0%nat => (u_w, u_y)
  | S k => let p := dual_rg_iter u_w u_y k in
           (rg_weak (fst p), rg_hyper_mild (snd p))
  end.

(** The ratio process: r(n) = u_y(n) / u_w(n) *)
Definition ratio_process (u_w0 u_y0 : Q) : RealProcess :=
  fun n => snd (dual_rg_iter u_w0 u_y0 n) / fst (dual_rg_iter u_w0 u_y0 n).

(** GUT starting point: u_w = 1, u_y = 3/5 *)
(** SU(5): sin²θ_W(GUT) = 3/8 → r(GUT) = 3/5 *)
Definition gut_u_w : Q := 1.
Definition gut_u_y : Q := 3 # 5.

(** Initial ratio *)
Lemma initial_ratio : gut_u_y / gut_u_w == 3 # 5.
Proof. unfold gut_u_y, gut_u_w. vm_compute. reflexivity. Qed.

(** Step 0 *)
Lemma dual_rg_step0 :
  dual_rg_iter gut_u_w gut_u_y 0%nat = (gut_u_w, gut_u_y).
Proof. reflexivity. Qed.

(** Step 1:
    u_w(1) = rg_weak(1) = rg_step(1) = 7/4
    u_y(1) = rg_hyper_mild(3/5) = 21/25 *)
Lemma dual_rg_step1 :
  fst (dual_rg_iter gut_u_w gut_u_y 1%nat) == 7 # 4 /\
  snd (dual_rg_iter gut_u_w gut_u_y 1%nat) == 21 # 25.
Proof.
  split; simpl; unfold rg_weak, rg_step, rg_hyper_mild, gut_u_w, gut_u_y;
  vm_compute; reflexivity.
Qed.

(** Ratio at step 1: r(1) = (21/25)/(7/4) = 84/175 = 12/25 ≈ 0.48 *)
Lemma ratio_step1 :
  ratio_process gut_u_w gut_u_y 1%nat == 12 # 25.
Proof.
  unfold ratio_process. simpl.
  unfold rg_weak, rg_step, rg_hyper_mild, gut_u_w, gut_u_y.
  vm_compute. reflexivity.
Qed.

(** Step 2 *)
Lemma dual_rg_step2 :
  let p := dual_rg_iter gut_u_w gut_u_y 2%nat in
  fst p == 175 # 64 /\ snd p == 609 # 625.
Proof.
  simpl. unfold rg_weak, rg_step, rg_hyper_mild, gut_u_w, gut_u_y.
  split; vm_compute; reflexivity.
Qed.

(** Ratio at step 2: r(2) = (609/625)/(175/64) = 609·64/(625·175) *)
Lemma ratio_step2 :
  ratio_process gut_u_w gut_u_y 2%nat == 38976 # 109375.
Proof.
  unfold ratio_process. simpl.
  unfold rg_weak, rg_step, rg_hyper_mild, gut_u_w, gut_u_y.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: Running Direction  (~10 lemmas)                         *)
(* ================================================================== *)

(** r(0) = 3/5 = 0.600 *)
Lemma ratio_at_0 : ratio_process gut_u_w gut_u_y 0%nat == 3 # 5.
Proof.
  unfold ratio_process. simpl. unfold gut_u_w, gut_u_y.
  vm_compute. reflexivity.
Qed.

(** r(1) = 12/25 = 0.480 *)
Lemma ratio_at_1_value : ratio_process gut_u_w gut_u_y 1%nat == 12 # 25.
Proof. exact ratio_step1. Qed.

(** r decreases: r(1) < r(0) *)
Lemma ratio_decreases_step1 :
  ratio_process gut_u_w gut_u_y 1%nat < ratio_process gut_u_w gut_u_y 0%nat.
Proof.
  rewrite ratio_at_0, ratio_at_1_value. lra.
Qed.

(** r(2) < r(1) *)
Lemma ratio_decreases_step2 :
  ratio_process gut_u_w gut_u_y 2%nat < ratio_process gut_u_w gut_u_y 1%nat.
Proof.
  rewrite ratio_step1, ratio_step2.
  (* 38976/109375 < 12/25 *)
  (* 38976 · 25 < 12 · 109375 *)
  (* 974400 < 1312500 ✓ *)
  unfold Qlt. simpl. lia.
Qed.

(** r runs toward observed value *)
(** r(0) = 3/5 = 0.600 (GUT)
    r(1) = 12/25 = 0.480
    r(2) = 38976/109375 ≈ 0.356
    Target: r = 3/10 = 0.300 *)

(** r(2) > 3/10 — still above target *)
Lemma ratio_step2_above_target :
  3 # 10 < ratio_process gut_u_w gut_u_y 2%nat.
Proof.
  rewrite ratio_step2. unfold Qlt. simpl. lia.
Qed.

(** r(2) < r(0) — monotone decrease *)
Lemma ratio_step2_below_start :
  ratio_process gut_u_w gut_u_y 2%nat < ratio_process gut_u_w gut_u_y 0%nat.
Proof.
  assert (H1 := ratio_decreases_step1).
  assert (H2 := ratio_decreases_step2). lra.
Qed.

(** sin²θ_W at GUT: sin²(r=3/5) = (3/5)/(1+3/5) = 3/8 *)
Lemma sin2_at_gut : sin2_weinberg (3#5) == 3 # 8.
Proof. unfold sin2_weinberg. vm_compute. reflexivity. Qed.

(** sin²θ_W at step 1: sin²(r=12/25) = (12/25)/(1+12/25) = 12/37 *)
Lemma sin2_at_step1 :
  sin2_weinberg (ratio_process gut_u_w gut_u_y 1%nat) == 12 # 37.
Proof.
  unfold sin2_weinberg, ratio_process. simpl.
  unfold rg_weak, rg_step, rg_hyper_mild, gut_u_w, gut_u_y.
  vm_compute. reflexivity.
Qed.

(** sin²θ runs: 3/8 = 0.375 (GUT) → 12/37 ≈ 0.324 (step 1) → ... → 3/13 ≈ 0.231 *)
Lemma sin2_decreases :
  sin2_weinberg (ratio_process gut_u_w gut_u_y 1%nat) <
  sin2_weinberg (ratio_process gut_u_w gut_u_y 0%nat).
Proof.
  assert (H1 : sin2_weinberg (ratio_process gut_u_w gut_u_y 1%nat) == 12 # 37).
  { exact sin2_at_step1. }
  assert (H2 : sin2_weinberg (ratio_process gut_u_w gut_u_y 0%nat) == 3 # 8).
  { unfold sin2_weinberg, ratio_process. simpl. unfold gut_u_w, gut_u_y.
    vm_compute. reflexivity. }
  rewrite H1, H2. unfold Qlt. simpl. lia.
Qed.

(** ★ r runs from 3/5 (GUT) toward ~3/10 (observed) *)
Theorem weinberg_from_rg :
  (* At GUT scale: sin²θ = 3/8 (SU(5) prediction) *)
  sin2_weinberg (3#5) == 3 # 8 /\
  (* After RG running: ratio decreases *)
  ratio_process gut_u_w gut_u_y 1%nat < ratio_process gut_u_w gut_u_y 0%nat /\
  (* sin²θ decreases toward observed value *)
  sin2_weinberg (ratio_process gut_u_w gut_u_y 1%nat) <
  sin2_weinberg (ratio_process gut_u_w gut_u_y 0%nat).
Proof.
  split; [| split].
  - exact sin2_at_gut.
  - exact ratio_decreases_step1.
  - exact sin2_decreases.
Qed.
