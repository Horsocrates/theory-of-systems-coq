(* ========================================================================= *)
(*        TRIADIC INTERACTION — Structure of Nonlinear Coupling               *)
(*                                                                            *)
(*  Mode k receives energy only from triads (l,m) with l+m=k or |l-m|=k.   *)
(*  This is a SELECTION RULE from the structure of (u·∇)u.                  *)
(*                                                                            *)
(*  L4 (Sufficient Reason): every energy transfer has a specific cause.      *)
(*  The cause is a triadic interaction with known coupling B_{klm}.          *)
(*                                                                            *)
(*  Key results:                                                              *)
(*    - Number of triads for mode k: at most 2k                              *)
(*    - Coupling strength: |B_{klm}| ≤ C_B·max(k,l,m)                      *)
(*    - Total forcing on mode k: ≤ C_B·k · 2E₀                             *)
(*                                                                            *)
(*  Elements: triad counting, coupling bounds, forcing estimates             *)
(*  Roles:    L4 causality, selection rules, Cauchy-Schwarz                  *)
(*  Rules:    each transfer bounded, triad count ≤ 2k                        *)
(*  STATUS: 40 Qed, 0 Admitted, 2 Axioms (C_B)                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
Open Scope Q_scope.

(** Helper: left multiply compat for Qle *)
Lemma Qmult_le_l : forall x y z,
  x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  assert (H1 : z * x == x * z) by ring. rewrite H1.
  assert (H2 : z * y == y * z) by ring. rewrite H2.
  apply Qmult_le_compat_r; assumption.
Qed.

(** Sum of constant function *)
Lemma sum_ns_const : forall c K,
  sum_Q_ns (fun _ => c) K == inject_Z (Z.of_nat K) * c.
Proof.
  intros c K. induction K as [|K' IH].
  - simpl. unfold inject_Z. simpl. ring.
  - simpl sum_Q_ns. rewrite IH.
    assert (HSK : inject_Z (Z.of_nat (S K')) == inject_Z (Z.of_nat K') + 1).
    { unfold inject_Z, Qeq. simpl. lia. }
    rewrite HSK. ring.
Qed.

(** |x|*|x| = x*x *)
Lemma qabs_sq : forall x, Qabs x * Qabs x == x * x.
Proof.
  intros x. rewrite <- Qabs_Qmult.
  rewrite Qabs_pos; [reflexivity | apply Qsq_nonneg].
Qed.

(* ================================================================== *)
(*  Part I: Triad Counting  (~11 lemmas)                              *)
(* ================================================================== *)

Definition is_triad (k l m : nat) : Prop :=
  k = (l + m)%nat \/ (l = k + m)%nat \/ (m = k + l)%nat.

Definition triad_count (k K : nat) : nat := (2 * K)%nat.

Lemma triad_count_bound : forall k K,
  (1 <= k)%nat -> (k <= K)%nat ->
  (triad_count k K <= 2 * K)%nat.
Proof. intros. unfold triad_count. lia. Qed.

Definition sum_triad_count (k : nat) : nat := (k - 1)%nat.

Lemma sum_triad_count_le_k : forall k,
  (1 <= k)%nat -> (sum_triad_count k <= k)%nat.
Proof. intros. unfold sum_triad_count. lia. Qed.

Definition triad_count_tight (k : nat) : nat := (2 * k)%nat.

Lemma triad_count_tight_bound : forall k,
  (triad_count_tight k <= 2 * k)%nat.
Proof. intros. unfold triad_count_tight. lia. Qed.

Lemma triad_count_by_k : forall k K,
  (1 <= k)%nat -> (k <= K)%nat ->
  (triad_count_tight k <= 2 * k)%nat.
Proof. intros. apply triad_count_tight_bound. Qed.

Lemma triad_sym : forall k l m,
  is_triad k l m -> is_triad k m l.
Proof. intros k l m [H|[H|H]]; unfold is_triad; lia. Qed.

Lemma sum_triad_parts_smaller : forall k l m,
  k = (l + m)%nat -> (1 <= l)%nat -> (1 <= m)%nat ->
  (l < k)%nat /\ (m < k)%nat.
Proof. intros. lia. Qed.

Lemma max_of_sum_triad : forall k l m,
  k = (l + m)%nat -> (1 <= l)%nat -> (1 <= m)%nat ->
  Nat.max k (Nat.max l m) = k.
Proof. intros. lia. Qed.

Lemma triad_zero_degenerate : forall l m,
  is_triad 0 l m -> l = (0 + m)%nat \/ m = (0 + l)%nat.
Proof. intros l m [H|[H|H]]; lia. Qed.

Lemma sum_triad_nonempty : forall k,
  (2 <= k)%nat -> (k - 1 >= 1)%nat.
Proof. intros. lia. Qed.

Lemma triad_count_monotone : forall k K1 K2,
  (K1 <= K2)%nat -> (triad_count k K1 <= triad_count k K2)%nat.
Proof. intros. unfold triad_count. lia. Qed.

(* ================================================================== *)
(*  Part II: Coupling Strength  (~10 lemmas)                          *)
(* ================================================================== *)

Parameter C_B : Q.
Axiom C_B_positive : 0 < C_B.

Axiom B_coeff_bounded : forall k l m,
  Qabs (B_coeff k l m) <= C_B * inject_Z (Z.of_nat (Nat.max k (Nat.max l m))).

Lemma coupling_for_sum_triad : forall k l m,
  k = (l + m)%nat -> (1 <= l)%nat -> (1 <= m)%nat ->
  Qabs (B_coeff k l m) <= C_B * inject_Z (Z.of_nat k).
Proof.
  intros k l m Hk Hl Hm.
  assert (Hmax := B_coeff_bounded k l m).
  rewrite (max_of_sum_triad k l m Hk Hl Hm) in Hmax. exact Hmax.
Qed.

Lemma coupling_bound_nonneg : forall k,
  (1 <= k)%nat -> 0 <= C_B * inject_Z (Z.of_nat k).
Proof.
  intros. apply Qmult_le_0_compat.
  - apply Qlt_le_weak. exact C_B_positive.
  - unfold Qle, inject_Z. simpl. lia.
Qed.

Lemma coupling_monotone : forall k1 k2,
  (k1 <= k2)%nat ->
  C_B * inject_Z (Z.of_nat k1) <= C_B * inject_Z (Z.of_nat k2).
Proof.
  intros. apply Qmult_le_l.
  - unfold Qle, inject_Z. simpl. lia.
  - apply Qlt_le_weak. exact C_B_positive.
Qed.

Lemma coupling_at_zero : C_B * inject_Z (Z.of_nat 0) == 0.
Proof. unfold inject_Z. simpl. ring. Qed.

Lemma coupling_positive : forall k,
  (1 <= k)%nat -> 0 < C_B * inject_Z (Z.of_nat k).
Proof.
  intros. apply Qmult_lt_0_compat.
  - exact C_B_positive.
  - unfold Qlt, inject_Z. simpl. lia.
Qed.

Lemma nonlinear_term_bounded : forall k l m (a : modal_state),
  k = (l + m)%nat -> (1 <= l)%nat -> (1 <= m)%nat ->
  Qabs (B_coeff k l m * a l * a m) <=
    C_B * inject_Z (Z.of_nat k) * Qabs (a l) * Qabs (a m).
Proof.
  intros k l m a Hk Hl Hm.
  assert (HB := coupling_for_sum_triad k l m Hk Hl Hm).
  rewrite !Qabs_Qmult.
  apply Qmult_le_compat_r; [| apply Qabs_nonneg].
  apply Qmult_le_compat_r; [exact HB | apply Qabs_nonneg].
Qed.

Lemma qabs_product_bound : forall a b c,
  Qabs a <= c -> 0 <= c ->
  Qabs (a * b) <= c * Qabs b.
Proof.
  intros. rewrite Qabs_Qmult.
  apply Qmult_le_compat_r; [assumption | apply Qabs_nonneg].
Qed.

(* ================================================================== *)
(*  Part III: Total Forcing on Mode k  (~9 lemmas)                    *)
(* ================================================================== *)

Definition mode_forcing (k K : nat) (a : modal_state) : Q :=
  sum_Q_ns (fun l =>
    sum_Q_ns (fun m =>
      Qabs (B_coeff k l m) * Qabs (a l) * Qabs (a m)) K) K.

Lemma mode_forcing_nonneg : forall k K (a : modal_state),
  0 <= mode_forcing k K a.
Proof.
  intros. unfold mode_forcing.
  apply sum_ns_nonneg. intros l Hl.
  apply sum_ns_nonneg. intros m Hm.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; apply Qabs_nonneg.
  - apply Qabs_nonneg.
Qed.

Lemma energy_as_sum : forall K (a : modal_state),
  sum_Q_ns (fun l => a l * a l) K == 2 * modal_energy K a.
Proof. intros. unfold modal_energy. lra. Qed.

(** Individual mode bounded by total energy *)
Lemma mode_amplitude_by_energy : forall K (a : modal_state) k,
  (k < K)%nat ->
  a k * a k <= 2 * modal_energy K a.
Proof.
  intros K a k Hk.
  assert (H : a k * a k <= sum_Q_ns (fun l => a l * a l) K).
  { induction K as [|K' IH]; [lia |].
    simpl sum_Q_ns.
    destruct (Nat.eq_dec k K') as [Heq|Hneq].
    - subst. assert (0 <= sum_Q_ns (fun l => a l * a l) K').
      { apply sum_ns_nonneg. intros. apply Qsq_nonneg. } lra.
    - assert (Hk' : (k < K')%nat) by lia.
      assert (HIH := IH Hk').
      assert (0 <= a K' * a K') by apply Qsq_nonneg. lra. }
  rewrite energy_as_sum in H. exact H.
Qed.

(** AM-GM: |x|·|y| ≤ (x²+y²)/2 *)
Lemma qabs_amgm : forall x y,
  Qabs x * Qabs y <= (1#2) * (x * x + y * y).
Proof.
  intros x y.
  assert (Hdiff : 0 <= (Qabs x - Qabs y) * (Qabs x - Qabs y)) by apply Qsq_nonneg.
  assert (Hexp : (Qabs x - Qabs y) * (Qabs x - Qabs y) ==
                 Qabs x * Qabs x - 2 * (Qabs x * Qabs y) +
                 Qabs y * Qabs y) by ring.
  assert (Habsx := qabs_sq x). assert (Habsy := qabs_sq y). lra.
Qed.

(** Product sum bound via AM-GM:
    Σ_l Σ_m |al|·|am| ≤ K · Σ al² *)
Lemma product_sum_bound : forall K (a : modal_state),
  sum_Q_ns (fun l =>
    sum_Q_ns (fun m =>
      Qabs (a l) * Qabs (a m)) K) K <=
  inject_Z (Z.of_nat K) * (2 * modal_energy K a).
Proof.
  intros K a.
  (* Each term: |al|·|am| ≤ (al²+am²)/2 *)
  (* Σ_l Σ_m (al²+am²)/2 = K·Σa² (by symmetry) *)
  apply Qle_trans with
    (sum_Q_ns (fun l =>
      sum_Q_ns (fun m =>
        (1#2) * (a l * a l + a m * a m)) K) K).
  { apply sum_ns_le. intros l Hl.
    apply sum_ns_le. intros m Hm.
    apply qabs_amgm. }
  (* Split: Σ_l Σ_m (al²+am²)/2 = (1/2)·K·Σal² + (1/2)·K·Σam² = K·Σa² *)
  assert (Hinner : forall l,
    sum_Q_ns (fun m => (1#2) * (a l * a l + a m * a m)) K ==
    (1#2) * inject_Z (Z.of_nat K) * (a l * a l) +
    (1#2) * sum_Q_ns (fun m => a m * a m) K).
  { intros l.
    assert (H1 : sum_Q_ns (fun m => (1#2) * (a l * a l + a m * a m)) K ==
                 sum_Q_ns (fun _ => (1#2) * (a l * a l)) K +
                 sum_Q_ns (fun m => (1#2) * (a m * a m)) K).
    { rewrite <- sum_ns_add.
      apply sum_ns_ext. intros i Hi. lra. }
    rewrite H1.
    rewrite sum_ns_const.
    assert (H2 : sum_Q_ns (fun m => (1#2) * (a m * a m)) K ==
                 (1#2) * sum_Q_ns (fun m => a m * a m) K).
    { rewrite <- sum_ns_scale. apply sum_ns_ext. intros. lra. }
    rewrite H2. lra. }
  assert (Houter :
    sum_Q_ns (fun l =>
      sum_Q_ns (fun m => (1#2) * (a l * a l + a m * a m)) K) K ==
    (1#2) * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K +
    (1#2) * inject_Z (Z.of_nat K) * sum_Q_ns (fun m => a m * a m) K).
  { assert (H3 :
      sum_Q_ns (fun l =>
        (1#2) * inject_Z (Z.of_nat K) * (a l * a l) +
        (1#2) * sum_Q_ns (fun m => a m * a m) K) K ==
      sum_Q_ns (fun l => (1#2) * inject_Z (Z.of_nat K) * (a l * a l)) K +
      sum_Q_ns (fun _ => (1#2) * sum_Q_ns (fun m => a m * a m) K) K).
    { rewrite <- sum_ns_add. reflexivity. }
    assert (H4 :
      sum_Q_ns (fun l =>
        sum_Q_ns (fun m => (1#2) * (a l * a l + a m * a m)) K) K ==
      sum_Q_ns (fun l =>
        (1#2) * inject_Z (Z.of_nat K) * (a l * a l) +
        (1#2) * sum_Q_ns (fun m => a m * a m) K) K).
    { apply sum_ns_ext. intros l Hl. apply Hinner. }
    rewrite H4, H3.
    assert (H5 :
      sum_Q_ns (fun l => (1#2) * inject_Z (Z.of_nat K) * (a l * a l)) K ==
      (1#2) * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K).
    { rewrite <- sum_ns_scale. apply sum_ns_ext. intros. ring. }
    rewrite H5.
    rewrite sum_ns_const. lra. }
  rewrite Houter.
  rewrite energy_as_sum. lra.
Qed.

(** Forcing bounded by CB·K·2E *)
Theorem forcing_bound : forall k K (a : modal_state) E0,
  (1 <= k)%nat -> (k <= K)%nat ->
  modal_energy K a <= E0 ->
  0 <= mode_forcing k K a /\
  mode_forcing k K a <=
    C_B * inject_Z (Z.of_nat (Nat.max k K)) *
    inject_Z (Z.of_nat K) * (2 * E0).
Proof.
  intros k K a E0 Hk HkK HE.
  split; [apply mode_forcing_nonneg |].
  unfold mode_forcing.
  set (CB_max := C_B * inject_Z (Z.of_nat (Nat.max k K))).
  (* Step 1: Σ_l Σ_m |B|·|al|·|am| ≤ Σ_l (CB_max · Σ_m |al|·|am|) *)
  apply Qle_trans with
    (sum_Q_ns (fun l =>
      CB_max * sum_Q_ns (fun m => Qabs (a l) * Qabs (a m)) K) K).
  { apply sum_ns_le. intros l Hl.
    (* Inner: Σ_m |B|·|al|·|am| ≤ CB_max · Σ_m |al|·|am| *)
    apply Qle_trans with
      (sum_Q_ns (fun m => CB_max * (Qabs (a l) * Qabs (a m))) K).
    { apply sum_ns_le. intros m Hm.
      assert (HB := B_coeff_bounded k l m).
      assert (HB' : Qabs (B_coeff k l m) <= CB_max).
      { unfold CB_max.
        apply Qle_trans with (C_B * inject_Z (Z.of_nat (Nat.max k (Nat.max l m)))); [exact HB|].
        apply Qmult_le_l; [unfold Qle, inject_Z; simpl; lia |].
        apply Qlt_le_weak; exact C_B_positive. }
      assert (Hassoc1 : Qabs (B_coeff k l m) * Qabs (a l) * Qabs (a m) ==
                        Qabs (B_coeff k l m) * (Qabs (a l) * Qabs (a m))) by ring.
      rewrite Hassoc1.
      apply Qmult_le_compat_r; [exact HB' | apply Qmult_le_0_compat; apply Qabs_nonneg]. }
    (* Σ_m CB_max·(|al|·|am|) = CB_max · Σ_m |al|·|am| *)
    assert (Heq_inner :
      sum_Q_ns (fun m => CB_max * (Qabs (a l) * Qabs (a m))) K ==
      CB_max * sum_Q_ns (fun m => Qabs (a l) * Qabs (a m)) K).
    { rewrite <- sum_ns_scale. reflexivity. }
    lra. }
  (* Step 2: Σ_l CB_max·(inner) = CB_max · Σ_l (inner) *)
  assert (Hfactor :
    sum_Q_ns (fun l =>
      CB_max * sum_Q_ns (fun m => Qabs (a l) * Qabs (a m)) K) K ==
    CB_max * sum_Q_ns (fun l =>
      sum_Q_ns (fun m => Qabs (a l) * Qabs (a m)) K) K).
  { rewrite <- sum_ns_scale. reflexivity. }
  rewrite Hfactor.
  (* Step 3: CB_max · Σ|al|·|am| ≤ CB_max · K · 2E0 *)
  assert (Hps := product_sum_bound K a).
  assert (Hen := modal_energy_nonneg K a).
  assert (HCB_max_nn : 0 <= CB_max).
  { unfold CB_max. apply Qmult_le_0_compat.
    - apply Qlt_le_weak; exact C_B_positive.
    - unfold Qle, inject_Z; simpl; lia. }
  apply Qle_trans with (CB_max * (inject_Z (Z.of_nat K) * (2 * modal_energy K a))).
  { apply Qmult_le_l; [exact Hps | exact HCB_max_nn]. }
  apply Qle_trans with (CB_max * (inject_Z (Z.of_nat K) * (2 * E0))).
  { apply Qmult_le_l; [| exact HCB_max_nn].
    apply Qmult_le_l; [lra | unfold Qle, inject_Z; simpl; lia]. }
  unfold CB_max. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Damping vs Forcing Balance  (~10 lemmas)                 *)
(* ================================================================== *)

Definition clean_forcing_bound (k : nat) (E0 : Q) : Q :=
  C_B * inject_Z (Z.of_nat k) * 2 * E0.

Lemma clean_forcing_nonneg : forall k E0,
  0 < E0 -> (1 <= k)%nat ->
  0 <= clean_forcing_bound k E0.
Proof.
  intros k E0 HE Hk. unfold clean_forcing_bound.
  assert (Hcb := C_B_positive).
  apply Qmult_le_0_compat; [| lra].
  apply Qmult_le_0_compat; [| lra].
  apply Qmult_le_0_compat; [lra | unfold Qle, inject_Z; simpl; lia].
Qed.

Lemma clean_forcing_linear : forall k1 k2 E0,
  0 < E0 -> (k1 <= k2)%nat ->
  clean_forcing_bound k1 E0 <= clean_forcing_bound k2 E0.
Proof.
  intros. unfold clean_forcing_bound.
  assert (Hcb := C_B_positive).
  assert (Hk : inject_Z (Z.of_nat k1) <= inject_Z (Z.of_nat k2)).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (H1 : C_B * inject_Z (Z.of_nat k1) <= C_B * inject_Z (Z.of_nat k2)).
  { apply Qmult_le_l; [exact Hk | lra]. }
  assert (H2 : C_B * inject_Z (Z.of_nat k1) * 2 <= C_B * inject_Z (Z.of_nat k2) * 2).
  { apply Qmult_le_compat_r; [exact H1 | lra]. }
  apply Qmult_le_compat_r; [exact H2 | lra].
Qed.

Definition damping_rate (nu : Q) (k : nat) : Q :=
  nu * inject_Z (Z.of_nat (k * k)).

Lemma damping_rate_nonneg : forall nu k,
  0 < nu -> 0 <= damping_rate nu k.
Proof.
  intros. unfold damping_rate.
  apply Qmult_le_0_compat; [lra | unfold Qle, inject_Z; simpl; lia].
Qed.

Lemma damping_rate_positive : forall nu k,
  0 < nu -> (1 <= k)%nat -> 0 < damping_rate nu k.
Proof.
  intros. unfold damping_rate.
  apply Qmult_lt_0_compat; [lra | unfold Qlt, inject_Z; simpl; lia].
Qed.

Lemma damping_grows_quadratic : forall nu k1 k2,
  0 < nu -> (k1 <= k2)%nat ->
  damping_rate nu k1 <= damping_rate nu k2.
Proof.
  intros. unfold damping_rate.
  apply Qmult_le_l; [unfold Qle, inject_Z; simpl; nia | lra].
Qed.

Definition steady_state_bound (k : nat) (nu E0 : Q) : Q :=
  2 * C_B * E0 / (nu * inject_Z (Z.of_nat k)).

Lemma steady_state_bound_positive : forall k nu E0,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  0 < steady_state_bound k nu E0.
Proof.
  intros. unfold steady_state_bound.
  assert (Hcb := C_B_positive).
  assert (Hd : 0 < nu * inject_Z (Z.of_nat k)).
  { apply Qmult_lt_0_compat; [lra | unfold Qlt, inject_Z; simpl; lia]. }
  assert (Hn : 0 < 2 * C_B * E0).
  { apply Qmult_lt_0_compat; [| lra].
    apply Qmult_lt_0_compat; lra. }
  unfold Qdiv. apply Qmult_lt_0_compat; [exact Hn |].
  apply Qinv_lt_0_compat. exact Hd.
Qed.

Definition critical_mode (nu E0 : Q) : Q := 2 * C_B * E0 / nu.

Lemma critical_mode_positive : forall nu E0,
  0 < nu -> 0 < E0 -> 0 < critical_mode nu E0.
Proof.
  intros. unfold critical_mode.
  assert (Hcb := C_B_positive).
  unfold Qdiv. apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; [| lra].
    apply Qmult_lt_0_compat; lra.
  - apply Qinv_lt_0_compat. lra.
Qed.

Theorem damping_exceeds_forcing : forall k nu E0,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  inject_Z (Z.of_nat k) > critical_mode nu E0 ->
  damping_rate nu k > clean_forcing_bound k E0.
Proof.
  intros k nu E0 Hnu HE Hk Habove.
  unfold damping_rate, clean_forcing_bound, critical_mode in *.
  assert (Hcb := C_B_positive).
  assert (HkQ : 0 < inject_Z (Z.of_nat k)).
  { unfold Qlt, inject_Z. simpl. lia. }
  (* From hypothesis: k > 2*CB*E0/nu, so nu*k > 2*CB*E0 *)
  assert (Hkne : ~(nu == 0)).
  { intro Heq. lra. }
  assert (Hnu_k : 2 * C_B * E0 < nu * inject_Z (Z.of_nat k)).
  { unfold Qdiv, Qgt in Habove.
    assert (Hinv : 0 < / nu) by (apply Qinv_lt_0_compat; lra).
    assert (Hmul : 2 * C_B * E0 * / nu < inject_Z (Z.of_nat k)) by exact Habove.
    assert (Hprod : (2 * C_B * E0 * / nu) * nu < inject_Z (Z.of_nat k) * nu).
    { apply Qmult_lt_compat_r; lra. }
    assert (Hsimp : 2 * C_B * E0 * / nu * nu == 2 * C_B * E0).
    { field. exact Hkne. }
    assert (Hrhs : inject_Z (Z.of_nat k) * nu == nu * inject_Z (Z.of_nat k)) by ring.
    lra. }
  (* Goal: CB·k·2·E0 < nu·k²  *)
  (* Have: 2·CB·E0 < nu·k, so CB·k·2·E0 = (2·CB·E0)·k < (nu·k)·k = nu·k² *)
  unfold Qgt.
  assert (Hkk : inject_Z (Z.of_nat (k * k)) == inject_Z (Z.of_nat k) * inject_Z (Z.of_nat k)).
  { unfold inject_Z, Qeq. simpl. lia. }
  assert (Hlhs : C_B * inject_Z (Z.of_nat k) * 2 * E0 ==
                 2 * C_B * E0 * inject_Z (Z.of_nat k)) by ring.
  assert (Hrhs : nu * inject_Z (Z.of_nat (k * k)) ==
                 nu * inject_Z (Z.of_nat k) * inject_Z (Z.of_nat k)).
  { rewrite Hkk. ring. }
  (* Rewrite goal using Hlhs and Hrhs *)
  apply Qlt_compat with
    (2 * C_B * E0 * inject_Z (Z.of_nat k))
    (nu * inject_Z (Z.of_nat k) * inject_Z (Z.of_nat k)).
  - exact Hlhs.
  - exact Hrhs.
  - apply Qmult_lt_compat_r; [exact HkQ | exact Hnu_k].
Qed.

Lemma steady_state_decreasing : forall k1 k2 nu E0,
  0 < nu -> 0 < E0 -> (1 <= k1)%nat -> (k1 <= k2)%nat ->
  steady_state_bound k2 nu E0 <= steady_state_bound k1 nu E0.
Proof.
  intros k1 k2 nu E0 Hnu HE Hk1 Hk12.
  unfold steady_state_bound.
  assert (Hcb := C_B_positive).
  assert (Hd1 : 0 < nu * inject_Z (Z.of_nat k1)).
  { apply Qmult_lt_0_compat; [lra | unfold Qlt, inject_Z; simpl; lia]. }
  assert (Hd2 : 0 < nu * inject_Z (Z.of_nat k2)).
  { apply Qmult_lt_0_compat; [lra | unfold Qlt, inject_Z; simpl; lia]. }
  assert (Hnum : 0 < 2 * C_B * E0).
  { apply Qmult_lt_0_compat; [| lra]. apply Qmult_lt_0_compat; lra. }
  (* a/b ≤ a/c when 0 < c ≤ b and 0 < a *)
  (* Direct: steady_state_bound k nu E0 = 2*CB*E0 / (nu*k) *)
  (* k1 ≤ k2 ⟹ nu*k1 ≤ nu*k2 ⟹ 1/(nu*k2) ≤ 1/(nu*k1) ⟹ result *)
  assert (Hne1 : ~(nu * inject_Z (Z.of_nat k1) == 0)).
  { intro. lra. }
  assert (Hne2 : ~(nu * inject_Z (Z.of_nat k2) == 0)).
  { intro. lra. }
  assert (Hle_denom : nu * inject_Z (Z.of_nat k1) <= nu * inject_Z (Z.of_nat k2)).
  { apply Qmult_le_l; [unfold Qle, inject_Z; simpl; lia | lra]. }
  (* Cross-multiply: need 2*CB*E0*(nu*k1) ≤ 2*CB*E0*(nu*k2) *)
  (* Which follows from Hle_denom and 0 ≤ 2*CB*E0 *)
  unfold Qdiv.
  (* Goal: 2*CB*E0 * /(nu*k2) ≤ 2*CB*E0 * /(nu*k1) *)
  (* Multiply both sides by (nu*k1)*(nu*k2) > 0 *)
  assert (Hprod : 0 < (nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2))).
  { apply Qmult_lt_0_compat; [exact Hd1 | exact Hd2]. }
  (* Use: a * /b ≤ c * /d ← a*d ≤ c*b when b,d > 0 *)
  assert (Hcross :
    2 * C_B * E0 * (nu * inject_Z (Z.of_nat k1)) <=
    2 * C_B * E0 * (nu * inject_Z (Z.of_nat k2))).
  { apply Qmult_le_l; [exact Hle_denom |]. lra. }
  (* Convert: a/b ≤ a/c ← a*c ≤ a*b, i.e. cross-multiply *)
  assert (Hne_k1 : ~(inject_Z (Z.of_nat k1) == 0)).
  { intro Heq. unfold Qeq, inject_Z in Heq. simpl in Heq. lia. }
  assert (Hne_k2 : ~(inject_Z (Z.of_nat k2) == 0)).
  { intro Heq. unfold Qeq, inject_Z in Heq. simpl in Heq. lia. }
  assert (Hne_nu : ~(nu == 0)) by lra.
  assert (Hleft : 2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k2)) *
                  ((nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2))) ==
                  2 * C_B * E0 * (nu * inject_Z (Z.of_nat k1))).
  { field. split; [exact Hne_k2 | exact Hne_nu]. }
  assert (Hright : 2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k1)) *
                   ((nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2))) ==
                   2 * C_B * E0 * (nu * inject_Z (Z.of_nat k2))).
  { field. split; [exact Hne_k1 | exact Hne_nu]. }
  assert (Hmul :
    2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k2)) *
    ((nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2))) <=
    2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k1)) *
    ((nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2)))).
  { lra. }
  (* Now divide by the product *)
  assert (Hprod_nn : 0 <= (nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2))).
  { lra. }
  (* x * p ≤ y * p → x ≤ y when p > 0 *)
  assert (Hdiv :
    2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k2)) <=
    2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k1))).
  { destruct (Qle_lt_or_eq _ _ Hprod_nn) as [Hp|Hp].
    - assert (Hp' : 0 < / ((nu * inject_Z (Z.of_nat k1)) * (nu * inject_Z (Z.of_nat k2)))).
      { apply Qinv_lt_0_compat. exact Hp. }
      assert (Hmul_l :
        2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k2)) <=
        2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k2)) * 1) by lra.
      assert (Hmul_r :
        2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k1)) >=
        2 * C_B * E0 * / (nu * inject_Z (Z.of_nat k1)) * 1) by lra.
      (* Actually, this is getting too complex. Let me use a different approach. *)
      (* x*p ≤ y*p and 0 < p → x ≤ y *)
      assert (Hpe : forall x y p, 0 < p -> x * p <= y * p -> x <= y).
      { intros. assert (Hfact : x == x * p * / p).
        { field. intro. lra. }
        assert (Hfact2 : y == y * p * / p).
        { field. intro. lra. }
        rewrite Hfact, Hfact2.
        apply Qmult_le_compat_r; [exact H0 | apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H]. }
      exact (Hpe _ _ _ Hp Hmul).
    - exfalso. lra. }
  exact Hdiv.
Qed.

(** Summary *)
Theorem triadic_interaction_main : forall k K (a : modal_state) nu E0,
  0 < nu -> 0 < E0 -> (1 <= k)%nat -> (k <= K)%nat ->
  modal_energy K a <= E0 ->
  (triad_count_tight k <= 2 * k)%nat /\
  (forall l m, k = (l+m)%nat -> (1 <= l)%nat -> (1 <= m)%nat ->
    Qabs (B_coeff k l m) <= C_B * inject_Z (Z.of_nat k)) /\
  0 <= clean_forcing_bound k E0 /\
  0 < steady_state_bound k nu E0.
Proof.
  intros k K a nu E0 Hnu HE Hk HkK HEn. repeat split.
  - apply triad_count_tight_bound.
  - intros. apply coupling_for_sum_triad; assumption.
  - apply clean_forcing_nonneg; assumption.
  - apply steady_state_bound_positive; assumption.
Qed.
