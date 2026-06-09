(** * PolyTimesGeom.v — n·zⁿ → 0: полином умножить на геометрию стремится к нулю
    Elements: рациональные стадии aₙ = n·zⁿ — конечные Q на каждом n.
    Roles:    aₙ затухает ГЕОМЕТРИЧЕСКИ после порога N₀ (отношение aₙ₊₁/aₙ=(n+1)/n·z ≤ r<1).
    Rules:    geom_decay (отношение ≤ r ⟹ aₙ ≤ a_{N₀}·rⁿ⁻ᴺ⁰); Qpow_limit_zero (r<1 ⟹ rᵐ→0).

    ЭТА ВЕХА (первый кирпич Tannery-ядра ln_mul): машинно — n·zⁿ → 0 для 0≤z<1.
    Финальный шаг оценки разности D_n ≤ z^{n+1}·exp(Hₙ) ≤ e·n·z^{n+1} → 0.  Самостоятельный
    переиспользуемый результат анализа, которого в репозитории не было.

    STATUS: 2 Qed, 0 Admitted, 0 axioms (наследует classic через SeriesConvergence).
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import SeriesConvergence.

Open Scope Q_scope.

(** Геометрическое затухание из ограничения отношения. *)
Lemma geom_decay : forall (r : Q) (a : nat -> Q) (N0 : nat),
  0 <= r ->
  (forall n, (N0 <= n)%nat -> 0 <= a n) ->
  (forall n, (N0 <= n)%nat -> a (S n) <= r * a n) ->
  forall d : nat, a (N0 + d)%nat <= a N0 * Qpow r d.
Proof.
  intros r a N0 Hr Hnn Hratio d. induction d as [|d IH].
  - rewrite Nat.add_0_r. cbn [Qpow]. rewrite Qmult_1_r. apply Qle_refl.
  - replace (N0 + S d)%nat with (S (N0 + d))%nat by lia.
    eapply Qle_trans; [ apply Hratio; lia | ].
    cbn [Qpow].
    apply Qle_trans with (r * (a N0 * Qpow r d)).
    + rewrite (Qmult_comm r (a (N0 + d)%nat)), (Qmult_comm r (a N0 * Qpow r d)).
      apply Qmult_le_compat_r; [ exact IH | exact Hr ].
    + apply Qle_lteq; right; ring.
Qed.

(** ★ n·zⁿ → 0 для 0 ≤ z < 1. *)
Theorem n_times_pow_limit : forall z : Q, 0 <= z -> z < 1 ->
  forall eps : Q, 0 < eps ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    inject_Z (Z.of_nat n) * Qpow z n < eps.
Proof.
  intros z Hz Hz1 eps Heps.
  destruct (Qlt_le_dec 0 z) as [Hzpos | Hz0].
  - (* 0 < z < 1 *)
    set (r := (1 + z) * (1 # 2)).
    assert (Hr0 : 0 < r) by (unfold r; lra).
    assert (Hr1 : r < 1) by (unfold r; lra).
    set (a := fun n => inject_Z (Z.of_nat n) * Qpow z n).
    assert (H1z : 0 < 1 - z) by lra.
    destruct (Qarchimedean (2 * z / (1 - z))) as [p Hp].
    set (N0 := Pos.to_nat p).
    assert (HN0pos : (0 < N0)%nat) by (unfold N0; apply Pos2Nat.is_pos).
    assert (HN0 : 2 * z / (1 - z) < inject_Z (Z.of_nat N0)).
    { unfold N0. rewrite (positive_nat_Z p). exact Hp. }
    (* отношение: для n ≥ N0, a(S n) ≤ r·a n *)
    assert (Hratio : forall n, (N0 <= n)%nat -> a (S n) <= r * a n).
    { intros n Hn. unfold a.
      assert (HnN0 : inject_Z (Z.of_nat N0) <= inject_Z (Z.of_nat n)).
      { rewrite <- Zle_Qle. apply inj_le. lia. }
      assert (Hbig : 2 * z / (1 - z) < inject_Z (Z.of_nat n)) by lra.
      assert (Hlin : 2 * z < inject_Z (Z.of_nat n) * (1 - z)).
      { assert (Hm : (2 * z / (1 - z)) * (1 - z) == 2 * z) by (field; lra).
        nra. }
      assert (HSn : inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1).
      { replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      cbn [Qpow]. rewrite HSn.
      assert (Hpn : 0 <= Qpow z n) by (apply Qpow_nonneg; lra).
      apply Qle_trans with ((r * inject_Z (Z.of_nat n)) * Qpow z n).
      + assert (Heq : (inject_Z (Z.of_nat n) + 1) * (z * Qpow z n)
                      == ((inject_Z (Z.of_nat n) + 1) * z) * Qpow z n) by ring.
        rewrite Heq.
        apply Qmult_le_compat_r; [ | exact Hpn ].
        unfold r.
        apply (Qmult_le_l _ _ 2 ltac:(lra)).
        assert (Hsimp : 2 * ((1 + z) * (1 # 2) * inject_Z (Z.of_nat n))
                        == (1 + z) * inject_Z (Z.of_nat n)) by ring.
        rewrite Hsimp. nra.
      + apply Qle_lteq; right. ring. }
    assert (Hann : forall n, (N0 <= n)%nat -> 0 <= a n).
    { intros n Hn. unfold a. apply Qmult_le_0_compat.
      - change (0:Q) with (inject_Z 0). rewrite <- Zle_Qle. apply Nat2Z.is_nonneg.
      - apply Qpow_nonneg; lra. }
    assert (HaN0pos : 0 < a N0).
    { unfold a. apply Qmult_lt_0_compat.
      - change (0:Q) with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
      - apply Qpow_pos; exact Hzpos. }
    destruct (Qpow_limit_zero r (Qlt_le_weak _ _ Hr0) Hr1 (eps / a N0)
                ltac:(apply Qlt_shift_div_l; [ exact HaN0pos | lra ])) as [M HM].
    exists (N0 + M)%nat. intros n Hn.
    assert (Hd := geom_decay r a N0 (Qlt_le_weak _ _ Hr0) Hann Hratio (n - N0)%nat).
    replace (N0 + (n - N0))%nat with n in Hd by lia.
    assert (Hpow : Qpow r (n - N0)%nat < eps / a N0) by (apply HM; lia).
    apply Qle_lt_trans with (a N0 * Qpow r (n - N0)%nat); [ exact Hd | ].
    assert (Hed : eps / a N0 * a N0 == eps) by (field; lra).
    assert (HQnn : 0 <= Qpow r (n - N0)%nat) by (apply Qpow_nonneg; lra).
    nra.
  - (* z = 0 *)
    assert (Hzeq : z == 0) by lra.
    exists 1%nat. intros n Hn.
    assert (Hp0 : Qpow z n == 0).
    { destruct n as [|m]; [ lia | ]. cbn [Qpow].
      transitivity (0 * Qpow z m).
      - apply Qmult_comp; [ exact Hzeq | reflexivity ].
      - ring. }
    rewrite Hp0. rewrite Qmult_0_r. exact Heps.
Qed.

(** Аудит аксиом. *)
Print Assumptions n_times_pow_limit.

(* ================================================================== *)
(*  СВОДКА: n·zⁿ → 0 (0≤z<1).  Первый кирпич Tannery-ядра ln_mul        *)
(*  (D_n ≤ e·n·z^{n+1} → 0).  ДАЛЕЕ: exp(Hₙ)≤e·n (гармонич.) + хвост.   *)
(* ================================================================== *)
