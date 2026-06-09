(** * Tannery.v — теорема Таннери: доминированная сходимость рядов (диагональная)
    Elements: двойная Q-таблица a k n; мажоранта M k; на каждой стадии — конечные суммы.
    Roles:    Tannery = роль-перестановка предела и бесконечной суммы при равномерной мажорации;
              хвост сходящейся ΣM мал + поточечное aₖₙ→0 ⟹ диагональная Σ_{k≤n} aₖₙ → 0.
    Rules:    разбиение Σ_{k≤n}=Σ_{k≤K}+Σ_{K<k≤n} (partial_sum_split); первая часть мала
              (равномерный N по k≤K, finite_uniform_N), вторая ≤ хвост ΣM.

    ЭТА ВЕХА (Tannery-кирпич #2 для ln_mul): машинно — абстрактная теорема Таннери над Q.
    Применение (далее): D_n = Σ_{k≤n}(1/k!)|bracket_{k,n}| → 0, доминанта (1/k!)·2Bᵏ, поточечно
    bracket→0 (eval_pow) ⟹ eval(exp∘log1m)~~exp_R(ln_proc).  Переиспользуемый результат анализа.

    STATUS: 4 Qed, 0 Admitted, 0 axioms (наследует classic через SeriesConvergence/CauchyProduct).
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.

Open Scope Q_scope.

(** Частичная сумма константы: Σ_{k≤K} c = (K+1)·c. *)
Lemma partial_sum_const : forall (c : Q) (K : nat),
  partial_sum (fun _ => c) K == inject_Z (Z.of_nat (S K)) * c.
Proof.
  intros c K. induction K as [|K IH].
  - cbn [partial_sum]. ring.
  - rewrite partial_sum_S, IH.
    assert (HSn : inject_Z (Z.of_nat (S (S K))) == inject_Z (Z.of_nat (S K)) + 1).
    { replace (Z.of_nat (S (S K))) with (Z.of_nat (S K) + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
    rewrite HSn. ring.
Qed.

(** Монотонность частичной суммы при ограничении на k ≤ N. *)
Lemma partial_sum_mono_le : forall (a b : nat -> Q) (N : nat),
  (forall k, (k <= N)%nat -> a k <= b k) -> partial_sum a N <= partial_sum b N.
Proof.
  intros a b N. induction N as [|N IH]; intros H.
  - cbn [partial_sum]. apply H; lia.
  - rewrite partial_sum_S, partial_sum_S.
    apply Qplus_le_compat.
    + apply IH. intros k Hk. apply H; lia.
    + apply H; lia.
Qed.

(** Равномерный порог для конечного семейства сходящихся свойств. *)
Lemma finite_uniform_N : forall (P : nat -> nat -> Prop) (K : nat),
  (forall k, (k <= K)%nat -> exists Nk, forall n, (Nk <= n)%nat -> P k n) ->
  exists N, forall k, (k <= K)%nat -> forall n, (N <= n)%nat -> P k n.
Proof.
  intros P K. induction K as [|K IH]; intros H.
  - destruct (H 0%nat (le_n 0)) as [N0 HN0]. exists N0. intros k Hk n Hn.
    assert (k = 0)%nat by lia. subst k. apply HN0; exact Hn.
  - destruct (H (S K) (le_n (S K))) as [NK HNK].
    destruct (IH (fun k Hk => H k (le_S _ _ Hk))) as [N' HN'].
    exists (Nat.max N' NK). intros k Hk n Hn.
    assert (k <= K \/ k = S K)%nat as [Hle | Heq] by lia.
    + apply HN'; [ exact Hle | lia ].
    + subst k. apply HNK; lia.
Qed.

(** ★★ ТЕОРЕМА ТАННЕРИ (диагональная доминированная сходимость).
    0≤aₖₙ≤Mₖ, ΣM сходится, aₖₙ→0 (поточечно по k) ⟹ Σ_{k≤n} aₖₙ → 0. *)
Theorem tannery : forall (a : nat -> nat -> Q) (M : nat -> Q),
  (forall k n, 0 <= a k n) ->
  (forall k n, a k n <= M k) ->
  is_cauchy (partial_sum M) ->
  (forall k eps, 0 < eps -> exists Nk, forall n, (Nk <= n)%nat -> a k n < eps) ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    partial_sum (fun k => a k n) n < eps.
Proof.
  intros a M Hann Hdom HcauchyM Hconv eps Heps.
  destruct (HcauchyM (eps * (1 # 2)) ltac:(lra)) as [K HK].
  assert (Htail : forall n, (K <= n)%nat ->
            partial_sum M n - partial_sum M K < eps * (1 # 2)).
  { intros n Hn. assert (HK' := HK n K Hn (le_n K)).
    apply Qabs_Qlt_condition in HK'. lra. }
  assert (HSKpos : 0 < inject_Z (Z.of_nat (S K))).
  { change (0:Q) with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
  set (delta := eps / (2 * inject_Z (Z.of_nat (S K)))).
  assert (Hdelta : 0 < delta) by (unfold delta; apply Qlt_shift_div_l; lra).
  destruct (finite_uniform_N (fun k n => a k n < delta) K
              (fun k _ => Hconv k delta Hdelta)) as [N1 HN1].
  exists (Nat.max N1 (S K)). intros n Hn.
  assert (HKn : (S K <= n)%nat) by lia.
  rewrite (partial_sum_split (fun k => a k n) K n HKn).
  apply Qle_lt_trans with (eps * (1#2) + (partial_sum M n - partial_sum M K)).
  - apply Qplus_le_compat.
    + (* Σ_{k≤K} a k n <= (K+1)·delta = eps/2 *)
      apply Qle_trans with (partial_sum (fun _ => delta) K).
      * apply partial_sum_mono_le. intros k Hk.
        apply Qlt_le_weak. apply HN1; [ exact Hk | lia ].
      * rewrite partial_sum_const. unfold delta.
        apply Qle_lteq; right. field. lra.
    + (* Σ_{K<k≤n} a k n <= partial_sum M n - partial_sum M K *)
      assert (HMsplit : partial_sum M n
                        == partial_sum M K
                           + partial_sum (fun j => M (S (K + j))%nat) (n - S K)%nat)
        by (apply (partial_sum_split M K n HKn)).
      assert (Heq2 : partial_sum (fun j => M (S (K + j))%nat) (n - S K)%nat
                     == partial_sum M n - partial_sum M K) by (rewrite HMsplit; ring).
      rewrite <- Heq2.
      apply partial_sum_monotone. intro j. apply Hdom.
  - assert (Ht := Htail n ltac:(lia)). lra.
Qed.

(** Аудит аксиом. *)
Print Assumptions tannery.

(* ================================================================== *)
(*  СВОДКА: теорема Таннери (диагональная доминированная сходимость).   *)
(*  Кирпич #2 внешней половины ln_mul.  ДАЛЕЕ: домината P_{k,n}≤(σ_n)ᵏ   *)
(*  (индукция + conv_le_square) + per-k bracket→0 (eval_pow) + сборка.  *)
(* ================================================================== *)
