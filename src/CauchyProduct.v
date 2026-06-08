(** * CauchyProduct.v — путь I к теореме Мертенса (произведение Коши) над Q

    Цель (горизонт ln_mul из Log2FunctionalEq.v): для абсолютно сходящихся рядов Σaᵢ, Σbⱼ
    их произведение Коши Σcₙ (cₙ = Σ_{i+j=n} aᵢbⱼ) сходится к (Σaᵢ)(Σbⱼ) — теорема Мертенса.
    Это движок, отсутствующий в репо (см. Log2FunctionalEq: автор репо даже Abort-нул
    partial_sum_tail).  Строим с нуля, 0-Admitted, по кускам.

    ЭТОТ ФАЙЛ — ПОЛНАЯ теорема Мертенса (все три вехи):
      1. свёртка conv + конечная ПЕРЕСТАНОВКА сумм (Fubini для треугольных частичных сумм):
           Σ_{n≤N} Σ_{i≤n} gᵢ·h(n−i)  ==  Σ_{i≤N} gᵢ·(частичная сумма h до N−i);
      2. треугольник ⊆ квадрат ⟹ Σ|conv| ≤ (Σ|a|)(Σ|b|) → сходимость свёртки;
      3. РАВЕНСТВО МЕРТЕНСА: series_limit (conv a b) ~~ (series_limit a)·(series_limit b)
         через разностное тождество AₙBₙ−Cₙ = Σ aᵢ·(Bₙ−B(n−i)), структурное расщепление
         вне-диагонали по порогу K (воскрешённый Abort-нутый partial_sum_tail репо) и капстоун ε/2.

    ============ E/R/R разбор ============
      Elements: частичные суммы над Q; свёртка conv a b n.
      Roles:    произведение Коши = роль-перемножение рядов; Fubini = перестановка ролей сумм;
                предел произведения = роль-предел (Мертенс).
      Rules:    partial_sum-рекуррентность; линейность; Nat.sub_succ_l (S N−i = S(N−i) при i≤N);
                расщепление Σ по K; Cauchy-хвосты Σ|a|, Σ|b| → 0.
    ДИАГНОСТИКА (P4): всё конечно на каждой стадии N (Element); предел произведения — role-limit
      (теорема Мертенса), строится КАК ПРОЦЕСС, не как завершённый объект.  0-аксиомно
      (только classic через SeriesConvergence; swap и mertens_diff_eq аксиомо-СВОБОДНЫ).

    STATUS: 19 Qed, 0 Admitted, 0 axioms (только classic; partial_sum_conv_swap и mertens_diff_eq
            аксиомо-СВОБОДНЫ; mertens_cauchy_product — только classic).
            ВСЕ ТРИ ВЕХИ ГОТОВЫ.  Движок ln_mul (Log2FunctionalEq.v) теперь имеет реальный
            фундамент: горизонт ln_mul_functional_equation сводится к этой теореме Мертенса.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Вспомогательное: расширяемость и линейность partial_sum            *)
(* ================================================================== *)

(** Если суммируемые члены равны (по Qeq) до индекса N, то и частичные суммы равны. *)
Lemma partial_sum_ext_le : forall (f g : nat -> Q) (N : nat),
  (forall i, (i <= N)%nat -> f i == g i) -> partial_sum f N == partial_sum g N.
Proof.
  intros f g N. induction N as [|N IH]; intros H.
  - simpl. apply H. lia.
  - simpl.
    assert (HN : partial_sum f N == partial_sum g N).
    { apply IH. intros i Hi. apply H. lia. }
    assert (HS : f (S N) == g (S N)) by (apply H; lia).
    rewrite HN, HS. reflexivity.
Qed.

(** Линейность частичной суммы по сложению членов. *)
Lemma partial_sum_plus : forall (f g : nat -> Q) (N : nat),
  partial_sum (fun i => f i + g i) N == partial_sum f N + partial_sum g N.
Proof.
  intros f g N. induction N as [|N IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(* ================================================================== *)
(*  Свёртка (член произведения Коши)                                   *)
(* ================================================================== *)

(** cₙ = Σ_{i=0}^{n} aᵢ · b(n−i). *)
Definition conv (a b : nat -> Q) (n : nat) : Q :=
  partial_sum (fun i => a i * b (n - i)%nat) n.

(* ================================================================== *)
(*  ★ Сердечник: конечная перестановка сумм (Fubini для треугольника)   *)
(* ================================================================== *)

(** ★ Σ_{n≤N} Σ_{i≤n} gᵢ·h(n−i) == Σ_{i≤N} gᵢ·(частичная сумма h до N−i).
    Группировка треугольной двойной суммы по столбцу i.  Индукция по N с ключом
    S N − i = S(N − i) при i ≤ N (Nat.sub_succ_l) и partial_sum-рекуррентностью. *)
Lemma partial_sum_conv_swap : forall (g h : nat -> Q) (N : nat),
  partial_sum (conv g h) N ==
  partial_sum (fun i => g i * partial_sum h (N - i)%nat) N.
Proof.
  intros g h. induction N as [|N IH].
  - unfold conv. simpl. reflexivity.
  - (* раскрываем обе partial_sum при S N по рекуррентности (дефинизионно) *)
    change (partial_sum (conv g h) (S N))
      with (partial_sum (conv g h) N + conv g h (S N)).
    change (partial_sum (fun i => g i * partial_sum h (S N - i)%nat) (S N))
      with (partial_sum (fun i => g i * partial_sum h (S N - i)%nat) N
            + g (S N) * partial_sum h (S N - S N)%nat).
    (* conv g h (S N) (2-е вхождение conv) раскрываем: Σ_{i≤N} gᵢ·h(SN−i) + g(SN)·h(SN−SN) *)
    unfold conv at 2.
    change (partial_sum (fun i => g i * h (S N - i)%nat) (S N))
      with (partial_sum (fun i => g i * h (S N - i)%nat) N
            + g (S N) * h (S N - S N)%nat).
    replace (S N - S N)%nat with 0%nat by lia.
    change (partial_sum h 0%nat) with (h 0%nat).
    (* IH: partial_sum (conv g h) N -> столбцовая форма с (N−i) *)
    rewrite IH.
    (* Цель: psF N + (psGconv N + g(SN)·h0) == psH' N + g(SN)·h0,
       где F=λi.gᵢ·ps h(N−i), Gconv=λi.gᵢ·h(SN−i), H'=λi.gᵢ·ps h(SN−i). *)
    transitivity (partial_sum (fun i => g i * partial_sum h (N - i)%nat
                                        + g i * h (S N - i)%nat) N
                  + g (S N) * h 0%nat).
    + rewrite partial_sum_plus. ring.
    + rewrite (partial_sum_ext_le
                (fun i => g i * partial_sum h (N - i)%nat + g i * h (S N - i)%nat)
                (fun i => g i * partial_sum h (S N - i)%nat) N).
      * reflexivity.
      * intros i Hi.
        replace (S N - i)%nat with (S (N - i))%nat by lia.
        change (partial_sum h (S (N - i)%nat))
          with (partial_sum h (N - i)%nat + h (S (N - i)%nat)).
        ring.
Qed.

(* ================================================================== *)
(*  Веха 2: треугольник ⊆ квадрат ⟹ сходимость свёртки                  *)
(* ================================================================== *)

(** Вынос постоянного множителя справа. *)
Lemma partial_sum_scale_r : forall (f : nat -> Q) (c : Q) (N : nat),
  partial_sum (fun i => f i * c) N == partial_sum f N * c.
Proof. intros f c N. induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

(** Частичная сумма неотрицательных членов неотрицательна. *)
Lemma partial_sum_nonneg : forall (a : nat -> Q) (N : nat),
  (forall n, 0 <= a n) -> 0 <= partial_sum a N.
Proof.
  intros a N Ha. induction N as [|N IH]; simpl.
  - apply Ha.
  - assert (Ha' := Ha (S N)). lra.
Qed.

(** Монотонность частичной суммы по верхнему индексу (для неотрицательных членов). *)
Lemma partial_sum_le_upper : forall (a : nat -> Q) (m n : nat),
  (forall k, 0 <= a k) -> (m <= n)%nat -> partial_sum a m <= partial_sum a n.
Proof.
  intros a m n Ha Hmn. induction Hmn as [|n Hmn IH].
  - apply Qle_refl.
  - simpl. assert (0 <= a (S n)) by apply Ha. lra.
Qed.

(** Свёртка неотрицательных рядов неотрицательна. *)
Lemma conv_nonneg : forall (g h : nat -> Q) (n : nat),
  (forall k, 0 <= g k) -> (forall k, 0 <= h k) -> 0 <= conv g h n.
Proof.
  intros g h n Hg Hh. unfold conv. apply partial_sum_nonneg.
  intro i. apply Qmult_le_0_compat; [ apply Hg | apply Hh ].
Qed.

(** ★ Треугольник ⊆ квадрат: Σ_{n≤N} conv ≤ (Σ_{≤N} g)(Σ_{≤N} h). *)
Lemma conv_le_square : forall (g h : nat -> Q) (N : nat),
  (forall n, 0 <= g n) -> (forall n, 0 <= h n) ->
  partial_sum (conv g h) N <= partial_sum g N * partial_sum h N.
Proof.
  intros g h N Hg Hh.
  rewrite partial_sum_conv_swap.
  eapply Qle_trans.
  - apply partial_sum_monotone with (b := fun i => g i * partial_sum h N).
    intro i.
    assert (Hle : partial_sum h (N - i)%nat <= partial_sum h N)
      by (apply partial_sum_le_upper; [ exact Hh | lia ]).
    rewrite (Qmult_comm (g i) (partial_sum h (N - i)%nat)),
            (Qmult_comm (g i) (partial_sum h N)).
    apply Qmult_le_compat_r; [ exact Hle | apply Hg ].
  - rewrite partial_sum_scale_r. apply Qle_refl.
Qed.

(** ★ ВЕХА 2: произведение Коши неотрицательных абсолютно-ограниченных рядов СХОДИТСЯ
    (Cauchy над Q).  Через partial_sum_nonneg_bound + треугольник⊆квадрат + границы. *)
Lemma conv_cauchy : forall (g h : nat -> Q) (Mg Mh : Q),
  (forall n, 0 <= g n) -> (forall n, 0 <= h n) ->
  (forall N, partial_sum g N <= Mg) -> (forall N, partial_sum h N <= Mh) ->
  is_cauchy (partial_sum (conv g h)).
Proof.
  intros g h Mg Mh Hg Hh HMg HMh.
  apply partial_sum_nonneg_bound with (B := Mg * Mh).
  - intro n. apply conv_nonneg; assumption.
  - intro N. eapply Qle_trans; [ apply conv_le_square; assumption | ].
    assert (Hg0 : 0 <= partial_sum g N) by (apply partial_sum_nonneg; exact Hg).
    assert (Hh0 : 0 <= partial_sum h N) by (apply partial_sum_nonneg; exact Hh).
    assert (Hmg0 : 0 <= Mg) by (apply Qle_trans with (partial_sum g N); [ exact Hg0 | apply HMg ]).
    eapply Qle_trans.
    + apply Qmult_le_compat_r; [ apply HMg | exact Hh0 ].
    + rewrite (Qmult_comm Mg (partial_sum h N)), (Qmult_comm Mg Mh).
      apply Qmult_le_compat_r; [ apply HMh | exact Hmg0 ].
Qed.

(* ================================================================== *)
(*  Веха 3 (Мертенс), часть A: разностное тождество + оценки            *)
(* ================================================================== *)

(** Линейность частичной суммы по вычитанию. *)
Lemma partial_sum_minus : forall (f g : nat -> Q) (N : nat),
  partial_sum (fun i => f i - g i) N == partial_sum f N - partial_sum g N.
Proof. intros f g N. induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

(** Треугольное неравенство для частичной суммы. *)
Lemma partial_sum_abs_le : forall (f : nat -> Q) (N : nat),
  Qabs (partial_sum f N) <= partial_sum (fun i => Qabs (f i)) N.
Proof.
  intros f N. induction N as [|N IH]; simpl.
  - apply Qle_refl.
  - eapply Qle_trans; [ apply Qabs_triangle | ]. lra.
Qed.

(** ★ РАЗНОСТНОЕ ТОЖДЕСТВО Мертенса: AₙBₙ − Cₙ == Σ_{i≤n} aᵢ·(psb n − psb(n−i)).
    Через Fubini-перестановку (Cₙ) + вынос множителя (AₙBₙ) + линейность.
    Превращает вне-диагональ в контролируемую блочную сумму. *)
Lemma mertens_diff_eq : forall (a b : nat -> Q) (n : nat),
  partial_sum a n * partial_sum b n - partial_sum (conv a b) n
  == partial_sum (fun i => a i * (partial_sum b n - partial_sum b (n - i)%nat)) n.
Proof.
  intros a b n.
  rewrite partial_sum_conv_swap.
  rewrite <- (partial_sum_scale_r a (partial_sum b n) n).
  rewrite <- partial_sum_minus.
  apply partial_sum_ext_le. intros i Hi. ring.
Qed.

(** Блочное треугольное неравенство: |psb n − psb m| ≤ psabs n − psabs m (m ≤ n). *)
Lemma partial_sum_block_abs : forall (b : nat -> Q) (m n : nat),
  (m <= n)%nat ->
  Qabs (partial_sum b n - partial_sum b m)
  <= partial_sum (fun k => Qabs (b k)) n - partial_sum (fun k => Qabs (b k)) m.
Proof.
  intros b m n Hmn. induction Hmn as [|n Hmn IH].
  - assert (H1 : partial_sum b m - partial_sum b m == 0) by ring.
    assert (H2 : partial_sum (fun k => Qabs (b k)) m
                 - partial_sum (fun k => Qabs (b k)) m == 0) by ring.
    rewrite H1, H2. assert (Qabs 0 == 0) by reflexivity. lra.
  - assert (Htri : Qabs (partial_sum b (S n) - partial_sum b m)
                   <= Qabs (partial_sum b n - partial_sum b m) + Qabs (b (S n))).
    { assert (Heq : partial_sum b (S n) - partial_sum b m
                    == (partial_sum b n - partial_sum b m) + b (S n)) by (simpl; ring).
      rewrite Heq. apply Qabs_triangle. }
    eapply Qle_trans; [ exact Htri | ].
    assert (Hps : partial_sum (fun k => Qabs (b k)) (S n)
                  == partial_sum (fun k => Qabs (b k)) n + Qabs (b (S n))) by (simpl; ring).
    rewrite Hps. lra.
Qed.

(** Частичные суммы |b| образуют Cauchy-процесс (если |b| ограничены). *)
Lemma partial_sum_abs_cauchy : forall (b : nat -> Q) (Mb : Q),
  (forall N, partial_sum (fun k => Qabs (b k)) N <= Mb) ->
  is_cauchy (partial_sum (fun k => Qabs (b k))).
Proof.
  intros b Mb HMb.
  apply partial_sum_nonneg_bound with (B := Mb).
  - intro n. apply Qabs_nonneg.
  - exact HMb.
Qed.

(* ================================================================== *)
(*  Веха 3 (Мертенс), часть B: структурное расщепление + капстоун ε/2   *)
(* ================================================================== *)

(** Одношаговое разворачивание частичной суммы (дефинизионно). *)
Lemma partial_sum_S : forall (f : nat -> Q) (n : nat),
  partial_sum f (S n) = partial_sum f n + f (S n).
Proof. reflexivity. Qed.

(** Монотонность частичной суммы по членам (поточечно до N). *)
Lemma partial_sum_le_ext : forall (f g : nat -> Q) (N : nat),
  (forall i, (i <= N)%nat -> f i <= g i) -> partial_sum f N <= partial_sum g N.
Proof.
  intros f g N. induction N as [|N IH]; intros H.
  - simpl. apply H. lia.
  - simpl.
    assert (HN : partial_sum f N <= partial_sum g N)
      by (apply IH; intros i Hi; apply H; lia).
    assert (HS : f (S N) <= g (S N)) by (apply H; lia).
    lra.
Qed.

(** ★ Структурное РАСЩЕПЛЕНИЕ суммы (воскрешённый Abort-нутый partial_sum_tail репо):
    Σ_{i≤n} f == Σ_{i≤K} f + Σ_{0≤j≤n−SK} f(S(K+j))  (хвост за K), при S K ≤ n.
    Индукция по n; ключи: Nat.sub_succ_l (S n − S K = S(n − S K)) и
    K + S(n − S K) = n при S K ≤ n. *)
Lemma partial_sum_split : forall (f : nat -> Q) (K n : nat),
  (S K <= n)%nat ->
  partial_sum f n ==
  partial_sum f K + partial_sum (fun j => f (S (K + j))%nat) (n - S K)%nat.
Proof.
  intros f K n. induction n as [|n IH]; intro Hn.
  - lia.
  - destruct (Nat.eq_dec (S K) (S n)) as [Heq | Hneq].
    + (* K = n: хвост пуст (длина 0) *)
      assert (HKn : K = n) by lia. subst K.
      rewrite partial_sum_S.
      replace (S n - S n)%nat with 0%nat by lia.
      assert (Hz : partial_sum (fun j => f (S (n + j))%nat) 0 == f (S n)).
      { simpl. replace (n + 0)%nat with n by lia. reflexivity. }
      rewrite Hz. reflexivity.
    + (* S K < S n, т.е. S K ≤ n: разворачиваем хвост на один шаг *)
      assert (HSKn : (S K <= n)%nat) by lia.
      rewrite partial_sum_S.
      rewrite (IH HSKn).
      replace (S n - S K)%nat with (S (n - S K))%nat by lia.
      rewrite partial_sum_S.
      cbv beta.
      replace (S (K + S (n - S K)))%nat with (S n) by lia.
      ring.
Qed.

(** ★ КЛЮЧЕВАЯ ОЦЕНКА Мертенса (блочная).  При S K ≤ n и Mb ≥ Σ|b|:
        |AₙBₙ − Cₙ|  ≤  (Σ_{i≤K}|aᵢ|)·(Σ|b| на хвосте (n−K, n])
                       +  Mb·(Σ|a| на (K, n]).
    Доказательство: разностное тождество (mertens_diff_eq) под Qabs → треугольник →
    расщепление вне-диагонали по K (partial_sum_split).  ГОЛОВА i≤K: блок b у конца
    (n−i ≥ n−K) мажорируется блоком (n−K, n]; ХВОСТ i>K: |Bn − B(n−i)| ≤ Σ|b| ≤ Mb. *)
Lemma mertens_error_bound : forall (a b : nat -> Q) (K n : nat) (Mb : Q),
  (S K <= n)%nat ->
  (forall N, partial_sum (fun k => Qabs (b k)) N <= Mb) ->
  Qabs (partial_sum a n * partial_sum b n - partial_sum (conv a b) n)
  <= partial_sum (fun k => Qabs (a k)) K
       * (partial_sum (fun k => Qabs (b k)) n
          - partial_sum (fun k => Qabs (b k)) (n - K)%nat)
     + Mb * (partial_sum (fun k => Qabs (a k)) n
             - partial_sum (fun k => Qabs (a k)) K).
Proof.
  intros a b K n Mb HKn HMb.
  (* 1) разностное тождество Мертенса под Qabs *)
  assert (Hd : partial_sum a n * partial_sum b n - partial_sum (conv a b) n
               == partial_sum (fun i => a i
                     * (partial_sum b n - partial_sum b (n - i)%nat)) n)
    by (apply mertens_diff_eq).
  rewrite Hd.
  (* 2) треугольник: |Σ Fᵢ| ≤ Σ |Fᵢ| *)
  eapply Qle_trans; [ apply partial_sum_abs_le | ]. cbv beta.
  (* 3) |aᵢ·(…)| = |aᵢ|·|…| *)
  rewrite (partial_sum_ext_le
             _ (fun i => Qabs (a i)
                  * Qabs (partial_sum b n - partial_sum b (n - i)%nat)) n).
  2:{ intros i _. rewrite Qabs_Qmult. reflexivity. }
  (* 4) расщепление Σ по K: голова (≤K) + хвост (>K) *)
  rewrite (partial_sum_split
             (fun i => Qabs (a i)
                * Qabs (partial_sum b n - partial_sum b (n - i)%nat)) K n HKn).
  apply Qplus_le_compat.
  - (* ===== ГОЛОВА: Σ_{i≤K} |aᵢ|·|Bn−B(n−i)| ≤ (Σ_{≤K}|a|)·(Σ|b| на (n−K,n]) ===== *)
    eapply Qle_trans.
    + apply partial_sum_le_ext with
        (g := fun i => Qabs (a i)
                 * (partial_sum (fun k => Qabs (b k)) n
                    - partial_sum (fun k => Qabs (b k)) (n - K)%nat)).
      intros i Hi.
      rewrite (Qmult_comm (Qabs (a i))
                 (Qabs (partial_sum b n - partial_sum b (n - i)%nat))).
      rewrite (Qmult_comm (Qabs (a i))
                 (partial_sum (fun k => Qabs (b k)) n
                  - partial_sum (fun k => Qabs (b k)) (n - K)%nat)).
      apply Qmult_le_compat_r; [ | apply Qabs_nonneg ].
      eapply Qle_trans.
      { apply partial_sum_block_abs. lia. }
      assert (Hmon : partial_sum (fun k => Qabs (b k)) (n - K)%nat
                     <= partial_sum (fun k => Qabs (b k)) (n - i)%nat)
        by (apply partial_sum_le_upper; [ intro; apply Qabs_nonneg | lia ]).
      lra.
    + rewrite partial_sum_scale_r. apply Qle_refl.
  - (* ===== ХВОСТ: Σ_{i>K} |aᵢ|·|Bn−B(n−i)| ≤ Mb·(Σ|a| на (K,n]) ===== *)
    cbv beta.
    eapply Qle_trans.
    + apply partial_sum_le_ext with
        (g := fun j => Qabs (a (S (K + j))%nat) * Mb).
      intros j _.
      rewrite (Qmult_comm (Qabs (a (S (K + j))%nat))
                 (Qabs (partial_sum b n - partial_sum b (n - S (K + j))%nat))).
      rewrite (Qmult_comm (Qabs (a (S (K + j))%nat)) Mb).
      apply Qmult_le_compat_r; [ | apply Qabs_nonneg ].
      eapply Qle_trans.
      { apply partial_sum_block_abs. lia. }
      assert (Hnn : 0 <= partial_sum (fun k => Qabs (b k)) (n - S (K + j))%nat)
        by (apply partial_sum_nonneg; intro; apply Qabs_nonneg).
      assert (Hub := HMb n). lra.
    + rewrite partial_sum_scale_r.
      assert (Hsplit := partial_sum_split (fun k => Qabs (a k)) K n HKn).
      cbv beta in Hsplit.
      assert (HX : partial_sum (fun j => Qabs (a (S (K + j))%nat)) (n - S K)%nat
                   == partial_sum (fun k => Qabs (a k)) n
                      - partial_sum (fun k => Qabs (a k)) K)
        by (rewrite Hsplit; ring).
      rewrite HX.
      rewrite (Qmult_comm (partial_sum (fun k => Qabs (a k)) n
                           - partial_sum (fun k => Qabs (a k)) K) Mb).
      apply Qle_refl.
Qed.

(** ★★★ ТЕОРЕМА МЕРТЕНСА (произведение Коши над Q как процесс).
    Для абсолютно ограниченных рядов Σaᵢ, Σbⱼ (Σ|a| ≤ Ma, Σ|b| ≤ Mb) предел произведения
    Коши Σcₙ (cₙ = conv a b n) совпадает с произведением пределов:
        series_limit (conv a b)  ~~  (series_limit a)·(series_limit b).
    Капстоун ε/2: K — порог Коши для Σ|a| (хвост за K), Nb — для Σ|b| (блок у конца);
    при n ≥ SK+Nb+K блочная оценка mertens_error_bound даёт обе части < ε/2. *)
Theorem mertens_cauchy_product :
  forall (a b : nat -> Q) (Ma Mb : Q)
    (HMa : forall N, partial_sum (fun k => Qabs (a k)) N <= Ma)
    (HMb : forall N, partial_sum (fun k => Qabs (b k)) N <= Mb)
    (HSa : is_cauchy (partial_sum a))
    (HSb : is_cauchy (partial_sum b))
    (Hconv : is_cauchy (partial_sum (conv a b))),
  series_limit (conv a b) Hconv
  ~~ cauchy_mul (series_limit a HSa) (series_limit b HSb).
Proof.
  intros a b Ma Mb HMa HMb HSa HSb Hconv.
  (* Ma, Mb ≥ 0 *)
  assert (HMa0 : 0 <= Ma).
  { assert (H := HMa 0%nat). simpl in H.
    eapply Qle_trans; [ apply Qabs_nonneg | exact H ]. }
  assert (HMb0 : 0 <= Mb).
  { assert (H := HMb 0%nat). simpl in H.
    eapply Qle_trans; [ apply Qabs_nonneg | exact H ]. }
  (* Σ|a|, Σ|b| — Cauchy (ограничены + монотонны) *)
  assert (HCa : is_cauchy (partial_sum (fun k => Qabs (a k))))
    by (apply partial_sum_nonneg_bound with (B := Ma);
        [ intro; apply Qabs_nonneg | exact HMa ]).
  assert (HCb : is_cauchy (partial_sum (fun k => Qabs (b k))))
    by (apply partial_sum_nonneg_bound with (B := Mb);
        [ intro; apply Qabs_nonneg | exact HMb ]).
  unfold cauchy_equiv. intros eps Heps.
  (* δ_a (хвост), δ_b (голова) *)
  assert (Hda : 0 < eps * (1#2) * / (Mb + 1))
    by (apply Qmult_lt_0_compat;
        [ apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra ]).
  assert (Hdb : 0 < eps * (1#2) * / (Ma + 1))
    by (apply Qmult_lt_0_compat;
        [ apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra ]).
  destruct (HCa (eps * (1#2) * / (Mb + 1)) Hda) as [K HK].
  destruct (HCb (eps * (1#2) * / (Ma + 1)) Hdb) as [Nb HNb].
  exists (S K + Nb + K)%nat. intros n Hn.
  assert (HKn : (S K <= n)%nat) by lia.
  (* привести cs_seq пределов к partial_sum (дефинизионно) *)
  change (cs_seq (series_limit (conv a b) Hconv) n)
    with (partial_sum (conv a b) n).
  change (cs_seq (cauchy_mul (series_limit a HSa) (series_limit b HSb)) n)
    with (partial_sum a n * partial_sum b n).
  rewrite Qabs_Qminus.  (* |Cₙ − AₙBₙ| = |AₙBₙ − Cₙ| *)
  (* ===== ГОЛОВА < ε/2 ===== *)
  assert (HDb_nn : 0 <= partial_sum (fun k => Qabs (b k)) n
                        - partial_sum (fun k => Qabs (b k)) (n - K)%nat).
  { assert (partial_sum (fun k => Qabs (b k)) (n - K)%nat
            <= partial_sum (fun k => Qabs (b k)) n)
      by (apply partial_sum_le_upper; [ intro; apply Qabs_nonneg | lia ]). lra. }
  assert (HDb_lt : partial_sum (fun k => Qabs (b k)) n
                   - partial_sum (fun k => Qabs (b k)) (n - K)%nat
                   < eps * (1#2) * / (Ma + 1)).
  { assert (Hcb := HNb n (n - K)%nat ltac:(lia) ltac:(lia)).
    rewrite (Qabs_pos _ HDb_nn) in Hcb. exact Hcb. }
  assert (HP1 : partial_sum (fun k => Qabs (a k)) K
                * (partial_sum (fun k => Qabs (b k)) n
                   - partial_sum (fun k => Qabs (b k)) (n - K)%nat)
                < eps * (1#2)).
  { assert (HpaK : partial_sum (fun k => Qabs (a k)) K <= Ma) by apply HMa.
    assert (Hs1 : partial_sum (fun k => Qabs (a k)) K
                  * (partial_sum (fun k => Qabs (b k)) n
                     - partial_sum (fun k => Qabs (b k)) (n - K)%nat)
                  <= (Ma + 1)
                  * (partial_sum (fun k => Qabs (b k)) n
                     - partial_sum (fun k => Qabs (b k)) (n - K)%nat)).
    { apply Qmult_le_compat_r; [ lra | exact HDb_nn ]. }
    assert (Hs2 : (Ma + 1)
                  * (partial_sum (fun k => Qabs (b k)) n
                     - partial_sum (fun k => Qabs (b k)) (n - K)%nat)
                  < (Ma + 1) * (eps * (1#2) * / (Ma + 1))).
    { setoid_replace ((Ma + 1)
        * (partial_sum (fun k => Qabs (b k)) n
           - partial_sum (fun k => Qabs (b k)) (n - K)%nat))
        with ((partial_sum (fun k => Qabs (b k)) n
               - partial_sum (fun k => Qabs (b k)) (n - K)%nat) * (Ma + 1)) by ring.
      setoid_replace ((Ma + 1) * (eps * (1#2) * / (Ma + 1)))
        with ((eps * (1#2) * / (Ma + 1)) * (Ma + 1)) by ring.
      apply Qmult_lt_compat_r; [ lra | exact HDb_lt ]. }
    assert (Hs3 : (Ma + 1) * (eps * (1#2) * / (Ma + 1)) == eps * (1#2))
      by (field; lra).
    lra. }
  (* ===== ХВОСТ < ε/2 ===== *)
  assert (HEa_nn : 0 <= partial_sum (fun k => Qabs (a k)) n
                        - partial_sum (fun k => Qabs (a k)) K).
  { assert (partial_sum (fun k => Qabs (a k)) K
            <= partial_sum (fun k => Qabs (a k)) n)
      by (apply partial_sum_le_upper; [ intro; apply Qabs_nonneg | lia ]). lra. }
  assert (HEa_lt : partial_sum (fun k => Qabs (a k)) n
                   - partial_sum (fun k => Qabs (a k)) K
                   < eps * (1#2) * / (Mb + 1)).
  { assert (Hca := HK n K ltac:(lia) ltac:(lia)).
    rewrite (Qabs_pos _ HEa_nn) in Hca. exact Hca. }
  assert (HP2 : Mb * (partial_sum (fun k => Qabs (a k)) n
                      - partial_sum (fun k => Qabs (a k)) K)
                < eps * (1#2)).
  { assert (Hs1 : Mb * (partial_sum (fun k => Qabs (a k)) n
                        - partial_sum (fun k => Qabs (a k)) K)
                  <= (Mb + 1) * (partial_sum (fun k => Qabs (a k)) n
                                 - partial_sum (fun k => Qabs (a k)) K)).
    { apply Qmult_le_compat_r; [ lra | exact HEa_nn ]. }
    assert (Hs2 : (Mb + 1) * (partial_sum (fun k => Qabs (a k)) n
                              - partial_sum (fun k => Qabs (a k)) K)
                  < (Mb + 1) * (eps * (1#2) * / (Mb + 1))).
    { setoid_replace ((Mb + 1) * (partial_sum (fun k => Qabs (a k)) n
                                  - partial_sum (fun k => Qabs (a k)) K))
        with ((partial_sum (fun k => Qabs (a k)) n
               - partial_sum (fun k => Qabs (a k)) K) * (Mb + 1)) by ring.
      setoid_replace ((Mb + 1) * (eps * (1#2) * / (Mb + 1)))
        with ((eps * (1#2) * / (Mb + 1)) * (Mb + 1)) by ring.
      apply Qmult_lt_compat_r; [ lra | exact HEa_lt ]. }
    assert (Hs3 : (Mb + 1) * (eps * (1#2) * / (Mb + 1)) == eps * (1#2))
      by (field; lra).
    lra. }
  (* собираем: |AₙBₙ − Cₙ| ≤ ГОЛОВА + ХВОСТ < ε/2 + ε/2 = ε *)
  eapply Qle_lt_trans.
  - exact (mertens_error_bound a b K n Mb HKn HMb).
  - lra.
Qed.

(** Аудит аксиом: должно быть ТОЛЬКО classic. *)
Print Assumptions partial_sum_conv_swap.
Print Assumptions mertens_cauchy_product.
Print Assumptions mertens_diff_eq.
Print Assumptions conv_cauchy.

(* ================================================================== *)
(*  СВОДКА (теорема Мертенса, ПОЛНАЯ, 19 Qed, 0 Admitted):              *)
(*   1. conv + Fubini-перестановка (partial_sum_conv_swap, аксиомо-своб.)*)
(*   2. сходимость произведения Коши (conv_cauchy)                       *)
(*   3. mertens_cauchy_product (только classic):                         *)
(*      series_limit(conv a b) ~~ cauchy_mul(series_limit a)(s_l b)      *)
(*      via mertens_diff_eq (аксиомо-своб.) + partial_sum_split + ε/2.   *)
(*  Применение: фундамент горизонта ln_mul_functional_equation          *)
(*  (Log2FunctionalEq.v) — ln(x)+ln(y) для рядов через произведение Коши.*)
(* ================================================================== *)
