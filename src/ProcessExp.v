(** * ProcessExp.v — ВЕЩЕСТВЕННАЯ (процессная) экспонента exp_R : CauchySeq → CauchySeq

    Цель (горизонт ln_mul): определить экспоненту вещественного числа-ПРОЦЕССА P (а не
    рационального аргумента, как exp_limit), доказать корректность (Cauchy) и теорему
    сложения для процессов.  Это движок, отсутствующий в репо: его требует маршрут
    L(x)+L(y)~~L(x⊕y) (нужна E(L(x)), exp от ПРОЦЕССА L(x)).

    КОНСТРУКЦИЯ (через completeness): exp_R P := diagonal_limit (fun n => exp_limit (P n)),
    где diagonal_limit (Completeness.v) берёт предел meta-Cauchy последовательности процессов.
    meta_cauchy (fun n => exp_limit (P n)) требует двух равномерных оценок (P ограничен B):
      (1) equi-Cauchy: хвост exp-ряда РАВНОМЕРНО мал для всех |arg|≤B (мажорируется exp_term B);
      (2) cross-closeness: близкие аргументы → близкие частичные суммы (Липшиц по аргументу),
          опираясь на |aᵏ−bᵏ| ≤ k·Bᵏ⁻¹·|a−b| (телескоп степеней).

    ЭТОТ ФАЙЛ (первая веха): аналитический сердечник — оценки степеней:
      Qpow_le_mono_base (монотонность Qpow по основанию) и
      Qpow_diff_bound : |aᵏ⁺¹−bᵏ⁺¹| ≤ (k+1)·Bᵏ·|a−b| (при |a|,|b|≤B) — Липшиц-ядро.

    ============ E/R/R разбор ============
      Elements: рациональные приближения P n; exp_term (P n) k; диагональ exp_limit (P n).
      Roles:    exp_R = роль-функция (вещественная экспонента); диагональ = роль-предел
                ПОСЛЕДОВАТЕЛЬНОСТИ процессов (completeness); ограниченность P = роль-граница B.
      Rules:    meta_cauchy = (равномерный хвост exp над |·|≤B) ∧ (Липшиц |aᵏ−bᵏ|≤k·Bᵏ⁻¹·|a−b|);
                diagonal_converges связывает exp_limit(P n) → exp_R P.
      P4: exp_R(P) — role-limit ПОСЛЕДОВАТЕЛЬНОСТИ role-limit'ов (процесс процессов), но
          diagonal_limit делает из него один Cauchy-процесс.  0-аксиомно (только classic).

    STATUS: 15 Qed, 0 Admitted, 0 axioms (все оценки аксиомо-СВОБОДНЫ; exp_R/exp_meta_cauchy/exp_R_add — classic).
            ★★★ ВЕЩЕСТВЕННАЯ ЭКСПОНЕНТА ПОСТРОЕНА + ГОМОМОРФИЗМ: exp_R : CauchySeq → CauchySeq (exp от ПРОЦЕССА,
            через diagonal_limit) И exp_R_add : exp_R(P+R) ~~ exp_R(P)·exp_R(R) — ТЕОРЕМА СЛОЖЕНИЯ.
            Пилоны meta_cauchy: equi-Cauchy (exp_partial_tail_bound[_sym]) + cross-closeness (exp_partial_lipschitz
            + exp_pred_sum_bound).  Теорема сложения — ДИАГОНАЛЬНЫЙ Мертенс: exp_R_diag_mertens_bound (per-n
            разностная оценка с равномерными мажорантами exp_term BP/BR, через exp_conv_id + mertens_error_bound,
            АКСИОМО-СВОБОДНА) + капстоун ε/2 на Cauchy-модулях exp-рядов от BP, BR.
            ОСТАЁТСЯ для ln_mul: E∘L=1/(1−x) (exp_R(L(x))~~геометрический предел) и инъективность exp_R.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import PowerSeries.
From ToS Require Import CauchyProduct.
From ToS Require Import ExpFunctionalEquation.
From ToS Require Import Completeness.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Аналитический сердечник: оценки степеней Qpow                       *)
(* ================================================================== *)

(** Одношаговое разворачивание Qpow (дефинизионно). *)
Lemma Qpow_S : forall (x : Q) (k : nat), Qpow x (S k) = x * Qpow x k.
Proof. reflexivity. Qed.

(** Монотонность Qpow по основанию (для неотрицательных). *)
Lemma Qpow_le_mono_base : forall (a b : Q) (k : nat),
  0 <= a -> a <= b -> Qpow a k <= Qpow b k.
Proof.
  intros a b k Ha Hab. induction k as [|k IH].
  - simpl. apply Qle_refl.
  - rewrite !Qpow_S.
    apply Qle_trans with (a * Qpow b k).
    + rewrite (Qmult_comm a (Qpow a k)), (Qmult_comm a (Qpow b k)).
      apply Qmult_le_compat_r; [ exact IH | exact Ha ].
    + apply Qmult_le_compat_r; [ exact Hab | apply Qpow_nonneg; lra ].
Qed.

(** ★ ЛИПШИЦ-ЯДРО: |aᵏ⁺¹ − bᵏ⁺¹| ≤ (k+1)·Bᵏ·|a−b| при |a|,|b| ≤ B.
    Телескоп степеней: aᵏ⁺²−bᵏ⁺² = a(aᵏ⁺¹−bᵏ⁺¹) + (a−b)bᵏ⁺¹; индукция по k. *)
Lemma Qpow_diff_bound : forall (a b B : Q) (k : nat),
  Qabs a <= B -> Qabs b <= B ->
  Qabs (Qpow a (S k) - Qpow b (S k))
  <= inject_Z (Z.of_nat (S k)) * Qpow B k * Qabs (a - b).
Proof.
  intros a b B k Ha Hb.
  assert (HB : 0 <= B) by (eapply Qle_trans; [ apply Qabs_nonneg | exact Ha ]).
  induction k as [|k IH].
  - (* k = 0 : |a − b| ≤ 1·1·|a−b| *)
    rewrite !Qpow_S.
    change (Qpow a 0%nat) with (1 : Q). change (Qpow b 0%nat) with (1 : Q).
    change (Qpow B 0%nat) with (1 : Q).
    assert (E1 : a * 1 - b * 1 == a - b) by ring. rewrite E1.
    assert (E2 : inject_Z (Z.of_nat 1%nat) * 1 == 1) by (vm_compute; reflexivity).
    rewrite E2. lra.
  - (* шаг *)
    rewrite (Qpow_S a (S k)), (Qpow_S b (S k)).
    assert (Hdec : a * Qpow a (S k) - b * Qpow b (S k)
                   == a * (Qpow a (S k) - Qpow b (S k)) + (a - b) * Qpow b (S k)) by ring.
    rewrite Hdec.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    rewrite !Qabs_Qmult.
    assert (T1 : Qabs a * Qabs (Qpow a (S k) - Qpow b (S k))
                 <= B * (inject_Z (Z.of_nat (S k)) * Qpow B k * Qabs (a - b))).
    { eapply Qle_trans.
      - apply Qmult_le_compat_r; [ exact Ha | apply Qabs_nonneg ].
      - rewrite (Qmult_comm B (Qabs (Qpow a (S k) - Qpow b (S k)))),
                (Qmult_comm B (inject_Z (Z.of_nat (S k)) * Qpow B k * Qabs (a - b))).
        apply Qmult_le_compat_r; [ exact IH | exact HB ]. }
    assert (T2 : Qabs (a - b) * Qabs (Qpow b (S k))
                 <= Qabs (a - b) * Qpow B (S k)).
    { rewrite Qabs_Qpow.
      rewrite (Qmult_comm (Qabs (a - b)) (Qpow (Qabs b) (S k))),
              (Qmult_comm (Qabs (a - b)) (Qpow B (S k))).
      apply Qmult_le_compat_r; [ apply Qpow_le_mono_base; [ apply Qabs_nonneg | exact Hb ]
                              | apply Qabs_nonneg ]. }
    eapply Qle_trans; [ apply Qplus_le_compat; [ exact T1 | exact T2 ] | ].
    assert (Heq : B * (inject_Z (Z.of_nat (S k)) * Qpow B k * Qabs (a - b))
                  + Qabs (a - b) * Qpow B (S k)
                  == inject_Z (Z.of_nat (S (S k))) * Qpow B (S k) * Qabs (a - b)).
    { rewrite (Qpow_S B k).
      assert (Hinj : inject_Z (Z.of_nat (S (S k))) == inject_Z (Z.of_nat (S k)) + 1).
      { replace (Z.of_nat (S (S k))) with (Z.of_nat (S k) + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      rewrite Hinj. ring. }
    rewrite Heq. apply Qle_refl.
Qed.

(* ================================================================== *)
(*  Перенос Липшиц-оценки на exp_term (деление на факториал)            *)
(* ================================================================== *)

(** Рекуррентность факториала (дефинизионно). *)
Lemma Qfact_S : forall j, Qfact (S j) = inject_Z (Z.of_nat (S j)) * Qfact j.
Proof. reflexivity. Qed.

(** ★ Липшиц для члена exp-ряда: |exp_term a (Sj) − exp_term b (Sj)| ≤ exp_term B j · |a−b|.
    Делим Qpow_diff_bound на (Sj)!: inject_Z(Sj)·/(Sj)! = /j!, поэтому (Sj)·Bʲ/(Sj)! = Bʲ/j!. *)
Lemma exp_term_diff_bound : forall (a b B : Q) (j : nat),
  Qabs a <= B -> Qabs b <= B ->
  Qabs (exp_term a (S j) - exp_term b (S j)) <= exp_term B j * Qabs (a - b).
Proof.
  intros a b B j Ha Hb.
  assert (HSj : 0 < inject_Z (Z.of_nat (S j))) by (unfold Qlt; simpl; lia).
  assert (HSjn : ~ inject_Z (Z.of_nat (S j)) == 0) by lra.
  assert (HfSj : 0 < Qfact (S j)) by apply Qfact_pos.
  assert (Hkey : inject_Z (Z.of_nat (S j)) * / Qfact (S j) == / Qfact j).
  { rewrite Qfact_S. rewrite Qinv_mult_distr. rewrite Qmult_assoc.
    rewrite Qmult_inv_r by exact HSjn. rewrite Qmult_1_l. reflexivity. }
  unfold exp_term.
  assert (Hf : Qpow a (S j) * / Qfact (S j) - Qpow b (S j) * / Qfact (S j)
               == (Qpow a (S j) - Qpow b (S j)) * / Qfact (S j)) by ring.
  rewrite Hf, Qabs_Qmult.
  rewrite (Qabs_pos (/ Qfact (S j)))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HfSj).
  eapply Qle_trans.
  - apply Qmult_le_compat_r.
    + exact (Qpow_diff_bound a b B j Ha Hb).
    + apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HfSj.
  - assert (Heq : inject_Z (Z.of_nat (S j)) * Qpow B j * Qabs (a - b) * / Qfact (S j)
                  == (inject_Z (Z.of_nat (S j)) * / Qfact (S j)) * (Qpow B j * Qabs (a - b)))
      by ring.
    rewrite Heq, Hkey.
    assert (Heq2 : / Qfact j * (Qpow B j * Qabs (a - b))
                   == Qpow B j * / Qfact j * Qabs (a - b)) by ring.
    rewrite Heq2. apply Qle_refl.
Qed.

(* ================================================================== *)
(*  Пилон 1: CROSS-CLOSENESS (Липшиц частичных сумм по аргументу)       *)
(* ================================================================== *)

(** ★ Липшиц частичных сумм exp-ряда по аргументу:
        |Σ_{k≤n} exp_term a k − Σ_{k≤n} exp_term b k| ≤ |a−b| · Σ_{k≤n} exp_term B (pred k).
    Индукция по n: член k=0 даёт 0 (exp_term _ 0 = 1), член k=S j добавляет
    exp_term B j·|a−b| (exp_term_diff_bound), что ровно достраивает сумму-мажоранту. *)
Lemma exp_partial_lipschitz : forall (a b B : Q) (n : nat),
  Qabs a <= B -> Qabs b <= B ->
  Qabs (partial_sum (exp_term a) n - partial_sum (exp_term b) n)
  <= Qabs (a - b) * partial_sum (fun k => exp_term B (pred k)) n.
Proof.
  intros a b B n Ha Hb.
  induction n as [|n IH].
  - (* n = 0 : |1 − 1| = 0 ≤ |a−b|·1 *)
    change (partial_sum (exp_term a) 0%nat) with (exp_term a 0%nat).
    change (partial_sum (exp_term b) 0%nat) with (exp_term b 0%nat).
    change (partial_sum (fun k => exp_term B (pred k)) 0%nat) with (exp_term B (pred 0)).
    change (pred 0%nat) with 0%nat.
    rewrite (exp_term_0 a), (exp_term_0 b), (exp_term_0 B).
    assert (H11 : (1:Q) - 1 == 0) by ring. rewrite H11.
    assert (Q0 : Qabs 0 == 0) by reflexivity. rewrite Q0.
    rewrite Qmult_1_r. apply Qabs_nonneg.
  - (* шаг *)
    change (partial_sum (exp_term a) (S n))
      with (partial_sum (exp_term a) n + exp_term a (S n)).
    change (partial_sum (exp_term b) (S n))
      with (partial_sum (exp_term b) n + exp_term b (S n)).
    change (partial_sum (fun k => exp_term B (pred k)) (S n))
      with (partial_sum (fun k => exp_term B (pred k)) n + exp_term B (pred (S n))).
    change (pred (S n)) with n.
    assert (Hdec : (partial_sum (exp_term a) n + exp_term a (S n))
                   - (partial_sum (exp_term b) n + exp_term b (S n))
                   == (partial_sum (exp_term a) n - partial_sum (exp_term b) n)
                      + (exp_term a (S n) - exp_term b (S n))) by ring.
    rewrite Hdec.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    eapply Qle_trans.
    + apply Qplus_le_compat.
      * exact IH.
      * exact (exp_term_diff_bound a b B n Ha Hb).
    + assert (Heq : Qabs (a - b) * partial_sum (fun k => exp_term B (pred k)) n
                    + exp_term B n * Qabs (a - b)
                    == Qabs (a - b)
                       * (partial_sum (fun k => exp_term B (pred k)) n + exp_term B n))
        by ring.
      rewrite Heq. apply Qle_refl.
Qed.

(** Равномерная мажоранта сдвинутой суммы: Σ exp_term B (pred k) ≤ exp_term B 0 + MB.
    Голова (k=0) = 1; хвост (k=S j) = Σ exp_term B j ≤ MB (partial_sum_head). *)
Lemma exp_pred_sum_bound : forall (B MB : Q) (n : nat),
  0 <= B ->
  (forall N, partial_sum (exp_term B) N <= MB) ->
  partial_sum (fun k => exp_term B (pred k)) n <= exp_term B 0 + MB.
Proof.
  intros B MB n HB HMB.
  assert (HMB0 : 0 <= MB).
  { eapply Qle_trans; [ | apply (HMB 0%nat) ].
    change (partial_sum (exp_term B) 0%nat) with (exp_term B 0%nat).
    apply exp_term_nonneg; exact HB. }
  destruct n as [|m].
  - change (partial_sum (fun k => exp_term B (pred k)) 0%nat) with (exp_term B (pred 0)).
    change (pred 0%nat) with 0%nat. lra.
  - rewrite partial_sum_head. cbv beta.
    change (pred 0%nat) with 0%nat.
    assert (Htail : partial_sum (fun k => exp_term B (pred (S k))) m
                    == partial_sum (exp_term B) m).
    { apply partial_sum_ext_le. intros i _. change (pred (S i)) with i. reflexivity. }
    rewrite Htail. assert (HMm := HMB m). lra.
Qed.

(* ================================================================== *)
(*  Пилон 2: EQUI-CAUCHY (равномерный хвост exp-ряда над |·|≤B)         *)
(* ================================================================== *)

(** Блочная монотонность: при f ≤ g поточечно и n ≤ m,
    (Σf на (n,m]) ≤ (Σg на (n,m]). *)
Lemma partial_sum_block_mono : forall (f g : nat -> Q) (n m : nat),
  (n <= m)%nat -> (forall k, f k <= g k) ->
  partial_sum f m - partial_sum f n <= partial_sum g m - partial_sum g n.
Proof.
  intros f g n m Hnm Hfg. induction Hnm as [|m Hnm IH].
  - lra.
  - change (partial_sum f (S m)) with (partial_sum f m + f (S m)).
    change (partial_sum g (S m)) with (partial_sum g m + g (S m)).
    assert (Hf := Hfg (S m)). lra.
Qed.

(** ★ ПИЛОН equi-Cauchy: хвост exp-ряда РАВНОМЕРНО мажорируется хвостом exp_term B
    для всех |x| ≤ B:  |Σ_{≤m} exp_term x − Σ_{≤n} exp_term x| ≤ Σ exp_term B на (n,m]. *)
Lemma exp_partial_tail_bound : forall (x B : Q) (m n : nat),
  Qabs x <= B -> (n <= m)%nat ->
  Qabs (partial_sum (exp_term x) m - partial_sum (exp_term x) n)
  <= partial_sum (exp_term B) m - partial_sum (exp_term B) n.
Proof.
  intros x B m n Hx Hnm.
  eapply Qle_trans; [ apply partial_sum_block_abs; exact Hnm | ].
  apply partial_sum_block_mono; [ exact Hnm | ].
  intro k. rewrite exp_term_abs. unfold exp_term.
  apply Qmult_le_compat_r.
  - apply Qpow_le_mono_base; [ apply Qabs_nonneg | exact Hx ].
  - apply Qlt_le_weak; apply Qinv_lt_0_compat; apply Qfact_pos.
Qed.

(** Симметричный хвост (для equi-Cauchy без оговорки порядка m,n). *)
Lemma exp_partial_tail_bound_sym : forall (x B : Q) (m n : nat),
  Qabs x <= B ->
  Qabs (partial_sum (exp_term x) m - partial_sum (exp_term x) n)
  <= Qabs (partial_sum (exp_term B) m - partial_sum (exp_term B) n).
Proof.
  intros x B m n Hx.
  assert (Hcase : (n <= m \/ m <= n)%nat) by lia.
  destruct Hcase as [Hnm | Hmn].
  - eapply Qle_trans; [ exact (exp_partial_tail_bound x B m n Hx Hnm) | apply Qle_Qabs ].
  - rewrite Qabs_Qminus.
    eapply Qle_trans; [ exact (exp_partial_tail_bound x B n m Hx Hmn) | ].
    rewrite (Qabs_Qminus (partial_sum (exp_term B) m) (partial_sum (exp_term B) n)).
    apply Qle_Qabs.
Qed.

(* ================================================================== *)
(*  ★★★ СБОРКА: meta_cauchy ⟹ exp_R := diagonal_limit                  *)
(* ================================================================== *)

(** ★ Последовательность процессов (fun n => exp_limit (P n)) — meta-Cauchy.
    Пилон equi-Cauchy: exp_partial_tail_bound_sym (равномерно по k, |P k|≤B) +
    Cauchy-модуль exp-ряда от B.  Пилон cross-closeness: exp_partial_lipschitz +
    exp_pred_sum_bound (мажоранта C) + Cauchy-модуль P при ε/C. *)
Lemma exp_meta_cauchy : forall (P : CauchySeq),
  meta_cauchy (fun n => exp_limit (P n)).
Proof.
  intros P.
  destruct (cauchy_bounded P) as [B [HBpos HB]].
  assert (HB0 : 0 <= B) by lra.
  destruct (cauchy_bounded (exp_limit B)) as [MB [HMBpos HMB']].
  assert (HMB : forall N, partial_sum (exp_term B) N <= MB).
  { intro N. assert (Hb := HMB' N).
    change (cs_seq (exp_limit B) N) with (partial_sum (exp_term B) N) in Hb.
    assert (Hnn : 0 <= partial_sum (exp_term B) N)
      by (apply partial_sum_nonneg; intro; apply exp_term_nonneg; exact HB0).
    rewrite (Qabs_pos _ Hnn) in Hb. exact Hb. }
  assert (HC : 0 < exp_term B 0 + MB).
  { assert (Hone : exp_term B 0 == 1) by apply exp_term_0.
    assert (HMB0 : 0 <= MB).
    { eapply Qle_trans; [ | apply (HMB 0%nat) ].
      change (partial_sum (exp_term B) 0%nat) with (exp_term B 0%nat).
      apply exp_term_nonneg; exact HB0. }
    lra. }
  intros eps Heps.
  assert (HepsC : 0 < eps * / (exp_term B 0 + MB))
    by (apply Qmult_lt_0_compat; [ exact Heps | apply Qinv_lt_0_compat; exact HC ]).
  destruct (exp_series_cauchy B eps Heps) as [N1 HN1].
  destruct (cs_cauchy P (eps * / (exp_term B 0 + MB)) HepsC) as [N2 HN2].
  exists (N1 + N2)%nat. split.
  - (* equi-Cauchy *)
    intros k m n Hk Hm Hn.
    change (cs_seq (exp_limit (P k)) m) with (partial_sum (exp_term (P k)) m).
    change (cs_seq (exp_limit (P k)) n) with (partial_sum (exp_term (P k)) n).
    eapply Qle_lt_trans.
    + exact (exp_partial_tail_bound_sym (P k) B m n (HB k)).
    + apply HN1; lia.
  - (* cross-closeness *)
    intros k l n Hk Hl Hn.
    change (cs_seq (exp_limit (P k)) n) with (partial_sum (exp_term (P k)) n).
    change (cs_seq (exp_limit (P l)) n) with (partial_sum (exp_term (P l)) n).
    eapply Qle_lt_trans.
    + exact (exp_partial_lipschitz (P k) (P l) B n (HB k) (HB l)).
    + eapply Qle_lt_trans with (Qabs (P k - P l) * (exp_term B 0 + MB)).
      * rewrite (Qmult_comm (Qabs (P k - P l))
                   (partial_sum (fun j => exp_term B (pred j)) n)).
        rewrite (Qmult_comm (Qabs (P k - P l)) (exp_term B 0 + MB)).
        apply Qmult_le_compat_r;
          [ apply exp_pred_sum_bound; [ exact HB0 | exact HMB ] | apply Qabs_nonneg ].
      * assert (Hlt : Qabs (P k - P l) < eps * / (exp_term B 0 + MB)) by (apply HN2; lia).
        assert (Hstep : Qabs (P k - P l) * (exp_term B 0 + MB)
                        < (eps * / (exp_term B 0 + MB)) * (exp_term B 0 + MB))
          by (apply Qmult_lt_compat_r; [ exact HC | exact Hlt ]).
        assert (Hceq : (eps * / (exp_term B 0 + MB)) * (exp_term B 0 + MB) == eps)
          by (field; lra).
        rewrite Hceq in Hstep. exact Hstep.
Qed.

(** ★★★ ВЕЩЕСТВЕННАЯ (процессная) ЭКСПОНЕНТА: exp от ПРОЦЕССА P.
    exp_R P = предел последовательности exp_limit (P n) (через diagonal_limit). *)
Definition exp_R (P : CauchySeq) : CauchySeq :=
  diagonal_limit (fun n => exp_limit (P n)) (exp_meta_cauchy P).

(* ================================================================== *)
(*  К теореме сложения exp_R: равномерная мажоризация + диагональный     *)
(*  Мертенс (per-n разностная оценка с равномерными константами).        *)
(* ================================================================== *)

(** |exp_term x k| ≤ exp_term B k при |x| ≤ B. *)
Lemma exp_term_abs_bound : forall (x B : Q) (k : nat),
  Qabs x <= B -> Qabs (exp_term x k) <= exp_term B k.
Proof.
  intros x B k Hx. rewrite exp_term_abs. unfold exp_term.
  apply Qmult_le_compat_r.
  - apply Qpow_le_mono_base; [ apply Qabs_nonneg | exact Hx ].
  - apply Qlt_le_weak; apply Qinv_lt_0_compat; apply Qfact_pos.
Qed.

(** Σ|exp_term x| ≤ Σ exp_term B (равномерно по аргументу |x| ≤ B). *)
Lemma exp_abs_partial_le_B : forall (x B : Q) (N : nat),
  Qabs x <= B ->
  partial_sum (fun k => Qabs (exp_term x k)) N <= partial_sum (exp_term B) N.
Proof.
  intros x B N Hx. apply partial_sum_le_ext. intros i _.
  apply exp_term_abs_bound; exact Hx.
Qed.

(** ★ ДИАГОНАЛЬНЫЙ МЕРТЕНС (аналитическое ядро теоремы сложения exp_R):
    per-n разностная оценка с РАВНОМЕРНЫМИ мажорантами exp_term BP, exp_term BQ.
    |Σexp_term(aₙ) n · Σexp_term(bₙ) n − Σexp_term(aₙ+bₙ) n|
      ≤ MP·(Σexp_term BQ на (n−K,n])  +  MQ·(Σexp_term BP на (K,n]),
    aₙ=P n, bₙ=Q n.  Через exp_conv_id (Σexp_term(a+b)=Σconv) + mertens_error_bound
    + поточечную мажоризацию |exp_term(P n)|≤exp_term BP и блочную монотонность. *)
Lemma exp_R_diag_mertens_bound :
  forall (P R : CauchySeq) (BP BR MP MR : Q) (K n : nat),
  (forall m, Qabs (cs_seq P m) <= BP) -> (forall m, Qabs (cs_seq R m) <= BR) ->
  (forall N, partial_sum (exp_term BP) N <= MP) ->
  (forall N, partial_sum (exp_term BR) N <= MR) ->
  (S K <= n)%nat ->
  Qabs (partial_sum (exp_term (cs_seq P n)) n * partial_sum (exp_term (cs_seq R n)) n
        - partial_sum (exp_term (cs_seq P n + cs_seq R n)) n)
  <= MP * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)
   + MR * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K).
Proof.
  intros P R BP BR MP MR K n HBP HBR HMP HMR HKn.
  assert (HBP0 : 0 <= BP) by (eapply Qle_trans; [ apply Qabs_nonneg | apply (HBP n) ]).
  assert (HBR0 : 0 <= BR) by (eapply Qle_trans; [ apply Qabs_nonneg | apply (HBR n) ]).
  assert (HMP0 : 0 <= MP).
  { eapply Qle_trans; [ | apply (HMP 0%nat) ].
    change (partial_sum (exp_term BP) 0%nat) with (exp_term BP 0%nat).
    apply exp_term_nonneg; exact HBP0. }
  assert (HMR0 : 0 <= MR).
  { eapply Qle_trans; [ | apply (HMR 0%nat) ].
    change (partial_sum (exp_term BR) 0%nat) with (exp_term BR 0%nat).
    apply exp_term_nonneg; exact HBR0. }
  (* Σexp_term(a+b) n = Σ conv n *)
  assert (Hconv : partial_sum (exp_term (cs_seq P n + cs_seq R n)) n
                  == partial_sum (conv (exp_term (cs_seq P n)) (exp_term (cs_seq R n))) n).
  { apply partial_sum_ext_le. intros i _. symmetry. apply exp_conv_id. }
  rewrite Hconv.
  assert (HMbR : forall N, partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) N <= MR).
  { intro N. eapply Qle_trans; [ apply exp_abs_partial_le_B; apply HBR | apply HMR ]. }
  eapply Qle_trans.
  { exact (mertens_error_bound (exp_term (cs_seq P n)) (exp_term (cs_seq R n)) K n MR HKn HMbR). }
  apply Qplus_le_compat.
  - (* Part1: Σ|exp_term P n| K · Rблок ≤ MP · BRблок *)
    assert (HX : partial_sum (fun k => Qabs (exp_term (cs_seq P n) k)) K <= MP)
      by (eapply Qle_trans; [ apply exp_abs_partial_le_B; apply HBP | apply HMP ]).
    assert (HYnn : 0 <= partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) n
                        - partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) (n - K)%nat).
    { assert (partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) (n - K)%nat
              <= partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) n)
        by (apply partial_sum_le_upper; [ intro; apply Qabs_nonneg | lia ]). lra. }
    assert (HYle : partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) n
                   - partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) (n - K)%nat
                   <= partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)
      by (apply partial_sum_block_mono; [ lia | intro k; apply exp_term_abs_bound; apply HBR ]).
    eapply Qle_trans with
      (MP * (partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) n
             - partial_sum (fun k => Qabs (exp_term (cs_seq R n) k)) (n - K)%nat)).
    + apply Qmult_le_compat_r; [ exact HX | exact HYnn ].
    + rewrite (Qmult_comm MP _), (Qmult_comm MP
                (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)).
      apply Qmult_le_compat_r; [ exact HYle | exact HMP0 ].
  - (* Part2: MR · Pхвост ≤ MR · BPблок *)
    rewrite (Qmult_comm MR _), (Qmult_comm MR
              (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K)).
    apply Qmult_le_compat_r; [ | exact HMR0 ].
    apply partial_sum_block_mono; [ lia | intro k; apply exp_term_abs_bound; apply HBP ].
Qed.

(** ★★★ ТЕОРЕМА СЛОЖЕНИЯ ВЕЩЕСТВЕННОЙ ЭКСПОНЕНТЫ: exp_R(P+R) ~~ exp_R(P)·exp_R(R).
    Диагональный Мертенс: разность на диагонали ограничена exp_R_diag_mertens_bound
    с равномерными мажорантами; капстоун ε/2 на Cauchy-модулях exp-рядов от BP, BR. *)
Theorem exp_R_add : forall (P R : CauchySeq),
  exp_R (cauchy_add P R) ~~ cauchy_mul (exp_R P) (exp_R R).
Proof.
  intros P R.
  destruct (cauchy_bounded P) as [BP [HBPpos HBP]].
  destruct (cauchy_bounded R) as [BR [HBRpos HBR]].
  assert (HBP0 : 0 <= BP) by lra.
  assert (HBR0 : 0 <= BR) by lra.
  destruct (cauchy_bounded (exp_limit BP)) as [MP [HMPpos HMP']].
  destruct (cauchy_bounded (exp_limit BR)) as [MR [HMRpos HMR']].
  assert (HMP : forall N, partial_sum (exp_term BP) N <= MP).
  { intro N. assert (Hb := HMP' N).
    change (cs_seq (exp_limit BP) N) with (partial_sum (exp_term BP) N) in Hb.
    assert (Hnn : 0 <= partial_sum (exp_term BP) N)
      by (apply partial_sum_nonneg; intro; apply exp_term_nonneg; exact HBP0).
    rewrite (Qabs_pos _ Hnn) in Hb. exact Hb. }
  assert (HMR : forall N, partial_sum (exp_term BR) N <= MR).
  { intro N. assert (Hb := HMR' N).
    change (cs_seq (exp_limit BR) N) with (partial_sum (exp_term BR) N) in Hb.
    assert (Hnn : 0 <= partial_sum (exp_term BR) N)
      by (apply partial_sum_nonneg; intro; apply exp_term_nonneg; exact HBR0).
    rewrite (Qabs_pos _ Hnn) in Hb. exact Hb. }
  assert (HMP0 : 0 <= MP).
  { eapply Qle_trans; [ | apply (HMP 0%nat) ].
    change (partial_sum (exp_term BP) 0%nat) with (exp_term BP 0%nat).
    apply exp_term_nonneg; exact HBP0. }
  assert (HMR0 : 0 <= MR).
  { eapply Qle_trans; [ | apply (HMR 0%nat) ].
    change (partial_sum (exp_term BR) 0%nat) with (exp_term BR 0%nat).
    apply exp_term_nonneg; exact HBR0. }
  unfold cauchy_equiv. intros eps Heps.
  assert (HdP : 0 < eps * (1#2) * / (MR + 1))
    by (apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra ]).
  assert (HdR : 0 < eps * (1#2) * / (MP + 1))
    by (apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra ]).
  destruct (exp_series_cauchy BP (eps * (1#2) * / (MR + 1)) HdP) as [K HK].
  destruct (exp_series_cauchy BR (eps * (1#2) * / (MP + 1)) HdR) as [NR HNR].
  exists (S K + NR + K)%nat. intros n Hn.
  assert (HKn : (S K <= n)%nat) by lia.
  change (cs_seq (exp_R (cauchy_add P R)) n)
    with (partial_sum (exp_term (cs_seq P n + cs_seq R n)) n).
  change (cs_seq (cauchy_mul (exp_R P) (exp_R R)) n)
    with (partial_sum (exp_term (cs_seq P n)) n * partial_sum (exp_term (cs_seq R n)) n).
  rewrite Qabs_Qminus.
  (* ГОЛОВА (R-блок) < ε/2 *)
  assert (HP1 : MP * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)
                < eps * (1#2)).
  { assert (Hnn : 0 <= partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat).
    { assert (partial_sum (exp_term BR) (n - K)%nat <= partial_sum (exp_term BR) n)
        by (apply partial_sum_le_upper; [ intro; apply exp_term_nonneg; exact HBR0 | lia ]). lra. }
    assert (Hlt : partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat
                  < eps * (1#2) * / (MP + 1)).
    { assert (Hc := HNR n (n - K)%nat ltac:(lia) ltac:(lia)).
      rewrite (Qabs_pos _ Hnn) in Hc. exact Hc. }
    assert (Hs1 : MP * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)
                  <= (MP + 1) * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat))
      by (apply Qmult_le_compat_r; [ lra | exact Hnn ]).
    assert (Hs2 : (MP + 1) * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat)
                  < (MP + 1) * (eps * (1#2) * / (MP + 1))).
    { setoid_replace ((MP + 1) * (partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat))
        with ((partial_sum (exp_term BR) n - partial_sum (exp_term BR) (n - K)%nat) * (MP + 1)) by ring.
      setoid_replace ((MP + 1) * (eps * (1#2) * / (MP + 1)))
        with ((eps * (1#2) * / (MP + 1)) * (MP + 1)) by ring.
      apply Qmult_lt_compat_r; [ lra | exact Hlt ]. }
    assert (Hs3 : (MP + 1) * (eps * (1#2) * / (MP + 1)) == eps * (1#2)) by (field; lra).
    lra. }
  (* ХВОСТ (P-хвост) < ε/2 *)
  assert (HP2 : MR * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K) < eps * (1#2)).
  { assert (Hnn : 0 <= partial_sum (exp_term BP) n - partial_sum (exp_term BP) K).
    { assert (partial_sum (exp_term BP) K <= partial_sum (exp_term BP) n)
        by (apply partial_sum_le_upper; [ intro; apply exp_term_nonneg; exact HBP0 | lia ]). lra. }
    assert (Hlt : partial_sum (exp_term BP) n - partial_sum (exp_term BP) K
                  < eps * (1#2) * / (MR + 1)).
    { assert (Hc := HK n K ltac:(lia) ltac:(lia)).
      rewrite (Qabs_pos _ Hnn) in Hc. exact Hc. }
    assert (Hs1 : MR * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K)
                  <= (MR + 1) * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K))
      by (apply Qmult_le_compat_r; [ lra | exact Hnn ]).
    assert (Hs2 : (MR + 1) * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K)
                  < (MR + 1) * (eps * (1#2) * / (MR + 1))).
    { setoid_replace ((MR + 1) * (partial_sum (exp_term BP) n - partial_sum (exp_term BP) K))
        with ((partial_sum (exp_term BP) n - partial_sum (exp_term BP) K) * (MR + 1)) by ring.
      setoid_replace ((MR + 1) * (eps * (1#2) * / (MR + 1)))
        with ((eps * (1#2) * / (MR + 1)) * (MR + 1)) by ring.
      apply Qmult_lt_compat_r; [ lra | exact Hlt ]. }
    assert (Hs3 : (MR + 1) * (eps * (1#2) * / (MR + 1)) == eps * (1#2)) by (field; lra).
    lra. }
  eapply Qle_lt_trans.
  - exact (exp_R_diag_mertens_bound P R BP BR MP MR K n HBP HBR HMP HMR HKn).
  - lra.
Qed.

(** Аудит аксиом. *)
Print Assumptions Qpow_diff_bound.
Print Assumptions exp_term_diff_bound.
Print Assumptions exp_partial_lipschitz.
Print Assumptions exp_partial_tail_bound.
Print Assumptions exp_meta_cauchy.
Print Assumptions exp_R_diag_mertens_bound.
Print Assumptions exp_R_add.
