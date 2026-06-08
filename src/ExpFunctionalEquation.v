(** * ExpFunctionalEquation.v — теорема сложения экспоненты через Мертенса (путь к ln_mul)

    ГОРИЗОНТ ln_mul (Log2FunctionalEq.v): L(x)+L(y) ~~ L(x⊕y), L(x)=−ln(1−x)=Σxᵐ/m,
    x⊕y=x+y−xy.  Это АДДИТИВНОЕ тождество ⟹ маршрут через экспоненту E(u)=Σuⁿ/n!
    (роль-обратную к ln), НЕ через произведение Коши log-рядов (то дало бы ln·ln, не ln+ln):
        E(L(x)+L(y)) ~~ E(L(x))·E(L(y)) ~~ 1/((1−x)(1−y)) ~~ 1/(1−(x⊕y)) ~~ E(L(x⊕y))
        ⟹(инъективность E)⟹ L(x)+L(y) ~~ L(x⊕y).
    ЦЕНТРАЛЬНОЕ ДОМИНО — теорема сложения E(u+v) ~~ E(u)·E(v) — это РОВНО применение
    mertens_cauchy_product (CauchyProduct.v).

    ЭТОТ ФАЙЛ — «проводка» Мертенса к exp: лемма exp_add_from_conv сводит ВСЮ теорему
    сложения экспоненты к ОДНОМУ чисто алгебраическому тождеству свёртки
        conv (exp_term u) (exp_term v) n == exp_term (u+v) n
    (биномиальное (u+v)ⁿ=ΣC(n,i)uⁱvⁿ⁻ⁱ, делённое на n! — в репо отсутствует).
    Тем самым весь анализ (сходимость, абс-границы, предел) уже закрыт; остаётся алгебра.

    ============ E/R/R разбор ============
      Elements: exp_term x n = xⁿ/n! — каждая стадия точна над Q; свёртка conv.
      Roles:    E = роль-обратная к ln; теорема сложения = роль-гомоморфизм (+ → ·);
                Мертенс = движок, переносящий покоэффициентное conv в предельное равенство.
      Rules:    |exp_term u k| = exp_term |u| k (Qfact>0); абс-границы из cauchy_bounded;
                is_cauchy переносится по поточечному Qeq; conv→exp_term(u+v) (горизонт, алгебра).
    ДИАГНОСТИКА (P4): E(u+v)~~E(u)E(v) — роль-предел (Мертенс), процесс, не объект; здесь
      сведён к конечной покоэффициентной алгебре.  0-аксиомно (только classic).

    STATUS: 11 Qed, 0 Admitted, 0 axioms (только classic; exp_add — изолированно только classic).
            ГОТОВО: БЕЗУСЛОВНАЯ теорема сложения экспоненты exp_add : E(u+v) ~~ E(u)·E(v) над Q,
            как равенство процессов — первое полное применение mertens_cauchy_product.  Цепочка:
            проводка к exp (exp_add_from_conv) + биномиальное тождество свёртки exp_conv_id
            (рекуррентность (n+1)cₙ₊₁=(u+v)cₙ из exp_term_ratio + переиндексация Vandermonde).
            ОСТАЁТСЯ (горизонт ln_mul): E∘L=1/(1−x) (композиция рядов) и инъективность E.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import PowerSeries.
From ToS Require Import CauchyProduct.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Вспомогательное                                                    *)
(* ================================================================== *)

(** is_cauchy переносится по поточечному равенству (Qeq) последовательностей. *)
Lemma is_cauchy_ext : forall f g : nat -> Q,
  (forall n, f n == g n) -> is_cauchy f -> is_cauchy g.
Proof.
  intros f g Hfg Hf eps Heps.
  destruct (Hf eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  assert (Heq : g m - g n == f m - f n)
    by (rewrite <- (Hfg m), <- (Hfg n); reflexivity).
  rewrite Heq. apply HN; assumption.
Qed.

(** |exp_term x k| = exp_term |x| k  (так как k! > 0). *)
Lemma exp_term_abs : forall (x : Q) (k : nat),
  Qabs (exp_term x k) == exp_term (Qabs x) k.
Proof.
  intros x k. unfold exp_term.
  rewrite Qabs_Qmult, Qabs_Qpow.
  assert (Hpos : 0 < / Qfact k) by (apply Qinv_lt_0_compat; apply Qfact_pos).
  rewrite (Qabs_pos (/ Qfact k)) by lra. reflexivity.
Qed.

(** exp_term неотрицательного аргумента неотрицателен. *)
Lemma exp_term_nonneg : forall (x : Q) (k : nat),
  0 <= x -> 0 <= exp_term x k.
Proof.
  intros x k Hx. unfold exp_term.
  apply Qmult_le_0_compat.
  - apply Qpow_nonneg; exact Hx.
  - assert (0 < / Qfact k) by (apply Qinv_lt_0_compat; apply Qfact_pos). lra.
Qed.

(** Частичные суммы |exp_term u| ограничены (через cauchy_bounded exp_limit|u|). *)
Lemma exp_abs_partial_bounded : forall (u : Q),
  exists Ma : Q, forall N, partial_sum (fun k => Qabs (exp_term u k)) N <= Ma.
Proof.
  intros u.
  destruct (cauchy_bounded (exp_limit (Qabs u))) as [Ma [HMa_pos HMa_bnd]].
  exists Ma. intro N.
  assert (Hext : partial_sum (fun k => Qabs (exp_term u k)) N
                 == partial_sum (exp_term (Qabs u)) N).
  { apply partial_sum_ext_le. intros i _. apply exp_term_abs. }
  rewrite Hext.
  assert (Hnn : 0 <= partial_sum (exp_term (Qabs u)) N).
  { apply partial_sum_nonneg. intro k. apply exp_term_nonneg. apply Qabs_nonneg. }
  assert (Hb := HMa_bnd N).
  change (cs_seq (exp_limit (Qabs u)) N) with (partial_sum (exp_term (Qabs u)) N) in Hb.
  rewrite (Qabs_pos _ Hnn) in Hb. exact Hb.
Qed.

(* ================================================================== *)
(*  ★ ПРОВОДКА МЕРТЕНСА К EXP                                           *)
(* ================================================================== *)

(** ★ Условная теорема сложения экспоненты: ЕСЛИ покоэффициентно
        conv (exp_term u)(exp_term v) n == exp_term (u+v) n  (биномиальное тождество),
    ТО E(u+v) ~~ E(u)·E(v).  Весь АНАЛИЗ (сходимость, абс-границы, предел) закрыт здесь
    через mertens_cauchy_product; остаётся лишь алгебра свёртки.  0-аксиомно (только classic). *)
Lemma exp_add_from_conv : forall u v : Q,
  (forall n, conv (exp_term u) (exp_term v) n == exp_term (u + v) n) ->
  exp_limit (u + v) ~~ cauchy_mul (exp_limit u) (exp_limit v).
Proof.
  intros u v Hid.
  (* абс-границы для Мертенса *)
  destruct (exp_abs_partial_bounded u) as [Ma HMa].
  destruct (exp_abs_partial_bounded v) as [Mb HMb].
  (* свёртка — Cauchy (поточечно равна exp-ряду от u+v) *)
  assert (Hconv_c : is_cauchy (partial_sum (conv (exp_term u) (exp_term v)))).
  { apply is_cauchy_ext with (f := partial_sum (exp_term (u + v))).
    - intro n. apply partial_sum_ext_le. intros i _. symmetry. apply Hid.
    - apply exp_series_cauchy. }
  (* Мертенс *)
  assert (Hmert := mertens_cauchy_product (exp_term u) (exp_term v) Ma Mb
                     HMa HMb (exp_series_cauchy u) (exp_series_cauchy v) Hconv_c).
  (* exp_limit (u+v) ~~ series_limit (conv ...) Hconv_c  (поточечно равные последовательности) *)
  eapply cauchy_equiv_trans; [ | exact Hmert ].
  unfold cauchy_equiv. intros eps Heps. exists 0%nat. intros n _.
  change (cs_seq (exp_limit (u + v)) n) with (partial_sum (exp_term (u + v)) n).
  change (cs_seq (series_limit (conv (exp_term u) (exp_term v)) Hconv_c) n)
    with (partial_sum (conv (exp_term u) (exp_term v)) n).
  assert (HZ : partial_sum (exp_term (u + v)) n
               - partial_sum (conv (exp_term u) (exp_term v)) n == 0).
  { assert (Heq : partial_sum (exp_term (u + v)) n
                  == partial_sum (conv (exp_term u) (exp_term v)) n).
    { apply partial_sum_ext_le. intros i _. symmetry. apply Hid. }
    rewrite Heq. ring. }
  rewrite HZ.
  assert (Q0 : Qabs 0 == 0) by reflexivity.
  rewrite Q0. exact Heps.
Qed.

(* ================================================================== *)
(*  ★ БИНОМИАЛЬНОЕ ТОЖДЕСТВО СВЁРТКИ ⟹ безусловная теорема сложения      *)
(* ================================================================== *)

(** Расщепление частичной суммы с ГОЛОВЫ: Σ_{i≤S n} f = f 0 + Σ_{i≤n} f(S i). *)
Lemma partial_sum_head : forall (f : nat -> Q) (n : nat),
  partial_sum f (S n) == f 0%nat + partial_sum (fun i => f (S i)) n.
Proof.
  intros f n. induction n as [|n IH].
  - simpl. ring.
  - change (partial_sum f (S (S n))) with (partial_sum f (S n) + f (S (S n))).
    rewrite IH.
    change (partial_sum (fun i => f (S i)) (S n))
      with (partial_sum (fun i => f (S i)) n + (fun i => f (S i)) (S n)).
    cbv beta. ring.
Qed.

(** exp_term x 0 = 1. *)
Lemma exp_term_0 : forall x : Q, exp_term x 0%nat == 1.
Proof. intro x. unfold exp_term. simpl. field. Qed.

(** База: свёртка в 0 = 1 = exp_term (u+v) 0. *)
Lemma exp_conv_zero : forall u v : Q,
  conv (exp_term u) (exp_term v) 0%nat == exp_term (u + v) 0%nat.
Proof.
  intros u v. unfold conv.
  transitivity (exp_term u 0%nat * exp_term v 0%nat).
  - reflexivity.
  - rewrite (exp_term_0 u), (exp_term_0 v), (exp_term_0 (u + v)). ring.
Qed.

(** ★ РЕКУРРЕНТНОСТЬ свёртки exp: (n+1)·cₙ₊₁ == (u+v)·cₙ.
    Сердце теоремы сложения (Vandermonde/Pascal без биномиальных коэффициентов):
    (u+v)·cₙ распадается на u·cₙ+v·cₙ; u·Aᵢ=(i+1)Aᵢ₊₁, v·Bⱼ=(j+1)Bⱼ₊₁ (exp_term_ratio)
    с переиндексацией суммируются ровно в (n+1)·cₙ₊₁ (коэффициент i+(n+1−i)=n+1 у каждого члена). *)
Lemma exp_conv_rec : forall (u v : Q) (n : nat),
  inject_Z (Z.of_nat (S n)) * conv (exp_term u) (exp_term v) (S n)
  == (u + v) * conv (exp_term u) (exp_term v) n.
Proof.
  intros u v n.
  (* RHS == SU + SV (распределение + exp_term_ratio) *)
  assert (HRHS :
    (u + v) * partial_sum (fun i => exp_term u i * exp_term v (n - i)%nat) n
    == partial_sum (fun i => inject_Z (Z.of_nat (S i)) * exp_term u (S i) * exp_term v (n - i)%nat) n
     + partial_sum (fun i => exp_term u i * (inject_Z (Z.of_nat (S (n - i))) * exp_term v (S (n - i)))) n).
  { assert (Hsplit :
      (u + v) * partial_sum (fun i => exp_term u i * exp_term v (n - i)%nat) n
      == u * partial_sum (fun i => exp_term u i * exp_term v (n - i)%nat) n
       + v * partial_sum (fun i => exp_term u i * exp_term v (n - i)%nat) n) by ring.
    rewrite Hsplit. apply Qplus_comp.
    - rewrite <- partial_sum_scale. apply partial_sum_ext_le. intros i _. cbv beta.
      assert (Hr : u * exp_term u i == inject_Z (Z.of_nat (S i)) * exp_term u (S i))
        by (symmetry; apply exp_term_ratio).
      transitivity ((u * exp_term u i) * exp_term v (n - i)%nat).
      + ring.
      + rewrite Hr. ring.
    - rewrite <- partial_sum_scale. apply partial_sum_ext_le. intros i _. cbv beta.
      assert (Hr : v * exp_term v (n - i)%nat
                   == inject_Z (Z.of_nat (S (n - i))) * exp_term v (S (n - i)))
        by (symmetry; apply exp_term_ratio).
      transitivity (exp_term u i * (v * exp_term v (n - i)%nat)).
      + ring.
      + rewrite Hr. reflexivity. }
  (* LHS == P-сумма + Q-сумма (расщепление коэффициента n+1 = i + (n+1−i)) *)
  assert (HLHS :
    inject_Z (Z.of_nat (S n)) * partial_sum (fun i => exp_term u i * exp_term v (S n - i)%nat) (S n)
    == partial_sum (fun i => inject_Z (Z.of_nat i) * (exp_term u i * exp_term v (S n - i)%nat)) (S n)
     + partial_sum (fun i => inject_Z (Z.of_nat (S n - i)) * (exp_term u i * exp_term v (S n - i)%nat)) (S n)).
  { rewrite <- partial_sum_plus. rewrite <- partial_sum_scale.
    apply partial_sum_ext_le. intros i Hi. cbv beta.
    assert (Hadd : inject_Z (Z.of_nat (S n))
                   == inject_Z (Z.of_nat i) + inject_Z (Z.of_nat (S n - i))).
    { rewrite <- inject_Z_plus.
      assert (HZ : Z.of_nat (S n) = (Z.of_nat i + Z.of_nat (S n - i))%Z)
        by (rewrite <- Nat2Z.inj_add; f_equal; lia).
      rewrite HZ. reflexivity. }
    rewrite Hadd. ring. }
  (* P-сумма == SU (голова i=0 нулевая; S n − S i = n − i) *)
  assert (HA :
    partial_sum (fun i => inject_Z (Z.of_nat i) * (exp_term u i * exp_term v (S n - i)%nat)) (S n)
    == partial_sum (fun i => inject_Z (Z.of_nat (S i)) * exp_term u (S i) * exp_term v (n - i)%nat) n).
  { rewrite partial_sum_head. cbv beta.
    assert (Hz : inject_Z (Z.of_nat 0%nat) * (exp_term u 0%nat * exp_term v (S n - 0)%nat) == 0).
    { change (inject_Z (Z.of_nat 0%nat)) with 0. ring. }
    rewrite Hz. rewrite Qplus_0_l.
    apply partial_sum_ext_le. intros i Hi.
    replace (S n - S i)%nat with (n - i)%nat by lia. ring. }
  (* Q-сумма == SV (хвост i=S n нулевой; S n − i = S(n − i)) *)
  assert (HB :
    partial_sum (fun i => inject_Z (Z.of_nat (S n - i)) * (exp_term u i * exp_term v (S n - i)%nat)) (S n)
    == partial_sum (fun i => exp_term u i * (inject_Z (Z.of_nat (S (n - i))) * exp_term v (S (n - i)))) n).
  { rewrite partial_sum_S. cbv beta.
    assert (Htail : inject_Z (Z.of_nat (S n - S n))
                    * (exp_term u (S n) * exp_term v (S n - S n)%nat) == 0).
    { replace (S n - S n)%nat with 0%nat by lia.
      change (inject_Z (Z.of_nat 0%nat)) with 0. ring. }
    rewrite Htail. rewrite Qplus_0_r.
    apply partial_sum_ext_le. intros i Hi.
    replace (S n - i)%nat with (S (n - i))%nat by lia. ring. }
  (* собираем *)
  unfold conv.
  rewrite HLHS, HA, HB. symmetry. exact HRHS.
Qed.

(** ★ ТОЖДЕСТВО СВЁРТКИ: conv (exp_term u)(exp_term v) n == exp_term (u+v) n.
    Индукция по n: база exp_conv_zero; шаг — рекуррентность exp_conv_rec + exp_term_ratio
    дают (n+1)·cₙ₊₁ == (n+1)·exp_term(u+v)(S n); сокращаем (n+1)>0. *)
Lemma exp_conv_id : forall (u v : Q) (n : nat),
  conv (exp_term u) (exp_term v) n == exp_term (u + v) n.
Proof.
  intros u v n. induction n as [|n IH].
  - apply exp_conv_zero.
  - assert (Hrec := exp_conv_rec u v n).
    assert (Hexp : inject_Z (Z.of_nat (S n)) * exp_term (u + v) (S n)
                   == (u + v) * exp_term (u + v) n) by (apply exp_term_ratio).
    assert (Hstep : inject_Z (Z.of_nat (S n)) * conv (exp_term u) (exp_term v) (S n)
                    == inject_Z (Z.of_nat (S n)) * exp_term (u + v) (S n)).
    { rewrite Hrec, IH. symmetry. exact Hexp. }
    assert (Hzpos : 0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia).
    assert (Hzn : ~ inject_Z (Z.of_nat (S n)) == 0) by lra.
    setoid_replace (conv (exp_term u) (exp_term v) (S n))
      with (/ inject_Z (Z.of_nat (S n))
            * (inject_Z (Z.of_nat (S n)) * conv (exp_term u) (exp_term v) (S n)))
      by (field; exact Hzn).
    rewrite Hstep. field; exact Hzn.
Qed.

(** ★★★ БЕЗУСЛОВНАЯ ТЕОРЕМА СЛОЖЕНИЯ ЭКСПОНЕНТЫ (E(u+v) ~~ E(u)·E(v)) над Q,
    как равенство ПРОЦЕССОВ.  Первое полное применение mertens_cauchy_product;
    центральное домино маршрута к ln_mul.  0-аксиомно (только classic). *)
Theorem exp_add : forall u v : Q,
  exp_limit (u + v) ~~ cauchy_mul (exp_limit u) (exp_limit v).
Proof.
  intros u v. apply exp_add_from_conv. intro n. apply exp_conv_id.
Qed.

(** Аудит аксиом: должно быть ТОЛЬКО classic. *)
Print Assumptions exp_add_from_conv.
Print Assumptions exp_add.

(* ================================================================== *)
(*  СВОДКА: БЕЗУСЛОВНАЯ теорема сложения экспоненты exp_add ГОТОВА        *)
(*  (E(u+v) ~~ E(u)·E(v) над Q, 0-аксиомно) — первое полное применение  *)
(*  Мертенса.  Цепочка: exp_add_from_conv (проводка) + exp_conv_id       *)
(*  (биномиальное тождество свёртки via рекуррентность (n+1)cₙ₊₁=(u+v)cₙ).*)
(*  Для полного снятия горизонта ln_mul_functional_equation остаётся:    *)
(*  E∘L=1/(1−x) (композиция степенных рядов) и инъективность E.          *)
(* ================================================================== *)
