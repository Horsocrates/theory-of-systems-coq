(** * FormalPowerSeries.v — ФУНКЦИЯ КАК ПРОЦЕСС: степенной ряд = коэффициент-процесс

    Реализация H59 (следующий фронтир финитизации — функции).  В процессной онтологии ToS
    числа реифицированы как процессы (RealProcess := nat→Q); ЗДЕСЬ так же реифицируется
    АНАЛИТИЧЕСКАЯ ФУНКЦИЯ — как её коэффициент-процесс Тейлора:
        FPS := nat → Q   (функция f(x)=Σ cₙxⁿ ЕСТЬ последовательность коэффициентов cₙ).
    Граница Element/role-limit (H1) поднимается на уровень функций:
        Element    ⟺ МНОГОЧЛЕН (конечно ненулевых коэф., «процесс терминирует»);
        role-limit ⟺ ТРАНСЦЕНДЕНТНАЯ (бесконечный ряд, «процесс не терминирует»).

    ЭТА ВЕХА (фундамент слоя): FPS-алгебра (операции), реификация геометрической / exp / log,
    ★ ФОРМАЛЬНОЕ тождество геометрической `(1−X)·(1/(1−x)) = 1` на уровне коэффициентов
    (`geom_inverse_fps`), и СВИДЕТЕЛИ границы на уровне функций: многочлены = Element
    (`fps_one_polynomial`), геометрическая/exp = role-limit (`geom_not_polynomial`,
    `exp_fps_not_polynomial`).  Умножение FPS = свёртка Коши (`conv` из CauchyProduct).

    ============ E/R/R разбор ============
      Elements: коэффициенты cₙ ∈ Q — конечные данные на каждой стадии n.
      Roles:    FPS = роль-ФУНКЦИЯ (реифицированная как процесс коэффициентов); умножение =
                роль-свёртка; (1−X)·geom=1 = определяющая роль обратной геометрической.
      Rules:    свёртка Коши (conv); многочлен ⟺ хвост коэф. ≡ 0; role-limit ⟺ нет такого хвоста.
    ДИАГНОСТИКА (P4): функция-как-коэффициент-процесс — Element (многочлен) ⟺ терминирует,
      role-limit (трансцендентная) ⟺ не терминирует.  То же H1, на уровень выше.  0-аксиомно.

    STATUS: 13 Qed, 0 Admitted, 0 axioms (все ключевые аксиомо-СВОБОДНЫ, вкл. fps_deriv_mul).
            ГОТОВО: (1) FPS-реификация + граница Element/role-limit на уровне функций; (2) FPS-исчисление —
            exp'=exp, (−ln(1−x))'=1/(1−x); (3) СТРУКТУРНОЕ СЕРДЦЕ ode_geom_unique (ОДУ h'=h·geom, h(0)=1 ⟹ h=geom);
            (4) ★ ПРАВИЛО ЛЕЙБНИЦА fps_deriv_mul: (a·b)'=a'·b+a·b' — фундамент цепного правила, тот же Vandermonde-
            переиндекс, что в exp_conv_rec, аксиомо-СВОБОДЕН.
            ОСТАЁТСЯ: fps_pow + power rule (g^k)'=k·g^{k-1}·g' (индукция на fps_deriv_mul) → compose + цепное
            правило (compose exp_fps log1m_fps уд. h'=h·geom) ⟹ compose=geom (через ode_geom_unique) — формальное
            сердце E∘L; затем аналитический мост eval(f∘g) → горизонт ln_mul.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
From ToS Require Import ExpFunctionalEquation.
From ToS Require Import PowerSeries.

Open Scope Q_scope.

(* ================================================================== *)
(*  Реификация: ФУНКЦИЯ = коэффициент-процесс                          *)
(* ================================================================== *)

(** Формальный степенной ряд = процесс коэффициентов. *)
Definition FPS := nat -> Q.

(** Экстенсиональное равенство рядов (поточечно по коэффициентам). *)
Definition fps_eq (f g : FPS) : Prop := forall n, f n == g n.

(** Базовые объекты-функции. *)
Definition fps_zero : FPS := fun _ => 0.
Definition fps_one  : FPS := fun n => match n with O => 1 | S _ => 0 end.
Definition fps_X    : FPS := fun n => match n with S O => 1 | _ => 0 end.

(** Операции (FPS-алгебра). *)
Definition fps_add (f g : FPS) : FPS := fun n => f n + g n.
Definition fps_neg (f : FPS) : FPS := fun n => - f n.
Definition fps_sub (f g : FPS) : FPS := fun n => f n - g n.
Definition fps_scale (c : Q) (f : FPS) : FPS := fun n => c * f n.
(** Умножение = свёртка Коши (cₙ = Σ_{i+j=n} aᵢbⱼ). *)
Definition fps_mul (f g : FPS) : FPS := conv f g.
(** Формальная производная: коэф. xⁿ у f' есть (n+1)·c₍ₙ₊₁₎. *)
Definition fps_deriv (f : FPS) : FPS := fun n => inject_Z (Z.of_nat (S n)) * f (S n).

(* ================================================================== *)
(*  Реифицированные конкретные функции                                 *)
(* ================================================================== *)

(** 1/(1−x) = Σ xⁿ — геометрическая, все коэффициенты = 1. *)
Definition geom_fps : FPS := fun _ => 1.
(** exp(x) = Σ xⁿ/n!. *)
Definition exp_fps : FPS := fun n => / Qfact n.
(** −ln(1−x) = Σ_{m≥1} xᵐ/m — коэф. x⁰=0, xᵐ=1/m. *)
Definition log1m_fps : FPS :=
  fun n => match n with O => 0 | S k => / inject_Z (Z.of_nat (S k)) end.

(* ================================================================== *)
(*  Граница Element/role-limit НА УРОВНЕ ФУНКЦИЙ (H1 на уровень выше)   *)
(* ================================================================== *)

(** Функция-как-процесс ТЕРМИНИРУЕТ ⟺ многочлен (хвост коэффициентов ≡ 0). *)
Definition is_polynomial (f : FPS) : Prop :=
  exists N, forall n, (N <= n)%nat -> f n == 0.

(** Element: fps_one (=1) — многочлен (хвост с индекса 1 нулевой). *)
Lemma fps_one_polynomial : is_polynomial fps_one.
Proof.
  exists 1%nat. intros n Hn. destruct n as [|k]; [ lia | cbn [fps_one]; reflexivity ].
Qed.

(** Element: fps_X (=x) — многочлен. *)
Lemma fps_X_polynomial : is_polynomial fps_X.
Proof.
  exists 2%nat. intros n Hn. destruct n as [|[|k]]; [ lia | lia | cbn [fps_X]; reflexivity ].
Qed.

(** ★ role-limit: геометрическая 1/(1−x) — НЕ многочлен (все cₙ=1≠0): функция-процесс
    НЕ терминирует.  Прямой свидетель H1 на уровне функций. *)
Lemma geom_not_polynomial : ~ is_polynomial geom_fps.
Proof.
  intros [N H]. specialize (H N (Nat.le_refl N)). unfold geom_fps in H. lra.
Qed.

(** ★ role-limit: exp — НЕ многочлен (cₙ=1/n!≠0). *)
Lemma exp_fps_not_polynomial : ~ is_polynomial exp_fps.
Proof.
  intros [N H]. specialize (H N (Nat.le_refl N)). unfold exp_fps in H.
  assert (0 < / Qfact N) by (apply Qinv_lt_0_compat; apply Qfact_pos). lra.
Qed.

(* ================================================================== *)
(*  ★ ФОРМАЛЬНОЕ ТОЖДЕСТВО: (1−X)·geom = 1  (т.е. 1/(1−x) реифицирована  *)
(*    и её определяющее уравнение доказано на уровне коэффициентов)     *)
(* ================================================================== *)

(** Хвост частичной суммы коэффициентов (1,−1,0,0,…) с индекса ≥1 равен 0. *)
Lemma oneminusX_tail_zero : forall m,
  partial_sum (fun i => fps_sub fps_one fps_X i) (S m) == 0.
Proof.
  induction m as [|m IH].
  - unfold fps_sub. cbn [partial_sum fps_one fps_X]. ring.
  - change (partial_sum (fun i => fps_sub fps_one fps_X i) (S (S m)))
      with (partial_sum (fun i => fps_sub fps_one fps_X i) (S m)
            + fps_sub fps_one fps_X (S (S m))).
    rewrite IH. unfold fps_sub. cbn [fps_one fps_X]. ring.
Qed.

(** ★ (1−X)·(1/(1−x)) = 1 как РАВЕНСТВО КОЭФФИЦИЕНТ-ПРОЦЕССОВ.
    Свёртка (1,−1,0,…) с (1,1,1,…) даёт (1,0,0,…)=fps_one: определяющее уравнение
    геометрической функции, доказанное формально (функция реифицирована). *)
Lemma geom_inverse_fps : fps_eq (fps_mul (fps_sub fps_one fps_X) geom_fps) fps_one.
Proof.
  intro n. unfold fps_mul, conv.
  assert (Hmul1 : partial_sum (fun i => fps_sub fps_one fps_X i * geom_fps (n - i)%nat) n
                  == partial_sum (fun i => fps_sub fps_one fps_X i) n).
  { apply partial_sum_ext_le. intros i _. unfold geom_fps. ring. }
  rewrite Hmul1.
  destruct n as [|m].
  - unfold fps_sub. cbn [partial_sum fps_one fps_X]. ring.
  - rewrite oneminusX_tail_zero. cbn [fps_one]. reflexivity.
Qed.

(* ================================================================== *)
(*  FPS-ИСЧИСЛЕНИЕ: производные реифицированных функций                 *)
(*  (реифицированные функции удовлетворяют своим определяющим ОДУ)      *)
(* ================================================================== *)

(** ★ exp' = exp на уровне коэффициентов: (n+1)·exp(n+1) = (n+1)/(n+1)! = 1/n! = exp(n). *)
Lemma exp_fps_deriv : fps_eq (fps_deriv exp_fps) exp_fps.
Proof.
  intro n. unfold fps_deriv, exp_fps.
  assert (HSn : ~ inject_Z (Z.of_nat (S n)) == 0)
    by (assert (0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia); lra).
  change (Qfact (S n)) with (inject_Z (Z.of_nat (S n)) * Qfact n).
  rewrite Qinv_mult_distr, Qmult_assoc, Qmult_inv_r by exact HSn.
  rewrite Qmult_1_l. reflexivity.
Qed.

(** ★ (−ln(1−x))' = 1/(1−x): (n+1)·log1m(n+1) = (n+1)·1/(n+1) = 1 = geom(n).
    Реифицированный логарифм имеет производной реифицированную геометрическую. *)
Lemma log1m_deriv : fps_eq (fps_deriv log1m_fps) geom_fps.
Proof.
  intro n. unfold fps_deriv, geom_fps.
  change (log1m_fps (S n)) with (/ inject_Z (Z.of_nat (S n))).
  assert (HSn : ~ inject_Z (Z.of_nat (S n)) == 0)
    by (assert (0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia); lra).
  apply Qmult_inv_r. exact HSn.
Qed.

(* ================================================================== *)
(*  ★ ОДУ-ХАРАКТЕРИЗАЦИЯ: единственность решения h' = h·geom            *)
(*    (структурное сердце E∘L; чистый маршрут через conv·ones=Σ)        *)
(* ================================================================== *)

(** Свёртка с геометрической (=всеединичной) есть частичная сумма: conv a geom = Σa. *)
Lemma conv_ones : forall (a : FPS) (n : nat),
  conv a geom_fps n == partial_sum a n.
Proof.
  intros a n. unfold conv. apply partial_sum_ext_le. intros i _. unfold geom_fps. ring.
Qed.

(** Сокращение: a·x = a, a≠0 ⟹ x = 1. *)
Lemma qcancel : forall a x : Q, ~ a == 0 -> a * x == a -> x == 1.
Proof.
  intros a x Ha H.
  transitivity (/ a * (a * x)).
  - symmetry. rewrite Qmult_assoc, (Qmult_comm (/ a) a), (Qmult_inv_r a Ha).
    apply Qmult_1_l.
  - rewrite H, (Qmult_comm (/ a) a). apply (Qmult_inv_r a Ha).
Qed.

(** ★★ СТРУКТУРНОЕ СЕРДЦЕ: ОДУ h' = h·geom (т.е. (1−x)h'=h) с h(0)=1 имеет
    ЕДИНСТВЕННОЕ решение geom = 1/(1−x).  Из h'=h·geom: (n+1)h(n+1)=Σ_{≤n}h
    (conv·geom=Σ); индукцией Σ_{≤n}h = n+1, откуда h(n)=1.  Это conditional-сердце
    E∘L: остаётся показать, что exp∘log1m удовлетворяет ОДУ (цепное правило). *)
Lemma ode_geom_unique : forall h : FPS,
  (forall n, fps_deriv h n == fps_mul h geom_fps n) ->
  h 0%nat == 1 ->
  fps_eq h geom_fps.
Proof.
  intros h Hode H0.
  assert (Hrec : forall n, inject_Z (Z.of_nat (S n)) * h (S n) == partial_sum h n).
  { intro n. assert (Hh := Hode n). unfold fps_deriv, fps_mul in Hh.
    rewrite conv_ones in Hh. exact Hh. }
  assert (Hnz : forall n, ~ inject_Z (Z.of_nat (S n)) == 0).
  { intro n. assert (0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia). lra. }
  assert (Hps : forall n, partial_sum h n == inject_Z (Z.of_nat (S n))).
  { induction n as [|m IH].
    - change (partial_sum h 0%nat) with (h 0%nat). rewrite H0. reflexivity.
    - change (partial_sum h (S m)) with (partial_sum h m + h (S m)).
      assert (HhSm : h (S m) == 1).
      { apply (qcancel (inject_Z (Z.of_nat (S m)))); [ apply Hnz | ].
        rewrite (Hrec m). exact IH. }
      rewrite IH, HhSm.
      assert (Hinj : inject_Z (Z.of_nat (S (S m))) == inject_Z (Z.of_nat (S m)) + 1).
      { replace (Z.of_nat (S (S m))) with (Z.of_nat (S m) + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      rewrite Hinj. ring. }
  intro n. unfold geom_fps. destruct n as [|m].
  - exact H0.
  - apply (qcancel (inject_Z (Z.of_nat (S m)))); [ apply Hnz | ].
    rewrite (Hrec m). exact (Hps m).
Qed.

(** Проверка-следствие: сама geom удовлетворяет ОДУ h'=h·geom (geom'=geom·geom). *)
Lemma geom_satisfies_ode : forall n,
  fps_deriv geom_fps n == fps_mul geom_fps geom_fps n.
Proof.
  intro n. unfold fps_deriv, fps_mul. rewrite conv_ones.
  (* inject_Z(S n) * geom(S n) == partial_sum geom n;  geom≡1 ⟹ (n+1)·1 == Σ 1 = n+1 *)
  unfold geom_fps.
  assert (Hsum : partial_sum (fun _ : nat => (1:Q)) n == inject_Z (Z.of_nat (S n))).
  { induction n as [|m IH].
    - reflexivity.
    - change (partial_sum (fun _ : nat => (1:Q)) (S m))
        with (partial_sum (fun _ : nat => (1:Q)) m + 1).
      rewrite IH.
      replace (Z.of_nat (S (S m))) with (Z.of_nat (S m) + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
  rewrite Hsum. ring.
Qed.

(* ================================================================== *)
(*  ★ ПРАВИЛО ЛЕЙБНИЦА (производная произведения) — фундамент цепного   *)
(*    правила.  Тот же Vandermonde-переиндекс, что в exp_conv_rec.       *)
(* ================================================================== *)

(** ★ (a·b)' = a'·b + a·b' на уровне коэффициентов:
        (n+1)·conv a b (n+1) == conv a' b n + conv a b' n  (a'=fps_deriv a).
    Расщепление коэффициента n+1 = i + (n+1−i); голова→a'·b, хвост→a·b'. *)
Lemma fps_deriv_mul : forall (a b : FPS) (n : nat),
  inject_Z (Z.of_nat (S n)) * conv a b (S n)
  == conv (fps_deriv a) b n + conv a (fps_deriv b) n.
Proof.
  intros a b n.
  assert (HLHS :
    inject_Z (Z.of_nat (S n)) * conv a b (S n)
    == partial_sum (fun i => inject_Z (Z.of_nat i) * (a i * b (S n - i)%nat)) (S n)
     + partial_sum (fun i => inject_Z (Z.of_nat (S n - i)) * (a i * b (S n - i)%nat)) (S n)).
  { unfold conv. rewrite <- partial_sum_plus. rewrite <- partial_sum_scale.
    apply partial_sum_ext_le. intros i Hi. cbv beta.
    assert (Hadd : inject_Z (Z.of_nat (S n))
                   == inject_Z (Z.of_nat i) + inject_Z (Z.of_nat (S n - i))).
    { rewrite <- inject_Z_plus.
      assert (HZ : Z.of_nat (S n) = (Z.of_nat i + Z.of_nat (S n - i))%Z)
        by (rewrite <- Nat2Z.inj_add; f_equal; lia).
      rewrite HZ. reflexivity. }
    rewrite Hadd. ring. }
  rewrite HLHS.
  assert (HA :
    partial_sum (fun i => inject_Z (Z.of_nat i) * (a i * b (S n - i)%nat)) (S n)
    == conv (fps_deriv a) b n).
  { unfold conv. rewrite partial_sum_head. cbv beta.
    assert (Hz : inject_Z (Z.of_nat 0%nat) * (a 0%nat * b (S n - 0)%nat) == 0)
      by (change (inject_Z (Z.of_nat 0%nat)) with 0; ring).
    rewrite Hz. rewrite Qplus_0_l.
    apply partial_sum_ext_le. intros i Hi. cbv beta. unfold fps_deriv.
    replace (S n - S i)%nat with (n - i)%nat by lia. ring. }
  assert (HB :
    partial_sum (fun i => inject_Z (Z.of_nat (S n - i)) * (a i * b (S n - i)%nat)) (S n)
    == conv a (fps_deriv b) n).
  { unfold conv. rewrite partial_sum_S. cbv beta.
    assert (Htail : inject_Z (Z.of_nat (S n - S n))
                    * (a (S n) * b (S n - S n)%nat) == 0)
      by (replace (S n - S n)%nat with 0%nat by lia;
          change (inject_Z (Z.of_nat 0%nat)) with 0; ring).
    rewrite Htail. rewrite Qplus_0_r.
    apply partial_sum_ext_le. intros i Hi. cbv beta. unfold fps_deriv.
    replace (S n - i)%nat with (S (n - i))%nat by lia. ring. }
  rewrite HA, HB. reflexivity.
Qed.

(** Аудит аксиом. *)
Print Assumptions geom_inverse_fps.
Print Assumptions geom_not_polynomial.
Print Assumptions exp_fps_deriv.
Print Assumptions log1m_deriv.
Print Assumptions ode_geom_unique.
Print Assumptions fps_deriv_mul.

(* ================================================================== *)
(*  СВОДКА (веха 1 слоя «функция-как-процесс»): FPS = коэффициент-      *)
(*  процесс реифицирует аналитическую функцию; граница Element          *)
(*  (многочлен) / role-limit (трансцендентная) = H1 на уровне функций;  *)
(*  определяющее уравнение геометрической доказано формально.           *)
(*  ДАЛЕЕ: композиция FPS + compose exp_fps log1m_fps = geom_fps (cₙ=1)  *)
(*  → формальное сердце E∘L → аналитический мост → горизонт ln_mul.     *)
(* ================================================================== *)
