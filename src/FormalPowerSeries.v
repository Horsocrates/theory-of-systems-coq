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

    STATUS: 6 Qed, 0 Admitted, 0 axioms (geom_inverse_fps, geom_not_polynomial аксиомо-СВОБОДНЫ).
            Следующая веха: композиция FPS (подстановка) + `compose exp_fps log1m_fps = geom_fps`
            (cₙ=1, рекуррентность как exp_conv_id) → формальное сердце E∘L; затем аналитический
            мост eval(f∘g) → снятие горизонта ln_mul.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
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

(** Аудит аксиом. *)
Print Assumptions geom_inverse_fps.
Print Assumptions geom_not_polynomial.

(* ================================================================== *)
(*  СВОДКА (веха 1 слоя «функция-как-процесс»): FPS = коэффициент-      *)
(*  процесс реифицирует аналитическую функцию; граница Element          *)
(*  (многочлен) / role-limit (трансцендентная) = H1 на уровне функций;  *)
(*  определяющее уравнение геометрической доказано формально.           *)
(*  ДАЛЕЕ: композиция FPS + compose exp_fps log1m_fps = geom_fps (cₙ=1)  *)
(*  → формальное сердце E∘L → аналитический мост → горизонт ln_mul.     *)
(* ================================================================== *)
