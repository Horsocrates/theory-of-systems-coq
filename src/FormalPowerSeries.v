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

    STATUS: 37 Qed, 0 Admitted, 0 axioms (ВСЕ ключевые аксиомо-СВОБОДНЫ, вкл. fps_chain_rule, compose_exp_log1m_is_geom).
            ГОТОВО: (1) FPS-реификация + граница Element/role-limit на уровне функций; (2) FPS-исчисление —
            exp'=exp, (−ln(1−x))'=1/(1−x); (3) СТРУКТУРНОЕ СЕРДЦЕ ode_geom_unique (ОДУ h'=h·geom, h(0)=1 ⟹ h=geom);
            (4) ★ ПРАВИЛО ЛЕЙБНИЦА fps_deriv_mul: (a·b)'=a'·b+a·b'; (5) ★ КОЛЬЦЕВАЯ СТРУКТУРА: свёртка КОММУТАТИВНА
            (conv_comm), АССОЦИАТИВНА (conv_assoc — тройная сумма Коши через треугольный Fubini-своп
            partial_sum_triangle_swap), с единицей fps_one — FPS коммутативное кольцо; (6) ★★ ПРАВИЛО СТЕПЕНИ
            fps_pow_deriv: (gᵏ⁺¹)'=(k+1)·gᵏ·g'; (7) ★★ КОМПОЗИЦИЯ fps_compose (f∘g при g(0)=0, усечена т.к. (gᵏ)ₙ=0 при
            k>n — fps_pow_low_order) + ★★★ ЦЕПНОЕ ПРАВИЛО fps_chain_rule (f∘g)'=(f'∘g)·g' (через conv_compose_swap:
            квадрат⟷треугольник partial_sum_swap + зануление); (8) ★★★★ ФОРМАЛЬНОЕ СЕРДЦЕ E∘L:
            compose_exp_log1m_is_geom — exp(−ln(1−x))=1/(1−x) на уровне коэффициент-процессов (h'=h·geom + ode_geom_unique).
            E∘L ЗАКРЫТ ФОРМАЛЬНО.  Всё аксиомо-СВОБОДНО.
            ОСТАЁТСЯ: аналитический мост eval(f∘g) x ~~ exp_R(ln_proc x) ~~ geometric_limit x (от формальных рядов к
            процессам-числам CauchyReal) → горизонт ln_mul L(x)+L(y)~~L(x⊕y).
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

(* ================================================================== *)
(*  ★ КОЛЬЦЕВАЯ СТРУКТУРА FPS: свёртка коммутативна, ассоциативна,      *)
(*    с единицей fps_one.  (FPS — коммутативное кольцо; фундамент power  *)
(*    rule и цепного правила.)  Всё аксиомо-СВОБОДНО.                    *)
(* ================================================================== *)

(** Разворот конечной суммы: Σ_{i≤n} f(n−i) = Σ_{i≤n} f(i).  Голову LHS снимаем
    через partial_sum_head, хвост переиндексируем (S n − S i = n − i), IH. *)
Lemma partial_sum_rev : forall (f : nat -> Q) (n : nat),
  partial_sum (fun i => f (n - i)%nat) n == partial_sum f n.
Proof.
  intros f. induction n as [|n IH].
  - reflexivity.
  - rewrite partial_sum_head. cbv beta.
    replace (S n - 0)%nat with (S n) by lia.
    rewrite (partial_sum_ext_le (fun i => f (S n - S i)%nat) (fun i => f (n - i)%nat) n).
    + rewrite IH, partial_sum_S. ring.
    + intros i Hi. replace (S n - S i)%nat with (n - i)%nat by lia. reflexivity.
Qed.

(** ★ КОММУТАТИВНОСТЬ свёртки: conv a b = conv b a (переиндекс i ↦ n−i). *)
Lemma conv_comm : forall (a b : FPS) (n : nat), conv a b n == conv b a n.
Proof.
  intros a b n. unfold conv.
  transitivity (partial_sum (fun i => a (n - i)%nat * b (n - (n - i))%nat) n).
  - symmetry. apply (partial_sum_rev (fun j => a j * b (n - j)%nat) n).
  - apply partial_sum_ext_le. intros i Hi.
    replace (n - (n - i))%nat with i by lia. ring.
Qed.

(** Частичная сумма нулей = 0. *)
Lemma partial_sum_zero : forall n, partial_sum (fun _ : nat => (0:Q)) n == 0.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (partial_sum (fun _ : nat => (0:Q)) (S n))
      with (partial_sum (fun _ : nat => (0:Q)) n + 0).
    rewrite IH. ring.
Qed.

(** ★ ЛЕВАЯ ЕДИНИЦА: conv fps_one f = f (выживает только член i=0). *)
Lemma conv_one_l : forall (f : FPS) (n : nat), conv fps_one f n == f n.
Proof.
  intros f n. unfold conv. destruct n as [|m].
  - cbn [partial_sum fps_one]. replace (0 - 0)%nat with 0%nat by lia. ring.
  - rewrite partial_sum_head. cbv beta.
    change (fps_one 0%nat) with (1:Q).
    replace (S m - 0)%nat with (S m) by lia.
    rewrite (partial_sum_ext_le
              (fun i => fps_one (S i) * f (S m - S i)%nat) (fun _ => 0) m).
    + rewrite partial_sum_zero. ring.
    + intros i Hi. cbn [fps_one]. ring.
Qed.

(** ★ ПРАВАЯ ЕДИНИЦА (из коммутативности). *)
Lemma conv_one_r : forall (f : FPS) (n : nat), conv f fps_one n == f n.
Proof. intros f n. rewrite conv_comm. apply conv_one_l. Qed.

(** ★ Треугольный Fubini-своп: Σ_{i≤n} Σ_{j≤i} F i j == Σ_{j≤n} Σ_{t≤n−j} F (j+t) j.
    Перегруппировка треугольника {(i,j): j≤i≤n} по столбцу j (i=j+t).  Индукция по n:
    при шаге верхний предел внутренней суммы S n − j = S(n − j) добавляет ровно F (S n) j. *)
Lemma partial_sum_triangle_swap : forall (F : nat -> nat -> Q) (n : nat),
  partial_sum (fun i => partial_sum (fun j => F i j) i) n ==
  partial_sum (fun j => partial_sum (fun t => F (j + t)%nat j) (n - j)%nat) n.
Proof.
  intros F. induction n as [|n IH].
  - cbn [partial_sum]. replace (0 - 0)%nat with 0%nat by lia.
    cbn [partial_sum]. replace (0 + 0)%nat with 0%nat by lia. reflexivity.
  - change (partial_sum (fun i => partial_sum (fun j => F i j) i) (S n))
      with (partial_sum (fun i => partial_sum (fun j => F i j) i) n
            + partial_sum (fun j => F (S n) j) (S n)).
    change (partial_sum (fun j => partial_sum (fun t => F (j + t)%nat j) (S n - j)%nat) (S n))
      with (partial_sum (fun j => partial_sum (fun t => F (j + t)%nat j) (S n - j)%nat) n
            + partial_sum (fun t => F (S n + t)%nat (S n)) (S n - S n)%nat).
    replace (S n - S n)%nat with 0%nat by lia.
    change (partial_sum (fun t => F (S n + t)%nat (S n)) 0%nat)
      with (F (S n + 0)%nat (S n)).
    replace (S n + 0)%nat with (S n) by lia.
    rewrite (partial_sum_ext_le
              (fun j => partial_sum (fun t => F (j + t)%nat j) (S n - j)%nat)
              (fun j => partial_sum (fun t => F (j + t)%nat j) (n - j)%nat + F (S n) j) n).
    2:{ intros j Hj.
        replace (S n - j)%nat with (S (n - j)) by lia.
        change (partial_sum (fun t => F (j + t)%nat j) (S (n - j)))
          with (partial_sum (fun t => F (j + t)%nat j) (n - j)%nat + F (j + S (n - j))%nat j).
        replace (j + S (n - j))%nat with (S n) by lia. reflexivity. }
    rewrite partial_sum_plus.
    rewrite <- IH.
    change (partial_sum (fun j => F (S n) j) (S n))
      with (partial_sum (F (S n)) n + F (S n) (S n)).
    ring.
Qed.

(** ★★ АССОЦИАТИВНОСТЬ свёртки: conv (conv a b) c = conv a (conv b c).
    Обе стороны равны канонической Σ_{j+t≤n} a_j b_t c_{n−j−t}.  Правая — простым
    выносом a_j (partial_sum_scale); левая — выносом c_{n−i} (partial_sum_scale_r)
    плюс треугольный своп (i↦(j,t)=(j,i−j)).  Тройная сумма Коши, аксиомо-СВОБОДНО. *)
Lemma conv_assoc : forall (a b c : FPS) (n : nat),
  conv (conv a b) c n == conv a (conv b c) n.
Proof.
  intros a b c n.
  transitivity (partial_sum
    (fun j => partial_sum (fun t => a j * b t * c (n - j - t)%nat) (n - j)%nat) n).
  - (* conv (conv a b) c n == каноническая *)
    unfold conv at 1.
    assert (Hstep : forall i, (i <= n)%nat ->
              conv a b i * c (n - i)%nat
              == partial_sum (fun j => a j * b (i - j)%nat * c (n - i)%nat) i).
    { intros i Hi. unfold conv. symmetry.
      apply (partial_sum_scale_r (fun j => a j * b (i - j)%nat) (c (n - i)%nat) i). }
    rewrite (partial_sum_ext_le _ _ n Hstep).
    rewrite (partial_sum_triangle_swap (fun i j => a j * b (i - j)%nat * c (n - i)%nat) n).
    apply partial_sum_ext_le. intros j Hj. cbv beta.
    apply partial_sum_ext_le. intros t Ht. cbv beta.
    replace ((j + t) - j)%nat with t by lia.
    replace (n - (j + t))%nat with (n - j - t)%nat by lia. reflexivity.
  - (* каноническая == conv a (conv b c) n *)
    symmetry. unfold conv at 1.
    apply partial_sum_ext_le. intros j Hj. cbv beta. unfold conv.
    rewrite <- (partial_sum_scale (a j) (fun t => b t * c (n - j - t)%nat) (n - j)%nat).
    apply partial_sum_ext_le. intros t Ht. cbv beta.
    rewrite Qmult_assoc. reflexivity.
Qed.

(* ---- fps_eq-обёртки: FPS — коммутативное кольцо с единицей fps_one ---- *)

Lemma fps_mul_comm : forall a b, fps_eq (fps_mul a b) (fps_mul b a).
Proof. intros a b n. apply conv_comm. Qed.

Lemma fps_mul_one_l : forall f, fps_eq (fps_mul fps_one f) f.
Proof. intros f n. apply conv_one_l. Qed.

Lemma fps_mul_one_r : forall f, fps_eq (fps_mul f fps_one) f.
Proof. intros f n. apply conv_one_r. Qed.

Lemma fps_mul_assoc : forall a b c,
  fps_eq (fps_mul (fps_mul a b) c) (fps_mul a (fps_mul b c)).
Proof. intros a b c n. unfold fps_mul. apply conv_assoc. Qed.

(* ================================================================== *)
(*  ★ СТЕПЕНЬ FPS и ПРАВИЛО СТЕПЕНИ: (gᵏ⁺¹)' = (k+1)·gᵏ·g'             *)
(*    Индукция по k поверх правила Лейбница fps_deriv_mul + кольцо.      *)
(* ================================================================== *)

(** k-я степень ряда: g⁰ = 1, gᵏ⁺¹ = g·gᵏ. *)
Fixpoint fps_pow (g : FPS) (k : nat) : FPS :=
  match k with
  | O => fps_one
  | S k' => fps_mul g (fps_pow g k')
  end.

(** ★★ ПРАВИЛО СТЕПЕНИ (coefficient-уровень): (gᵏ⁺¹)' = (k+1)·gᵏ·g'.
    Индукция по k.  Шаг: (g·gᵏ⁺¹)' = g'·gᵏ⁺¹ + g·(gᵏ⁺¹)' [Лейбниц]; по IH второй член
    = g·((k+1)·gᵏ·g') = (k+1)·(g·gᵏ)·g' = (k+1)·gᵏ⁺¹·g' [вынос скаляра + АССОЦИАТИВНОСТЬ];
    первый член = gᵏ⁺¹·g' [КОММУТАТИВНОСТЬ]; сумма (1+(k+1))·gᵏ⁺¹·g' = (k+2)·gᵏ⁺¹·g'. *)
Lemma fps_pow_deriv : forall (g : FPS) (k : nat) (n : nat),
  fps_deriv (fps_pow g (S k)) n
  == inject_Z (Z.of_nat (S k)) * conv (fps_pow g k) (fps_deriv g) n.
Proof.
  intros g k. induction k as [|k IH].
  - (* база k=0: (g¹)' = 1·g⁰·g' = g' *)
    intros n.
    change (fps_deriv (fps_pow g (S 0)) n)
      with (inject_Z (Z.of_nat (S n)) * conv g fps_one (S n)).
    rewrite (conv_one_r g (S n)).
    change (conv (fps_pow g 0) (fps_deriv g) n)
      with (conv fps_one (fps_deriv g) n).
    rewrite (conv_one_l (fps_deriv g) n).
    assert (H1 : inject_Z (Z.of_nat (S 0)) == 1) by reflexivity.
    rewrite H1. unfold fps_deriv. ring.
  - (* шаг *)
    intros n.
    change (fps_deriv (fps_pow g (S (S k))) n)
      with (inject_Z (Z.of_nat (S n)) * conv g (fps_pow g (S k)) (S n)).
    rewrite (fps_deriv_mul g (fps_pow g (S k)) n).
    assert (Hconv_g : conv g (fps_deriv (fps_pow g (S k))) n
                      == inject_Z (Z.of_nat (S k))
                         * conv g (conv (fps_pow g k) (fps_deriv g)) n).
    { unfold conv at 1 2.
      rewrite <- (partial_sum_scale (inject_Z (Z.of_nat (S k)))
                   (fun i => g i * conv (fps_pow g k) (fps_deriv g) (n - i)%nat) n).
      apply partial_sum_ext_le. intros i Hi.
      rewrite (IH (n - i)%nat). ring. }
    rewrite Hconv_g.
    rewrite <- (conv_assoc g (fps_pow g k) (fps_deriv g) n).
    change (conv (conv g (fps_pow g k)) (fps_deriv g) n)
      with (conv (fps_pow g (S k)) (fps_deriv g) n).
    rewrite (conv_comm (fps_deriv g) (fps_pow g (S k)) n).
    assert (Hinj : inject_Z (Z.of_nat (S (S k)))
                   == inject_Z (Z.of_nat (S k)) + 1).
    { replace (Z.of_nat (S (S k))) with (Z.of_nat (S k) + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
    rewrite Hinj. ring.
Qed.

(** ★ Правило степени как fps_eq-равенство рядов. *)
Lemma fps_pow_deriv_eq : forall g k,
  fps_eq (fps_deriv (fps_pow g (S k)))
         (fps_scale (inject_Z (Z.of_nat (S k))) (fps_mul (fps_pow g k) (fps_deriv g))).
Proof. intros g k n. unfold fps_scale, fps_mul. apply fps_pow_deriv. Qed.

(* ================================================================== *)
(*  ★ КОМПОЗИЦИЯ FPS и ЦЕПНОЕ ПРАВИЛО — формальное сердце E∘L.          *)
(*    f∘g при g(0)=0: коэффициент усечён (Σ_{k≤n} fₖ·(gᵏ)ₙ, т.к. при     *)
(*    g(0)=0 ряд gᵏ имеет порядок ≥ k ⟹ (gᵏ)ₙ=0 при k>n).               *)
(* ================================================================== *)

(** ★ Зануление младших порядков: g(0)=0 ⟹ (gᵏ)ᵢ=0 при i<k.  (gᵏ имеет
    порядок ≥ k.)  Индукция по k: член j=0 убивает g(0)=0, член j≥1 — IH. *)
Lemma fps_pow_low_order : forall (g : FPS), g 0%nat == 0 ->
  forall k i, (i < k)%nat -> fps_pow g k i == 0.
Proof.
  intros g Hg0. induction k as [|k IH]; intros i Hi.
  - lia.
  - change (fps_pow g (S k) i) with (conv g (fps_pow g k) i).
    unfold conv.
    rewrite (partial_sum_ext_le (fun j => g j * fps_pow g k (i - j)%nat) (fun _ => 0) i).
    + apply partial_sum_zero.
    + intros j Hj. destruct j as [|j'].
      * rewrite Hg0. ring.
      * assert (Hz : fps_pow g k (i - S j')%nat == 0) by (apply IH; lia).
        rewrite Hz. ring.
Qed.

(** Удлинение частичной суммы нулевым хвостом: если a k=0 при i<k≤n, то
    Σ_{≤i} a = Σ_{≤n} a. *)
Lemma partial_sum_extend_zero : forall (a : nat -> Q) (n i : nat),
  (i <= n)%nat -> (forall k, (i < k)%nat -> (k <= n)%nat -> a k == 0) ->
  partial_sum a i == partial_sum a n.
Proof.
  intros a n. induction n as [|n IH]; intros i Hi Hz.
  - assert (i = 0)%nat by lia. subst i. reflexivity.
  - assert (i <= n \/ i = S n)%nat as [Hle | Heq] by lia.
    + assert (Hz' : forall k, (i < k)%nat -> (k <= n)%nat -> a k == 0)
        by (intros; apply Hz; lia).
      assert (Ha : a (S n) == 0) by (apply Hz; lia).
      rewrite partial_sum_S, Ha, (IH i Hle Hz'). ring.
    + subst i. reflexivity.
Qed.

(** ★ Квадратный Fubini: Σ_{i≤n} Σ_{k≤m} T i k == Σ_{k≤m} Σ_{i≤n} T i k.
    Перестановка двойной суммы по прямоугольнику (индексы независимы). *)
Lemma partial_sum_swap : forall (T : nat -> nat -> Q) (m n : nat),
  partial_sum (fun i => partial_sum (fun k => T i k) m) n
  == partial_sum (fun k => partial_sum (fun i => T i k) n) m.
Proof.
  intros T m. induction n as [|n IH].
  - change (partial_sum (fun i => partial_sum (fun k => T i k) m) 0%nat)
      with (partial_sum (fun k => T 0%nat k) m).
    apply partial_sum_ext_le. intros k Hk. cbn [partial_sum]. reflexivity.
  - rewrite (partial_sum_S (fun i => partial_sum (fun k => T i k) m) n). cbv beta.
    rewrite IH, <- partial_sum_plus.
    apply partial_sum_ext_le. intros k Hk.
    rewrite (partial_sum_S (fun i => T i k) n). cbv beta. reflexivity.
Qed.

(** Композиция рядов f∘g (корректна при g(0)=0): (f∘g)ₙ = Σ_{k≤n} fₖ·(gᵏ)ₙ. *)
Definition fps_compose (f g : FPS) : FPS :=
  fun n => partial_sum (fun k => f k * fps_pow g k n) n.

(** (f∘g)(0) = f(0). *)
Lemma fps_compose_zero : forall f g, fps_compose f g 0%nat == f 0%nat.
Proof.
  intros f g. unfold fps_compose. cbn [partial_sum fps_pow fps_one]. ring.
Qed.

(** Производная композиции (сырая форма): (f∘g)'ₙ = Σ_{k≤n+1} fₖ·(gᵏ)'ₙ. *)
Lemma fps_deriv_compose_raw : forall f g n,
  fps_deriv (fps_compose f g) n
  == partial_sum (fun k => f k * fps_deriv (fps_pow g k) n) (S n).
Proof.
  intros f g n. unfold fps_deriv, fps_compose.
  rewrite <- (partial_sum_scale (inject_Z (Z.of_nat (S n)))
               (fun k => f k * fps_pow g k (S n)) (S n)).
  apply partial_sum_ext_le. intros k Hk. ring.
Qed.

(* ---- конгруэнции свёртки/композиции по fps_eq ---- *)

Lemma conv_congr_l : forall a a' b n, fps_eq a a' -> conv a b n == conv a' b n.
Proof.
  intros a a' b n Ha. unfold conv. apply partial_sum_ext_le.
  intros i Hi. rewrite (Ha i). reflexivity.
Qed.

Lemma conv_congr_r : forall a b b' n, fps_eq b b' -> conv a b n == conv a b' n.
Proof.
  intros a b b' n Hb. unfold conv. apply partial_sum_ext_le.
  intros i Hi. rewrite (Hb (n - i)%nat). reflexivity.
Qed.

Lemma fps_compose_congr_l : forall F F' g n,
  fps_eq F F' -> fps_compose F g n == fps_compose F' g n.
Proof.
  intros F F' g n HF. unfold fps_compose. apply partial_sum_ext_le.
  intros k Hk. rewrite (HF k). reflexivity.
Qed.

(** ★★ КЛЮЧЕВОЕ ТОЖДЕСТВО: conv (f∘g) h = Σ_{k≤n} fₖ·conv (gᵏ) h  (при g(0)=0).
    conv(f∘g)h = Σ_{i≤n}(Σ_{k≤i} fₖ(gᵏ)ᵢ)h_{n−i} [треугольник]; удлиняем внутр. сумму
    i→n (нули при k>i, fps_pow_low_order) до КВАДРАТА; меняем порядок (partial_sum_swap);
    выносим fₖ — получаем Σ_{k≤n} fₖ·conv(gᵏ)h.  Это база цепного правила. *)
Lemma conv_compose_swap : forall (F g h : FPS) (n : nat),
  g 0%nat == 0 ->
  conv (fps_compose F g) h n
  == partial_sum (fun k => F k * conv (fps_pow g k) h n) n.
Proof.
  intros F g h n Hg0.
  unfold conv at 1. unfold fps_compose.
  (* вынос h(n−i) внутрь треугольной суммы *)
  rewrite (partial_sum_ext_le
    (fun i => partial_sum (fun k => F k * fps_pow g k i) i * h (n - i)%nat)
    (fun i => partial_sum (fun k => F k * fps_pow g k i * h (n - i)%nat) i) n).
  2:{ intros i Hi. symmetry.
      apply (partial_sum_scale_r (fun k => F k * fps_pow g k i) (h (n - i)%nat) i). }
  (* удлинение внутренней суммы i→n (нули при k>i) *)
  rewrite (partial_sum_ext_le
    (fun i => partial_sum (fun k => F k * fps_pow g k i * h (n - i)%nat) i)
    (fun i => partial_sum (fun k => F k * fps_pow g k i * h (n - i)%nat) n) n).
  2:{ intros i Hi.
      apply (partial_sum_extend_zero
               (fun k => F k * fps_pow g k i * h (n - i)%nat) n i Hi).
      intros k Hk1 Hk2.
      assert (Hz : fps_pow g k i == 0)
        by (apply fps_pow_low_order; [ exact Hg0 | lia ]).
      rewrite Hz. ring. }
  (* квадрат: перестановка порядка суммирования *)
  rewrite (partial_sum_swap (fun i k => F k * fps_pow g k i * h (n - i)%nat) n n).
  (* вынос Fₖ + свёртка обратно *)
  apply partial_sum_ext_le. intros k Hk. unfold conv.
  rewrite <- (partial_sum_scale (F k) (fun i => fps_pow g k i * h (n - i)%nat) n).
  apply partial_sum_ext_le. intros i Hi. ring.
Qed.

(** ★★★ ЦЕПНОЕ ПРАВИЛО FPS: (f∘g)' = (f'∘g)·g'  (при g(0)=0).
    (f∘g)'ₙ = Σ_{k≤n+1} fₖ·(gᵏ)'ₙ [fps_deriv_compose_raw]; член k=0 зануляется ((g⁰)'=0),
    переиндекс k=k'+1 + ПРАВИЛО СТЕПЕНИ даёт Σ_{k'≤n} f'_{k'}·conv(gᵏ')g'; по conv_compose_swap
    это есть conv(f'∘g)g'.  Аксиомо-СВОБОДНО. *)
Lemma fps_chain_rule : forall f g n,
  g 0%nat == 0 ->
  fps_deriv (fps_compose f g) n
  == conv (fps_compose (fps_deriv f) g) (fps_deriv g) n.
Proof.
  intros f g n Hg0.
  rewrite fps_deriv_compose_raw.
  rewrite partial_sum_head. cbv beta.
  assert (Hhead : f 0%nat * fps_deriv (fps_pow g 0) n == 0).
  { assert (Hd0 : fps_deriv (fps_pow g 0) n == 0).
    { change (fps_pow g 0) with fps_one. unfold fps_deriv. cbn [fps_one]. ring. }
    rewrite Hd0. ring. }
  rewrite Hhead, Qplus_0_l.
  rewrite (partial_sum_ext_le
    (fun k => f (S k) * fps_deriv (fps_pow g (S k)) n)
    (fun k => fps_deriv f k * conv (fps_pow g k) (fps_deriv g) n) n).
  2:{ intros k Hk. rewrite (fps_pow_deriv g k n). unfold fps_deriv. ring. }
  rewrite (conv_compose_swap (fps_deriv f) g (fps_deriv g) n Hg0). reflexivity.
Qed.

(** ★★★★ ФОРМАЛЬНОЕ СЕРДЦЕ E∘L: exp(−ln(1−x)) = 1/(1−x).
    h := exp_fps ∘ log1m_fps удовлетворяет ОДУ h'=h·geom: цепное правило даёт
    h' = (exp'∘log1m)·log1m' = (exp∘log1m)·geom = h·geom (exp'=exp, log1m'=geom);
    h(0)=exp(0)=1.  По ode_geom_unique ⟹ h = geom = 1/(1−x).  E∘L закрыт ФОРМАЛЬНО
    (на уровне коэффициент-процессов).  Аксиомо-СВОБОДНО. *)
Lemma compose_exp_log1m_is_geom :
  fps_eq (fps_compose exp_fps log1m_fps) geom_fps.
Proof.
  assert (Hlog0 : log1m_fps 0%nat == 0) by reflexivity.
  apply ode_geom_unique.
  - intro n.
    rewrite (fps_chain_rule exp_fps log1m_fps n Hlog0).
    unfold fps_mul.
    rewrite (conv_congr_r (fps_compose (fps_deriv exp_fps) log1m_fps)
                          (fps_deriv log1m_fps) geom_fps n log1m_deriv).
    rewrite (conv_congr_l (fps_compose (fps_deriv exp_fps) log1m_fps)
                          (fps_compose exp_fps log1m_fps) geom_fps n
              (fun m => fps_compose_congr_l (fps_deriv exp_fps) exp_fps log1m_fps m
                          exp_fps_deriv)).
    reflexivity.
  - rewrite fps_compose_zero. unfold exp_fps. reflexivity.
Qed.

(** Аудит аксиом. *)
Print Assumptions geom_inverse_fps.
Print Assumptions geom_not_polynomial.
Print Assumptions exp_fps_deriv.
Print Assumptions log1m_deriv.
Print Assumptions ode_geom_unique.
Print Assumptions fps_deriv_mul.
Print Assumptions conv_comm.
Print Assumptions conv_assoc.
Print Assumptions fps_pow_deriv.
Print Assumptions fps_chain_rule.
Print Assumptions compose_exp_log1m_is_geom.

(* ================================================================== *)
(*  СВОДКА (веха 1 слоя «функция-как-процесс»): FPS = коэффициент-      *)
(*  процесс реифицирует аналитическую функцию; граница Element          *)
(*  (многочлен) / role-limit (трансцендентная) = H1 на уровне функций;  *)
(*  определяющее уравнение геометрической доказано формально.           *)
(*  ДАЛЕЕ: композиция FPS + compose exp_fps log1m_fps = geom_fps (cₙ=1)  *)
(*  → формальное сердце E∘L → аналитический мост → горизонт ln_mul.     *)
(* ================================================================== *)
