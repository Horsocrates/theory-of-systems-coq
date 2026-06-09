(** * HyperfiniteSum.v — интеграл как стандартная часть гиперконечной римановой суммы:
      ∫₀¹ f = st(Σₖ f(k·δ)·δ), δ = 1/n бесконечно малая сетка.  Парный к DerivativeViaInfinitesimal —
      обе половины анализа едины тенью `st` инфинитезимального выражения.  Батч A Части XVIII.

   КОНТЕКСТ.  Производная (`DerivativeViaInfinitesimal`) = st(Δf/δ); ИНТЕГРАЛ = st(Σ f(kδ)·δ).  Один
   приём (тень бесконечно малого выражения) даёт ОБЕ половины исчисления — это сердце нестандартного
   анализа: дифференцирование и интегрирование суть одна операция `st` над процессами с ∞-малой δ.

   ★ ФЛАГМАН (genuine).  ∫₀¹ x = 1/2 через тень.  Левая риманова сумма с n подынтервалами (сетка 1/n,
   точки k/n, k=0..n−1) = Σₖ (k/n)·(1/n) = (Σk)/n² = [n(n−1)/2]/n² = (n−1)/(2n) = 1/2 − 1/(2n) (закрытая
   форма через сумму Гаусса Σk = n(n−1)/2, доказанную над ℕ).  Сетка δ=1/n НЕнулевая на каждом шаге ⟹
   сумма законна; `st` (предел, δ→0 по Архимеду) убирает остаток 1/(2n) ⟹ ∫₀¹ x = 1/2 ТОЧНО.

   ★ ГРАНИЦА.  Предел 1/2 РАЦИОНАЛЕН ⟹ риманов процесс (n−1)/(2n) сходится ВНУТРЬ Element-стороны —
   интегрирование полинома НЕ выходит за границу финитизации (как и дифференцирование, парно).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Доказана ЗАКРЫТАЯ ФОРМА римановой суммы (`rsumlin_closed`:
   Σ = Qof(Σk)·h²) — то есть это НАСТОЯЩАЯ термwise сумма, не подставленная формула — и флагман ∫x=1/2
   (`integral_x_converges`).  ⚠ ∫x² = 1/3 (через Σk² = (n−1)n(2n−1)/6) НЕ доказывается здесь (мессовая
   квадратичная сумма) — честно отмечено как обобщение, цитата.  Общий ∫ гладкой функции = арена
   `RiemannIntegration.v` (цитата).  δ→0 — Архимед (стандартный QArith).

   Elements: GProc; rsumlin (термwise рим. сумма); sumk (Гаусс Σk над ℕ); Qof (ℕ→ℚ); delta; converges.
   Roles:    δ=роль-сетка (∞-малая); rsumlin=роль-аппроксимация площади; st=роль-тень/интеграл; sumk=Гаусс.
   Rules:    δ≠0 (сумма законна); rsumlin = Qof(Σk)·h² (точно); 2·Σk=n(n−1); st убирает остаток ⟹ ∫x=1/2.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: ∫₀¹f = st(Σ f(kδ)δ) — интеграл через ∞-малую сетку; парный к производной (обе = st инфинитезим.).
     Rules (L5): δ≠0 ⟹ сумма законна; rsumlin=Qof(Σk)·h² (точно); 2Σk=n(n−1) (Гаусс); st убирает остаток
                 ⟹ ∫x=1/2; ∫ полинома = Element (предел рационален).
     Roles (L4): δ=роль-сетка (∞-малая); rsumlin=роль-аппроксимация площади; st=роль-тень; sumk=Гаусс-счётчик.
     Elements  : GProc; rsumlin; sumk; Qof; delta; converges.
     ОБРАЗУЮЩИЕ: DerivativeViaInfinitesimal (δ/converges/Архимед — ПАРНЫЙ: производная↔интеграл); GermInfinitesimal
                 (δ ∞-мало); RiemannIntegration над ℚ (цитата); Гаусс Σk=n(n−1)/2.
     ВЛОЖЕННЫЕ : закрытая форма (Element, точно) vs st-шаг (тень 1/2); сетка δ (∞-малая) vs предел (Element).
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (рим. сумма R(n)=(n−1)/(2n)): Elements — процесс рац. частичных площадей; Roles —
                 аппроксимация ∫; Rules — n↦1/2−1/(2n) Element (частичная сумма рациональна, сетка ненулева); тень
                 1/2 НЕ член (R(n)<1/2 всегда), но РАЦИОНАЛЬНА ⟹ сходимость ВНУТРЬ Element; та же структура, что
                 DQ(x²)=2x+δ у производной — оба к Element-пределу.
   ДИАГНОСТИКА (P4): всё конечно-глубинно (Element); δ→0=Архимед; ∫ полинома=Element. ЧЕСТНО: ∫x доказан;
                 ∫x² (Σk²) — цитата; общий ∫ = RiemannIntegration (цитата).

   STATUS: 10 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  ℕ→ℚ инъекция и её аддитивность / сдвиг / положительность               *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.
Definition Qof (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma Qof_add : forall a b, Qof (a + b)%nat == Qof a + Qof b.
Proof. intros a b. unfold Qof. rewrite Nat2Z.inj_add. rewrite inject_Z_plus. reflexivity. Qed.

Lemma Qof_S : forall m, Qof (S m) == Qof m + 1.
Proof.
  intro m. replace (S m) with (m + 1)%nat by lia.
  rewrite Qof_add. assert (H1 : Qof 1 == 1) by reflexivity. rewrite H1. reflexivity.
Qed.

Lemma Qof_pos : forall m, 0 < Qof (S m).
Proof. intro m. unfold Qof, Qlt. simpl. lia. Qed.

(* ===================================================================== *)
(*  Сумма Гаусса Σk над ℕ → ℚ-тождество 2·Σk = n(n−1)                       *)
(* ===================================================================== *)

Fixpoint sumk (n : nat) : nat :=
  match n with O => O | S k => sumk k + k end.

(** ★ Гаусс в ℚ: 2·Σ_{j<n} j = n·(n−1) (доказано индукцией, без ℕ-вычитания). *)
Lemma sumk_closed_Q : forall n, 2 * Qof (sumk n) == Qof n * (Qof n - 1).
Proof.
  induction n as [|k IH].
  - assert (H0 : Qof (sumk 0) == 0) by reflexivity.
    assert (H0' : Qof 0 == 0) by reflexivity.
    rewrite H0, H0'. ring.
  - change (sumk (S k)) with (sumk k + k)%nat.
    rewrite Qof_add. rewrite (Qof_S k).
    setoid_replace ((Qof k + 1) * ((Qof k + 1) - 1))
      with (Qof k * (Qof k - 1) + 2 * Qof k) by ring.
    rewrite <- IH. ring.
Qed.

(* ===================================================================== *)
(*  Термwise левая риманова сумма для f(x)=x и её закрытая форма            *)
(* ===================================================================== *)

(** rsumlin n h = Σ_{k=0}^{n-1} (k·h)·h  — точки k·h, сетка h, интегранд f(x)=x. *)
Fixpoint rsumlin (n : nat) (h : Q) : Q :=
  match n with O => 0 | S k => rsumlin k h + (Qof k * h) * h end.

(** ★ Закрытая форма: настоящая термwise сумма = Qof(Σk)·h² (не подставленная формула). *)
Lemma rsumlin_closed : forall n h, rsumlin n h == Qof (sumk n) * h * h.
Proof.
  induction n as [|k IH]; intro h.
  - assert (H0 : Qof (sumk 0) == 0) by reflexivity. cbn [rsumlin]. rewrite H0. ring.
  - cbn [rsumlin]. rewrite IH.
    change (sumk (S k)) with (sumk k + k)%nat. rewrite Qof_add. ring.
Qed.

(** Интеграл-кандидат: риманова сумма с n точками и сеткой 1/n. *)
Definition integral_x (n : nat) : Q := rsumlin n (/ Qof n).

(** ★ ∫-сумма для n=S m в явном виде: 1/2 − (1/2)·(1/n). *)
Lemma integral_x_closed : forall m, integral_x (S m) == (1#2) - (1#2) * / Qof (S m).
Proof.
  intro m. unfold integral_x. rewrite rsumlin_closed.
  pose proof (Qof_pos m) as Hpos.
  assert (Hq : ~ Qof (S m) == 0).
  { intro Hc. rewrite Hc in Hpos. exact (Qlt_irrefl 0 Hpos). }
  assert (HA : Qof (sumk (S m)) == Qof (S m) * (Qof (S m) - 1) / 2).
  { pose proof (sumk_closed_Q (S m)) as HC. rewrite <- HC. field. }
  rewrite HA. field. exact Hq.
Qed.

(* ===================================================================== *)
(*  Бесконечно малая сетка δ=1/(n+1) → 0 (Архимед, из DerivativeViaInfinitesimal) *)
(* ===================================================================== *)

Definition converges (x : GProc) (L : Q) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> (- eps < x n - L) /\ (x n - L < eps).

Definition delta (m : nat) : Q := / Qof (S m).

Lemma delta_pos : forall m, 0 < delta m.
Proof. intro m. unfold delta. apply Qinv_lt_0_compat. apply Qof_pos. Qed.

Lemma delta_converges_0 : converges delta 0.
Proof.
  intros eps Heps.
  assert (Hne_eps : ~ eps == 0).
  { intro Hc. rewrite Hc in Heps. exact (Qlt_irrefl 0 Heps). }
  destruct (Qarchimedean (/ eps)) as [p Hp].
  exists (Pos.to_nat p). intros n Hn.
  assert (HQpos : 0 < Qof (S n)) by apply Qof_pos.
  assert (Hne : ~ Qof (S n) == 0).
  { intro Hc. rewrite Hc in HQpos. exact (Qlt_irrefl 0 HQpos). }
  split.
  - assert (Hr : delta n - 0 == delta n) by ring. rewrite Hr.
    pose proof (delta_pos n). lra.
  - assert (Hr : delta n - 0 == delta n) by ring. rewrite Hr.
    unfold delta.
    assert (Hlt : / eps < Qof (S n)).
    { apply Qlt_le_trans with (inject_Z (Z.pos p)).
      - exact Hp.
      - unfold Qof. rewrite <- Zle_Qle. lia. }
    apply (proj1 (Qmult_lt_l (/ Qof (S n)) eps (Qof (S n)) HQpos)).
    rewrite (Qmult_inv_r (Qof (S n)) Hne).
    assert (Hk : eps * / eps < eps * Qof (S n)).
    { apply (proj2 (Qmult_lt_l (/ eps) (Qof (S n)) eps Heps)). exact Hlt. }
    rewrite (Qmult_inv_r eps Hne_eps) in Hk.
    rewrite Qmult_comm. exact Hk.
Qed.

(* ===================================================================== *)
(*  ★ ФЛАГМАН: ∫₀¹ x = 1/2 через тень римановой суммы                       *)
(* ===================================================================== *)

(** ★★ ∫₀¹ x = 1/2: риманова сумма (n−1)/(2n), тень (предел) = 1/2 ТОЧНО.
    Сетка δ нигде не нуль (суммировали законно), 1/2 достигается лишь в тени. *)
Lemma integral_x_converges : converges integral_x (1#2).
Proof.
  intros eps Heps.
  destruct (delta_converges_0 eps Heps) as [N HN].
  exists (S N). intros n Hn.
  destruct n as [|m].
  - exfalso. lia.
  - assert (Hm : (N <= m)%nat) by lia.
    destruct (HN m Hm) as [D1 D2].
    pose proof (delta_pos m) as Dp.
    rewrite (integral_x_closed m).
    unfold delta in D1, D2, Dp.
    split; lra.
Qed.

(* ===================================================================== *)
(*  Капстоун: интеграл как тень гиперконечной суммы                         *)
(* ===================================================================== *)

(** Гиперконечное интегрирование над процессами (0 аксиом):
      (★ закрытая форма)  настоящая термwise риманова сумма = Qof(Σk)·h² (не подставленная формула);
      (★ явный вид)       ∫-сумма для n точек = 1/2 − (1/2)/n;
      (★ флагман)         st даёт ∫₀¹ x = 1/2 ТОЧНО — интеграл без предела ε-δ, через тень ∞-малой сетки.
    Парный к производной: ∫ = st(Σ f(kδ)δ), f' = st(Δf/δ) — обе половины анализа суть одна операция `st`.
    Граница: предел 1/2 рационален ⟹ интегрирование полинома НЕ выходит за границу финитизации. *)
Theorem hyperfinite_sum_summary :
  (forall n h, rsumlin n h == Qof (sumk n) * h * h)
  /\ (forall m, integral_x (S m) == (1#2) - (1#2) * / Qof (S m))
  /\ converges integral_x (1#2).
Proof.
  split; [ exact rsumlin_closed |].
  split; [ exact integral_x_closed | exact integral_x_converges ].
Qed.
