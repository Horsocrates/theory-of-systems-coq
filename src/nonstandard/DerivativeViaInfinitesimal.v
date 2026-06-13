(** * DerivativeViaInfinitesimal.v — производная как стандартная часть разностного отношения:
      f'(x) = st((f(x+δ) − f(x))/δ).  δ НЕнулевой ⟹ деление законно (нет 0/0); st отбрасывает
      остаток (δ→0) ⟹ производная ТОЧНА.  Климакс Батча A Части XVIII.

   КОНТЕКСТ.  После GermInfinitesimal (δ = 1/(n+1), δ≠0, δ бесконечно мало) и StandardPart
   (st/converges, единственность тени) собирается сам смысл нестандартного исчисления: производная
   БЕЗ epsilon-delta предела, через бесконечно малое приращение, тень которого и есть наклон касательной.

   ★ РАЗРЕШЕНИЕ ПАРАДОКСА БЕРКЛИ (genuine).  Классическая критика флюксий: «(f(x+o)−f(x))/o упрощают
   при o≠0, ПОТОМ полагают o=0 — призрак исчезнувших величин».  Здесь противоречия НЕТ: δ — процесс,
   на КАЖДОМ шаге δₙ>0 (`delta_nonzero`), деление законно; «o=0» — это НЕ подстановка нуля, а взятие
   ТЕНИ (`st`), отдельная операция (предел процесса).  δ нигде не равно нулю и нигде не «становится»
   нулём — оно исчезает лишь в тени.  Машинно: разностное отношение = производная + остаток·δ (точное
   тождество), `st` убирает остаток.

   ★ ТОЧНЫЕ ТОЖДЕСТВА (Element-сторона, чистая field-алгебра, δ≠0):
     (x²)   (f(x+δ)−f(x))/δ = 2x + δ          (`dq_sq`)
     (x³)   (f(x+δ)−f(x))/δ = 3x² + 3xδ + δ²  (`dq_cube`)
     (x)    (f(x+δ)−f(x))/δ = 1               (`dq_id`)
     (c)    (f(x+δ)−f(x))/δ = 0               (`dq_const`)

   ★ ПРОИЗВОДНЫЕ ЧЕРЕЗ ТЕНЬ (st, через δ→0 по Архимеду):
     f(x)=x²  ⟹ f'(x) = 2x   (`deriv_sq`, флагман)
     f(x)=x³  ⟹ f'(x) = 3x²  (`deriv_cube`)
     f(x)=x   ⟹ f'(x) = 1    (`deriv_id`)
     f(x)=c   ⟹ f'(x) = 0    (`deriv_const`)

   ★ ГРАНИЦА.  Производная ПОЛИНОМА = Element: предел 2x рационален (при рациональном x) — процесс
   2x+δₙ сходится ВНУТРЬ Element-стороны (контраст с √2-процессами, что сходятся к role-limit).  Значит
   дифференцирование полиномов НЕ выходит за границу финитизации; role-limit появился бы лишь для
   трансцендентного f (exp и т.п. — нетерминирующий процесс, цитата к GermInfinitesimal/exp).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  st-шаг куба ТЕПЕРЬ доказан (`deriv_cube`): остаток
   3xδ+δ² ограничен (3|x|+1)·δ через Qabs и исчезает (δ→0).  `converges` для x²/x³/x/const доказан
   полностью.  Общий xⁿ (биномиальное разложение (x+δ)ⁿ) — горизонт.  δ→0 — Архимед (стандартный
   QArith).  st-производная как ОБЩАЯ операция на гладких процессах — арена будущего файла (цитата).

   Elements: GProc=nat→Q; delta=1/(n+1); diffquot; f_sq/f_cube/f_id/f_const; converges (двустор., lra).
   Roles:    δ=роль-приращение (∞-малое, ненулевое); diffquot=роль-наклон-секущей; st=роль-тень; f'=касательная.
   Rules:    δ≠0 (деление законно); diffquot = производная + остаток·δ (точно); st убирает остаток ⟹ f' точна.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: f'(x)=st((f(x+δ)−f(x))/δ) — производная через бесконечно малое над процессами.
     Rules (L5): δ≠0 ⟹ деление законно (нет 0/0); diffquot = производная + остаток·δ (Element-тождество);
                 st отбрасывает остаток (δ→0) ⟹ f' точна; f' полинома = Element.
     Roles (L4): δ=роль-приращение (∞-малое ненулевое); diffquot=роль-наклон-секущей; st=роль-тень; f'=касательная.
     Elements  : GProc; delta; diffquot; f_sq/f_cube/f_id/f_const; converges.
     ОБРАЗУЮЩИЕ: GermInfinitesimal (δ, δ≠0, ∞-мало); StandardPart (converges, единственность тени);
                 Архимед (δ→0); CauchyReal (предел как процесс, цитата).
     ВЛОЖЕННЫЕ : алгебр. тождество (Element, точное) vs st-шаг (тень); полином (f' Element) vs трансц. (role-limit).
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (DQ(x²)ₙ=2x+δₙ): Elements — процесс рац. наклонов секущих; Roles — приближение
                 касательной; Rules — правило n↦2x+1/(n+1) Element (член рационален, знаменатель ненулев); тень 2x
                 НЕ член (δₙ>0 всегда), но РАЦИОНАЛЬНА ⟹ сходимость ВНУТРЬ Element; призрак Беркли = δₙ (ненулев на
                 шаге, исчезает в тени).
   ДИАГНОСТИКА (P4): всё конечно-глубинно (Element); δ→0 = Архимед (процесс, не завершённая малость); f'
                 полинома = Element. ЧЕСТНО: куб — тождество доказано, st-шаг опущен; x²/x/const доказаны полностью.

   STATUS: 15 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Бесконечно малое δ = 1/(n+1) (реплицировано из GermInfinitesimal.v)     *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.

Definition Qsn (n : nat) : Q := inject_Z (Z.of_nat (S n)).

Lemma Qsn_pos : forall n, 0 < Qsn n.
Proof. intro n. unfold Qsn, Qlt. simpl. lia. Qed.

Definition delta (n : nat) : Q := / Qsn n.

Lemma delta_pos : forall n, 0 < delta n.
Proof. intro n. unfold delta. apply Qinv_lt_0_compat. apply Qsn_pos. Qed.

(** ★ δ НЕнулевое на КАЖДОМ шаге — деление на δ законно (нет 0/0). *)
Lemma delta_nonzero : forall n, ~ delta n == 0.
Proof.
  intros n H. pose proof (delta_pos n) as Hp. rewrite H in Hp. exact (Qlt_irrefl 0 Hp).
Qed.

(** Деление положительных положительно (реплицировано из GermInfinitesimal). *)
Lemma Qdiv_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a / b.
Proof.
  intros a b Ha Hb.
  assert (Hinv : 0 < / b) by (apply Qinv_lt_0_compat; exact Hb).
  unfold Qdiv. apply (proj2 (Qmult_lt_l 0 (/ b) a Ha)) in Hinv.
  rewrite Qmult_0_r in Hinv. exact Hinv.
Qed.

(** ★ δ ≤ 1 на каждом шаге (1/(n+1) ≤ 1) — нужно для оценки δ² ≤ δ. *)
Lemma delta_le_1 : forall n, delta n <= 1.
Proof.
  intro n. unfold delta.
  assert (Hp : 0 < Qsn n) by apply Qsn_pos.
  assert (Hne : ~ Qsn n == 0) by (intro Hc; rewrite Hc in Hp; exact (Qlt_irrefl 0 Hp)).
  assert (Hinv : 0 < / Qsn n) by (apply Qinv_lt_0_compat; exact Hp).
  assert (H1 : 1 <= Qsn n) by (unfold Qsn, Qle; simpl; lia).
  pose proof (Qmult_le_compat_r 1 (Qsn n) (/ Qsn n) H1 (Qlt_le_weak _ _ Hinv)) as H.
  rewrite Qmult_1_l in H. rewrite (Qmult_inv_r (Qsn n) Hne) in H. exact H.
Qed.

(* ===================================================================== *)
(*  Сходимость (двусторонняя, из StandardPart.v) и δ → 0 (Архимед)          *)
(* ===================================================================== *)

Definition converges (x : GProc) (L : Q) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> (- eps < x n - L) /\ (x n - L < eps).

(** ★ δ → 0: для любого eps найдётся хвост, где 1/(n+1) < eps (Архимед). *)
Lemma delta_converges_0 : converges delta 0.
Proof.
  intros eps Heps.
  assert (Hne_eps : ~ eps == 0).
  { intro Hc. rewrite Hc in Heps. exact (Qlt_irrefl 0 Heps). }
  destruct (Qarchimedean (/ eps)) as [p Hp].
  exists (Pos.to_nat p). intros n Hn.
  assert (HQpos : 0 < Qsn n) by apply Qsn_pos.
  assert (Hne : ~ Qsn n == 0).
  { intro Hc. rewrite Hc in HQpos. exact (Qlt_irrefl 0 HQpos). }
  split.
  - assert (Hr : delta n - 0 == delta n) by ring. rewrite Hr.
    pose proof (delta_pos n). lra.
  - assert (Hr : delta n - 0 == delta n) by ring. rewrite Hr.
    assert (Hlt : / eps < Qsn n).
    { apply Qlt_le_trans with (inject_Z (Z.pos p)).
      - exact Hp.
      - unfold Qsn. rewrite <- Zle_Qle. lia. }
    unfold delta.
    apply (proj1 (Qmult_lt_l (/ Qsn n) eps (Qsn n) HQpos)).
    rewrite (Qmult_inv_r (Qsn n) Hne).
    assert (Hk : eps * / eps < eps * Qsn n).
    { apply (proj2 (Qmult_lt_l (/ eps) (Qsn n) eps Heps)). exact Hlt. }
    rewrite (Qmult_inv_r eps Hne_eps) in Hk.
    rewrite Qmult_comm. exact Hk.
Qed.

(* ===================================================================== *)
(*  Разностное отношение и точные тождества (field-алгебра, δ≠0)            *)
(* ===================================================================== *)

Definition diffquot (f : Q -> Q) (x : Q) (n : nat) : Q := (f (x + delta n) - f x) / delta n.

Definition f_sq    (x : Q) : Q := x * x.
Definition f_cube  (x : Q) : Q := x * x * x.
Definition f_id    (x : Q) : Q := x.
Definition f_const (c x : Q) : Q := c.

(** ★ (x²): разностное отношение = 2x + δ (точно, на Element-стороне). *)
Lemma dq_sq : forall x n, diffquot f_sq x n == 2 * x + delta n.
Proof. intros x n. unfold diffquot, f_sq. field. apply delta_nonzero. Qed.

(** ★ (x³): разностное отношение = 3x² + 3xδ + δ². *)
Lemma dq_cube : forall x n, diffquot f_cube x n == 3 * x * x + 3 * x * delta n + delta n * delta n.
Proof. intros x n. unfold diffquot, f_cube. field. apply delta_nonzero. Qed.

(** (x): разностное отношение = 1. *)
Lemma dq_id : forall x n, diffquot f_id x n == 1.
Proof. intros x n. unfold diffquot, f_id. field. apply delta_nonzero. Qed.

(** (c): разностное отношение = 0. *)
Lemma dq_const : forall c x n, diffquot (f_const c) x n == 0.
Proof. intros c x n. unfold diffquot, f_const. field. apply delta_nonzero. Qed.

(* ===================================================================== *)
(*  ★ Производные через тень (st): остаток исчезает (δ→0)                   *)
(* ===================================================================== *)

(** ★★ ФЛАГМАН: f(x)=x² ⟹ f'(x)=2x.  Разностное отношение 2x+δ; тень = 2x ТОЧНО.
    δ нигде не нуль (делили законно), 2x достигается лишь в тени. *)
Lemma deriv_sq : forall x, converges (diffquot f_sq x) (2 * x).
Proof.
  intros x eps Heps. destruct (delta_converges_0 eps Heps) as [N HN].
  exists N. intros n Hn. destruct (HN n Hn) as [HA HB].
  rewrite (dq_sq x n). split; lra.
Qed.

(** f(x)=x ⟹ f'(x)=1 (разностное отношение тождественно 1). *)
Lemma deriv_id : forall x, converges (diffquot f_id x) 1.
Proof.
  intros x eps Heps. exists 0%nat. intros n _. rewrite (dq_id x n). split; lra.
Qed.

(** f(x)=c ⟹ f'(x)=0 (разностное отношение тождественно 0). *)
Lemma deriv_const : forall c x, converges (diffquot (f_const c) x) 0.
Proof.
  intros c x eps Heps. exists 0%nat. intros n _. rewrite (dq_const c x n). split; lra.
Qed.

(** ★★ f(x)=x³ ⟹ f'(x)=3x²: остаток 3xδ+δ² ограничен (3|x|+1)·δ и исчезает в тени (δ→0).
    Полный st-шаг куба, парный к флагману x². *)
Lemma deriv_cube : forall x, converges (diffquot f_cube x) (3 * x * x).
Proof.
  intros x eps Heps.
  assert (Hxle : x <= Qabs x) by apply Qle_Qabs.
  assert (Hxge : (- Qabs x) <= x).
  { pose proof (Qle_Qabs (- x)) as H. rewrite Qabs_opp in H. lra. }
  assert (Hq : 0 <= Qabs x) by apply Qabs_nonneg.
  assert (HM : 0 < 3 * Qabs x + 1) by lra.
  assert (Hbnd : 0 < eps / (3 * Qabs x + 1)) by (apply Qdiv_pos; [ exact Heps | exact HM ]).
  destruct (delta_converges_0 (eps / (3 * Qabs x + 1)) Hbnd) as [N HN].
  exists N. intros n Hn. destruct (HN n Hn) as [HA HB].
  pose proof (delta_pos n) as Hd0. pose proof (delta_le_1 n) as Hd1.
  assert (HBd : delta n < eps / (3 * Qabs x + 1)) by lra.
  assert (Hne : ~ (3 * Qabs x + 1) == 0) by lra.
  assert (Hmd : (3 * Qabs x + 1) * delta n < eps).
  { apply Qlt_le_trans with ((3 * Qabs x + 1) * (eps / (3 * Qabs x + 1))).
    - apply (proj2 (Qmult_lt_l (delta n) (eps / (3 * Qabs x + 1)) (3 * Qabs x + 1) HM)). exact HBd.
    - setoid_replace ((3 * Qabs x + 1) * (eps / (3 * Qabs x + 1))) with eps by (field; exact Hne).
      apply Qle_refl. }
  assert (HMe : (3 * Qabs x + 1) * delta n == 3 * (Qabs x * delta n) + delta n) by ring.
  assert (Hxd1 : x * delta n <= Qabs x * delta n)
    by (apply Qmult_le_compat_r; [ exact Hxle | exact (Qlt_le_weak _ _ Hd0) ]).
  assert (Hxd2 : (- Qabs x) * delta n <= x * delta n)
    by (apply Qmult_le_compat_r; [ exact Hxge | exact (Qlt_le_weak _ _ Hd0) ]).
  assert (Hdd : delta n * delta n <= 1 * delta n)
    by (apply Qmult_le_compat_r; [ exact Hd1 | exact (Qlt_le_weak _ _ Hd0) ]).
  assert (Hdd0 : 0 <= delta n * delta n).
  { pose proof (Qmult_le_compat_r 0 (delta n) (delta n) (Qlt_le_weak _ _ Hd0) (Qlt_le_weak _ _ Hd0)) as H0.
    rewrite Qmult_0_l in H0. exact H0. }
  rewrite (dq_cube x n). split; lra.
Qed.

(* ===================================================================== *)
(*  Капстоун: производная как тень разностного отношения                    *)
(* ===================================================================== *)

(** Нестандартное исчисление над процессами (0 аксиом):
      (★ нет 0/0)     δ ≠ 0 на каждом шаге — деление на приращение законно;
      (★ тождество)   разностное отношение x² = 2x + δ ТОЧНО (Element-сторона);
      (★ флагман)     st даёт f'(x²) = 2x ТОЧНО — производная без epsilon-предела;
      (линейность)    f'(x)=1, f'(c)=0.
    Парадокс Беркли растворён: δ — процесс, ненулевой на шаге (делим), исчезает лишь в тени (st).
    Граница: предел 2x рационален ⟹ дифференцирование полинома НЕ выходит за границу финитизации. *)
Theorem derivative_summary :
  (forall n, ~ delta n == 0)
  /\ (forall x n, diffquot f_sq x n == 2 * x + delta n)
  /\ (forall x, converges (diffquot f_sq x) (2 * x))
  /\ (forall x, converges (diffquot f_cube x) (3 * x * x))
  /\ (forall x, converges (diffquot f_id x) 1)
  /\ (forall c x, converges (diffquot (f_const c) x) 0).
Proof.
  split; [ exact delta_nonzero |].
  split; [ exact dq_sq |].
  split; [ exact deriv_sq |].
  split; [ exact deriv_cube |].
  split; [ exact deriv_id | exact deriv_const ].
Qed.
