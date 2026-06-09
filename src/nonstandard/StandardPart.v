(** * StandardPart.v — стандартная часть (тень) как ЧАСТИЧНАЯ функция на germ-процессах:
      ТОТАЛЬНА и однозначна на сходящихся (Element), НЕОПРЕДЕЛЕНА на ограниченно-расходящихся
      (role-limit: нужен выбор подпоследовательности = ультрафильтр).  Свидетель — осциллятор alt=±1.

   КОНТЕКСТ.  Часть XVIII «Нестандартный анализ над процессами», Батч A (после GermInfinitesimal,
   UltrafilterRoleLimit).  Стандартная часть st(x) («тень») = вещественное, к которому germ x бесконечно
   близок.  В обычном NSA st тотальна на конечных гипердействительных — но РОВНО потому, что ультрафильтр
   выбирает предел подпоследовательности.  ЗДЕСЬ, на Element-стороне (Фреше, без ультрафильтра), st
   ЧАСТИЧНА: определена там, где процесс сходится; неопределена на ограниченно-расходящихся.

   ★ ГЛАВНЫЙ РЕЗУЛЬТАТ (genuine).  st — частичная функция, и её частичность — НЕ дефект, а граница
   финитизации (H1) в форме «тень»:
     (Element)     сходящийся germ имеет ЕДИНСТВЕННУЮ тень (`shadow_unique`); константы имеют тень.
     (role-limit)  осциллятор alt(n)=(−1)ⁿ ОГРАНИЧЕН (`alt_bounded`), но НЕ Коши (`alt_not_cauchy`) и
                   НЕ имеет тени (`no_shadow_for_alt`) — ибо тень требует выбора «какая подпоследовательность
                   есть предел»: mod «Evens велико» тень = 1, mod «Odds велико» тень = −1, два несовместимых
                   значения (`alt_shadow_mod_evens/odds`) ⟹ канона нет ⟹ ультрафильтр (role-limit).

   ★ МАШИННЫЙ МОСТ к UltrafilterRoleLimit.v.  `alt = even_ind − odd_ind` (`alt_decomp`): осциллятор без
   тени есть РАЗНОСТЬ тех же двух индикаторов, чьё ПРОИЗВЕДЕНИЕ — делитель нуля.  Один и тот же
   неразрешённый раскол Evens/Odds проявляется ДВАЖДЫ: аддитивно (нет тени) и мультипликативно (делитель
   нуля).  Та же граница, две алгебраические формы.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Двусторонняя формулировка сходимости (−eps < · < eps)
   выбрана сознательно — она чисто линейна (lra), без Qabs.  st как ОТОБРАЖЕНИЕ в RealProcess (nat→Q) для
   ПРОИЗВОЛЬНОГО Коши-germ — арена `CauchyReal.v` (цитата, не передоказывается здесь); тень тогда = сам
   процесс как вещественное.  Здесь доказано: единственность тени, тень констант, и ПОЛНАЯ частичность на
   каноническом свидетеле alt.  Genuine — частичность st = граница финитизации в форме «тень» + машинный
   мост (alt = even_ind − odd_ind) к делителю нуля.

   Elements: GProc=nat→Q; converges/is_cauchy/bounded (двусторонние); alt=(−1)ⁿ; even_ind/odd_ind; gconst.
   Roles:    germ=процесс; тень=роль-стандартное-значение; сходимость=роль-Коши; alt=роль-осциллятор.
   Rules:    st однозначна где есть (L5); тотальна на сходящихся (Element), нет на огранич.-расходящихся
             (role-limit); alt — два несовместимых значения тени; alt = even_ind − odd_ind.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: стандартная часть st как ЧАСТИЧНАЯ функция; частичность = граница финитизации в форме «тень».
     Rules (L5): shadow_unique (L5-детерминизм); тотальна на сходящихся, нет на огранич.-расход.; alt — две
                 тени ±1; alt = even_ind − odd_ind.
     Roles (L4): germ=процесс; тень=роль-станд.-значение; сходимость=роль-Коши; alt=роль-осциллятор/свидетель.
     Elements  : GProc; converges/is_cauchy/bounded (двустор., lra); alt; even_ind/odd_ind; gconst.
     ОБРАЗУЮЩИЕ: UltrafilterRoleLimit (тот же Evens/Odds-раскол: alt=even_ind−odd_ind, аддитивный след);
                 GermInfinitesimal (germ-кольцо); CauchyReal (RealProcess, тень как процесс, цитата);
                 RoleLimitLadder (цена выбора подпоследовательности).
     ВЛОЖЕННЫЕ : сходящийся (Element, тень единственна) vs огранич.-расходящийся (role-limit, нет тени).
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (alt): Elements ±1 чередуются; Roles осциллятор; Rules — значение тени НЕ
                 определено внутренне (нужен внешний выбор «какая подпоследовательность — предел») ⟹ система
                 НЕПОЛНА ⟹ role-limit-значение; та же структура, что неопределённый unit-статус even_ind.
   ДИАГНОСТИКА (P4): всё конечно-глубинно по координате (Element); единственный role-limit — тень
                 огранич.-расходящегося (выбор подпоследовательности/ультрафильтр), НЕ ассертим — два значения alt.
   ЧЕСТНО: st в RealProcess для общего Коши-germ = цитата к CauchyReal; здесь — единственность + частичность.

   STATUS: 12 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Процессы и сходимость (двусторонняя — чисто линейная, без Qabs)         *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.

(** Сходимость к рациональному L (двусторонне: −eps < xₙ−L < eps). *)
Definition converges (x : GProc) (L : Q) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> (- eps < x n - L) /\ (x n - L < eps).

Definition has_shadow (x : GProc) : Prop := exists L, converges x L.

(** Свойство Коши (двусторонне). *)
Definition is_cauchy (x : GProc) : Prop :=
  forall eps, 0 < eps -> exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
    (- eps < x m - x n) /\ (x m - x n < eps).

(** Ограниченность (двусторонне). *)
Definition bounded (x : GProc) : Prop := exists B, forall n, (- B <= x n) /\ (x n <= B).

(** Канонический свидетель: осциллятор alt(n) = (−1)ⁿ; индикаторы; константа. *)
Definition alt (n : nat) : Q := if Nat.even n then 1 else Qopp 1.
Definition even_ind (n : nat) : Q := if Nat.even n then 1 else 0.
Definition odd_ind  (n : nat) : Q := if Nat.odd  n then 1 else 0.
Definition gconst (q : Q) (n : nat) : Q := q.

(** Фильтры-уточнения (= «объявить Evens / Odds большим»), как в UltrafilterRoleLimit. *)
Definition geq_on_evens (x y : GProc) : Prop :=
  exists N, forall n, (N <= n)%nat -> Nat.even n = true -> x n == y n.
Definition geq_on_odds (x y : GProc) : Prop :=
  exists N, forall n, (N <= n)%nat -> Nat.odd n = true -> x n == y n.

(* ===================================================================== *)
(*  st однозначна там, где существует (L5-детерминизм)                      *)
(* ===================================================================== *)

(** Зажим: если 0 ≤ окрестность для всех eps, то значение нуль. *)
Lemma small_two_sided : forall a, (forall eps, 0 < eps -> - eps < a /\ a < eps) -> a == 0.
Proof.
  intros a H.
  assert (Hle : a <= 0).
  { destruct (Qlt_le_dec 0 a) as [Hlt | Hle]; [| exact Hle].
    destruct (H a Hlt) as [_ Ha]. exfalso. apply (Qlt_irrefl a Ha). }
  assert (Hge : 0 <= a).
  { destruct (Qlt_le_dec a 0) as [Hlt | Hge]; [| exact Hge].
    assert (Hpos : 0 < - a) by lra.
    destruct (H (- a) Hpos) as [Ha _]. exfalso. lra. }
  apply Qle_antisym; assumption.
Qed.

(** ★ Тень ЕДИНСТВЕННА (стандартная часть корректно определена там, где есть). *)
Lemma shadow_unique : forall x L1 L2, converges x L1 -> converges x L2 -> L1 == L2.
Proof.
  intros x L1 L2 H1 H2.
  assert (Hz : L1 - L2 == 0).
  { apply small_two_sided. intros eps Heps.
    assert (Hh : 0 < (1#2) * eps) by lra.
    destruct (H1 _ Hh) as [N1 HN1].
    destruct (H2 _ Hh) as [N2 HN2].
    destruct (HN1 (Nat.max N1 N2) (Nat.le_max_l _ _)) as [A1 A2].
    destruct (HN2 (Nat.max N1 N2) (Nat.le_max_r _ _)) as [B1 B2].
    split; lra. }
  lra.
Qed.

(** Element-сторона: константы имеют тень (тривиальный сходящийся процесс). *)
Lemma const_has_shadow : forall q, has_shadow (gconst q).
Proof.
  intro q. exists q. intros eps Heps. exists 0%nat. intros n _.
  unfold gconst. split; lra.
Qed.

(* ===================================================================== *)
(*  Значения осциллятора alt                                                *)
(* ===================================================================== *)

Lemma alt_even : forall n, Nat.even n = true -> alt n = 1.
Proof. intros n H. unfold alt. rewrite H. reflexivity. Qed.

Lemma alt_odd : forall n, Nat.even n = false -> alt n = Qopp 1.
Proof. intros n H. unfold alt. rewrite H. reflexivity. Qed.

(* ===================================================================== *)
(*  ★ role-limit: alt ограничен, но НЕ Коши и НЕ имеет тени                 *)
(* ===================================================================== *)

(** alt ограничен: −1 ≤ alt n ≤ 1. *)
Lemma alt_bounded : bounded alt.
Proof.
  exists 1. intro n. destruct (Nat.even n) eqn:E.
  - rewrite (alt_even _ E). split; lra.
  - rewrite (alt_odd _ E). split; lra.
Qed.

(** alt НЕ Коши: соседние чёт/нечёт отличаются на 2 (свидетель eps=1). *)
Lemma alt_not_cauchy : ~ is_cauchy alt.
Proof.
  intros HC. destruct (HC 1 ltac:(lra)) as [N HN].
  assert (He : Nat.even (2 * N) = true).
  { replace (2 * N)%nat with (0 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  assert (Ho : Nat.even (2 * N + 1) = false).
  { replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  destruct (HN (2 * N)%nat (2 * N + 1)%nat ltac:(lia) ltac:(lia)) as [H1 H2].
  rewrite (alt_even _ He), (alt_odd _ Ho) in H2. lra.
Qed.

(** ★★ alt НЕ имеет тени: предполагаемая тень L должна лежать и в (0,2), и в (−2,0). *)
Lemma no_shadow_for_alt : ~ has_shadow alt.
Proof.
  intros [L HL]. destruct (HL 1 ltac:(lra)) as [N HN].
  assert (He : Nat.even (2 * N) = true).
  { replace (2 * N)%nat with (0 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  assert (Ho : Nat.even (2 * N + 1) = false).
  { replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  destruct (HN (2 * N)%nat ltac:(lia)) as [Ea Eb].
  destruct (HN (2 * N + 1)%nat ltac:(lia)) as [Oa Ob].
  rewrite (alt_even _ He) in Ea, Eb.
  rewrite (alt_odd _ Ho) in Oa, Ob.
  lra.
Qed.

(* ===================================================================== *)
(*  ★ Две несовместимые тени = неканоничность = role-limit                  *)
(* ===================================================================== *)

(** Объяви «Evens велико» — тень alt = 1. *)
Lemma alt_shadow_mod_evens : geq_on_evens alt (gconst 1).
Proof.
  exists 0%nat. intros n _ He. unfold gconst. rewrite (alt_even _ He). reflexivity.
Qed.

(** Объяви «Odds велико» — тень alt = −1. *)
Lemma alt_shadow_mod_odds : geq_on_odds alt (gconst (Qopp 1)).
Proof.
  exists 0%nat. intros n _ Ho. unfold gconst.
  assert (He : Nat.even n = false).
  { rewrite <- Nat.negb_odd. rewrite Ho. reflexivity. }
  rewrite (alt_odd _ He). reflexivity.
Qed.

(* ===================================================================== *)
(*  ★ Машинный мост: alt = even_ind − odd_ind                               *)
(* ===================================================================== *)

(** Осциллятор без тени = РАЗНОСТЬ двух индикаторов, чьё ПРОИЗВЕДЕНИЕ — делитель нуля
    (UltrafilterRoleLimit).  Один раскол Evens/Odds, две алгебраические формы. *)
Lemma alt_decomp : forall n, alt n == even_ind n - odd_ind n.
Proof.
  intro n. unfold alt, even_ind, odd_ind.
  destruct (Nat.even n) eqn:E.
  - assert (Ho : Nat.odd n = false).
    { rewrite <- Nat.negb_even. rewrite E. reflexivity. }
    rewrite Ho. cbv iota. ring.
  - assert (Ho : Nat.odd n = true).
    { rewrite <- Nat.negb_even. rewrite E. reflexivity. }
    rewrite Ho. cbv iota. ring.
Qed.

(* ===================================================================== *)
(*  Капстоун: частичность стандартной части                                 *)
(* ===================================================================== *)

(** Стандартная часть (тень) — ЧАСТИЧНАЯ функция, и частичность = граница финитизации (0 аксиом):
      (★ единственность)  сходящийся germ имеет ЕДИНСТВЕННУЮ тень (L5-детерминизм);
      (Element)           константы имеют тень;
      (★ role-limit)      alt ограничен, но НЕ Коши и НЕ имеет тени;
      (★ неканоничность)  mod «Evens велико» тень alt = 1, mod «Odds велико» тень alt = −1.
    Тень огранич.-расходящегося требует выбора подпоследовательности (ультрафильтр) — role-limit.
    Мост: alt = even_ind − odd_ind — тот же Evens/Odds-раскол, что делитель нуля, в аддитивной форме. *)
Theorem standard_part_summary :
  (forall x L1 L2, converges x L1 -> converges x L2 -> L1 == L2)
  /\ (forall q, has_shadow (gconst q))
  /\ bounded alt
  /\ ~ is_cauchy alt
  /\ ~ has_shadow alt
  /\ geq_on_evens alt (gconst 1)
  /\ geq_on_odds alt (gconst (Qopp 1)).
Proof.
  split; [ exact shadow_unique |].
  split; [ exact const_has_shadow |].
  split; [ exact alt_bounded |].
  split; [ exact alt_not_cauchy |].
  split; [ exact no_shadow_for_alt |].
  split; [ exact alt_shadow_mod_evens | exact alt_shadow_mod_odds ].
Qed.
