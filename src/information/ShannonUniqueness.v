(** * ShannonUniqueness.v — M1: единственность меры информации (Element-ядро + role-limit-горизонт).

   Мотив M1 части XVII: энтропия Шеннона возникает как ЕДИНСТВЕННАЯ мера информации, удовлетворяющая
   аддитивности и нормировке.  Полная теорема (Шеннон–Хинчин–Фаддеев) реально-аналитична: непрерывность
   над ℝ ⇒ −Σ pᵢ log pᵢ единственно.  Непрерывность над завершённым ℝ — это role-limit-сторона границы
   финитизации.  Здесь закрыто честное ELEMENT-ЯДРО M1 и точно локализован role-limit.

   ★ ЧТО ДОКАЗАНО (0 аксиом, ℚ-арифметика, Element-сторона):
     -- f(2^k) = k: аддитивность + нормировка ВЫНУЖДАЮТ меру совпасть с log₂ на ДИАДИЧЕСКОЙ решётке
        (f_two_pow); это и есть крукс Хинчина (шаг f(mⁿ)=n·f(m)) на конечной стороне;
     -- f(bᵏ) = k·f(b) на всей мультипликативной решётке (f_pow_self);
     -- ЕДИНСТВЕННОСТЬ на диадической решётке: любые две аддитивно-нормированные меры совпадают на 2^k
        (uniqueness_dyadic).

   ★ ГДЕ ВХОДИТ role-limit (точно локализовано, не стена):
     аддитивность+нормировка пиннят лишь решётку; ДОвинтить меру на всех n (т.е. до полного log₂) можно
     только МОНОТОННОСТЬЮ — а она ЗАЖИМАЕТ f(3) в сужающийся рациональный интервал (mono_traps_three:
     1<f(3)<2; mono_narrows_three: 3/2<f(3)<2; и так далее), пиннящий f(3) к log₂3 ∉ ℚ.  То есть полная
     мера Шеннона есть ПРОЦЕСС (предел сужающихся ℚ-интервалов), а не завершённый ℚ-объект — ровно
     role-limit-сторона (то же log₂3, что трит в ShannonSynthesis).  Машинно: интервал сужается; что
     предел иррационален — цитата (DyadicBits.log2_3_irrational), не передоказывается.

   HONEST SCOPE.  НЕ доказываем: полную реально-аналитическую Хинчина (непрерывность над ℝ); расширение
   правилом группировки до −Σ pᵢ log pᵢ для ПРОИЗВОЛЬНЫХ распределений (стандартно, механически);
   иррациональность самого предела (цитата).  Underdetermination без монотонности — честно: аддитивность
   задаёт f её значениями на ПРОСТЫХ, и они свободны (напр. 2-адическая оценка аддитивна+нормирована, но
   = 0 на нечётных), оттого монотонность необходима — отсюда и role-limit.

   Elements: мера f : nat -> Q на «n равновероятных исходов»; диадическая решётка 2^k.
   Roles:    f = роль-мера информации; диадический скелет = Element-роль (точно log₂); полная мера = role-limit-процесс.
   Rules:    аддитивность f(mn)=f(m)+f(n) + нормировка f(2)=1 вынуждают f=log₂ на решётке; монотонность зажимает остаток в процесс.
   ДИАГНОСТИКА (P4): M1-единственность ФОРСИРОВАНА на Element-стороне (решётка, 0-ax); полная мера — role-limit (сужающийся процесс к log₂3∉ℚ), не завершённый объект.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia ZArith.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Мера информации: аддитивность + нормировка                            *)
(* ===================================================================== *)

(** f n = информация «n равновероятных исходов». *)
Definition additive (f : nat -> Q) : Prop :=
  forall m n, (0 < m)%nat -> (0 < n)%nat -> f (m * n)%nat == f m + f n.

Definition normalized (f : nat -> Q) : Prop := f 2%nat == 1.

(** Монотонность (строгая): больше исходов — больше информации. *)
Definition monotone (f : nat -> Q) : Prop :=
  forall m n, (m < n)%nat -> f m < f n.

(* --- вспомогательные --- *)

Lemma nat_pow_pos : forall b k, (0 < b)%nat -> (0 < b ^ k)%nat.
Proof. intros b k Hb. induction k as [|k IH]; simpl; [ lia | nia ]. Qed.

Lemma injZ_succ : forall k, inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1.
Proof.
  intro k. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity.
Qed.

(** Аддитивность форсирует f(1)=0. *)
Lemma add_f1 : forall f, additive f -> f 1%nat == 0.
Proof.
  intros f H. pose proof (H 1%nat 1%nat ltac:(lia) ltac:(lia)) as H1.
  simpl in H1. lra.
Qed.

(* ===================================================================== *)
(*  Element-ядро: f форсирована = log₂ на мультипликативной решётке        *)
(* ===================================================================== *)

(** f(bᵏ) = k·f(b): аддитивность ВЫНУЖДАЕТ степенной закон на всей решётке. *)
Lemma f_pow_self : forall f, additive f -> forall b k, (0 < b)%nat ->
  f (b ^ k)%nat == inject_Z (Z.of_nat k) * f b.
Proof.
  intros f Hadd b k Hb. induction k as [|k IH].
  - change (b ^ 0)%nat with 1%nat. rewrite (add_f1 f Hadd).
    assert (E : inject_Z (Z.of_nat 0) == 0) by reflexivity. rewrite E. ring.
  - replace (b ^ S k)%nat with (b * b ^ k)%nat by reflexivity.
    rewrite (Hadd b (b ^ k)%nat Hb (nat_pow_pos b k Hb)).
    rewrite IH, injZ_succ. ring.
Qed.

(** f(2^k) = k: диадический скелет совпадает с log₂ — точно, 0-ax. *)
Lemma f_two_pow : forall f, additive f -> normalized f -> forall k,
  f (2 ^ k)%nat == inject_Z (Z.of_nat k).
Proof.
  intros f Hadd Hnorm k.
  rewrite (f_pow_self f Hadd 2 k ltac:(lia)).
  unfold normalized in Hnorm. rewrite Hnorm. ring.
Qed.

(** ЕДИНСТВЕННОСТЬ на диадической решётке: любые две аддит.-норм. меры совпадают на 2^k. *)
Theorem uniqueness_dyadic : forall f g,
  additive f -> normalized f -> additive g -> normalized g ->
  forall k, f (2 ^ k)%nat == g (2 ^ k)%nat.
Proof.
  intros f g Hf Hnf Hg Hng k.
  rewrite (f_two_pow f Hf Hnf k), (f_two_pow g Hg Hng k). reflexivity.
Qed.

(* ===================================================================== *)
(*  role-limit: монотонность зажимает f(3) в сужающийся процесс к log₂3     *)
(* ===================================================================== *)

(** Первый зажим: 1 < f(3) < 2 (между f(2)=1 и f(4)=2). *)
Lemma mono_traps_three : forall f, additive f -> normalized f -> monotone f ->
  1 < f 3%nat /\ f 3%nat < 2.
Proof.
  intros f Hadd Hnorm Hmono.
  assert (F2 : f 2%nat == 1) by exact Hnorm.
  assert (F4 : f 4%nat == 2).
  { pose proof (f_two_pow f Hadd Hnorm 2) as H.
    replace (2 ^ 2)%nat with 4%nat in H by reflexivity.
    assert (E : inject_Z (Z.of_nat 2) == 2) by reflexivity. rewrite E in H. exact H. }
  split.
  - rewrite <- F2. apply Hmono. lia.
  - rewrite <- F4. apply Hmono. lia.
Qed.

(** Сужение (следующая ступень процесса): 3/2 < f(3) < 2 — через f(9)=2·f(3), f(8)=3, f(16)=4. *)
Lemma mono_narrows_three : forall f, additive f -> normalized f -> monotone f ->
  3 < (2 * f 3%nat) /\ (2 * f 3%nat) < 4.
Proof.
  intros f Hadd Hnorm Hmono.
  assert (F9 : f 9%nat == 2 * f 3%nat).
  { pose proof (f_pow_self f Hadd 3 2 ltac:(lia)) as H.
    replace (3 ^ 2)%nat with 9%nat in H by reflexivity.
    assert (E : inject_Z (Z.of_nat 2) == 2) by reflexivity. rewrite E in H. exact H. }
  assert (F8 : f 8%nat == 3).
  { pose proof (f_two_pow f Hadd Hnorm 3) as H.
    replace (2 ^ 3)%nat with 8%nat in H by reflexivity.
    assert (E : inject_Z (Z.of_nat 3) == 3) by reflexivity. rewrite E in H. exact H. }
  assert (F16 : f 16%nat == 4).
  { pose proof (f_two_pow f Hadd Hnorm 4) as H.
    replace (2 ^ 4)%nat with 16%nat in H by reflexivity.
    assert (E : inject_Z (Z.of_nat 4) == 4) by reflexivity. rewrite E in H. exact H. }
  split.
  - rewrite <- F9, <- F8. apply Hmono. lia.
  - rewrite <- F9, <- F16. apply Hmono. lia.
Qed.

(* ===================================================================== *)
(*  Капстоун M1                                                            *)
(* ===================================================================== *)

(** M1 (Element-ядро + role-limit-горизонт):
      (форсировано)  f(2^k)=k — диадический скелет вынужден = log₂ (0-ax);
      (единственно)  любые две аддит.-норм. меры совпадают на диадической решётке;
      (role-limit)   монотонность зажимает f(3) в сужающийся рациональный интервал (3/2, 2) —
                     процесс, пиннящий f(3) к log₂3 ∉ ℚ, а не завершённый ℚ-объект.
    Полная реально-аналитическая единственность (непрерывность над ℝ) и группировка до −Σ pᵢ log pᵢ —
    горизонт; underdetermination без монотонности — честный (простые свободны). *)
Theorem shannon_measure_M1 : forall f, additive f -> normalized f ->
  (forall k, f (2 ^ k)%nat == inject_Z (Z.of_nat k))
  /\ (forall g, additive g -> normalized g -> forall k, f (2 ^ k)%nat == g (2 ^ k)%nat)
  /\ (monotone f -> (3 # 2) < f 3%nat /\ f 3%nat < 2).
Proof.
  intros f Hadd Hnorm. split; [ | split ].
  - exact (f_two_pow f Hadd Hnorm).
  - intros g Hg Hng. exact (uniqueness_dyadic f g Hadd Hnorm Hg Hng).
  - intro Hmono.
    pose proof (mono_narrows_three f Hadd Hnorm Hmono) as [Hlo _].
    pose proof (mono_traps_three f Hadd Hnorm Hmono) as [_ Hhi].
    split; [ lra | exact Hhi ].
Qed.
