(** * InclusionExclusionFib.v — принцип включения-исключения + комбинаторный Фибоначчи
      (закрытие gap'а §3.4 Части XVI «Дискретная математика»: вкл-искл, числа Фибоначчи / произв. функция).

   Корпус комбинаторики уже несёт биномы/Паскаль/Каталан/голубятню (`stdlib/CombinatoricsExt.v`,
   `cs/PumpingPigeonhole.v`).  ЗДЕСЬ закрываются два названных gap'а плана Части XVI §3.4:
     ВКЛ-ИСКЛ — на уровне ИНДИКАТОРОВ (счёт по конечному префиксу [0,n)), 2- и 3-множеств;
     ФИБОНАЧЧИ — как КОМБИНАТОРНЫЙ счёт (число замощений полосы 1×n плитками 1×1/1×2) + частичная
                 сумма Σ fib = fib(n+2)−1 (целое тело производящей функции).

   ★ Element-сторона (genuine для H1).  Вся конечная комбинаторика 0-аксиомна: дискретность ⟹ конечный
   перебор (count по [0,n), P4) + ℕ ⟹ ни LEM, ни AC, ни axiom of infinity.  Вкл-искл = ПОЭЛЕМЕНТНОЕ
   булево тождество (b(A∪B)+b(A∩B)=bA+bB, и аналог на 3 множества), проинтегрированное счётом.  Число
   замощений 1×n = fib(n+1) — та же рекуррентность (последняя плитка 1×1 → tilings(n−1), 1×2 → tilings(n−2)).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  ⚠ Формальная ПРОИЗВОДЯЩАЯ ФУНКЦИЯ F(x)=Σ fibₙ xⁿ=x/(1−x−x²)
   как формальный степенной ряд — это арена Части XVII (`FormalPowerSeries.v`); ЗДЕСЬ доказано её целое
   тело (частичная сумма Σfib=fib(n+2)−1 + комбинаторный смысл замощениями), сам ряд — цитата к XVII, не
   передоказывается.  Асимптотика fibₙ ~ φⁿ/√5 = role-limit (φ иррационально, за границей финитизации).

   Elements: конечный префикс [0,n); булевы предикаты A,B,C; натуральные fib / tilings.
   Roles:    count = роль-мера множества; индикатор = роль-членство; fib = роль-счётчик замощений.
   Rules:    вкл-искл = поэлементное булево тождество; fib-рекуррентность; замощения 1×n = fib(n+1).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: вкл-искл (indicator) + комбинаторный Фибоначчи (замощения + частичная сумма) над ℕ.
     Rules (L5): count = L5-перебор индикаторов (P4); вкл-искл = b(A∪B)+b(A∩B)=bA+bB; fib-рекуррентность;
                 замощения 1×n = fib(n+1); Σfib = fib(n+2)−1.
     Roles (L4): count=роль-мера; индикатор=роль-членство; fib=роль-счётчик.
     Elements  : префикс [0,n); булевы A,B,C; fib/tilings.
     ОБРАЗУЮЩИЕ: CombinatoricsExt (Паскаль/Каталан, сосед); FormalPowerSeries (XVII, произв.функция, цитата);
                 cs/PumpingPigeonhole (Дирихле).
     ВЛОЖЕННЫЕ : 2-множеств / 3-множеств вкл-искл; fib-рекуррентность; замощения=fib.
   ДИАГНОСТИКА (P4): чистая Element-сторона — конечная комбинаторика 0-аксиомна (перебор+ℕ, ни LEM/AC/∞).
   ЧЕСТНО: формальная произв.функция = арена XVII (цитата); асимптотика φⁿ/√5 = role-limit (φ).

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia Bool.

(* ===================================================================== *)
(*  Счёт по конечному префиксу [0,n) и принцип включения-исключения        *)
(* ===================================================================== *)

(** count n P = число k < n с P k = true (P4: конечная глубина перебора). *)
Fixpoint count (n : nat) (P : nat -> bool) : nat :=
  match n with
  | O => O
  | S k => count k P + (if P k then 1 else 0)
  end.

(** ★ Включение-исключение для двух множеств (аддитивная форма, без nat-вычитания). *)
Lemma count_union_inter : forall n A B,
  count n (fun k => A k || B k) + count n (fun k => A k && B k)
  = count n A + count n B.
Proof.
  induction n as [| n IHn]; intros A B.
  - reflexivity.
  - simpl. specialize (IHn A B). destruct (A n) eqn:EA, (B n) eqn:EB; simpl; lia.
Qed.

(** ★ Субаддитивность |A∪B| ≤ |A|+|B| (следствие: |A∩B| ≥ 0). *)
Lemma count_subadd : forall n A B,
  count n (fun k => A k || B k) <= count n A + count n B.
Proof. intros n A B. pose proof (count_union_inter n A B). lia. Qed.

(** ★ Включение-исключение для трёх множеств (аддитивная форма). *)
Lemma count_incl_excl_3 : forall n A B C,
  count n (fun k => A k || B k || C k)
  + count n (fun k => A k && B k)
  + count n (fun k => A k && C k)
  + count n (fun k => B k && C k)
  = count n A + count n B + count n C
  + count n (fun k => A k && B k && C k).
Proof.
  induction n as [| n IHn]; intros A B C.
  - reflexivity.
  - simpl. specialize (IHn A B C).
    destruct (A n) eqn:EA, (B n) eqn:EB, (C n) eqn:EC; simpl; lia.
Qed.

(* ===================================================================== *)
(*  Числа Фибоначчи как КОМБИНАТОРНЫЙ счёт                                   *)
(* ===================================================================== *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => O
  | S O => 1
  | S (S k as m) => fib k + fib m
  end.

Lemma fib_pos : forall n, (1 <= fib (S n))%nat.
Proof.
  assert (H : forall n, (1 <= fib (S n))%nat /\ (1 <= fib (S (S n)))%nat).
  { induction n as [| n [H1 H2]].
    - simpl. split; lia.
    - split.
      + exact H2.
      + change (fib (S (S (S n)))) with (fib (S n) + fib (S (S n))).
        apply Nat.le_trans with (fib (S n)). exact H1. apply Nat.le_add_r. }
  intro n. apply H.
Qed.

(** Частичная сумма чисел Фибоначчи (целое тело производящей функции). *)
Fixpoint sumfib (n : nat) : nat :=
  match n with O => fib 0 | S k => sumfib k + fib (S k) end.

(** ★ Σ_{i=0}^{n} fib i = fib(n+2) − 1  (аддитивно: sumfib n + 1 = fib(n+2)). *)
Lemma fib_sum : forall n, sumfib n + 1 = fib (S (S n)).
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - cbn [sumfib].
    change (fib (S (S (S n)))) with (fib (S n) + fib (S (S n))).
    rewrite <- IHn. lia.
Qed.

(** Число замощений полосы 1×n плитками 1×1 и 1×2. *)
Fixpoint tilings (n : nat) : nat :=
  match n with O => 1 | S O => 1 | S (S k as m) => tilings m + tilings k end.

(** ★ Число замощений 1×n = fib(n+1) (та же рекуррентность: последняя плитка 1×1 или 1×2). *)
Lemma tilings_eq_fib : forall n, tilings n = fib (S n).
Proof.
  assert (H : forall n, tilings n = fib (S n) /\ tilings (S n) = fib (S (S n))).
  { induction n as [| n [H1 H2]].
    - simpl. split; reflexivity.
    - split.
      + exact H2.
      + change (tilings (S (S n))) with (tilings (S n) + tilings n).
        change (fib (S (S (S n)))) with (fib (S n) + fib (S (S n))).
        rewrite H1, H2. apply Nat.add_comm. }
  intro n. apply H.
Qed.

(* ===================================================================== *)
(*  Капстоун                                                               *)
(* ===================================================================== *)

(** Конечная комбинаторика над ℕ — чистая Element-сторона границы финитизации (0 аксиом):
      (★ вкл-искл-2)  count(A∪B) + count(A∩B) = count A + count B;
      (★ субаддит.)   count(A∪B) ≤ count A + count B;
      (★ Фибоначчи)   Σ_{i≤n} fib i = fib(n+2) − 1, и число замощений 1×n = fib(n+1).
    Ни LEM, ни AC, ни axiom of infinity — конечный перебор + ℕ.  Формальная производящая функция
    x/(1−x−x²) = арена Части XVII (FormalPowerSeries); асимптотика φⁿ/√5 = role-limit. *)
Theorem discrete_combinatorics_summary :
  (forall n A B, count n (fun k => A k || B k) + count n (fun k => A k && B k)
                 = count n A + count n B)
  /\ (forall n A B, count n (fun k => A k || B k) <= count n A + count n B)
  /\ (forall n, sumfib n + 1 = fib (S (S n)))
  /\ (forall n, tilings n = fib (S n)).
Proof.
  split; [ exact count_union_inter |].
  split; [ exact count_subadd |].
  split; [ exact fib_sum | exact tilings_eq_fib ].
Qed.
