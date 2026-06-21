(** * ExpectationProcess.v — математическое ожидание E[·] над ℚ как ПРОЦЕСС: дискретное
      (категориальное) E = точная ℚ (Element); континуальное E=∫ = role-limit
      (закрывает горизонт C отчёта docs/AI-ProcessMath-vs-Infinity.md).

    Каталог AI #9,10,15,30: ожидания E[·]=∫·dμ (диффузия, VAE, score-matching) — завершённый
    интеграл Лебега по ℝ^n; на практике оцениваются Монте-Карло (1/N)Σ.  ToS: ожидание — процесс.
    Дискретное (категориальное) ожидание E[f]=Σ p_i f_i над рациональными p_i,f_i — ТОЧНОЕ
    рациональное (Element; это и есть то, что ИИ реально считает над softmax-выходом).  Континуальное
    E=∫ — role-limit: конечно-сеточная риманова сумма точна (Element), но строго промахивается мимо
    завершённого интеграла; разрешение (число точек) неограниченно (нет завершённого интеграла = ¬P4).
    Монте-Карло частичная средняя = Element-стадия процесса-ожидания.

    ============ E/R/R разбор ============
      Rules (L5): E[f]=Σ p_i f_i (дискретно) / ∫f dμ (континуально); интеграл = предел частичных сумм.
      Roles (L4): E — роль-величина; дискретное (категориальное) E = точная ℚ (Element);
        континуальное E=∫ = role-limit.
      Elements (L1+P4): p_i,f_i∈ℚ; конечная сумма Eexp; Монте-Карло частичная сумма; Риман-сетка — точны.
    ДИАГНОСТИКА (P4): завершённый интеграл реифицирует role-limit.  Дискретное E точно (Element,
      Eexp_concrete=7/4; линейность); континуальный ∫₀¹x=½ = role-limit (Риман-сумма строго > ½,
      riemann_exceeds_integral; разрешение неограниченно, grid_unbounded, ¬P4).  Монте-Карло = Element-стадии.
    ЧЕСТНАЯ СТЕНА: общий континуальный E как актуальный Cauchy-процесс — надстройка
      (RiemannIntegration/CauchyReal); здесь самодостаточная дискретная Element-сторона + Риман-role-limit
      пример (∫₀¹x=½) в стиле DyadicBits/WidthProcessKernel.  ВСЕ ожидания генеративного ИИ
      оцениваются Монте-Карло (#30) = Element-стадии.  Самодостаточно (Stdlib), 0 аксиом.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  Дискретное (категориальное) ожидание E[f] = Σ p_i·f_i (Element)    *)
(* ================================================================= *)

Fixpoint Qsum (l : list Q) : Q :=
  match l with [] => 0 | x :: r => x + Qsum r end.

(** Распределение задаём списком пар (вероятность, значение). *)
Fixpoint Eexp (d : list (Q * Q)) : Q :=
  match d with [] => 0 | (p, v) :: r => p * v + Eexp r end.

(** ELEMENT: ожидание рациональных данных над рациональным распределением — ТОЧНОЕ рациональное.
    E над (½,¼,¼) значений (1,2,3) = ½·1 + ¼·2 + ¼·3 = 7/4. *)
Lemma Eexp_concrete : Eexp [(1#2, 1); (1#4, 2); (1#4, 3)] == 7 # 4.
Proof. vm_compute; reflexivity. Qed.

(** Линейность по значениям: E[c·f] = c·E[f]. *)
Lemma Eexp_scale : forall (c : Q) (d : list (Q * Q)),
  Eexp (map (fun pv => (fst pv, c * snd pv)) d) == c * Eexp d.
Proof.
  intros c d. induction d as [| [p v] r IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Ожидание константы: E[c] = c·Σp (=c при нормировке Σp=1). *)
Lemma Eexp_const : forall (c : Q) (ps : list Q),
  Eexp (map (fun p => (p, c)) ps) == c * Qsum ps.
Proof.
  intros c ps. induction ps as [| p r IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Монте-Карло частичная сумма — точная ℚ на каждой выборке (Element-стадия). *)
Lemma mc_stage_exact : Qsum [3#10; 7#10; 1#2] == 3 # 2.
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  Континуальное ожидание / интеграл = role-limit                    *)
(*  Пример: ∫₀¹ x dx = ½; правая риманова сумма R_n = tri n / n²        *)
(* ================================================================= *)

(** Треугольное число tri n = Σ_{i=1}^{n} i. *)
Fixpoint tri (n : nat) : nat :=
  match n with O => O | S m => S m + tri m end.

Lemma tri_closed : forall n, (2 * tri n = n * (n + 1))%nat.
Proof. induction n as [| m IH]; simpl; nia. Qed.

(** Риманова сумма (правая) функции f(x)=x на [0,1] при n подынтервалах: R_n = tri n / n². *)
Definition rsum (n : nat) : Q :=
  inject_Z (Z.of_nat (tri n)) / inject_Z (Z.of_nat (n * n)).

(** ELEMENT: конечно-сеточная риманова сумма — ТОЧНАЯ ℚ.  R_2 = tri 2 / 4 = 3/4. *)
Lemma rsum_2 : rsum 2 == 3 # 4.
Proof. vm_compute; reflexivity. Qed.

(** ROLE-LIMIT: при любой конечной сетке n≥1 риманова сумма СТРОГО превышает интеграл ½
    (кросс-умножено: n² < 2·tri n), т.е. ∫=½ НИКОГДА не достигается на конечной сетке. *)
Lemma riemann_exceeds_integral : forall n, (1 <= n)%nat -> (n * n < 2 * tri n)%nat.
Proof. intros n Hn. assert (H := tri_closed n). nia. Qed.

(** Разрешение (число точек сетки) растёт за любой предел — нет завершённого интеграла (¬P4). *)
Lemma grid_unbounded : forall B : nat, exists n : nat, (B < n)%nat.
Proof. intro B. exists (S B). lia. Qed.

(* ================================================================= *)
(*  CAPSTONE                                                          *)
(* ================================================================= *)

(** ★★★ ОЖИДАНИЕ E[·] НАД ℚ — ГРАНИЦА Element ↔ role-limit:
      (Element)    дискретное (категориальное) E = ТОЧНАЯ ℚ (Eexp=7/4), линейно — это и есть
                   ожидание, которое ИИ реально считает над softmax/категориальным выходом;
      (role-limit) континуальный интеграл ½ строго превышается каждой конечной римановой суммой
                   (n²<2·tri n) — не достигается на конечной сетке; разрешение неограниченно (¬P4).
    Завершённый интеграл реифицирует role-limit; Монте-Карло частичные средние = Element-стадии. *)
Theorem expectation_boundary :
  (Eexp [(1#2, 1); (1#4, 2); (1#4, 3)] == 7 # 4)
  /\ (forall c d, Eexp (map (fun pv => (fst pv, c * snd pv)) d) == c * Eexp d)
  /\ (forall n, (1 <= n)%nat -> (n * n < 2 * tri n)%nat)
  /\ (forall B : nat, exists n : nat, (B < n)%nat).
Proof.
  split; [ exact Eexp_concrete
         | split; [ exact Eexp_scale
                  | split; [ exact riemann_exceeds_integral | exact grid_unbounded ] ] ].
Qed.

Print Assumptions expectation_boundary.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Ожидание над ℚ: дискретное (категориальное) E=Σp_i·f_i = ТОЧНАЯ ℚ          *)
(*  (Element, Eexp_concrete=7/4, Eexp_scale/const линейность; Монте-Карло      *)
(*  частичная сумма mc_stage_exact); континуальный ∫₀¹x=½ = role-limit         *)
(*  (риманова сумма rsum строго > ½: riemann_exceeds_integral n²<2·tri n;      *)
(*  разрешение неограниченно grid_unbounded, ¬P4).  Капстоун                   *)
(*  expectation_boundary.  Закрывает горизонт C отчёта AI-ProcessMath.         *)
(* ========================================================================= *)
