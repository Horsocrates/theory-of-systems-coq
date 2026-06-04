(** * FinitizationVerdict.v — the capstone of the physics reckoning: ONE verdict theorem.
      Bundles the three pillars — FinitizationNoCutoff (CHSH/Tsirelson), GranularFloor (the
      general role-limit floor = the surd theorem), QubitCeiling (Palmer) — and FinitistQM's
      two sides into a single dichotomy: a GRANULAR theory (bounded resolution q ≤ Q) is stuck
      with a UNIFORM gap ≥ 1/Q² (a falsifiable deviation), while ToS (unbounded process) BEATS any
      granular bound (gap < 1/Q² for some config) — so ToS predicts NO deviation from continuum QM
      and is empirically QM, while the granular programs (Palmer/Carroll/'t Hooft) are falsifiable.
      The separator is the surd theorem (GeneralSqrt): floor positivity = √D irrational.  The
      honest verdict: ToS makes the SAME predictions as QM (no new physics) but its ontology
      (process, not substrate) is distinct from — and machine-separated from — the granular
      finitizers.  P4 (finite actuality) ≠ a finite substrate.

    Elements: the uniform Q-deviation bound; the ToS Pell configuration that beats any Q; the
              qubit ceiling (L1 + P4)
    Roles:    Element side = each finite-actual configuration (rational, gap ≥ floor); role-limit =
              √D (an unbounded process).  Granular = bounded resolution (a falsifiable deviation);
              ToS = unbounded process (no deviation, empirically QM)
    Rules:    granular(Q) ⟹ every config has gap ≥ 1/Q² (uniform); ToS (unbounded q) ⟹ for any Q a
              config with gap < 1/Q²; the separator is √D-irrationality (floor ≥ 1)

    THE DEEP POINT — the verdict, machine-checked.  A granular theory restricted to resolution
    q ≤ Q has EVERY configuration's gap ≥ 1/Q² (`granular_deviation`: q² ≤ Q²·|q²D − p²|, since the
    floor |q²D − p²| ≥ 1 and q ≤ Q) — a fixed, falsifiable deviation.  ToS (the Pell tower, with q
    unbounded reaching the floor exactly) BEATS any such bound: for every Q there is a configuration
    with q > Q and |q²·2 − p²| = 1, i.e. gap 1/q² < 1/Q² (`tos_beats_granular`).  So ToS predicts no
    deviation (it gets arbitrarily below any granular floor), while a granular theory cannot — they
    are empirically distinguishable, and ToS is the one indistinguishable from continuum QM.  The
    separator is the surd theorem: the floor is positive exactly because √D is irrational
    (GeneralSqrt).  Element = a finite-actual config; role-limit = the unbounded process that beats
    every bound.  The verdict: ToS-finitization = empirically QM, formally separated from the
    granular finitizers; P4 ≠ a finite substrate.

    ============ E/R/R разбор ============
      Rules (L5): гранулярная(Q) ⟹ равномерный зазор ≥1/Q² (q≤Q ∧ пол≥1); ToS (q неогр.) ⟹ ∀Q ∃
                  конфигурация с зазором <1/Q²; разделитель = √D-иррациональность (пол≥1).
      Roles (L4): Element = конечно-актуальная конфигурация; role-limit = √D (неограниченный процесс).
                  Гранулярная = ограниченное разрешение (отклонение); ToS = процесс (нет отклонения, =КМ).
      Elements  : равномерная Q-граница; ToS Пелль-конфигурация, бьющая Q; потолок кубитов (L1+P4).
    ДИАГНОСТИКА (P4): ВЕРДИКТ — ToS НЕ предсказывает отклонения (бьёт любой гранулярный предел), формально
    отделена от гранулярных теорий (предсказывающих ≥1/Q², фальсифицируемо). Разделитель = сурд-теорема. ToS =
    эмпирически КМ, с Гизином, против гранулярных. P4 = конечная актуальность ≠ конечный субстрат. Вклад — точная
    демаркация, не предсказание новой физики.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import stdlib.GeneralSqrt.
From ToS Require Import stdlib.GranularFloor.
From ToS Require Import stdlib.FinitizationNoCutoff.
From ToS Require Import stdlib.QubitCeiling.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Granular theories predict a uniform, falsifiable deviation ≥ 1/Q²       *)
(* ===================================================================== *)

(** ★ A granular theory restricted to resolution q ≤ Q has EVERY configuration's gap to the
    role-limit √D bounded below by 1/Q²: at integer scale, q² ≤ Q²·|q²D − p²| (since the floor
    |q²D − p²| ≥ 1 by GeneralSqrt and q ≤ Q).  So the gap |D − (p/q)²| ≥ 1/Q² > 0 — a fixed,
    falsifiable deviation that no q ≤ Q can beat. *)
Theorem granular_deviation : forall D p q Q : Z,
  (forall m : Z, m * m <> D) -> 0 < q -> q <= Q ->
  q * q <= Q * Q * Z.abs (q * q * D - p * p).
Proof.
  intros D p q Q Hns Hq HqQ.
  pose proof (granular_floor D p q Hns Hq) as Hfloor.
  assert (0 <= Q * Q) by nia.
  nia.
Qed.

(* ===================================================================== *)
(*  ToS (unbounded process) beats any granular bound                       *)
(* ===================================================================== *)

(** ★ ToS imposes no bound: for any granular resolution Q there is a (Pell) configuration with
    q > Q that reaches the floor exactly, |q²·2 − p²| = 1 — gap 1/q² < 1/Q².  ToS gets arbitrarily
    below any granular deviation, so it predicts no deviation from continuum QM (here for √2 /
    Tsirelson; the same holds for every √D by GranularFloor). *)
Theorem tos_beats_granular : forall Q : Z,
  exists p q : Z, 0 < q /\ Q < q /\ Z.abs (q * q * 2 - p * p) = 1.
Proof.
  intros Q.
  set (k := Z.to_nat (Z.max 0 Q)).
  exists (pp k), (qq k).
  pose proof (qq_pos k) as Hpos.
  pose proof (q_unbounded k) as Hub.
  pose proof (pell_inv k) as Hinv.
  assert (Hid : Z.of_nat k = Z.max 0 Q).
  { unfold k. rewrite Z2Nat.id by lia. reflexivity. }
  rewrite Hid in Hub.
  split; [ lia | split ].
  - lia.
  - assert (Hgap : qq k * qq k * 2 - pp k * pp k = 1) by lia.
    rewrite Hgap. reflexivity.
Qed.

(* ===================================================================== *)
(*  THE VERDICT                                                           *)
(* ===================================================================== *)

(** ★★ The finitization verdict, machine-checked:
      (a) GRANULAR THEORIES ARE FALSIFIABLE — bounded resolution q ≤ Q forces a uniform gap
          ≥ 1/Q² for every role-limit √D (`granular_deviation`);
      (b) ToS PREDICTS NO DEVIATION — the unbounded process beats any granular bound
          (`tos_beats_granular`: a config with q > Q and gap 1/q² < 1/Q²), and the qubit
          denominator is unbounded (`qubit_ceiling`), so ToS imposes no ceiling;
      (c) THE TARGET IS A ROLE-LIMIT — the Tsirelson/√2 optimum is genuinely irrational
          (`tsirelson_role_limit`), the unbounded process the rationals approach.
    So ToS-finitization is empirically QM and formally separated from the granular finitizers;
    the separator is the surd theorem.  P4 (finite actuality) ≠ a finite substrate. *)
Theorem finitization_verdict :
  (forall D p q Q : Z, (forall m : Z, m * m <> D) -> 0 < q -> q <= Q ->
     q * q <= Q * Q * Z.abs (q * q * D - p * p))
  /\ (forall Q : Z, exists p q : Z, 0 < q /\ Q < q /\ Z.abs (q * q * 2 - p * p) = 1)
  /\ (forall Q : Z, exists m : nat, Q < pow2 m)
  /\ (~ (exists s : Q, (s * s == 8)%Q)).
Proof.
  split; [ exact granular_deviation | ].
  split; [ exact tos_beats_granular | ].
  split; [ exact qubit_ceiling | exact tsirelson_role_limit ].
Qed.
