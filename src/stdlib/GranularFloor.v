(** * GranularFloor.v — the general physics no-go: role-limit ⟹ a granular floor 1/q², and the
      whole verdict REDUCES to the surd theorem (GeneralSqrt).  Generalizes FinitizationNoCutoff.v
      (which was D=8 / Tsirelson) to EVERY role-limit √D.  For a non-square D, the gap between a
      rational configuration (p/q)² and D, at integer scale, is |q²D − p²| ≥ 1 — a NONZERO-integer
      floor (because q²D = p² would make D a perfect square, contradicting GeneralSqrt).  Hence a
      granular theory (bounded resolution q ≤ Q) predicts a fixed gap ≥ 1/Q² > 0 (falsifiable),
      while ToS (q unbounded, Pell reaching the floor exactly) predicts the gap → 0 (no deviation).
      The physics is number theory: the deviation-or-not verdict is the √D-irrationality theorem.

    Elements: the integer gap |q²D − p²|; the concrete D=2 floors (=1 at (7,5), (41,29)); the
              perfect-square contrast D=4 (gap 0 achievable) (L1 + P4)
    Roles:    Element side = each rational config has gap ≥ 1/q² > 0 (never exactly the role-limit);
              role-limit = √D, gap 0 only at the unreachable exact point.  Granular (q≤Q) ⟹ gap
              ≥ 1/Q² (deviation); ToS (q unbounded) ⟹ gap → 0 (no deviation)
    Rules:    D non-square ⟹ q²D ≠ p² (GeneralSqrt) ⟹ |q²D − p²| ≥ 1 ⟹ gap ≥ 1/q²; Pell reaches
              the floor exactly (=1) with q unbounded ⟹ floor → 0

    THE DEEP POINT — the physics no-go IS the surd theorem.  For a role-limit √D (D non-square),
    no rational configuration hits it exactly: q²D ≠ p² (`nonsquare_gap_nonzero`, via GeneralSqrt's
    `not_perfect_square_irrational` — q²D = p² would make (p/q)² = D a perfect square).  A nonzero
    integer has absolute value ≥ 1, so the gap floor is |q²D − p²| ≥ 1 (`granular_floor`), i.e.
    |D − (p/q)²| ≥ 1/q².  A GRANULAR theory frozen at resolution Q therefore predicts a fixed
    positive gap ≥ 1/Q² — a falsifiable deviation.  But the floor is TIGHT and VANISHING: Pell
    reaches |q²D − p²| = 1 with q unbounded (`floor_achieved_75`, `floor_achieved_4129` for D=2),
    so ToS's gap 1/q² → 0 — no deviation.  The perfect-square case is the contrast: D=4 admits
    q²D = p² exactly (`perfect_square_gap_zero`, q=1,p=2), so its root IS an Element and the floor
    is 0.  Thus "does finitization predict a deviation?" reduces to "is √D a role-limit?" =
    "is D a non-square?" — the verdict is number theory.  Element = a rational config (gap ≥ 1/q²);
    role-limit = √D, reached only by an unbounded process.

    ============ E/R/R разбор ============
      Rules (L5): D не квадрат ⟹ q²D≠p² (GeneralSqrt) ⟹ |q²D−p²|≥1 ⟹ зазор≥1/q²; Пелль достигает
                  пол точно (=1) при q неограниченном ⟹ пол→0.
      Roles (L4): Element = рациональная конфигурация (зазор≥1/q²>0); role-limit = √D (зазор 0 только в
                  недостижимой точке). Гранулярная (q≤Q) ⟹ зазор≥1/Q² (отклонение); ToS (q неогр.) ⟹ →0.
      Elements  : целочисленный зазор |q²D−p²|; полы D=2 (=1 при (7,5),(41,29)); контраст D=4 (зазор 0).
    ДИАГНОСТИКА (P4): физический no-go = ТЕОРЕМА О СУРДАХ. Положительность пола (≥1) = ровно GeneralSqrt
    (√D∉ℚ ⟺ D не квадрат ⟺ q²D≠p²). «Предсказывает ли финитизация отклонение?» = «√D role-limit?» = «D не
    квадрат?» — вердикт есть число. Обобщает FinitizationNoCutoff (D=8) на каждый √D; физика = теория чисел.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import stdlib.GeneralSqrt.

Open Scope Z_scope.

(* ===================================================================== *)
(*  A nonzero integer has absolute value ≥ 1 — the floor mechanism         *)
(* ===================================================================== *)

Lemma nonzero_abs_ge_1 : forall n : Z, n <> 0 -> 1 <= Z.abs n.
Proof.
  intros n H. destruct (Z.abs_spec n) as [[? Habs] | [? Habs]]; lia.
Qed.

(* ===================================================================== *)
(*  A role-limit is never hit exactly: q²D ≠ p² (reduces to GeneralSqrt)    *)
(* ===================================================================== *)

(** Helper: the rational (p/q)² equals D when q²D = p². *)
Lemma ratio_square : forall p q D : Z, 0 < q -> p * p = D * (q * q) ->
  ((inject_Z p / inject_Z q) * (inject_Z p / inject_Z q) == inject_Z D)%Q.
Proof.
  intros p q D Hq Hpp.
  assert (Hq0 : ~ inject_Z q == 0).
  { intro Hc. unfold Qeq, inject_Z in Hc. simpl in Hc. lia. }
  assert (Hbridge : (inject_Z p * inject_Z p == inject_Z D * (inject_Z q * inject_Z q))%Q).
  { rewrite <- !inject_Z_mult. rewrite Hpp. reflexivity. }
  assert (Hstep : ((inject_Z p / inject_Z q) * (inject_Z p / inject_Z q)
                  == inject_Z p * inject_Z p / (inject_Z q * inject_Z q))%Q) by (field; exact Hq0).
  rewrite Hstep, Hbridge. field. exact Hq0.
Qed.

(** ★ For a non-square D, NO rational configuration hits the role-limit exactly: q²D ≠ p².
    This is exactly GeneralSqrt: q²D = p² would make (p/q)² = D a perfect square. *)
Lemma nonsquare_gap_nonzero : forall D p q : Z,
  (forall m : Z, m * m <> D) -> 0 < q -> q * q * D - p * p <> 0.
Proof.
  intros D p q Hns Hq Heq.
  apply (not_perfect_square_irrational D Hns).
  exists (inject_Z p / inject_Z q)%Q.
  apply ratio_square; [ exact Hq | lia ].
Qed.

(* ===================================================================== *)
(*  THE GENERAL GRANULAR FLOOR                                            *)
(* ===================================================================== *)

(** ★ The general no-go: for a role-limit √D (D non-square) and any rational configuration p/q
    (q > 0), the gap to the role-limit, at integer scale, is at least 1: |q²D − p²| ≥ 1.  Hence
    |D − (p/q)²| ≥ 1/q².  A granular theory with bounded resolution q ≤ Q predicts a fixed
    deviation ≥ 1/Q² > 0 — falsifiable; ToS (q unbounded) drives it to 0. *)
Theorem granular_floor : forall D p q : Z,
  (forall m : Z, m * m <> D) -> 0 < q -> 1 <= Z.abs (q * q * D - p * p).
Proof.
  intros D p q Hns Hq. apply nonzero_abs_ge_1. apply nonsquare_gap_nonzero; assumption.
Qed.

(* ===================================================================== *)
(*  The floor is TIGHT and VANISHING for D=2 (Pell reaches 1, q unbounded) *)
(* ===================================================================== *)

(** Pell reaches the floor exactly: |q²·2 − p²| = 1 at (p,q) = (7,5) and (41,29).  The
    resolution q grows (5, 29, …), so the gap 1/q² (= 1/25, 1/841, …) → 0: ToS imposes no cutoff
    and predicts no deviation, while a theory frozen at q=5 caps the gap at 1/25 (falsifiable). *)
Lemma floor_achieved_75 : Z.abs (5 * 5 * 2 - 7 * 7) = 1.
Proof. reflexivity. Qed.

Lemma floor_achieved_4129 : Z.abs (29 * 29 * 2 - 41 * 41) = 1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Contrast: a perfect square has gap 0 (its root is an Element)          *)
(* ===================================================================== *)

(** D = 4 is a perfect square: q²·4 = p² exactly at q=1, p=2 — gap 0.  So √4 = 2 is an Element
    and there is NO floor; the granular floor is specific to role-limits (non-squares). *)
Lemma perfect_square_gap_zero : 1 * 1 * 4 - 2 * 2 = 0.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The general physics no-go, reduced to the surd theorem:
      (a) GRANULAR FLOOR — for any role-limit √D (D non-square), every rational configuration has
          gap |q²D − p²| ≥ 1, i.e. ≥ 1/q² (`granular_floor`): a granular (bounded-q) theory predicts
          a falsifiable deviation; this is exactly GeneralSqrt (`nonsquare_gap_nonzero`);
      (b) TIGHT & VANISHING — Pell reaches the floor (=1) with q unbounded (`floor_achieved_75`,
          `floor_achieved_4129`): ToS's gap → 0, no deviation;
      (c) CONTRAST — a perfect square has gap 0 (`perfect_square_gap_zero`): the floor is specific
          to role-limits.  So the deviation-or-not verdict reduces to "is D a non-square?". *)
Theorem granular_floor_synthesis :
  (forall D p q : Z, (forall m : Z, m * m <> D) -> 0 < q -> 1 <= Z.abs (q * q * D - p * p))
  /\ Z.abs (5 * 5 * 2 - 7 * 7) = 1
  /\ Z.abs (29 * 29 * 2 - 41 * 41) = 1
  /\ 1 * 1 * 4 - 2 * 2 = 0.
Proof.
  split; [ exact granular_floor | ].
  split; [ exact floor_achieved_75 | ].
  split; [ exact floor_achieved_4129 | exact perfect_square_gap_zero ].
Qed.
