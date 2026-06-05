(** * MinimalLengthIsUnit.v — the true floor of Q2: WHY the minimal length is posited.  Not because ToS is
      too weak to derive it (a gap), but because it is a UNIT — the count<->length dictionary — and units
      are by category never derived (you cannot derive "1 meter").  This REFINES Q2's tag
      ScaleValue = Posited from "a ToS gap" to "a category necessity", and unifies the minimal quantities
      (length, time, action) into ONE posit (the granularity) related by DERIVED conversion ratios.

    -- The dictionary --
      A length = a COUNT times the granularity g (the minimal length): length_of_count g n = g * n.  The
      count n is Element (derivable); the continuum length is role-limit; g is the DICTIONARY converting
      the one to the other (H1's count = Element / length = role-limit boundary, made into a unit).

    -- Dimensionless physics is unit-free (DERIVED) --
      The ratio of two lengths equals the ratio of their counts — g CANCELS.  All physics (dimensionless
      ratios) lives in the counts (Element); g is just the unit.  Rescaling g (a different unit) leaves
      every dimensionless ratio invariant — so g is a GAUGE of length, a convention.

    -- One posit, not many --
      Minimal length, minimal time, ... are ONE posit (the granularity g) times FIXED conversion constants
      (c, hbar — themselves unit-conversions); the ratios between them are DERIVED, not independent posits.
      min_length = c * min_time, with c a fixed (derived) ratio for any g.

    -- The honest upgrade --
      "ScaleValue = Posited" is not a ToS weakness: g is the count<->length unit, and units are conventions
      that no theory derives.  Everything dimensionless (ratios, the energy-scaling of Q2) IS derived; ONE
      convention (anchor) fixes the dictionary, after which all dimensionless physics is determined.  So the
      single posit is a UNIT, a category necessity — the strongest honest reading.

    -- HONEST scope --
      A conceptual/structural formalization (the dictionary model is a modelling choice).  It explains WHY
      the scale is posited (it is a unit) and shows the dimensionless content is unit-invariant; it does NOT
      derive a dimensionful value (impossible by category — units are conventions).

    Elements: length_of_count g n = g*n; ratios g-free; min_length = c*min_time; different g => different length
    Roles:    count = Element physics; g = unit/dictionary; ratios = derived (g-free); minimal quantities = one posit
    Rules:    a length = count * unit; dimensionless = g-invariant (derived); g = convention (a unit, not a gap)

    ============ E/R/R разбор ============
      Rules (L5): длина = счёт * g; g -- конвертер Element-счёта в role-limit-длину; безразмерное (отношения)
                  g-инвариантно (выведено); g -- калибровка (постулируется как единица, не как факт).
      Roles (L4): счёт = Element-физика; g = единица/словарь (мост); отношения длин = выведенное (g-свободно);
                  min-{длина,время,действие} = один постулат g + выведенные конверсии.
      Elements  : length_of_count g n := g*n; отношение g-свободно; min_length = c*min_time; разные g.
    ДИАГНОСТИКА (P4): Q2-"Posited" уточняется: g -- ЕДИНИЦА, постулируемая по категории (как метр), не дыра
    ToS.  Всё безразмерное выведено и g-инвариантно; постулируется одна конвенция (выбор единицы/якоря).
    Это УСИЛИВАЕТ честный вердикт.  Смычка: posit-reduction (один названный пол) + H1 (счёт=Element /
    длина=role-limit / g=словарь).  ЧЕСТНО: концептуальная формализация; значение не выводимо по категории.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The count <-> length dictionary                                        *)
(* ===================================================================== *)

(** A length = a COUNT n times the granularity unit g (the minimal length).  g converts the Element count
    to the role-limit continuum length — it is the dictionary, not a derived value. *)
Definition length_of_count (g n : Q) : Q := g * n.

(* ===================================================================== *)
(*  Dimensionless physics is unit-free (DERIVED)                           *)
(* ===================================================================== *)

(** ★ The ratio of two lengths equals the ratio of their counts — g CANCELS.  All dimensionless physics
    lives in the counts (Element); the unit g drops out. *)
Lemma length_ratio_unit_free : forall g m n,
  length_of_count g m * n == length_of_count g n * m.
Proof. intros g m n. unfold length_of_count. ring. Qed.

(** ★ Rescaling the unit (g1 -> g2) leaves every dimensionless ratio invariant — g is a GAUGE of length,
    a convention. *)
Lemma ratio_g_invariant : forall g1 g2 m n,
  length_of_count g1 m * length_of_count g2 n == length_of_count g1 n * length_of_count g2 m.
Proof. intros g1 g2 m n. unfold length_of_count. ring. Qed.

(** Concrete: the count ratio 3:6 is unit-free (g = 7 cancels). *)
Lemma ex_ratio : length_of_count 7 3 * 6 == length_of_count 7 6 * 3.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  One posit, not many                                                    *)
(* ===================================================================== *)

(** Minimal time and minimal length are ONE posit (the granularity g) times a FIXED conversion c. *)
Definition min_time (g : Q) : Q := g.
Definition min_length (c g : Q) : Q := c * g.

(** ★ The ratio min_length / min_time = c is FIXED (derived) for any granularity g — the minimal
    quantities are not independent posits; their ratios are derived conversions. *)
Lemma length_time_ratio_fixed : forall c g, min_length c g == c * min_time g.
Proof. intros c g. unfold min_length, min_time. ring. Qed.

(* ===================================================================== *)
(*  The value is a convention (a unit)                                     *)
(* ===================================================================== *)

(** ★ Different granularities give different absolute lengths — g is a UNIT (a convention), and units are
    by category never derived (you cannot derive "1 meter").  This is why the scale is posited. *)
Lemma value_is_convention : forall n, 0 < n -> ~ (length_of_count 1 n == length_of_count 2 n).
Proof. intros n Hn H. unfold length_of_count in H. lra. Qed.

(* ===================================================================== *)
(*  Capstone: the minimal length is a unit (the count<->length dictionary) *)
(* ===================================================================== *)

(** Q2's deeper floor — the minimal length is a UNIT:
      (ratios)     dimensionless content (length ratios) is g-invariant = the count ratios (Element);
      (rescale)    rescaling the unit leaves every ratio invariant — g is a gauge of length;
      (one posit)  minimal length = c * minimal time — one posit (g) with derived conversion ratios;
      (convention) different g give different lengths — g is a unit, a convention, never derived.
    So "the minimal length is posited" is a CATEGORY necessity (g is the count<->length unit), not a ToS
    gap: all dimensionless physics is derived and unit-free; one convention (anchor) fixes the dictionary.
    The strongest honest reading of Q2's posited scale. *)
Theorem minimal_length_is_unit :
  (forall g m n, length_of_count g m * n == length_of_count g n * m)
  /\ (forall g1 g2 m n, length_of_count g1 m * length_of_count g2 n
                     == length_of_count g1 n * length_of_count g2 m)
  /\ (forall c g, min_length c g == c * min_time g)
  /\ (forall n, 0 < n -> ~ (length_of_count 1 n == length_of_count 2 n)).
Proof.
  split; [ exact length_ratio_unit_free | ].
  split; [ exact ratio_g_invariant | ].
  split; [ exact length_time_ratio_fixed | exact value_is_convention ].
Qed.
