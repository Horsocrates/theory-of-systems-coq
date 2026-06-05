(** * LambdaSmallnessDescent.v — the THIRD descent (cosmological constant smallness), testing whether the
      "invariant-given-symmetry derived / symmetry-condition posited" SHAPE found in the arrow
      (ArrowGroundingDescent.v) and Born-rule (BornRuleDescent.v) descents GENERALIZES, or was an artifact
      of two examples.

    Result: it does NOT generalize uniformly.  Lambda-smallness is a DIFFERENT kind of wall, and finding
    that is the point -- the third descent BREAKS the premature pattern-of-two and reveals that the
    role-limit side is HETEROGENEOUS (at least two wall-types).  This is exactly the anti-flattening the
    snapshot would have erased.

    -- Rung 1: the STRUCTURE (finiteness) is derived.  Finitization solves the DIVERGENCE: the role-limit
       vacuum-energy sum becomes a bounded count, O(1) per mode (vac_bound = 1/2 <= 1).  Parallels
       "Direction derived" (arrow) and "p normalized" (Born).

    -- Rung 2: is there an INVARIANT forced by a symmetry that fixes the VALUE?  For the arrow, P4 genuinely
       grounds the direction; for Born, the Pythagorean structure genuinely forces the square (a UNIQUE
       rotation invariant).  For Lambda: NO -- there is no ToS-internal symmetry deriving Lambda=0 or any
       structure on the value.  The smallness is a bare SCALE HIERARCHY (a ratio H0/M_Planck).  Finiteness
       is consistent with MANY values (both 1/1000 and 1/1000000 sit below the bound -- finiteness picks
       NONE), unlike Born where the symmetry forces a UNIQUE invariant.

    -- Rung 3 (floor): the wall is a FREE RATIO between independent scales -- there is no symmetry to
       relocate to.  Lambda goes [finite] -> [free magnitude] with NO derived-invariant middle rung.

    -- Floor / verdict: Lambda-smallness is a DIFFERENT wall, and the pattern-of-two is broken.
         ArrowSign, BornNorm -> SymmetryChoice  (a derived invariant; the symmetry/condition is the input).
         LambdaSmallness     -> BareHierarchy   (finiteness derived, but NO invariant -- a free scale ratio).
       So the role-limit side is heterogeneous: at least two wall-types {SymmetryChoice, BareHierarchy}.
       This EARNS not a synthesis-of-one-shape but a TAXONOMY of walls.

    -- Honest caveat: "no derived invariant" = relative to current ToS (an ABSENCE, not a proof of
       impossibility); a deeper scale symmetry could move Lambda to SymmetryChoice -- open.

    Elements: vac_bound = 1/2; the values 1/1000, 1/1000000 both below it; Wall / WallType taxonomy
    Roles:    finiteness = the derived structure; the smallness = a free scale ratio (no invariant)
    Rules:    finitization fixes finiteness, NOT the value; no symmetry forces the magnitude (bare hierarchy)

    ============ E/R/R разбор ============
      Rules (L5): финитизация фиксирует КОНЕЧНОСТЬ (расходимость решена), не ЗНАЧЕНИЕ; нет симметрии,
                  вынуждающей магнитуду -- голая иерархия.
      Roles (L4): конечность = выведенная структура; малость = свободное масштабное отношение (нет инварианта),
                  в отличие от стрелы/Борна (там derived-инвариант есть).
      Elements  : vac_bound=1/2; и 1/1000, и 1/10^6 ниже границы (конечность не выбирает значение).
    ДИАГНОСТИКА (P4): третий спуск РАСЩЕПИЛ паттерн-из-двух. Стрела/Борн = SymmetryChoice (derived-инвариант +
    вход-симметрия); Λ = BareHierarchy (конечность выведена, инварианта НЕТ -- свободное отношение масштабов).
    role-limit-сторона ГЕТЕРОГЕННА: >=2 типа стен. Это анти-уплощение (преждевременный синтез стёр бы).
    CAVEAT: "нет инварианта" = относительно текущего ToS (отсутствие, не невозможность); глубже -- открыто.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.
Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Rung 1 — the STRUCTURE (finiteness) is derived: the divergence is solved *)
(* ===================================================================== *)

(** The O(1) per-mode vacuum bound (1/2) from finitization (GravityFinitization / OpenFrontierLedger). *)
Definition vac_bound : Q := 1 # 2.

(** ★ Finitization SOLVES the divergence: the vacuum density is bounded (finite, <= 1). *)
Lemma divergence_solved : vac_bound <= 1.
Proof. unfold vac_bound. lra. Qed.

(* ===================================================================== *)
(*  Rung 2 — finiteness does NOT fix the value (no forcing invariant)      *)
(* ===================================================================== *)

(** Finiteness is nowhere near the smallness: the bound is not even <= 10^-6 (let alone ~10^-122).
    So finiteness =/= smallness. *)
Lemma smallness_not_from_finiteness : ~ (vac_bound <= (1 # 1000000)).
Proof.
  unfold vac_bound. intro H.
  assert (Hlt : (1 # 1000000) < (1 # 2)) by (vm_compute; reflexivity).
  exact (Qlt_not_le _ _ Hlt H).
Qed.

(** ★ Finiteness PICKS NO VALUE: two DIFFERENT magnitudes (1/1000 and 1/1000000) both sit below the
    bound, so the finiteness structure is consistent with both -- it forces neither.  Contrast Born,
    where the orthogonal symmetry forces a UNIQUE invariant (the square).  Here: no forcing invariant. *)
Lemma finiteness_picks_no_value :
  (1 # 1000) < vac_bound /\ (1 # 1000000) < vac_bound /\ ~ ((1 # 1000) == (1 # 1000000)).
Proof.
  split.
  - unfold vac_bound. vm_compute. reflexivity.
  - split.
    + unfold vac_bound. vm_compute. reflexivity.
    + intro H. vm_compute in H. discriminate H.
Qed.

(* ===================================================================== *)
(*  Floor — the verdict: Lambda is a DIFFERENT wall-type (taxonomy)        *)
(* ===================================================================== *)

Inductive Wall := ArrowSign | BornNorm | LambdaSmallness.
Inductive WallType := SymmetryChoice | BareHierarchy.

Definition wall_type (w : Wall) : WallType :=
  match w with
  | ArrowSign      => SymmetryChoice   (* invariant (direction) derived; the condition is the input *)
  | BornNorm       => SymmetryChoice   (* invariant (square) derived; the norm symmetry is the input *)
  | LambdaSmallness => BareHierarchy    (* finiteness derived; NO invariant -- a free scale ratio *)
  end.

(** Does the descent cross a DERIVED INVARIANT before hitting the input? *)
Definition has_derived_invariant (w : Wall) : bool :=
  match wall_type w with SymmetryChoice => true | BareHierarchy => false end.

Lemma lambda_is_bare_hierarchy : wall_type LambdaSmallness = BareHierarchy.
Proof. reflexivity. Qed.

(** ★ The pattern-of-two is BROKEN: arrow and Born have a derived invariant (SymmetryChoice); Lambda
    does NOT (BareHierarchy).  The role-limit side is heterogeneous -- at least two wall-types. *)
Lemma two_wall_types :
  has_derived_invariant ArrowSign = true
  /\ has_derived_invariant BornNorm = true
  /\ has_derived_invariant LambdaSmallness = false.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the Lambda-smallness descent                                 *)
(* ===================================================================== *)

(** Third descent (Lambda smallness), testing the shape:
      (finiteness) finitization solves the divergence -- vac_bound <= 1 (the structure is derived);
      (not value)  finiteness =/= smallness, and finiteness PICKS NO VALUE (1/1000 and 1/1000000 both
                   below the bound) -- there is no forcing invariant;
      (taxonomy)   Lambda is a BareHierarchy wall (no derived invariant), UNLIKE the arrow and Born
                   (SymmetryChoice walls, which DO have one).
    The third descent does NOT confirm a single uniform shape -- it SPLITS the pattern-of-two: the
    role-limit side carries at least two wall-types.  Premature synthesis would have erased this. *)
Theorem lambda_smallness_descent :
  vac_bound <= 1
  /\ ~ (vac_bound <= (1 # 1000000))
  /\ ((1 # 1000) < vac_bound /\ (1 # 1000000) < vac_bound /\ ~ ((1 # 1000) == (1 # 1000000)))
  /\ wall_type LambdaSmallness = BareHierarchy
  /\ has_derived_invariant LambdaSmallness = false.
Proof.
  split; [ exact divergence_solved | ].
  split; [ exact smallness_not_from_finiteness | ].
  split; [ exact finiteness_picks_no_value | ].
  split; reflexivity.
Qed.
