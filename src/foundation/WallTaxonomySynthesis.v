(** * WallTaxonomySynthesis.v — the SYNTHESIS of the descent series: the corrected H1.

    The crude claim "everything bottoms at ONE wall H1" was a flattening.  Six descents INTO the magnitudes
    (not snapshots) revealed that the role-limit / wall side is HETEROGENEOUS: a taxonomy of FOUR wall-types.
    This file consolidates them and exhibits the organizing axis -- each type corresponds to a distinct KIND
    of MISSING INPUT -- machine-checked as a bijection.  It RESPECTS (explains) the heterogeneity rather than
    erasing it.

    -- The four types and what each LACKS (the meta-axis) --
      SymmetryChoice      lacks A STRUCTURE : a symmetry / boundary condition is unjustified
                          (arrow: the low-entropy past; Born: the orthogonal 2-norm symmetry).
      BareHierarchy       lacks A VALUE     : a free magnitude is unfixed
                          (Lambda: the smallness ratio; J: the CKM parameter values).
      HardStructure       lacks A PROOF     : an open, possibly-false estimate
                          (the NS nonlinearity bound -- the Millennium difficulty).
      FiniteButUncomputed lacks NOTHING     : nothing fundamental is missing -- just the computation
                          (the departure factor of eta -- a terminating process, not run).

    -- The common pattern across all walls --
      Every descent DERIVES the structure (the invariant-given-the-input); the wall is precisely at the
      MISSING INPUT.  So "ToS derives structure, the input-kind is the wall" is uniform; the HETEROGENEITY is
      entirely in WHICH KIND of input is missing.

    -- The machine content --
      lacks_injective + lacks_surjective : the map (type -> missing-input) is a BIJECTION -- the four types
                                           are exactly the four kinds of missing input.
      mag_classification                 : the six descended magnitudes, each tagged with its type.
      type_counts                        : the six cover the types 2,2,1,1 (empirical coverage).
      three_genuine / one_deflationary   : 3 GENUINE wall-types, 1 deflationary (FiniteButUncomputed = not a
                                           real wall -- the genuine-wall count is 3, not 4).

    -- HONEST scope --
      A CLASSIFICATION grounded in six inside-descents plus a completeness test (JFactorDescent), NOT a proof
      that four is exhaustive a priori.  The bijection type<->missing-input is the organizing OBSERVATION, not
      a deep theorem.  No magnitude's value is derived here.  The synthesis EXPLAINS the heterogeneity (the
      anti-flattening the correction demanded); it does not collapse it back to "one wall".

    Elements: WallType (4) / MissingInput (4); the bijection lacks; the 6 magnitudes; the counts
    Roles:    each type = the signature of a kind of missing input; structure derived is the common side
    Rules:    a wall is constituted by WHAT IT LACKS; sort by missing-input-kind {structure/value/proof/nothing}

    ============ E/R/R разбор ============
      Rules (L5): «стена» конституируется тем, ЧЕГО НЕ ХВАТАЕТ; сортировка по роду недостающего входа
                  {структура/значение/доказательство} или (дефляционно) ничего.
      Roles (L4): SymmetryChoice=нет структуры(симметрия/гранусловие); BareHierarchy=нет значения(магнитуда);
                  HardStructure=нет доказательства(открытая оценка); FiniteButUncomputed=ничего(дефляц.).
                  ОБЩЕЕ: структура выведена везде -- стена только на входе.
      Elements  : 4 типа <-> 4 входа (биекция, машинно); 6 магнитуд (2,2,1,1); 3 настоящих + 1 дефляционный.
    ДИАГНОСТИКА (P4): исправленный H1. role-limit-сторона НЕ одна стена -- таксономия 4 типов по роду
    недостающего входа (биекция типы<->входы). 3 настоящих + 1 дефляционный. Общий паттерн: вывод даёт
    структуру, стена = недостающий вход. ЧЕСТНО: классификация на 6 спусках + тест полноты, не доказательство
    априорной исчерпываемости; биекция -- наблюдение. ОБЪЯСНЯЕТ гетерогенность, не стирает (анти-уплощение).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith.
Import ListNotations.

(* ===================================================================== *)
(*  The meta-axis: four types <-> four kinds of missing input (bijection)  *)
(* ===================================================================== *)

Inductive WallType := SymmetryChoice | BareHierarchy | HardStructure | FiniteButUncomputed.
Inductive MissingInput := AStructure | AValue | AProof | Nothing.

Definition lacks (t : WallType) : MissingInput :=
  match t with
  | SymmetryChoice      => AStructure   (* a symmetry / boundary condition *)
  | BareHierarchy       => AValue       (* a free magnitude *)
  | HardStructure       => AProof       (* an open estimate *)
  | FiniteButUncomputed => Nothing      (* nothing fundamental -- just the computation *)
  end.

(** ★ The map type -> missing-input is INJECTIVE: distinct types lack distinct things. *)
Lemma lacks_injective : forall t1 t2, lacks t1 = lacks t2 -> t1 = t2.
Proof. intros [] []; simpl; intro H; try reflexivity; discriminate. Qed.

(** ★ ...and SURJECTIVE: every kind of missing input is the signature of some type.  Hence a BIJECTION:
    the four wall-types ARE exactly the four kinds of missing input. *)
Lemma lacks_surjective : forall i, exists t, lacks t = i.
Proof.
  intros [];
    [ exists SymmetryChoice | exists BareHierarchy | exists HardStructure | exists FiniteButUncomputed ];
    reflexivity.
Qed.

(* ===================================================================== *)
(*  The six descended magnitudes, classified                               *)
(* ===================================================================== *)

Inductive Magnitude :=
  | ArrowSign | BornNorm | LambdaSmallness | NSBound | DepartureSize | JFactorValue.

Definition mag_type (m : Magnitude) : WallType :=
  match m with
  | ArrowSign | BornNorm        => SymmetryChoice
  | LambdaSmallness | JFactorValue => BareHierarchy
  | NSBound                     => HardStructure
  | DepartureSize               => FiniteButUncomputed
  end.

Lemma mag_classification :
  mag_type ArrowSign = SymmetryChoice
  /\ mag_type BornNorm = SymmetryChoice
  /\ mag_type LambdaSmallness = BareHierarchy
  /\ mag_type NSBound = HardStructure
  /\ mag_type DepartureSize = FiniteButUncomputed
  /\ mag_type JFactorValue = BareHierarchy.
Proof. repeat split; reflexivity. Qed.

Definition wt_eqb (a b : WallType) : bool :=
  match a, b with
  | SymmetryChoice, SymmetryChoice => true
  | BareHierarchy, BareHierarchy => true
  | HardStructure, HardStructure => true
  | FiniteButUncomputed, FiniteButUncomputed => true
  | _, _ => false
  end.

Definition all_mags : list Magnitude :=
  [ArrowSign; BornNorm; LambdaSmallness; NSBound; DepartureSize; JFactorValue].

Definition type_count (t : WallType) : nat :=
  length (filter (fun m => wt_eqb (mag_type m) t) all_mags).

(** The six magnitudes cover the four types 2,2,1,1 (empirical coverage of the taxonomy). *)
Lemma type_counts :
  type_count SymmetryChoice = 2 /\ type_count BareHierarchy = 2
  /\ type_count HardStructure = 1 /\ type_count FiniteButUncomputed = 1.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  3 genuine wall-types, 1 deflationary                                    *)
(* ===================================================================== *)

Definition is_genuine (t : WallType) : bool :=
  match lacks t with Nothing => false | _ => true end.

Definition all_types : list WallType :=
  [SymmetryChoice; BareHierarchy; HardStructure; FiniteButUncomputed].

(** ★ Three of the four are genuine walls; one (FiniteButUncomputed) is deflationary -- not a real wall. *)
Lemma three_genuine : length (filter is_genuine all_types) = 3%nat.
Proof. reflexivity. Qed.

Lemma one_deflationary : is_genuine FiniteButUncomputed = false.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the corrected H1 (the wall taxonomy)                         *)
(* ===================================================================== *)

(** The synthesis -- the corrected H1:
      (bijection)    the four wall-types <-> the four kinds of missing input (lacks is injective AND
                     surjective): structure / value / proof / nothing;
      (genuine)      3 genuine wall-types, 1 deflationary (FiniteButUncomputed is not a real wall);
      (coverage)     the six descended magnitudes cover the types 2,2,1,1.
    The role-limit / wall side is NOT one wall -- it is a four-type taxonomy organized by the KIND of missing
    input.  The heterogeneity is EXPLAINED (each type = a distinct lack), not flattened.  A classification
    grounded in six inside-descents plus a completeness test; no value is derived here. *)
Theorem wall_taxonomy_synthesis :
  (forall t1 t2, lacks t1 = lacks t2 -> t1 = t2)
  /\ (forall i, exists t, lacks t = i)
  /\ length (filter is_genuine all_types) = 3%nat
  /\ is_genuine FiniteButUncomputed = false
  /\ (type_count SymmetryChoice = 2 /\ type_count BareHierarchy = 2
      /\ type_count HardStructure = 1 /\ type_count FiniteButUncomputed = 1).
Proof.
  split; [ exact lacks_injective | ].
  split; [ exact lacks_surjective | ].
  split; [ exact three_genuine | ].
  split; [ exact one_deflationary | exact type_counts ].
Qed.
