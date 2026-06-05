(** * WallTaxonomyReflexive.v — the REFLEXIVE turn: the wall-classification method applied to its OWN
      product (the four-type taxonomy of WallTaxonomySynthesis.v).  Is the taxonomy itself DERIVED or WALLED?

    The method sorts every claim into a DERIVED CORE plus a MISSING INPUT.  Turned on the taxonomy, it does
    not exempt itself: the taxonomy SPLITS the same way every magnitude it classifies does.

    -- The derived core (a theorem).  The bijection "four wall-types <-> four kinds of missing input" is
       machine-checked (bijection_injective + bijection_surjective).  GIVEN the four types, the organizing
       axis is a genuine theorem.

    -- The open rim (empirical, not a theorem).  "Exactly four types, no fifth" is NOT proven a priori -- it
       rests on six descents plus a completeness test (coverage_empirical: six checked, not all).  Nothing
       proven excludes a fifth type; the WallType inductive could carry more constructors.

    -- The gem (self-application).  The taxonomy's OWN gap is one of its OWN four types: exhaustiveness lacks
       a PROOF, so the taxonomy's own wall-type is HardStructure (self_application: lacks HardStructure =
       AProof).  The method classifies its own incompleteness by its own scheme.

    -- Verdict.  The taxonomy, descended by its own method, = a DERIVED core (the bijection) + an OPEN rim
       (exhaustiveness = HardStructure).  Same two-sided shape as every magnitude.  The method is
       self-consistent (Munchhausen-honest): it does not exempt itself.  HONEST: the taxonomy is a useful
       OBSERVATION with a proven core and an open rim -- not a theorem of a-priori completeness.

    Elements: WallType / MissingInput (re-encoded); the bijection; the 6 checked magnitudes; self-classification
    Roles:    Bijection = derived core (theorem); Exhaustiveness = open rim (empirical) = HardStructure
    Rules:    the method sorts every claim (incl. itself) into derived-core + missing-input; no self-exemption

    ============ E/R/R разбор ============
      Rules (L5): метод сортирует всякое утверждение (включая себя) на выведенное-ядро + недостающий-вход;
                  рефлексивность -- правило не исключает себя.
      Roles (L4): Биекция = выведенное ядро (теорема, lacks инъективна+сюръективна); Исчерпываемость =
                  открытый край (эмпирика, 6 спусков) = HardStructure (недостаёт доказательства полноты).
      Elements  : 6 магнитуд покрыты (длина=6, не все); биекция; WallType мог бы иметь больше конструкторов.
    ДИАГНОСТИКА (P4): таксономия, спущенная СВОИМ методом, РАСЩЕПЛЯЕТСЯ как всякая магнитуда: ядро (биекция,
    доказано) + край (исчерпываемость, открыто). Гем: собственный край таксономии = один из её же 4 типов --
    HardStructure (lacks HardStructure = AProof, недостаёт доказательства полноты). Метод НЕ освобождает себя
    -- само-консистентно (Мюнхгаузен). ЧЕСТНО: таксономия = полезное НАБЛЮДЕНИЕ (ядро доказано, край открыт),
    не теорема об априорной полноте.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith.
Import ListNotations.

(* ===================================================================== *)
(*  The taxonomy, re-encoded (from WallTaxonomySynthesis.v)                 *)
(* ===================================================================== *)

Inductive WallType := SymmetryChoice | BareHierarchy | HardStructure | FiniteButUncomputed.
Inductive MissingInput := AStructure | AValue | AProof | Nothing.

Definition lacks (t : WallType) : MissingInput :=
  match t with
  | SymmetryChoice      => AStructure
  | BareHierarchy       => AValue
  | HardStructure       => AProof
  | FiniteButUncomputed => Nothing
  end.

(* ===================================================================== *)
(*  The DERIVED core: the bijection is a theorem                           *)
(* ===================================================================== *)

(** ★ The map type -> missing-input is injective (distinct types lack distinct things). *)
Lemma bijection_injective : forall t1 t2, lacks t1 = lacks t2 -> t1 = t2.
Proof. intros [] []; simpl; intro H; try reflexivity; discriminate. Qed.

(** ★ ...and surjective.  GIVEN the four types, the 4<->4 axis is a genuine theorem. *)
Lemma bijection_surjective : forall i, exists t, lacks t = i.
Proof.
  intros [];
    [ exists SymmetryChoice | exists BareHierarchy | exists HardStructure | exists FiniteButUncomputed ];
    reflexivity.
Qed.

(* ===================================================================== *)
(*  The OPEN rim: coverage is empirical (six checked, not all)             *)
(* ===================================================================== *)

Inductive Magnitude :=
  | ArrowSign | BornNorm | LambdaSmallness | NSBound | DepartureSize | JFactorValue.

Definition checked : list Magnitude :=
  [ArrowSign; BornNorm; LambdaSmallness; NSBound; DepartureSize; JFactorValue].

(** ★ The empirical basis: SIX magnitudes were checked (a completeness test), NOT all possible magnitudes.
    Coverage of six is not exhaustiveness; nothing proven excludes a fifth type. *)
Lemma coverage_empirical : length checked = 6%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Self-classification: derived core + open rim (= HardStructure)         *)
(* ===================================================================== *)

Inductive TaxonomyAspect := TheBijection | TheExhaustiveness.
Inductive MetaStatus := DerivedCore | OpenRim.

Definition aspect_status (a : TaxonomyAspect) : MetaStatus :=
  match a with
  | TheBijection      => DerivedCore   (* the 4<->4 bijection is a machine-checked theorem *)
  | TheExhaustiveness => OpenRim        (* "exactly four, no fifth" is empirical, not a-priori proven *)
  end.

Lemma self_classification :
  aspect_status TheBijection = DerivedCore
  /\ aspect_status TheExhaustiveness = OpenRim.
Proof. split; reflexivity. Qed.

(** ★ THE GEM (self-application): the taxonomy's OWN gap is one of its OWN four types.  Exhaustiveness
    lacks a PROOF, so the taxonomy's own wall-type is HardStructure -- it classifies its own incompleteness
    by its own scheme.  The method does not exempt itself. *)
Definition taxonomy_own_wall_type : WallType := HardStructure.

Lemma self_application : lacks taxonomy_own_wall_type = AProof.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the reflexive verdict                                        *)
(* ===================================================================== *)

(** The reflexive turn -- the method applied to its own product:
      (derived core)  the bijection four-types <-> four-missing-inputs is a theorem (injective + surjective);
      (open rim)      "exactly four" rests on six checked magnitudes, not on a proof of exhaustiveness;
      (self-applied)  the taxonomy's own gap is HardStructure (lacks a proof of completeness) -- one of its
                      own four types.
    The taxonomy, descended by its own method, splits into a derived core plus an open rim -- the same
    two-sided shape as every magnitude it classifies.  The method is self-consistent (it does not exempt
    itself); the taxonomy is a useful OBSERVATION with a proven core and an open rim, not an a-priori
    completeness theorem. *)
Theorem taxonomy_reflexive :
  (forall t1 t2, lacks t1 = lacks t2 -> t1 = t2)
  /\ (forall i, exists t, lacks t = i)
  /\ length checked = 6%nat
  /\ aspect_status TheBijection = DerivedCore
  /\ aspect_status TheExhaustiveness = OpenRim
  /\ lacks taxonomy_own_wall_type = AProof.
Proof.
  split; [ exact bijection_injective | ].
  split; [ exact bijection_surjective | ].
  split; [ exact coverage_empirical | ].
  split; [ reflexivity | ].
  split; [ reflexivity | exact self_application ].
Qed.
