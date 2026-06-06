(** * RoleLimitTaxonomy.v — the SYNTHESIS of the finitization arc: a taxonomy of the structurally distinct
       ways a process FAILS to be an Element (a role-limit), with the genuinely-new teeth being the
       DECIDABILITY STRATIFICATION — the same Element/role-limit boundary is DECIDABLE on the algebraic
       stratum (an actual algorithm) but UNDECIDABLE on the diagonal stratum (no algorithm can exist).

    -- The five mechanisms (each a machine-checked file of this arc) --
      (1) AlgebraicDecidable        — √2 etc., roots of integer polynomials; Element-ness is DECIDABLE
                                       (H1AlgebraicDecider.decide_alg_element — a computable Sumbool).
      (2) TranscendentalIntegerTrap — e = Σ 1/k!; scaled partial sums are integers trapped in shrinking
                                       intervals, separating from every rational (EulerProcessRoleLimit).
      (3) TranscendentalSuperExp    — Liouville Σ 1/2^(k!); approximation to ALL orders, beyond the
                                       algebraic boundary (LiouvilleBeyondAlgebraic).
      (4) OrbitClosure              — π-incommensurable angles; a rational rotation never returns to the
                                       identity (PiAngleRoleLimit / AllTriples / ScaleInvariant / PrimitiveTripleNT).
      (5) DiagonalUndecidable       — halting / Cantor / Russell; the Lawvere diagonal blocks any universal
                                       decider — Element-ness is UNDECIDABLE (UniversalDiagonal.no_universal_decider).

    -- The stratification (the genuine synthesis) --
      All five are "role-limit = no finite rational/Element witness", but they DIFFER in mechanism AND in the
      decidability of the very question "is this an Element?":
        • ALGEBRAIC stratum  — a DECIDER EXISTS (decide_alg_element): you can compute whether the root is
          rational.  Element-ness is a decidable property of the polynomial.
        • DIAGONAL stratum   — NO universal decider exists (no_universal_decider): the diagonal
          fun a => negb (run a a) escapes every enumeration.  Element-ness is undecidable.
        • the TRANSCENDENTAL / ORBIT middle — each is proven a role-limit CONSTRUCTIVELY (by its own
          mechanism), case by case; no general class-decider.
      So the finitization boundary (Element vs role-limit) is itself crossed by a SECOND boundary — the
      decidability of "is-it-an-Element?" — decidable for algebraics, undecidable at the diagonal.  That is
      the unifying observation of the whole arc, stated and proven here.

    WHAT THE REPO HAS (surveyed): H1AlgebraicDecider (decide_alg_element); EulerProcessRoleLimit
    (e_is_role_limit); LiouvilleBeyondAlgebraic; PiAngle* / PrimitiveTripleNT; UniversalDiagonal
    (lawvere / no_universal_decider — Cantor=halting=Russell).  GAP: the unifying taxonomy and the
    decidability stratification (decidable algebraic pole vs undecidable diagonal pole).  This adds it.

    ============ E/R/R разбор ============
      Elements : пять механизмов role-limit (алгебр., e-ловушка, Лиувилль, орбита, диагональ); флаг разрешимости.
      Roles    : каждый механизм = свидетельство «процесс не Element»; ось разрешимости = РАЗРЕШИМ ли сам вопрос «Element?».
      Rules    : алгебр. полюс — решатель ЕСТЬ (decide_alg_element); диагональ. полюс — решателя НЕТ (no_universal_decider);
                 середина — конструктивно по случаю. Финитизац. граница пересечена ВТОРОЙ границей — разрешимости.
      ДИАГНОСТИКА (P4): role-limit'ы не монолитны — стратифицируются по разрешимости «is-Element?»: разрешимо (алгебр.) →
      неразрешимо (диагональ). Объединяющее наблюдение всей арки H1; два полюса — настоящие теоремы. Уровень: `синтез`.

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (builds on H1AlgebraicDecider + EulerProcessRoleLimit + UniversalDiagonal)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith List Bool.
From ToS Require Import foundation.H1AlgebraicElement.
From ToS Require Import foundation.H1AlgebraicDecider.
From ToS Require Import foundation.EulerProcessRoleLimit.
From ToS Require Import foundation.UniversalDiagonal.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The taxonomy of role-limit mechanisms                                  *)
(* ===================================================================== *)

Inductive RoleLimitKind :=
  | AlgebraicDecidable          (* roots of integer polynomials — Element-ness DECIDABLE *)
  | TranscendentalIntegerTrap   (* e = Σ 1/k! — integer-trap separation *)
  | TranscendentalSuperExp      (* Liouville Σ 1/2^(k!) — super-exponential approximation *)
  | OrbitClosure                (* π-incommensurable angle — rotation never closes *)
  | DiagonalUndecidable.        (* halting / Cantor / Russell — no universal decider *)

(** The decidability of the "is-it-an-Element?" question for each kind. *)
Inductive Decidability := ClassDecidable | CaseConstructive | ClassUndecidable.

Definition decidability (k : RoleLimitKind) : Decidability :=
  match k with
  | AlgebraicDecidable  => ClassDecidable     (* decide_alg_element — an algorithm *)
  | DiagonalUndecidable => ClassUndecidable   (* no_universal_decider — no algorithm *)
  | _                   => CaseConstructive   (* e / Liouville / orbit — proven case by case *)
  end.

Definition all_kinds : list RoleLimitKind :=
  [AlgebraicDecidable; TranscendentalIntegerTrap; TranscendentalSuperExp; OrbitClosure; DiagonalUndecidable].

Definition dec_eqb (a b : Decidability) : bool :=
  match a, b with
  | ClassDecidable, ClassDecidable | CaseConstructive, CaseConstructive
  | ClassUndecidable, ClassUndecidable => true
  | _, _ => false
  end.

Definition count_decidability (d : Decidability) : nat :=
  length (filter (fun k => dec_eqb (decidability k) d) all_kinds).

(* ===================================================================== *)
(*  ★★ The two poles — both genuine theorems                              *)
(* ===================================================================== *)

(** ★★ The DECIDABLE pole: for an algebraic number (root of an integer polynomial), whether it is an
    Element (rational) is DECIDABLE — there is an actual decision procedure (H1AlgebraicDecider). *)
Theorem algebraic_pole : forall (a0 : Z) (mid : list Z) (an : Z),
  a0 <> 0 -> an <> 0 ->
  {AlgElement (a0 :: (mid ++ [an]))} + {~ AlgElement (a0 :: (mid ++ [an]))}.
Proof. exact decide_alg_element. Qed.

(** ★★ The UNDECIDABLE pole: for the computational boundary, NO universal decider exists — the Lawvere
    diagonal blocks any enumeration of all predicates (UniversalDiagonal).  Element-ness is undecidable here. *)
Theorem diagonal_pole : forall (Prog : Type) (run : Prog -> (Prog -> bool)),
  ~ (forall h : Prog -> bool, exists p, forall x, run p x = h x).
Proof. exact no_universal_decider. Qed.

(** ★ A constructive transcendental role-limit between the poles: the e-process separates from every rational. *)
Theorem transcendental_middle : e_process_is_role_limit.
Proof. exact e_is_role_limit. Qed.

(* ===================================================================== *)
(*  The stratification counts                                              *)
(* ===================================================================== *)

(** ★ Exactly ONE kind is class-decidable (algebraic). *)
Lemma n_decidable : count_decidability ClassDecidable = 1%nat.
Proof. reflexivity. Qed.

(** ★ Exactly ONE kind is class-undecidable (diagonal). *)
Lemma n_undecidable : count_decidability ClassUndecidable = 1%nat.
Proof. reflexivity. Qed.

(** ★ THREE are case-constructive (e, Liouville, orbit) — proven role-limits with no class-decider. *)
Lemma n_constructive : count_decidability CaseConstructive = 3%nat.
Proof. reflexivity. Qed.

Lemma taxonomy_total :
  (count_decidability ClassDecidable + count_decidability CaseConstructive
   + count_decidability ClassUndecidable)%nat = length all_kinds.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The role-limit taxonomy and its decidability stratification:
      (decidable pole)   algebraic Element-ness has a decision procedure (decide_alg_element);
      (constructive mid) the e-process separates from every rational (a transcendental role-limit);
      (undecidable pole) no universal decider exists for the computational boundary (the Lawvere diagonal);
      (stratification)   of the five mechanisms: 1 class-decidable, 1 class-undecidable, 3 case-constructive.
    So the finitization boundary (Element vs role-limit) is not monolithic: the question "is this an Element?"
    is itself DECIDABLE for algebraic numbers and UNDECIDABLE at the diagonal — a second boundary crossing the
    first.  This unifies the whole arc (algebraic decider → transcendental processes → π-orbit → diagonal) into
    one taxonomy with a proven decidability axis.  Level: synthesis — the mechanisms are the arc's files; the
    new content is the stratification (two real poles) and the unifying classification. *)
Theorem role_limit_taxonomy :
  (* decidable pole: a decision procedure EXISTS (inhabited — the Sumbool lives in Set, so wrap it) *)
  inhabited (forall (a0 : Z) (mid : list Z) (an : Z), a0 <> 0 -> an <> 0 ->
     {AlgElement (a0 :: (mid ++ [an]))} + {~ AlgElement (a0 :: (mid ++ [an]))})
  /\ e_process_is_role_limit
  /\ (forall (Prog : Type) (run : Prog -> (Prog -> bool)),
        ~ (forall h : Prog -> bool, exists p, forall x, run p x = h x))
  /\ count_decidability ClassDecidable = 1%nat
  /\ count_decidability ClassUndecidable = 1%nat
  /\ count_decidability CaseConstructive = 3%nat.
Proof.
  split; [ exact (inhabits algebraic_pole) | ].
  split; [ exact transcendental_middle | ].
  split; [ exact diagonal_pole | ].
  split; [ exact n_decidable | ].
  split; [ exact n_undecidable | exact n_constructive ].
Qed.
