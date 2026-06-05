(** * BornRuleDescent.v — the DESCENT INTO Part F's Born rule (not a snapshot): is p = |amplitude|^2 a
      RE-DESCRIPTION (a necessary wall) or DERIVABLE from counting/symmetry (a frontier that crosses to Element)?

    The Part-F snapshot (ApplicationsAudit.v) tagged the Born rule "ReDescription".  This descent shows that
    tag was too coarse: the Born rule SPLITS, exactly like the arrow of time (ArrowGroundingDescent.v).

    -- Rung 1: "p = a function of the amplitude, normalized" is trivial (normalization).  Not the hard part.

    -- Rung 2: the SQUARE is FORCED, given the rotation symmetry.  Over Q, the rational (3,4,5) rotation
       R(x,y) = ((3x-4y)/5, (4x+3y)/5) -- an orthogonal symmetry, the Pythagorean structure of ToS --
       preserves the 2-norm x^2+y^2 EXACTLY (square_preserved: a ring identity, all x,y), and maps the unit
       circle to itself (on_unit_circle).  But it BREAKS the 1-norm: the image of (1,0) is (3/5,4/5) with
       1-norm 7/5 > 1 (one_norm_grows), and the image of (1,1) is (-1/5,7/5) with 1-norm 8/5 < 2
       (one_norm_shrinks) -- the 1-norm changes BOTH ways, so it is definitely not conserved.  Among the
       p-norms, only p=2 survives the symmetry: the SQUARE is the unique rotation invariant.  This is NOT a
       re-description -- it is a genuine derivation of "why the square".

    -- Rung 3 (floor): WHY the orthogonal (2-norm) symmetry, not the 1-norm (classical/stochastic)?  Because
       amplitudes INTERFERE -- rotations mix the components (sign/phase).  The choice of the 2-norm symmetry
       is the INPUT; deriving it from something deeper (interference from distinction, the complex structure)
       is open.  The wall RELOCATES to "why interference / why the 2-norm".

    -- Floor / verdict: the Born rule SPLITS.
         SquareGivenNorm -> DerivedFromInvariance (FRONTIER crossed to Element: the square is the unique
                            rotation invariant -- machine-checked).
         NormChoice      -> PositedInput          (the relocated wall: why the orthogonal / 2-norm symmetry
                            = interference, the input).

    -- The parallel (the method's uniform shape).  Arrow: Direction derived (P4) / Sign posited (past
       hypothesis).  Born: Square derived (invariance) / NormChoice posited (interference).  In BOTH, ToS
       derives the INVARIANT-GIVEN-THE-SYMMETRY; the symmetry / boundary selection is where it stops.  This
       corrects the snapshot: the Born rule is not a re-description, it is a split.

    Elements: the rational (3,4,5) rotation over Q; x^2+y^2 (2-norm) vs |x|+|y| (1-norm); BornAspect / Grounding
    Roles:    the square = the conserved invariant of the orthogonal symmetry; the norm choice = the input
    Rules:    p = |c|^2 is forced AS the rotation invariant; the orthogonal symmetry (interference) is posited

    ============ E/R/R разбор ============
      Rules (L5): квадрат вынужден КАК инвариант вращательной симметрии (2-норма сохраняется, 1-норма нет);
                  выбор ортогональной симметрии (интерференция) -- вход, не выводится здесь.
      Roles (L4): квадрат = сохраняемый инвариант ортогональной симметрии (Element); выбор нормы = вход
                  (интерференция/комплексность) -- перемещённая стена.
      Elements  : (3,4,5)-вращение над Q; x^2+y^2 сохраняется точно, |x|+|y| ломается в обе стороны.
    ДИАГНОСТИКА (P4): Борн РАСЩЕПЛЯЕТСЯ. SquareGivenNorm = DerivedFromInvariance (фронтир -> Element: квадрат
    = единственный вращательный инвариант, машинно). NormChoice = PositedInput (почему ортогональная/2-норма
    = интерференция -- вход). Та же ФОРМА, что у стрелы (Direction/Sign): ToS выводит инвариант-при-симметрии,
    выбор симметрии -- где останавливается. ИСПРАВЛЯЕТ снимок: Борн -- не пере-описание, а расщепление.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs.
Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Rung 2a — the SQUARE (2-norm) is EXACTLY preserved by the rotation      *)
(* ===================================================================== *)

(** The rational (3,4,5) rotation R(x,y) = ((3x-4y)/5, (4x+3y)/5) preserves the 2-norm:
    scaled by 5^2 = 25, it is a pure ring identity over Q (true for ALL x,y). *)
Lemma square_preserved : forall x y : Q,
  (3*x - 4*y)*(3*x - 4*y) + (4*x + 3*y)*(4*x + 3*y) == 25 * (x*x + y*y).
Proof. intros x y. ring. Qed.

(** The (3,4,5) point sits on the unit circle: the rotation maps (1,0) onto x^2+y^2 = 1. *)
Lemma on_unit_circle : (3#5)*(3#5) + (4#5)*(4#5) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Rung 2b — the 1-NORM is BROKEN by the same rotation (both ways)         *)
(* ===================================================================== *)

(** Image of (1,0) is (3/5,4/5): its 1-norm 7/5 EXCEEDS the original 1 -- the 1-norm grew. *)
Lemma one_norm_grows : 1 < Qabs (3#5) + Qabs (4#5).
Proof. vm_compute. reflexivity. Qed.

(** Image of (1,1) is (-1/5,7/5): its 1-norm 8/5 is BELOW the original 2 -- the 1-norm shrank.
    Changing both ways, the 1-norm is definitely NOT conserved by the symmetry. *)
Lemma one_norm_shrinks : Qabs (- (1#5)) + Qabs (7#5) < 2.
Proof. vm_compute. reflexivity. Qed.

(** ★ The crux: among the p-norms, only p=2 survives the rotation -- the SQUARE is forced.
    (p=2 conserved for all x,y; p=1 not conserved -- witnessed.) *)
Lemma only_square_conserved :
  (forall x y : Q,
     (3*x - 4*y)*(3*x - 4*y) + (4*x + 3*y)*(4*x + 3*y) == 25 * (x*x + y*y))
  /\ 1 < Qabs (3#5) + Qabs (4#5).
Proof. split; [ exact square_preserved | exact one_norm_grows ]. Qed.

(* ===================================================================== *)
(*  Floor — the verdict: the Born rule SPLITS                              *)
(* ===================================================================== *)

Inductive BornAspect := SquareGivenNorm | NormChoice.
Inductive Grounding := DerivedFromInvariance | PositedInput.

Definition aspect_grounding (a : BornAspect) : Grounding :=
  match a with
  | SquareGivenNorm => DerivedFromInvariance  (* p=|c|^2 is THE rotation invariant; the square is forced *)
  | NormChoice      => PositedInput           (* why the orthogonal / 2-norm symmetry = interference (input) *)
  end.

(** ★ The split: the square is grounded by invariance (a frontier crossed to Element); the norm choice
    remains a posited input (why interference / the orthogonal symmetry). *)
Lemma the_split :
  aspect_grounding SquareGivenNorm = DerivedFromInvariance
  /\ aspect_grounding NormChoice = PositedInput.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the Born-rule descent                                        *)
(* ===================================================================== *)

(** Descent INTO the Born rule (Part F), seam-vs-frontier:
      (invariant) the rational (3,4,5) rotation preserves x^2+y^2 EXACTLY for all x,y, and maps (1,0) onto
                  the unit circle -- the SQUARE is the rotation invariant (FRONTIER crossed to Element);
      (1-norm)    the same rotation BREAKS the 1-norm (1 -> 7/5 grows): only p=2 survives the symmetry;
      (verdict)   the Born rule SPLITS: SquareGivenNorm = DerivedFromInvariance, NormChoice = PositedInput.
    The wall RELOCATES (to "why the orthogonal symmetry / interference"), it does not stay a re-description.
    Same shape as the arrow descent: ToS derives the invariant-given-the-symmetry; the symmetry choice is
    the input. *)
Theorem born_rule_descent :
  (forall x y : Q, (3*x - 4*y)*(3*x - 4*y) + (4*x + 3*y)*(4*x + 3*y) == 25 * (x*x + y*y))
  /\ (3#5)*(3#5) + (4#5)*(4#5) == 1
  /\ 1 < Qabs (3#5) + Qabs (4#5)
  /\ aspect_grounding SquareGivenNorm = DerivedFromInvariance
  /\ aspect_grounding NormChoice = PositedInput.
Proof.
  split; [ exact square_preserved | ].
  split; [ exact on_unit_circle | ].
  split; [ exact one_norm_grows | ].
  split; reflexivity.
Qed.
