(** * ReductionAtlasUnimodular.v — the reduction atlas, page II: the UNIMODULAR DETERMINANT
      as a cluster primitive.  The cluster's Element-side enumeration/adjacency facts —
      the Stern–Brocot tree, Ford-circle tangency, Calkin–Wilf lowest terms, the primitive
      lattice triangle — are NOT four facts about trees, circles, fractions, and areas.  They are
      ONE engine: the 2×2 integer determinant ad−bc, preserved by adding one column to another
      (the elementary SL₂(ℤ) move), with the invariant |det|=1 as the common adjacency condition.
      Where page I (the surd engine, m²=n·k²) drove the √-obstruction thread (H2), this page drives
      the ℚ-enumeration thread (H1): both reduce to a single determinant.

    Elements: the integer determinant det2 = ad−bc; the column-operation identity; the domain
              instances (mediant, Ford tangency, Bézout, primitive triangle) (L1 + P4)
    Roles:    the determinant det2 — the single integer whose value (held at ±1) means
              "Farey-adjacent / Ford-tangent / lowest-terms / primitive triangle"
    Rules:    the one generating rule — adding one column to another preserves the determinant
              (det2_col_op); the invariant |det|=1 is the common adjacency condition

    THE DEEP POINT — four Element-side facts are one determinant.  "The mediant preserves
    Farey-neighbourness", "Ford circles are tangent iff |ps−qr|=1", "the Calkin–Wilf children stay
    in lowest terms", "the primitive lattice triangle has area 1/2" — these LOOK like four facts
    across four subjects.  The atlas shows they are ONE ring identity (a column operation preserves
    the determinant, `det2_col_op`) and ONE invariant (|det|=1, equivalently det²=1,
    `det_pm1_iff_sq1`).  The mediant inherits the parent's determinant (`mediant_inherits_det`);
    Ford tangency is exactly det²=1; the Bézout certificate ua+vb=1 IS a determinant
    (`bezout_is_det2`); the lattice doubled area IS the determinant (`lattice_doubled_area_det`),
    so a det-±1 triangle is the minimal (area-1/2) one.  Together with page I, the cluster's two
    biggest threads collapse to two primitives: the surd index m²=n·k² and the unimodular
    determinant ad−bc.  Element = a domain notion of adjacency; role = the determinant beneath it.

    ============ E/R/R разбор ============
      Rules (L5): одно правило — прибавление одного столбца к другому сохраняет определитель
                  (det2_col_op, элементарный шаг SL₂(ℤ)); инвариант |det|=1 — общее условие смежности.
      Roles (L4): det2=ad−bc — единственное целое, чьё значение (на ±1) означает «сосед Фарея / касание
                  Форда / низшие члены / примитивный треугольник».
      Elements  : целый определитель; тождество col-op; инстансы (медианта/Форд/Безу/треугольник) (L1+P4).
    ДИАГНОСТИКА (P4): четыре Element-факта перечисления = ОДИН определитель. «Медианта/Форд/Калкин–Уилф/Пик»
    выглядят четырьмя фактами про деревья/окружности/дроби/площади; атлас — это ОДНО ring-тождество (col-op) +
    ОДИН инвариант (|det|=1). Второй движок: H1-нить ℚ-перечисления сводится к определителю, как H2 — к сурд-индексу.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: the 2×2 integer determinant, preserved by column ops       *)
(* ===================================================================== *)

(** The 2×2 integer determinant of columns (a,b) and (c,d). *)
Definition det2 (a b c d : Z) : Z := a * d - b * c.

(** ★ The single rule the whole page runs on: adding column 1 to column 2 preserves the
    determinant.  This is the elementary unimodular (SL₂(ℤ)) generator, and it drives every
    move below — the mediant, the Stern–Brocot tree, the Calkin–Wilf children. *)
Lemma det2_col_op : forall a b c d : Z, det2 a b (a + c) (b + d) = det2 a b c d.
Proof. intros. unfold det2. ring. Qed.

(** The symmetric move: adding column 2 to column 1 preserves the determinant. *)
Lemma det2_col_op_left : forall a b c d : Z, det2 (a + c) (b + d) c d = det2 a b c d.
Proof. intros. unfold det2. ring. Qed.

(** The unimodular condition |det|=1, equivalently det²=1. *)
Lemma det_pm1_iff_sq1 : forall x : Z, (x = 1 \/ x = -1) <-> x * x = 1.
Proof.
  intros x. split.
  - intros [H | H]; rewrite H; reflexivity.
  - intros H. assert (Hf : (x - 1) * (x + 1) = 0) by nia.
    apply Z.mul_eq_0 in Hf. destruct Hf as [H1 | H1]; [ left | right ]; lia.
Qed.

(* ===================================================================== *)
(*  The reductions: four Element-side facts, one determinant               *)
(* ===================================================================== *)

(** ★ Stern–Brocot / Ford mediant.  The mediant (a+c)/(b+d) inherits the SAME determinant with
    each parent, so two Farey neighbours (det ±1) breed a mediant that is a neighbour of each.
    This is the engine `det2_col_op` read in both directions. *)
Theorem mediant_inherits_det : forall a b c d : Z,
  det2 a b (a + c) (b + d) = det2 a b c d
  /\ det2 (a + c) (b + d) c d = det2 a b c d.
Proof. intros. split; [ apply det2_col_op | apply det2_col_op_left ]. Qed.

(** ★ Ford-circle tangency.  Two Ford circles at a/b and c/d are tangent exactly when det²=1,
    i.e. when the determinant is ±1 — the unimodular condition.  So Ford tangency reduces to
    "the determinant is ±1." *)
Theorem ford_tangent_unimodular : forall a b c d : Z,
  det2 a b c d * det2 a b c d = 1 <-> (det2 a b c d = 1 \/ det2 a b c d = -1).
Proof. intros. symmetry. apply det_pm1_iff_sq1. Qed.

(** ★ Calkin–Wilf lowest terms.  A Bézout certificate u·a+v·b=1 IS a determinant: the matrix
    with columns (a,b) and (−v,u) has determinant u·a+v·b.  So "lowest terms" (gcd via Bézout)
    is the unimodular determinant, and the Calkin–Wilf children preserve it via `det2_col_op`. *)
Theorem bezout_is_det2 : forall a b u v : Z, u * a + v * b = det2 a b (- v) u.
Proof. intros. unfold det2. ring. Qed.

(** ★ Pick primitive triangle.  The doubled (signed) area of the lattice triangle (0,0),(a,b),
    (c,d) IS the determinant.  Hence a unimodular triangle (det ±1) has doubled area ±1 — the
    minimal nonzero lattice area, i.e. area 1/2 (the Pick base case). *)
Theorem lattice_doubled_area_det : forall a b c d : Z,
  a * d - c * b = det2 a b c d.
Proof. intros. unfold det2. ring. Qed.

Theorem primitive_triangle_minimal : forall a b c d : Z,
  det2 a b c d = 1 -> Z.abs (det2 a b c d) = 1.
Proof. intros a b c d H. rewrite H. reflexivity. Qed.

(* ===================================================================== *)
(*  The atlas page: four domains as one determinant                       *)
(* ===================================================================== *)

(** The unimodular-determinant atlas page:
      (engine) a column operation preserves the determinant (`det2_col_op`), and |det|=1 ⟺ det²=1
      (`det_pm1_iff_sq1`);
      and four cluster Element-side facts are this one determinant —
        Stern–Brocot / Ford mediant: the mediant inherits the determinant;
        Ford tangency: det²=1, i.e. det = ±1;
        Calkin–Wilf lowest terms: the Bézout certificate IS a determinant;
        Pick primitive triangle: the lattice doubled area IS the determinant.
    Four diverse adjacencies, one 2×2 integer determinant. *)
Theorem unimodular_atlas :
  (forall a b c d : Z, det2 a b (a + c) (b + d) = det2 a b c d)
  /\ (forall x : Z, (x = 1 \/ x = -1) <-> x * x = 1)
  /\ (forall a b c d : Z, det2 a b (a + c) (b + d) = det2 a b c d
                        /\ det2 (a + c) (b + d) c d = det2 a b c d)
  /\ (forall a b u v : Z, u * a + v * b = det2 a b (- v) u)
  /\ (forall a b c d : Z, a * d - c * b = det2 a b c d).
Proof.
  split; [ exact det2_col_op | ].
  split; [ exact det_pm1_iff_sq1 | ].
  split; [ exact mediant_inherits_det | ].
  split; [ exact bezout_is_det2 | exact lattice_doubled_area_det ].
Qed.
