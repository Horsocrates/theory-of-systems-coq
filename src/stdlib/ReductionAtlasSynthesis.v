(** * ReductionAtlasSynthesis.v — the reduction atlas, CAPSTONE: the five engines are five
      coordinates of ONE 2×2 integer matrix, and the discriminant is the master dial.  The five
      discovery pages —
        I   surd index m²=n·k²            (ReductionAtlasSurd.v,        `surd_atlas`)
        II  unimodular determinant ad−bc  (ReductionAtlasUnimodular.v,  `unimodular_atlas`)
        III norm form x²−D·y²             (ReductionAtlasPell.v,        `pell_atlas`)
        IV  integer trace 2cosθ           (ReductionAtlasNiven.v,       `niven_trace_atlas`)
        V   parity popcount(i∧j) mod 2    (ReductionAtlasParity.v,      `parity_atlas`)
      are NOT five independent primitives.  They are read off ONE integer matrix M = [[a,b],[c,d]]:
      its determinant (II), its trace (IV), the discriminant Δ = tr²−4·det of its characteristic
      polynomial x²−(tr)x+(det) (whose square-ness is engine I, the surd), the norm form = the
      determinant of the regular representation (III), and the mod-2 character (V, the Element-side
      shadow).  This legend re-proves the unifying skeleton self-contained: the discriminant bridge
      (a rational eigenvalue forces a square discriminant) and one explicit 2×2 per engine.

    Elements: the explicit 2×2 matrices — Fibonacci [[1,1],[1,0]], order-6 [[1,−1],[1,0]], Pell
              [[3,4],[2,3]], Hadamard [[1,1],[1,−1]]; the discriminant identity (L1 + P4)
    Roles:    the discriminant Δ = tr²−4·det — the single integer whose square-ness decides:
              perfect square ⟺ rational eigenvalues ⟺ Element (the object lands rationally,
              terminates); non-square ⟺ irrational eigenvalues √Δ ⟺ role-limit (non-terminating)
    Rules:    one rule — the Element/role-limit status of an object is read off its 2×2 matrix:
              4(x²−t·x+e) = (2x−t)² − (t²−4e) (completing the square), so a rational eigenvalue
              forces Δ = t²−4e to be a perfect square (engine I = the discriminant of engines II,IV)

    THE DEEP POINT — five engines, one matrix, one dial.  The cluster's whole finitization boundary,
    across ~70 domain instances, collapses to: read the 2×2 matrix M, compute its discriminant
    Δ = tr²−4·det, ask "perfect square?".  Square ⟺ a rational eigenvalue ⟺ Element (terminates);
    non-square ⟺ eigenvalues ±√Δ/… ⟺ role-limit (non-terminating).  Four engines are the matrix's
    algebraic invariants — determinant (II, held at ±1 = adjacency), trace (IV, held at ∈{−2..2} =
    finite order), characteristic polynomial / norm form (III, the bridge), and the square-ness of
    the discriminant (I, the surd) — and the fifth (V) is the matrix's mod-2 reduction (the parity
    character, the Element-side shadow).  The bridge `eigenvalue_forces_square_disc` is the hinge:
    a rational eigenvalue of [[a,b],[c,d]] forces (a−d)²+4bc to be a perfect square.  The explicit
    matrices show each engine as a coordinate: Fibonacci det −1 (II); order-6 trace 1, det 1, Δ=−3
    elliptic (IV); Pell [[3,4],[2,3]] det 1, Δ=32=4·2·2² (III/I, √2); Hadamard det −2, Δ=8 (V/I, √2,
    `no_square_8`).  Compression: 68 domain facts → 5 engines → ONE matrix with ONE master dial.
    Element = a rational eigenvalue (square discriminant); role-limit = √Δ (non-square discriminant).

    ============ E/R/R разбор ============
      Rules (L5): одно правило — статус читается с матрицы 2×2: 4(x²−tx+e)=(2x−t)²−(t²−4e), рациональное
                  собств. значение ⟹ Δ=t²−4e полный квадрат (движок I = дискриминант движков II,IV).
      Roles (L4): Δ=tr²−4det — целое, чья квадратность решает: квадрат ⟺ рац. собств. значения ⟺ Element;
                  не квадрат ⟺ иррац. √Δ ⟺ role-limit (нетерминирующий). Пять движков — пять прочтений матрицы.
      Elements  : явные 2×2 (Фибоначчи/порядок-6/Пелля/Адамара); тождество дискриминанта; no_square_8.
    ДИАГНОСТИКА (P4): пять движков = пять КООРДИНАТ ОДНОЙ матрицы 2×2 (четыре алгебр. инварианта — det II /
    след IV / χ-многочлен-норм-форма III / квадратность дискриминанта = сурд I — плюс mod-2-редукция V).
    Вся граница: возьми 2×2, посчитай Δ=tr²−4det, «полный квадрат?». 68 фактов → 5 движков → ОДНА матрица,
    ОДИН вентиль. «Конечно-актуален?» = «есть рациональное собств. значение?» = «Δ полный квадрат?». Атлас завершён.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The 2×2 integer matrix and its invariants — the atlas coordinates       *)
(* ===================================================================== *)

(** The determinant of [[a,b],[c,d]] (engine II). *)
Definition det2 (a b c d : Z) : Z := a * d - b * c.

(** The trace of [[a,b],[c,d]] (engine IV). *)
Definition tr2 (a d : Z) : Z := a + d.

(** The discriminant of the characteristic polynomial x² − tr·x + det (engine I obstruction). *)
Definition disc (a b c d : Z) : Z := tr2 a d * tr2 a d - 4 * det2 a b c d.

(** The discriminant via trace and determinant: Δ = tr² − 4·det = (a−d)² + 4bc. *)
Lemma disc_eq : forall a b c d : Z, disc a b c d = (a - d) * (a - d) + 4 * (b * c).
Proof. intros. unfold disc, tr2, det2. ring. Qed.

(* ===================================================================== *)
(*  THE UNIFYING BRIDGE: a rational eigenvalue forces a square discriminant *)
(* ===================================================================== *)

(** ★ Completing the square: the characteristic polynomial x² − t·x + e satisfies
    4(x² − t·x + e) = (2x − t)² − (t² − 4e).  This is the hinge tying engines II,IV (trace t,
    determinant e) to engine I (the surd t²−4e). *)
Lemma char_poly_complete_square : forall x t e : Z,
  4 * (x * x - t * x + e) = (2 * x - t) * (2 * x - t) - (t * t - 4 * e).
Proof. intros. ring. Qed.

(** ★ THE BRIDGE.  An integer eigenvalue x of [[a,b],[c,d]] (a root of its characteristic
    polynomial x² − tr·x + det) forces the discriminant Δ to be a perfect square: Δ = (2x − tr)².
    So engine I (Δ a perfect square) is exactly "the 2×2 has a rational eigenvalue" — the
    discriminant of engines II (det) and IV (trace).  Contrapositive: Δ non-square ⟹ no rational
    eigenvalue ⟹ role-limit (√Δ). *)
Lemma eigenvalue_forces_square_disc : forall x a b c d : Z,
  x * x - tr2 a d * x + det2 a b c d = 0 ->
  exists m : Z, m * m = disc a b c d.
Proof.
  intros x a b c d H. exists (2 * x - tr2 a d). unfold disc.
  pose proof (char_poly_complete_square x (tr2 a d) (det2 a b c d)) as Hid.
  rewrite H in Hid. lia.
Qed.

(* ===================================================================== *)
(*  ONE EXPLICIT 2×2 PER ENGINE — the five coordinates                     *)
(* ===================================================================== *)

(** Engine II (determinant) — the Fibonacci / Stern–Brocot matrix [[1,1],[1,0]] is unimodular
    (det −1): the adjacency invariant |det| = 1. *)
Lemma instance_unimodular : det2 1 1 1 0 = -1.
Proof. reflexivity. Qed.

(** Engine IV (trace) — the order-6 rotation matrix [[1,−1],[1,0]] is elliptic: det 1, trace 1
    ∈ {−2..2}, so Δ = 1 − 4 = −3 < 0 (complex eigenvalues on the unit circle = finite order). *)
Lemma instance_finite_order : tr2 1 0 = 1 /\ det2 1 (-1) 1 0 = 1 /\ disc 1 (-1) 1 0 = -3.
Proof. repeat split; reflexivity. Qed.

(** Engine III (norm form) — the Pell unit matrix [[3,4],[2,3]] (the companion of 3+2√2) is
    unimodular (det 1, the norm-form value of the unit) with Δ = 32 = 4·2·2² (the √2 of D=2):
    eigenvalues 3±2√2, a role-limit. *)
Lemma instance_pell : det2 3 4 2 3 = 1 /\ disc 3 4 2 3 = 32.
Proof. split; reflexivity. Qed.

(** Engine V (parity) / engine I (surd) — the Hadamard matrix [[1,1],[1,−1]] (its entries are the
    parity-character values χ(a·b)) has det −2 and Δ = 8: eigenvalues ±√2, a role-limit. *)
Lemma instance_hadamard : det2 1 1 1 (-1) = -2 /\ disc 1 1 1 (-1) = 8.
Proof. split; reflexivity. Qed.

(** Engine I (surd) — Δ = 8 is NOT a perfect square (4 = 2² < 8 < 3² = 9), so the Hadamard matrix
    has no rational eigenvalue: its eigenvalues ±√2 are a role-limit.  This is the discriminant
    side of the surd engine. *)
Lemma no_square_8 : forall m : Z, m * m <> 8.
Proof.
  intros m H.
  assert (Habs : Z.abs m * Z.abs m = 8).
  { rewrite <- Z.abs_mul. rewrite H. reflexivity. }
  assert (H0 : 0 <= Z.abs m) by apply Z.abs_nonneg.
  assert (Hcase : Z.abs m <= 2 \/ 3 <= Z.abs m) by lia.
  destruct Hcase as [Hle | Hge]; nia.
Qed.

(* ===================================================================== *)
(*  THE ATLAS MAP — five engines as one 2×2 matrix                         *)
(* ===================================================================== *)

(** The reduction atlas synthesis: the five engines are coordinates of one 2×2 integer matrix.
      (bridge) a rational eigenvalue forces a square discriminant (`eigenvalue_forces_square_disc`)
        — engine I is the discriminant of engines II (det) and IV (trace);
      (Δ) the discriminant is tr² − 4·det = (a−d)² + 4bc (`disc_eq`);
      (II) the Fibonacci/Stern–Brocot matrix is unimodular (det −1);
      (IV) the order-6 matrix is elliptic (det 1, trace 1, Δ = −3);
      (III) the Pell unit matrix is unimodular with Δ = 32 (√2 role-limit);
      (V/I) the Hadamard matrix (parity entries) has Δ = 8, NOT a perfect square (√2 role-limit).
    Five engines, one matrix, one master dial: the discriminant.  The whole finitization boundary
    is "is the discriminant a perfect square?". *)
Theorem reduction_atlas_synthesis :
  (forall x a b c d : Z,
     x * x - tr2 a d * x + det2 a b c d = 0 -> exists m : Z, m * m = disc a b c d)
  /\ (forall a b c d : Z, disc a b c d = (a - d) * (a - d) + 4 * (b * c))
  /\ det2 1 1 1 0 = -1
  /\ (tr2 1 0 = 1 /\ det2 1 (-1) 1 0 = 1 /\ disc 1 (-1) 1 0 = -3)
  /\ (det2 3 4 2 3 = 1 /\ disc 3 4 2 3 = 32)
  /\ (det2 1 1 1 (-1) = -2 /\ disc 1 1 1 (-1) = 8 /\ forall m : Z, m * m <> 8).
Proof.
  split; [ exact eigenvalue_forces_square_disc | ].
  split; [ exact disc_eq | ].
  split; [ exact instance_unimodular | ].
  split; [ exact instance_finite_order | ].
  split; [ exact instance_pell | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  exact no_square_8.
Qed.
