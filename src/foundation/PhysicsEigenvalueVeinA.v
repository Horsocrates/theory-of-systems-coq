(** * PhysicsEigenvalueVeinA.v — the canonical vein-A decider discharges the rationality verdict of
       REAL physics eigenvalues: the Perron–Frobenius / golden spectral radius φ and the Helium CI
       ground-state energy are both role-limits (irrational), decided 0-axiom by "is Δ a perfect square?".

    THE OBSERVATION (from the vein-A physics-reach audit).
    Across the spectral-physics files, several central eigenvalues are 2×2 (or quadratically reducible)
    and the files COMPUTE the discriminant Δ = tr²−4det by hand, yet NONE invoke the canonical vein-A
    decider — they state the Element/role-limit verdict manually. This file connects the two cleanest to
    `rational_eigenvalue_iff_disc_square` (vein A), so the verdict is a 0-axiom decision, not a remark:

      - Perron–Frobenius / golden matrix [[1,1],[1,0]] (PerronFrobenius.v:51; = the Fibonacci matrix):
        trace 1, det −1 (golden_trace :62, golden_det :69), Δ = tr²−4det = 5 (golden_discriminant :84).
        5 is not a perfect square ⟹ the spectral radius φ is a ROLE-LIMIT (√5). Element foil: the matrix
        [[1,1],[1,1]] (trace 2, det 0, Δ=4=2²) has rational eigenvalues 0,2 — an ELEMENT.

      - Helium configuration-interaction 2×2 (HeCIMatrix.v): trace −1449/256 (he_CI_trace_value :40),
        det 524871/65536 (he_CI_det_value :46), Δ = (H11−H22)²+4H12² = tr²−4det = 117/65536
        (he_CI_disc_value :55). 117 = 9·13 is not a perfect square ⟹ the He CI ground-state energy is a
        ROLE-LIMIT (irrational). This REPLACES the hand-written "117=9·13 so irrational" remark at
        HeCIEigenvalue.v:21 with the decider.

    HONEST SCALE / NARROWNESS (the audit's verdict).
    Vein A is the correct, complete, decidable account of rationality for the 2×2 / quadratically-
    reducible spectral gap — and that case genuinely recurs (He CI in qchem, golden/PF and the Ising
    transfer block in condensed matter, a Markov price matrix in trading, plus graphene/BCS already
    bridged in GapPythagoreanBoundary). But it is a HANDFUL of 2×2 instances + their quadratic
    reductions, NOT a blanket principle: the larger-K lattice spectra (cosine eigenvalues −2cos(πk/(K+1)),
    trace invariants tr(Hⁿ)) and the non-spectral "gaps" (SSH |t1−t2|, BCS Padé, graphene Dirac point)
    lie OUTSIDE it. Sell vein A as "the decidable rationality boundary for quadratic/2×2 spectra", not
    "the governing principle of spectral physics". Level: synthesis+observation (a bridge; the algebra
    and the irrationalities are classical).

    ============ E/R/R разбор ============
      Elements : два РЕАЛЬНЫХ физических 2×2 — golden/PF [[1,1],[1,0]] (tr 1, det −1, Δ=5) и He CI
                 [[H11,H12],[H12,H22]] (tr −1449/256, det 524871/65536, Δ=117/65536); Element-фойл
                 full_mat [[1,1],[1,1]] (Δ=4).
      Roles    : собств. значение = спектральная наблюдаемая (φ Перрона–Фробениуса; основная энергия He CI);
                 рациональное = Element (актуализуемо), иррациональное = role-limit (континуум);
                 Δ-перфект-квадрат = вентиль-решатель вены A.
      Rules    : has_rat_eig tr det ⟺ Δ перфект-квадрат (rational_eigenvalue_iff_disc_square);
                 φ role-limit (Δ=5 не квадрат, rolelimit_5); He CI role-limit (Δ=117/65536, 117 не квадрат);
                 full_mat Element (Δ=4=2²).
      ДИАГНОСТИКА (P4): канонический разрешитель вены A выносит вердикт рациональности РЕАЛЬНЫХ физических
      собств. значений (φ, основная энергия гелия CI), заменяя ручную пометку «117=9·13 ⇒ иррационально»
      (HeCIEigenvalue.v:21). ЧЕСТНО (узость): вена A покрывает РОВНО 2×2/квадратично-сводимые спектры
      (~6-8 инстансов); бо́льшие-K косинус-спектры и неспектральные щели (SSH, BCS-Падэ, графен) — ВНЕ её.
      Уровень: `синтез+наблюдение` (мост).

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (imports foundation.DiscriminantCompleteEigenvalue,
                                          H1ConstructivityDecidable, stdlib.GeneralSqrt)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.H1ConstructivityDecidable.
From ToS Require Import foundation.DiscriminantCompleteEigenvalue.
From ToS Require Import stdlib.GeneralSqrt.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Perron–Frobenius / golden matrix [[1,1],[1,0]]: φ is a ROLE-LIMIT  *)
(* ===================================================================== *)

(** golden_mat = [[1,1],[1,0]] (PerronFrobenius.v:51) = the Fibonacci matrix: trace 1, det −1. *)
Definition golden_tr  : Q := 1.
Definition golden_det : Q := -(1).

(** Δ = tr²−4det = 5  (= golden_discriminant, PerronFrobenius.v:84). *)
Lemma golden_disc_is_5 : discQ golden_tr golden_det == inject_Z 5.
Proof. unfold discQ, golden_tr, golden_det. vm_compute. reflexivity. Qed.

(** ★ The golden / PF spectral radius φ is a ROLE-LIMIT: by vein A, the golden matrix has a rational
    eigenvalue ⟺ Δ=5 is a perfect square — and 5 is not (rolelimit_5). 0-axiom decider verdict. *)
Theorem golden_eigenvalue_role_limit : ~ has_rat_eig golden_tr golden_det.
Proof.
  rewrite rational_eigenvalue_iff_disc_square. intros [s Hs].
  rewrite golden_disc_is_5 in Hs. apply rolelimit_5. exists s. exact Hs.
Qed.

(** The Element foil: [[1,1],[1,1]] (trace 2, det 0, Δ=4=2²) HAS rational eigenvalues 0,2 — ELEMENT. *)
Definition full_tr  : Q := 2.
Definition full_det : Q := 0.

Theorem full_matrix_element : has_rat_eig full_tr full_det.
Proof.
  rewrite rational_eigenvalue_iff_disc_square. exists 2.
  unfold discQ, full_tr, full_det. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. Helium CI 2×2 ground state: a ROLE-LIMIT (Δ=117/65536)             *)
(* ===================================================================== *)

(** He CI invariants (HeCIMatrix.v): trace −1449/256 (:40), det 524871/65536 (:46). *)
Definition heci_tr  : Q := -(1449 # 256).
Definition heci_det : Q := 524871 # 65536.

(** Δ = tr²−4det = 117/65536  (= he_CI_disc, HeCIMatrix.v:55; 65536 = 256² is a perfect square). *)
Lemma heci_disc_is_117 : discQ heci_tr heci_det == 117 # 65536.
Proof. unfold discQ, heci_tr, heci_det. vm_compute. reflexivity. Qed.

(** 117 = 9·13 is not a perfect square (10²=100 < 117 < 121=11²). *)
Lemma rolelimit_117 : role_limit 117.
Proof.
  unfold role_limit, ElementZ. apply not_perfect_square_irrational.
  intros m. apply (not_square_strict m 10 117); lia.
Qed.

(** ★ The Helium CI ground-state energy is a ROLE-LIMIT (irrational): by vein A, He CI has a rational
    eigenvalue ⟺ Δ=117/65536 is a perfect square ⟺ 117 is a perfect square (65536=256²) — and 117 is
    not. This REPLACES the manual "117=9·13 so irrational" remark at HeCIEigenvalue.v:21 with the decider. *)
Theorem heci_eigenvalue_role_limit : ~ has_rat_eig heci_tr heci_det.
Proof.
  rewrite rational_eigenvalue_iff_disc_square. intros [s Hs].
  rewrite heci_disc_is_117 in Hs.            (* Hs : s*s == 117/65536 *)
  apply rolelimit_117. exists (256 * s).
  assert (Hgoal : (256 * s) * (256 * s) == 65536 * (s * s)) by ring.
  rewrite Hgoal, Hs. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Vein A's canonical decider discharges the rationality verdict of two REAL physics eigenvalues:
      (role-limit) Perron–Frobenius / golden φ — Δ=5, irrational (√5);
      (Element)    the [[1,1],[1,1]] foil — Δ=4, rational eigenvalues 0,2;
      (role-limit) Helium CI ground-state energy — Δ=117/65536, irrational (117 not a square);
    each a 0-axiom decision (not a hand remark). Honest: vein A covers exactly the 2×2 / quadratically-
    reducible spectra — a recurring but narrow slice, not all of spectral physics. *)
Theorem physics_eigenvalue_vein_A :
  (~ has_rat_eig golden_tr golden_det)
  /\ has_rat_eig full_tr full_det
  /\ (~ has_rat_eig heci_tr heci_det)
  /\ discQ golden_tr golden_det == inject_Z 5
  /\ discQ heci_tr heci_det == 117 # 65536.
Proof.
  split. exact golden_eigenvalue_role_limit.
  split. exact full_matrix_element.
  split. exact heci_eigenvalue_role_limit.
  split. exact golden_disc_is_5.
  exact heci_disc_is_117.
Qed.
