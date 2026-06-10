(** * EulerCharProtectedInteger.v — the Euler characteristic is ONE PROTECTED INTEGER computed FOUR ways
       that coincide — curvature (Gauss–Bonnet, geometry), combinatorics (V−E+F), homology (Betti
       b0−b1+b2), and the Dirac index — across geometry / topology / spectral. The Element-side face of
       "a topological invariant is a protected integer" (candidate 9th thread). Sphere χ=2, torus χ=0.

    THE OBSERVATION (a candidate 9th thread: topological invariant = protected integer = Element).
    The Euler characteristic χ is computed in the repo by FOUR genuinely different routes, in different
    clusters, with no file connecting them:
      - CURVATURE (geometry/DiscreteGaussBonnet.v): the total angular defect / π = 2·χ (discrete
        Gauss–Bonnet / Descartes) — for every Platonic solid Σδ/π = 4, so χ = 2;
      - COMBINATORICS: χ = V − E + F (`euler`);
      - HOMOLOGY (stdlib/H1_IndexTheorem.v, SimplicialHomology.v): χ = b0 − b1 + b2 (alternating sum of
        Betti numbers);
      - DIRAC INDEX (stdlib/H1_IndexTheorem.v): the index-theorem identification "analytic index = χ".
    For the 2-sphere all four give the integer 2; for the torus the combinatorial and Betti routes give 0.
    Geometry (curvature), topology (homology), and the spectral index AGREE on ONE integer.

    THE PROTECTED-INTEGER POINT.
    The continuum curvature (π-dependent — π is a role-limit) integrates to an INTEGER (χ ∈ ℤ, Element).
    The integrality IS the topological protection / quantization: χ cannot change under continuous
    deformation, so it distinguishes the topologies (sphere 2 ≠ torus 0). This is the geometry↔topology↔
    spectral face of the recurring thread "a topological invariant (Euler χ, Chern number, winding,
    instanton/monopole charge) is a protected integer = the Element side of the finitization boundary".

    WHAT IS NEW / HONEST SCALE.
    Gauss–Bonnet, the Euler–Poincaré V−E+F = Σ(−1)ⁱbᵢ, the genus formula, and the index theorem are all
    classical, and each route is already in the repo. NEW (synthesis+observation, machine-checked): the
    LITERAL coincidence of the four routes on one protected integer, tying the geometry curvature thread
    to the homology/index thread. Honest: the "analytic index" here is the index-theorem IDENTIFICATION
    (`index_from_chain := euler_char` in H1_IndexTheorem), not derived from actual Dirac zero modes
    (those live in H1_LatticeDirac); π itself is a role-limit (only defect/π is rational). The broader
    Chern/winding instances are referenced, not all formalized here. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : число Эйлера χ (защищённое целое ∈ ℤ); четыре вычисления — угловой дефект (Gauss–Bonnet,
                 кривизна), V−E+F (комбинаторика), b0−b1+b2 (Betti, гомологии), индекс Дирака; инстансы —
                 сфера (χ=2, 5 платоновых тел), тор (χ=0).
      Roles    : χ = топологический инвариант = Element (целое, дискретное); кривизна (континуум, π-зависимая)
                 = role-limit, но её интеграл = целое; «защищённость» = целочисленность (нельзя изменить непрерывно).
      Rules    : Gauss–Bonnet Σδ/π = 2χ (геометрия); V−E+F = χ (комбинаторика); b0−b1+b2 = χ (гомологии);
                 index = χ (теорема индекса); все совпадают на целом (сфера 2, тор 0).
      ДИАГНОСТИКА (P4): топологический инвариант = ЗАЩИЩЁННОЕ ЦЕЛОЕ = Element-сторона: континуум-кривизна
      (role-limit, π) интегрируется в ЦЕЛОЕ (Element) — целочисленность ЕСТЬ топологическая защита/квантование;
      χ не меняется при непрерывной деформации (сфера 2 ≠ тор 0). Геометрия↔топология↔спектр сходятся на одном
      целом. ЧЕСТНО: унификация совпадающих вычислений (index определён=χ, не выведен из реальных нуль-мод Дирака;
      π role-limit; Черн/winding referenced, не формализованы здесь). Уровень: `синтез+наблюдение`.

    STATUS: 4 Qed, 0 Admitted, 0 axioms  (imports geometry.DiscreteGaussBonnet; homology/index side replicated + cited)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From ToS Require Import geometry.DiscreteGaussBonnet.   (* total_defect_pi, euler, tri/sq/pent_angle, *_defect, gauss_bonnet_tetra *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  The homology / index side (replicated from stdlib/H1_IndexTheorem.v)   *)
(* ===================================================================== *)

(** χ as the alternating sum of Betti numbers (= H1_IndexTheorem.euler_betti / SimplicialHomology). *)
Definition euler_betti (b0 b1 b2 : nat) : Z := (Z.of_nat b0 - Z.of_nat b1 + Z.of_nat b2)%Z.

(** χ as the analytic index of the Dirac operator — the index-theorem identification
    (= H1_IndexTheorem.index_from_chain := euler_char). *)
Definition index_from_chain (V E F : Z) : Z := euler V E F.

(** Genus from χ via χ = 2 − 2g (= H1_IndexTheorem.genus_from_euler). *)
Definition genus_from_euler (chi : Z) : Q := 1 - inject_Z chi / 2.

(* ===================================================================== *)
(*  1. The 2-sphere: ONE protected integer χ=2, computed FOUR ways         *)
(* ===================================================================== *)

(** ★★ The Euler characteristic of the 2-sphere is the protected integer 2, computed by FOUR routes that
    coincide: curvature (Gauss–Bonnet angular defect = 2χ), combinatorics (V−E+F), homology (Betti
    b0−b1+b2), and the Dirac index. Geometry, topology, and the spectral index agree on one integer. *)
Theorem sphere_chi_four_ways :
  total_defect_pi 4 3 tri_angle == 2 * inject_Z (euler 4 6 4)   (* curvature (Gauss–Bonnet) = 2χ *)
  /\ (euler 4 6 4 = 2)%Z                                        (* combinatorics V−E+F *)
  /\ (euler_betti 1 0 1 = 2)%Z                                  (* homology Betti b0−b1+b2 *)
  /\ (index_from_chain 4 6 4 = 2)%Z.                            (* Dirac index = χ *)
Proof.
  split. exact gauss_bonnet_tetra.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  unfold index_from_chain, euler. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. The torus: a DIFFERENT protected integer χ=0                        *)
(* ===================================================================== *)

(** The torus has χ=0 (combinatorial mesh + Betti), distinct from the sphere's 2 — the integer that
    cannot change under continuous deformation distinguishes the two topologies; genus 1 vs 0. *)
Theorem torus_chi_zero :
  (euler 7 21 14 = 0)%Z /\ (euler_betti 1 2 1 = 0)%Z
  /\ genus_from_euler 2 == 0 /\ genus_from_euler 0 == 1.
Proof.
  split. { unfold euler. vm_compute. reflexivity. }
  split. { unfold euler_betti. vm_compute. reflexivity. }
  split; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  3. All five Platonic solids realize the sphere's protected integer 2   *)
(* ===================================================================== *)

(** All five Platonic solids give the SAME protected integer χ=2 via curvature — five different rational
    angular-defect sums (Σδ/π = 4 = 2χ), one integer. *)
Theorem all_platonic_chi_2 :
  total_defect_pi 4 3 tri_angle == 4 /\ total_defect_pi 8 3 sq_angle == 4
  /\ total_defect_pi 6 4 tri_angle == 4 /\ total_defect_pi 20 3 pent_angle == 4
  /\ total_defect_pi 12 5 tri_angle == 4.
Proof.
  split. exact tetra_defect.
  split. exact cube_defect.
  split. exact octa_defect.
  split. exact dodeca_defect.
  exact icosa_defect.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The Euler characteristic is a PROTECTED INTEGER = the Element-side topological invariant:
      (sphere) χ=2 via curvature (Gauss–Bonnet) = combinatorics (V−E+F) = homology (Betti) = Dirac index;
      (torus)  χ=0 via combinatorics = homology — a DIFFERENT integer (genus 1 vs 0);
      (Platonic) all five solids give the sphere's χ=2 (five rational defect sums, one integer).
    The continuum curvature (π-dependent role-limit) integrates to an INTEGER (Element) — the integrality
    IS the topological protection/quantization: χ cannot change under continuous deformation. The
    geometry↔topology↔spectral face of "topological invariant = protected integer = Element". *)
Theorem euler_char_protected_integer :
  (total_defect_pi 4 3 tri_angle == 2 * inject_Z (euler 4 6 4))
  /\ (euler 4 6 4 = 2)%Z /\ (euler_betti 1 0 1 = 2)%Z /\ (index_from_chain 4 6 4 = 2)%Z
  /\ (euler 7 21 14 = 0)%Z /\ (euler_betti 1 2 1 = 0)%Z.
Proof.
  split. exact gauss_bonnet_tetra.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { unfold index_from_chain, euler. vm_compute. reflexivity. }
  split. { unfold euler. vm_compute. reflexivity. }
  unfold euler_betti. vm_compute. reflexivity.
Qed.
