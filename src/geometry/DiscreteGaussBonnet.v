(** * DiscreteGaussBonnet.v — discrete Gauss–Bonnet (Descartes) for Platonic solids
    Elements: vertex/edge/face counts (ℤ); angle defects in units of π (ℚ)
    Roles:    curvature as the angular-DEFECT rule (Regge); Euler char as topology-role
    Rules:    defect = 2π − Σ(face angles); Σ(defects) = 2π·χ (Descartes / Gauss–Bonnet)
    STATUS:   9 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The ToS Element-side of curvature: Regge / discrete Gauss–Bonnet. The angular
    defect at a vertex where m faces (each with interior angle α) meet is
        δ = 2π − m·α.
    Measured IN UNITS OF π, every Platonic defect is RATIONAL (face angles are
    rational multiples of π: triangle π/3, square π/2, pentagon 3π/5), and the
    TOTAL defect over all vertices equals 2π·χ with χ = V−E+F = 2 (Descartes' "total
    angular defect = 4π" = the discrete Gauss–Bonnet theorem). So the curvature
    content is Element-side (rational in units of π) and equals the integer
    topological invariant 2χ.

    HONEST SCOPE: π itself is a continuum role-limit; the individual face angles
    (π/3, …) are NOT rational. What IS Element-side and proven here: each defect
    DIVIDED BY π is rational, their SUM = 4 = 2·χ, and χ ∈ ℤ. Curvature-as-defect
    is the discrete (Regge) replacement for the smooth curvature tensor (role-limit).

    RELATED (existing repo): the smooth-form Gauss–Bonnet Σδ = 4π·χ via Betti numbers
    is in stdlib/SimplicialHomology.v; Regge deficits for triangulations in
    stdlib/ReggeDictionary.v and process/ProcessRegge.v. This file is the unified
    Element-side statement for all five Platonic solids (rational defect = 2χ).
*)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Open Scope Q_scope.

(* face interior angle, measured in units of π *)
Definition tri_angle  : Q := 1 # 3.   (* equilateral triangle: π/3   *)
Definition sq_angle   : Q := 1 # 2.   (* square:               π/2   *)
Definition pent_angle : Q := 3 # 5.   (* regular pentagon:     3π/5  *)

(* angular defect at a vertex (in units of π) where m faces of interior angle a meet:
   δ/π = 2 − m·a *)
Definition vertex_defect_pi (m : nat) (a : Q) : Q :=
  2 - inject_Z (Z.of_nat m) * a.

(* total angular defect (in units of π) over V vertices *)
Definition total_defect_pi (V m : nat) (a : Q) : Q :=
  inject_Z (Z.of_nat V) * vertex_defect_pi m a.

(* Euler characteristic V − E + F *)
Definition euler (V E F : Z) : Z := V - E + F.

(* ===================== total angular defect = 4 (= 4π) for each solid ==== *)
(* tetrahedron: V=4, 3 triangles/vertex *)
Theorem tetra_defect  : total_defect_pi 4 3 tri_angle  == 4.
Proof. vm_compute. reflexivity. Qed.

(* cube: V=8, 3 squares/vertex *)
Theorem cube_defect   : total_defect_pi 8 3 sq_angle   == 4.
Proof. vm_compute. reflexivity. Qed.

(* octahedron: V=6, 4 triangles/vertex *)
Theorem octa_defect   : total_defect_pi 6 4 tri_angle  == 4.
Proof. vm_compute. reflexivity. Qed.

(* dodecahedron: V=20, 3 pentagons/vertex *)
Theorem dodeca_defect : total_defect_pi 20 3 pent_angle == 4.
Proof. vm_compute. reflexivity. Qed.

(* icosahedron: V=12, 5 triangles/vertex *)
Theorem icosa_defect  : total_defect_pi 12 5 tri_angle == 4.
Proof. vm_compute. reflexivity. Qed.

(* ===================== Euler characteristic = 2 for each ===================== *)
Theorem platonic_euler :
  (euler 4 6 4 = 2)%Z  /\ (euler 8 12 6 = 2)%Z /\ (euler 6 12 8 = 2)%Z /\
  (euler 20 30 12 = 2)%Z /\ (euler 12 30 20 = 2)%Z.
Proof. unfold euler. repeat split; reflexivity. Qed.

(* ===================== discrete Gauss–Bonnet: total defect = 2π·χ ========= *)
(* general bridge: if Σδ/π = 4 and χ = 2, then Σδ/π = 2·χ *)
Theorem gauss_bonnet_general : forall (Vn m : nat) (a : Q) (V E F : Z),
  total_defect_pi Vn m a == 4 -> (euler V E F = 2)%Z ->
  total_defect_pi Vn m a == 2 * inject_Z (euler V E F).
Proof.
  intros Vn m a V E F Hd He. rewrite Hd, He. vm_compute. reflexivity.
Qed.

(* capstone for the tetrahedron: Σ(angular defect)/π = 2·χ *)
Theorem gauss_bonnet_tetra :
  total_defect_pi 4 3 tri_angle == 2 * inject_Z (euler 4 6 4).
Proof. apply gauss_bonnet_general; [ apply tetra_defect | reflexivity ]. Qed.

(* the curvature content is Element-side: defect/π is rational and the SUM is the
   integer invariant 2χ — independent of the (role-limit) value of π itself. *)
Theorem defect_sum_is_rational : total_defect_pi 4 3 tri_angle == 4 # 1.
Proof. vm_compute. reflexivity. Qed.
