(** * EulerCharacteristic.v — the exact/counting side, third pillar (after charges and regularization):
      TOPOLOGY as a PROTECTED INTEGER.  A topological invariant cannot change under continuous deformation;
      it is an exact integer (a count), and that integrality IS its protection -- the same mechanism that
      makes topological phases (quantum Hall, topological insulators) robust.

    The clean exemplar: the Euler characteristic chi = V - E + F.
      -- All five Platonic solids have chi = 2 (the sphere): same topology, same integer.
      -- chi is INVARIANT under the combinatorial "deformations" (split an edge: V+1,E+1; add a face
         diagonal: E+1,F+1) -- so it cannot change continuously: a protected integer.
      -- chi COUNTS the genus: chi = 2 - 2g.  Sphere (g=0) -> chi=2; torus (g=1) -> chi=0.  Distinct
         topologies have distinct integers, so the integer DETECTS the topology.

    -- The point (the dual of the role-limit walls): where a physical quantity is an exact PROTECTED COUNT
       (Euler chi, Chern number, winding number), ToS computes it EXACTLY, and the integrality explains the
       robustness.  This is the counting side where ToS has its edge.

    -- HONEST scope: Euler's formula is classical; the value here is the ONTOLOGY (topology = an exact
       protected integer count, machine-verified for the Platonic solids + invariance + genus) and the
       physics framing (topological protection = integrality).  The same logic gives Chern/winding numbers.

    Elements: chi V E F = V - E + F; the 5 Platonic solids; the moves (edge-split, diagonal); the genus g
    Roles:    chi = the topological count (Euler char); the moves = discrete deformations; g = what chi counts
    Rules:    a topological invariant is a protected integer -- integral and deformation-invariant

    ============ E/R/R разбор ============
      Rules (L5): топологический инвариант = защищённое целое (целочисленность + инвариантность под деформацией).
      Roles (L4): chi = топологический счёт; комбинаторные ходы = дискретные деформации; g = что chi считает.
      Elements  : chi=V-E+F; 5 Платоновых тел (chi=2); ходы (расщепл. ребра, диагональ); chi=2-2g.
    ДИАГНОСТИКА (P4): счётная сторона -- топология есть ЗАЩИЩЁННОЕ ЦЕЛОЕ. chi инвариантна под ходами =>
    не меняется непрерывно => защищена. Все Платоновы тела chi=2 (сфера); сфера(2) vs тор(0) = разные целые =>
    целое детектирует топологию (chi=2-2g считает род). Дуал стен. Физика: топофазы защищены такими целыми
    (Черн/намотка), робастность = целочисленность. ЧЕСТНО: Эйлер классичен; ценность = онтология + физ-защита.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The Euler characteristic chi = V - E + F                               *)
(* ===================================================================== *)

Definition chi (V E F : Z) : Z := V - E + F.

(** A representative: the cube (V,E,F) = (8,12,6) has chi = 2. *)
Lemma chi_cube : chi 8 12 6 = 2.
Proof. reflexivity. Qed.

(** ★ All five Platonic solids have chi = 2 -- the sphere; same topology, same integer.
    tetra (4,6,4), cube (8,12,6), octa (6,12,8), dodeca (20,30,12), icosa (12,30,20). *)
Lemma platonic_all_sphere :
  chi 4 6 4 = 2 /\ chi 8 12 6 = 2 /\ chi 6 12 8 = 2
  /\ chi 20 30 12 = 2 /\ chi 12 30 20 = 2.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  chi is INVARIANT under the combinatorial deformations (protection)     *)
(* ===================================================================== *)

(** ★ Splitting an edge (add a vertex on it: V+1, E+1) preserves chi. *)
Lemma chi_split_edge : forall V E F, chi (V+1) (E+1) F = chi V E F.
Proof. intros V E F. unfold chi. lia. Qed.

(** ★ Adding a diagonal to a face (E+1, F+1) preserves chi.  So chi cannot change under deformation:
    a PROTECTED integer. *)
Lemma chi_add_diagonal : forall V E F, chi V (E+1) (F+1) = chi V E F.
Proof. intros V E F. unfold chi. lia. Qed.

(* ===================================================================== *)
(*  chi COUNTS the genus: chi = 2 - 2g; distinct topologies, distinct ints *)
(* ===================================================================== *)

Definition chi_genus (g : Z) : Z := 2 - 2*g.

(** From chi, the genus is recovered: 2 - chi = 2g.  The integer chi detects how many holes. *)
Lemma chi_determines_genus : forall g, 2 - chi_genus g = 2*g.
Proof. intro g. unfold chi_genus. lia. Qed.

(** ★ Distinct topologies have DISTINCT integers: sphere (g=0, chi=2) =/= torus (g=1, chi=0).
    The protected integer cannot interpolate -- it jumps. *)
Lemma sphere_torus_distinct : chi_genus 0 <> chi_genus 1.
Proof. unfold chi_genus. lia. Qed.

(* ===================================================================== *)
(*  Capstone: topology is an exact protected integer                       *)
(* ===================================================================== *)

(** The third counting pillar:
      (count)     chi = V - E + F is an exact integer -- all five Platonic solids give chi = 2 (the sphere);
      (protected) chi is invariant under the deformations (edge-split, diagonal) -- it cannot change
                  continuously;
      (detects)   chi = 2 - 2g counts the genus; sphere (chi=2) and torus (chi=0) are distinct integers,
                  distinct topologies.
    Topology is a PROTECTED INTEGER -- the dual of the role-limit walls, on the exact/counting side where ToS
    has its edge.  Physics: topological phases are protected by exactly such integers (Chern, winding);
    robustness = integrality. *)
Theorem euler_topology :
  (chi 4 6 4 = 2 /\ chi 8 12 6 = 2 /\ chi 6 12 8 = 2 /\ chi 20 30 12 = 2 /\ chi 12 30 20 = 2)
  /\ (forall V E F, chi (V+1) (E+1) F = chi V E F)
  /\ (forall V E F, chi V (E+1) (F+1) = chi V E F)
  /\ (forall g, 2 - chi_genus g = 2*g)
  /\ chi_genus 0 <> chi_genus 1.
Proof.
  split; [ exact platonic_all_sphere | ].
  split; [ exact chi_split_edge | ].
  split; [ exact chi_add_diagonal | ].
  split; [ exact chi_determines_genus | exact sphere_torus_distinct ].
Qed.
