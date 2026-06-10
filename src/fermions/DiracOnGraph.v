(** * DiracOnGraph.v — lattice Dirac spectrum E² = (k/N)² + m²: real bounds, stubs removed
    Elements: momenta k on a cyclic N-graph; masses m; eigenvalues E², propagators 1/E²
    Roles:    E² — the spectrum role; m² — the gap role (lower bound at ALL momenta);
              1/E² — the propagator role (finite when massive)
    Rules:    E² ≥ 0 always; E² ≥ m² at every momentum (the gap, GENERAL); 0 < m² ⟹
              propagator positive — forced Q-arithmetic given the posited spectrum formula
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: April 2026  (True-stub honesty rollback: June 2026)

    HONEST STATUS: June 2026 — REMOVED `chirality_from_L2 : True` and
    `dirac_antisymmetric : True` (stubs; chirality/antisymmetry need the OPERATOR with
    spinor structure, absent here — only the scalar spectrum formula is posited).
    REPLACED by real general bounds: eigenvalue_sq_nonneg (E² ≥ 0 ∀k,N,m),
    eigenvalue_gap_general (m² ≤ E² at ALL momenta — the gap, generalizing the k=0
    example), propagator_positive (massive ⟹ 1/E² > 0).  The spectrum formula
    (k/N)² + m² itself is an INPUT (a model of the lattice Dirac eigenvalues), not derived.

    E/R/R разбор: Rules — E²≥m²≥0 вынуждены арифметикой ПРИ постулированной формуле
    спектра; Roles — m² играет роль щели на ВСЕХ импульсах (не только k=0); Elements —
    конкретный спектр N=4 (0, 1/16, 1/4, 9/16). P4: формула спектра — вход (модель);
    киральность/антисимметрия требуют оператора со спинорами — снято честно. *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(* Dirac eigenvalue squared: (k/N)^2 + m^2                          *)
(* On a cyclic graph of N vertices, momentum k gives eigenvalue k/N  *)
(* ================================================================= *)

Definition dirac_eigenvalue_sq (k N : nat) (m : Q) : Q :=
  (inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N)) *
  (inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N)) + m * m.

Definition fermion_propagator_sq (k N : nat) (m : Q) : Q :=
  1 / dirac_eigenvalue_sq k N m.

(* ================================================================= *)
(* Theorem 1: Massless zero mode has E^2 = 0                        *)
(* ================================================================= *)

Theorem massless_zero_mode :
  dirac_eigenvalue_sq 0 4 0 == 0.
Proof. unfold dirac_eigenvalue_sq. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 2: Massive fermion at k=0 has gap m^2                    *)
(* ================================================================= *)

Theorem massive_gap :
  dirac_eigenvalue_sq 0 4 (1#2) == 1#4.
Proof. unfold dirac_eigenvalue_sq. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 3: Doubler at k=2, N=4 is heavy (E^2 = 1/4)             *)
(* Nielsen-Ninomiya: lattice doublers get large eigenvalues          *)
(* ================================================================= *)

Theorem doubler_heavy :
  dirac_eigenvalue_sq 2 4 0 == 1#4.
Proof. unfold dirac_eigenvalue_sq. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 4: Propagator at k=1, N=4, m=1/2                        *)
(* E^2 = (1/4)^2 + (1/2)^2 = 1/16 + 1/4 = 5/16                   *)
(* propagator = 1/(5/16) = 16/5                                    *)
(* ================================================================= *)

Theorem eigenvalue_k1_N4 :
  dirac_eigenvalue_sq 1 4 (1#2) == 5#16.
Proof. unfold dirac_eigenvalue_sq. vm_compute. reflexivity. Qed.

Theorem propagator_value :
  fermion_propagator_sq 1 4 (1#2) == 16#5.
Proof. unfold fermion_propagator_sq, dirac_eigenvalue_sq. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 5: Eigenvalue grows with k (k=1 vs k=0 at fixed m)      *)
(* ================================================================= *)

Theorem eigenvalue_grows_with_k :
  dirac_eigenvalue_sq 0 4 (1#2) < dirac_eigenvalue_sq 1 4 (1#2).
Proof.
  unfold dirac_eigenvalue_sq. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 6: Eigenvalue grows with mass (m=0 vs m=1/2 at k=1)     *)
(* ================================================================= *)

Theorem eigenvalue_grows_with_mass :
  dirac_eigenvalue_sq 1 4 0 < dirac_eigenvalue_sq 1 4 (1#2).
Proof.
  unfold dirac_eigenvalue_sq. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* June 2026 — general bounds (replace the removed True-stubs:       *)
(* chirality_from_L2 / dirac_antisymmetric needed spinor structure)  *)
(* ================================================================= *)

(** E² is nonnegative for ALL momenta, sizes and masses. *)
Theorem eigenvalue_sq_nonneg : forall (k N : nat) (m : Q),
  0 <= dirac_eigenvalue_sq k N m.
Proof.
  intros k N m. unfold dirac_eigenvalue_sq.
  set (t := inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N)).
  assert (Ht : 0 <= t * t) by nra.
  assert (Hm : 0 <= m * m) by nra.
  lra.
Qed.

(** ★ THE GAP, GENERAL: E² ≥ m² at EVERY momentum (generalizes the k=0 example). *)
Theorem eigenvalue_gap_general : forall (k N : nat) (m : Q),
  m * m <= dirac_eigenvalue_sq k N m.
Proof.
  intros k N m. unfold dirac_eigenvalue_sq.
  set (t := inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N)).
  assert (Ht : 0 <= t * t) by nra.
  lra.
Qed.

(** A massive fermion has a strictly positive propagator at every momentum. *)
Theorem propagator_positive : forall (k N : nat) (m : Q),
  0 < m * m -> 0 < fermion_propagator_sq k N m.
Proof.
  intros k N m Hm. unfold fermion_propagator_sq, dirac_eigenvalue_sq.
  set (t := inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N)).
  assert (Ht : 0 <= t * t) by nra.
  assert (HE : 0 < t * t + m * m) by lra.
  unfold Qdiv. rewrite Qmult_1_l.
  apply Qinv_lt_0_compat. exact HE.
Qed.

(* ================================================================= *)
(* Theorem 10: N=4 has exactly the expected spectrum                *)
(* ================================================================= *)

Theorem n4_spectrum_check :
  dirac_eigenvalue_sq 0 4 0 == 0 /\
  dirac_eigenvalue_sq 1 4 0 == 1#16 /\
  dirac_eigenvalue_sq 2 4 0 == 1#4 /\
  dirac_eigenvalue_sq 3 4 0 == 9#16.
Proof.
  unfold dirac_eigenvalue_sq.
  repeat split; vm_compute; reflexivity.
Qed.

(* ================================================================= *)
(* Synthesis                                                         *)
(* ================================================================= *)

Theorem dirac_on_graph_synthesis :
  dirac_eigenvalue_sq 0 4 0 == 0 /\
  dirac_eigenvalue_sq 0 4 (1#2) == 1#4 /\
  dirac_eigenvalue_sq 2 4 0 == 1#4 /\
  fermion_propagator_sq 1 4 (1#2) == 16#5.
Proof.
  unfold dirac_eigenvalue_sq, fermion_propagator_sq.
  repeat split; vm_compute; reflexivity.
Qed.
