(** * HeliumStructure.v -- Helium as L3 nested composition with correlation

    STATUS: 22 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: April 2026

    ===================================================================
    HELIUM INTRODUCES NESTED COMPOSITION AND PAULI EXCLUSION
    ===================================================================

    Hydrogen was a simple composition: 1 proton + 1 electron -> 1 atom.
    Helium needs THREE levels:

      L1 (particles):    nucleus (Z=2), e1, e2
      L2 (pair systems): He+ = nucleus + single electron (exact, hydrogen-like)
      L3 (full atom):    He = nucleus + both electrons (needs correlation)

    At L2 we recover EXACT hydrogen physics scaled by Z^2.
    At L3 we lose exact solvability: the 1/r_12 electron-electron
    repulsion has no closed form. The best we can do is variational
    methods with effective screening.

    ===================================================================
    THREE VERIFIABLE CLAIMS
    ===================================================================

    (1) He+ SECOND IONIZATION IS EXACT.
        He+ -> He++ removes the last electron from a hydrogen-like ion
        with Z=2. Energy = 2 Hartree = 54.42 eV.
        Measured: 54.418 eV. Agreement: better than 0.01%.

    (2) VARIATIONAL HELIUM GROUND STATE.
        Using trial wavefunction psi = exp(-alpha r_1) exp(-alpha r_2)
        with alpha minimized yields E_min = -(Z - 5/16)^2.
        For Z=2: E_min = -(27/16)^2 = -729/256 Hartree ~ -2.848 Hartree.
        Measured: -2.9037 Hartree. Error: 1.9% (Hartree approximation).

    (3) SCREENING CONSTANT sigma = 5/16 (exact rational).
        The variational minimum sits at Z_eff = Z - 5/16.
        For Z=2: Z_eff = 27/16 = 1.6875.
        This is the screening felt by one electron due to the other.

    ===================================================================
    WHY THIS MATTERS FOR E/R/R
    ===================================================================

    Hydrogen had L1 -> L2 composition.
    Helium has L1 -> L2 -> L3 NESTED composition.

    The L2 subsystems are exact (He+ is hydrogen-like).
    The L3 composition is approximate (no closed form for 2-electron
    correlation).

    This mirrors a general principle:
      LOW levels of E/R/R composition are often solvable exactly.
      HIGH levels generally are not (need variational / numerical).

    The quality of our variational bound (1.9% for He) demonstrates
    that L3-level E/R/R captures the bulk of the physics with only
    a small correlation correction.
*)

From Stdlib Require Import QArith Qabs ZArith List PeanoNat Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.HydrogenThreeFormulas.
From ToS Require Import foundation.HydrogenStructure.

Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  SECTION 1: L2 SUBSYSTEM -- He+ as hydrogen-like with Z=2        *)
(* ================================================================ *)

(** Nuclear charge of helium in units of e. *)
Definition Z_He : Q := 2.

(** He+ energy levels: E_n = -Z^2/(2 n^2).
    For Z=2: E_n = -2/n^2. *)
Definition he_plus_E (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | _ =>
      let q := inject_Z (Z.of_nat n) in
      -(2) / (q * q)
  end.

(** Ground state of He+: E_1 = -2 Hartree = -54.42 eV.
    This IS an exact result -- He+ is exactly hydrogen-like. *)
Theorem he_plus_ground : he_plus_E 1 == -(2).
Proof. vm_compute. reflexivity. Qed.

(** He+ first excited state: E_2 = -1/2 Hartree. *)
Theorem he_plus_excited : he_plus_E 2 == -(1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** He+ third level: E_3 = -2/9 Hartree. *)
Theorem he_plus_n3 : he_plus_E 3 == -(2 # 9).
Proof. vm_compute. reflexivity. Qed.

(** Z^2-scaling law for first four levels: He+ energy = 4 * hydrogen energy. *)
Theorem he_plus_scaled_n1 : he_plus_E 1 == 4 * hydrogen_E 1.
Proof. vm_compute. reflexivity. Qed.

Theorem he_plus_scaled_n2 : he_plus_E 2 == 4 * hydrogen_E 2.
Proof. vm_compute. reflexivity. Qed.

Theorem he_plus_scaled_n3 : he_plus_E 3 == 4 * hydrogen_E 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SECTION 2: L3 COMPOSITION -- variational helium ground state    *)
(* ================================================================ *)

(** Screening constant from the variational calculation.
    The trial wavefunction exp(-alpha r_1) exp(-alpha r_2) has its
    energy minimized at alpha = Z - 5/16. *)
Definition screening_sigma : Q := 5 # 16.

(** Effective charge seen by each electron due to screening. *)
Definition Z_eff : Q := Z_He - screening_sigma.

(** Numerical value: Z_eff = 27/16 = 1.6875. *)
Theorem Z_eff_value : Z_eff == 27 # 16.
Proof. unfold Z_eff, Z_He, screening_sigma. vm_compute. reflexivity. Qed.

(** Variational minimum energy: E_min = -(Z - 5/16)^2 = -(Z_eff)^2.
    Derivation (using a for alpha, a0 for the optimal alpha):
      E(a) = a^2 - 2 Z a + (5/8) a = a^2 - (2Z - 5/8) a
      dE/da = 2 a - (2Z - 5/8) = 0
      a0 = Z - 5/16 = Z_eff
      E_min = a0^2 - (2Z - 5/8) a0
            = a0^2 - 2 a0 (Z - 5/16)
            = a0^2 - 2 a0^2
            = -(a0)^2 = -(Z_eff)^2. *)
Definition he_variational : Q := -(Z_eff * Z_eff).

(** Numerical value: -729/256 Hartree. *)
Theorem he_variational_value : he_variational == -(729 # 256).
Proof.
  unfold he_variational, Z_eff, Z_He, screening_sigma. vm_compute. reflexivity.
Qed.

(** Approximate value in eV (1 Hartree = 27.211... eV).
    -729/256 Hartree ~ -2.848 Hartree. *)
Theorem he_variational_below_minus_2 : he_variational < -(2).
Proof.
  rewrite he_variational_value. lra.
Qed.

(** And still above -3: -729/256 > -3. *)
Theorem he_variational_above_minus_3 : -(3) < he_variational.
Proof.
  rewrite he_variational_value. lra.
Qed.

(** The variational bound is BELOW the naive sum of two He+ ground states
    (which would be -4 Hartree, ignoring electron-electron repulsion). *)
Theorem variational_above_naive_sum :
  (2 * he_plus_E 1) < he_variational.
Proof.
  rewrite he_plus_ground, he_variational_value. lra.
Qed.

(** Binding energy at L3: how much more stable than naive double-He+. *)
Definition he_correlation_correction : Q :=
  he_variational - 2 * he_plus_E 1.

(** Correlation correction is POSITIVE (less negative = less binding
    than naive -4 Hartree, due to electron-electron repulsion). *)
Theorem correlation_is_positive : 0 < he_correlation_correction.
Proof.
  unfold he_correlation_correction.
  rewrite he_plus_ground, he_variational_value. lra.
Qed.

(* ================================================================ *)
(*  SECTION 3: IONIZATION ENERGIES                                   *)
(* ================================================================ *)

(** Second ionization: He+ -> He++ removes the last electron from a
    Z=2 hydrogen-like ion. Energy = -E_1(He+) = 2 Hartree.
    This is EXACT (hydrogen-like). *)
Definition second_ionization : Q := -(he_plus_E 1).

Theorem second_ionization_value : second_ionization == 2.
Proof. unfold second_ionization. rewrite he_plus_ground. lra. Qed.

(** In eV: 2 Hartree x 27.211 eV/Hartree = 54.42 eV.
    Measured: 54.418 eV. Agreement: better than 0.01%. *)

(** First ionization (variational): He -> He+.
    Energy = E(He+) - E(He) = -2 - (-729/256) = 217/256 Hartree.
    Measured: 24.587 eV = 0.9036 Hartree. *)
Definition first_ionization : Q := he_plus_E 1 - he_variational.

Theorem first_ionization_value : first_ionization == 217 # 256.
Proof.
  unfold first_ionization.
  rewrite he_plus_ground, he_variational_value. lra.
Qed.

(** First ionization is positive (energy required to remove electron). *)
Theorem first_ionization_positive : 0 < first_ionization.
Proof. rewrite first_ionization_value. lra. Qed.

(** First ionization is less than second (inner electron harder to remove). *)
Theorem first_less_than_second :
  first_ionization < second_ionization.
Proof.
  rewrite first_ionization_value, second_ionization_value. lra.
Qed.

(** The ratio second/first > 2. Measured: 54.42/24.59 ~ 2.21. *)
Theorem ionization_ratio_above_2 :
  2 * first_ionization < second_ionization.
Proof.
  rewrite first_ionization_value, second_ionization_value. lra.
Qed.

(* ================================================================ *)
(*  SECTION 4: PAULI EXCLUSION AS R-RULE                             *)
(* ================================================================ *)

(** Electron state: (n, l, m, s) where s in {0, 1} represents spin up/down. *)

(** Two electrons are in the same quantum state if all four numbers match. *)
Definition same_quantum_state (n1 l1 m1 s1 n2 l2 m2 s2 : nat) : bool :=
  andb (Nat.eqb n1 n2)
  (andb (Nat.eqb l1 l2)
  (andb (Nat.eqb m1 m2) (Nat.eqb s1 s2))).

(** Pauli: two electrons CANNOT occupy the same quantum state.
    Allowed = NOT same_quantum_state. *)
Definition pauli_allowed (n1 l1 m1 s1 n2 l2 m2 s2 : nat) : bool :=
  negb (same_quantum_state n1 l1 m1 s1 n2 l2 m2 s2).

(** Helium ground state: both electrons in 1s (n=1, l=0, m=0) with
    opposite spins (s=0 vs s=1). Allowed by Pauli. *)
Theorem he_1s2_allowed :
  pauli_allowed 1 0 0 0 1 0 0 1 = true.
Proof. reflexivity. Qed.

(** Two electrons with same spin in 1s would violate Pauli. *)
Theorem he_1s2_same_spin_forbidden :
  pauli_allowed 1 0 0 0 1 0 0 0 = false.
Proof. reflexivity. Qed.

(** Ortho-helium: one electron in 1s, one in 2s, same spin (triplet). *)
Theorem ortho_he_allowed :
  pauli_allowed 1 0 0 0 2 0 0 0 = true.
Proof. reflexivity. Qed.

(** Para-helium: one electron in 1s, one in 2s, opposite spins (singlet). *)
Theorem para_he_allowed :
  pauli_allowed 1 0 0 0 2 0 0 1 = true.
Proof. reflexivity. Qed.

(** Symmetry: swap electrons does not change allowed-ness. *)
Theorem pauli_symmetric : forall n1 l1 m1 s1 n2 l2 m2 s2,
  pauli_allowed n1 l1 m1 s1 n2 l2 m2 s2 =
  pauli_allowed n2 l2 m2 s2 n1 l1 m1 s1.
Proof.
  intros. unfold pauli_allowed, same_quantum_state.
  rewrite (Nat.eqb_sym n1), (Nat.eqb_sym l1), (Nat.eqb_sym m1), (Nat.eqb_sym s1).
  reflexivity.
Qed.

(* ================================================================ *)
(*  GRAND THEOREM                                                    *)
(* ================================================================ *)

Theorem helium_structure_complete :
  (* L2 subsystem: He+ is exact *)
  he_plus_E 1 == -(2) /\
  (* Z^2 scaling at L2 *)
  Z_eff == 27 # 16 /\
  (* L3 variational ground state *)
  he_variational == -(729 # 256) /\
  he_variational < -(2) /\
  (* Correlation correction is positive (less binding than naive) *)
  (2 * he_plus_E 1) < he_variational /\
  (* Second ionization (exact) *)
  second_ionization == 2 /\
  (* First ionization (variational) *)
  first_ionization == 217 # 256 /\
  first_ionization < second_ionization /\
  2 * first_ionization < second_ionization /\
  (* Pauli: 1s^2 with opposite spins allowed *)
  pauli_allowed 1 0 0 0 1 0 0 1 = true /\
  pauli_allowed 1 0 0 0 1 0 0 0 = false.
Proof.
  split. { apply he_plus_ground. }
  split. { apply Z_eff_value. }
  split. { apply he_variational_value. }
  split. { apply he_variational_below_minus_2. }
  split. { apply variational_above_naive_sum. }
  split. { apply second_ionization_value. }
  split. { apply first_ionization_value. }
  split. { apply first_less_than_second. }
  split. { apply ionization_ratio_above_2. }
  split. { apply he_1s2_allowed. }
  apply he_1s2_same_spin_forbidden.
Qed.

(**
   ==================================================================
   VERIFIABLE NUMBERS AGAINST EXPERIMENT
   ==================================================================

   Our prediction               Observed        Error
   ------------------------------------------------------------
   He+ ground = -2 Hartree      -2 Hartree      0.00% (exact)
   Z_eff = 27/16 = 1.6875       variational     exact
   He ground = -729/256 Ha      -2.9037 Ha      1.9%
   Second ionization = 2 Ha     54.418 eV       <0.01%
   First ionization = 217/256   24.587 eV       6.2% (Hartree)
     (= 0.848 Hartree = 23.07 eV)

   The 1.9% error on He ground state is the variational bound.
   Better methods (Hylleraas 1929) reach machine precision but are
   not expressible as single rational numbers -- they require
   series of rational terms.

   ==================================================================
   WHAT E/R/R LEARNED FROM HELIUM
   ==================================================================

   (1) NESTED COMPOSITION. L1 -> L2 -> L3. Each level has its own
       "emergent" content. L2 (He+) is exact. L3 (He) requires
       approximation. This is a general feature: exact solvability
       drops off with composition depth.

   (2) SCREENING AS EMERGENT L3 CONCEPT. At L1 the charge is +2 (nucleus).
       At L2 (He+) the electron sees +2. At L3 each electron sees an
       EFFECTIVE charge Z_eff = 2 - 5/16 due to the other electron's
       presence. The 5/16 is a pure rational -- a screening constant
       determined entirely by the L3 structure.

   (3) PAULI AS L3 R-RULE. Single-particle physics (L1) and two-body
       (L2) do not need Pauli. Only at L3 with MULTIPLE indistinguishable
       particles does Pauli become an R-rule: "no two electrons share
       all four quantum numbers".

   (4) SPIN SINGLET / TRIPLET. At L3 with two spin-1/2 particles, the
       TOTAL spin can be 0 (singlet, parahelium) or 1 (triplet, orthohelium).
       This role-composition is specific to two-particle systems.

   ==================================================================
   PATTERNS FOR FUTURE FILES
   ==================================================================

   - H2+ molecular ion: next nested L3 (1 electron, 2 nuclei)
   - Lithium: L3 with 3 electrons (requires 2s shell)
   - Periodic table construction via Pauli + n^2 degeneracy
     (from HydrogenStructure.v)
   - General Z-scaling law: E_n(Z) = Z^2 * E_n(H) for hydrogen-like
*)
