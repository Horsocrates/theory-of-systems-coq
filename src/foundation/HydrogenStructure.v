(** * HydrogenStructure.v -- Composition + degeneracy + selection rules

    STATUS: 22 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: April 2026

    ===================================================================
    HYDROGEN INTRODUCES THREE NEW E/R/R PATTERNS
    ===================================================================

    The previous three-formula files (SHO, Qubit, Acoustic, Photon) each
    described a SINGLE system.  Hydrogen is the first example where:

      (1) COMPOSITION: two L1 particles (proton, electron) combine
          into a single L2 atom via R-coupling (Coulomb).  The whole
          is NOT the sum of the parts -- binding energy is emergent.

      (2) n^2 DEGENERACY: each energy level n contains n^2 distinct
          angular states (ignoring spin).  Degeneracy is MULTIPLICITY
          of roles at a single E-level.

      (3) SELECTION RULES: not all transitions are allowed. Delta l = +/-1
          is a new kind of R-rule -- a DISCRETE constraint on evolution.

    ===================================================================
    SECTION 1: COMPOSITION L1 x L1 -> L2
    ===================================================================

    Two free particles (proton at rest, electron at rest) have some
    reference energy.  Bound together they have LESS energy -- the
    difference is the binding energy.

    In Hartree units (our Q-framework):
      E_free  = 0     (reference: unbound proton + electron at rest)
      E_bound = -1/2  (bound ground state, from HydrogenThreeFormulas.v)
      E_binding = E_free - E_bound = 1/2  (energy released upon binding)

    In SI units:
      E_binding = (1/2) * m_e * c^2 * alpha^2 = 13.6057 eV
      Measured ionization energy of H:          13.5984 eV
      Agreement:                                0.05%

    ===================================================================
    SECTION 2: n^2 DEGENERACY FROM SO(4)
    ===================================================================

    For the n-th shell, angular quantum numbers satisfy l = 0, 1, ..., n-1,
    and for each l there are 2l+1 values of m.  Total states (spin aside):

      Sum_{l=0}^{n-1} (2l+1) = n^2

    This is a COMBINATORIAL theorem (pure nat arithmetic).

    The physical origin is the hidden SO(4) symmetry of the 1/r potential
    (Bertrand's theorem: only 1/r and r^2 give closed orbits; 1/r has an
    extra conserved quantity, the Laplace-Runge-Lenz vector).

    ===================================================================
    SECTION 3: SELECTION RULES
    ===================================================================

    Electric dipole transitions require Delta l = +/- 1 (photon carries
    angular momentum 1).  This is an R-rule DISCRETE constraint.

    Examples:
      s -> p: ALLOWED    (l = 0 -> 1)
      p -> s: ALLOWED    (l = 1 -> 0)
      p -> d: ALLOWED    (l = 1 -> 2)
      s -> d: FORBIDDEN  (l = 0 -> 2, Delta l = 2)
      s -> s: FORBIDDEN  (l = 0 -> 0, Delta l = 0)

    Selection rules EXPLAIN why the hydrogen spectrum has structure:
    most pairs (n, n') do NOT contribute to observed spectral lines,
    because the lower-angular states dominate in practice.
*)

From Stdlib Require Import QArith Qabs ZArith List PeanoNat Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.HydrogenThreeFormulas.

Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  SECTION 1: COMPOSITION -- L1 x L1 -> L2                          *)
(* ================================================================ *)

(** Reference free energy: proton and electron at rest, far apart. *)
Definition E_free : Q := 0.

(** Bound ground state energy (from HydrogenThreeFormulas.v). *)
Definition E_bound : Q := hydrogen_E 1.

(** Binding energy = free - bound. Positive = stability. *)
Definition E_binding : Q := E_free - E_bound.

(** Bound state lies BELOW the free reference. *)
Theorem bound_below_free : E_bound < E_free.
Proof.
  unfold E_bound, E_free.
  rewrite H_ground. lra.
Qed.

(** Binding energy = 1/2 Hartree = 13.6 eV (in SI). *)
Theorem binding_value : E_binding == 1 # 2.
Proof.
  unfold E_binding, E_free, E_bound.
  rewrite H_ground. lra.
Qed.

(** Binding energy is strictly positive -- composition is STABLE. *)
Theorem binding_positive : 0 < E_binding.
Proof. rewrite binding_value. lra. Qed.

(** EMERGENCE: atom's energy is NOT zero (even though free reference is). *)
Theorem atom_is_emergent : ~ (E_bound == E_free).
Proof.
  intro H. unfold E_bound, E_free in H.
  rewrite H_ground in H. lra.
Qed.

(** The "NEW information" from composition = binding energy. *)
Definition emergent_info : Q := -E_bound.

Theorem emergent_equals_binding : emergent_info == E_binding.
Proof.
  unfold emergent_info, E_binding, E_free.
  lra.
Qed.

(* ================================================================ *)
(*  SECTION 2: n^2 DEGENERACY                                        *)
(* ================================================================ *)

(** Count of angular states at shell n:
    Sum over l = 0, 1, ..., n-1 of (2l + 1). *)
Fixpoint angular_states (n : nat) : nat :=
  match n with
  | 0%nat => 0
  | S k => angular_states k + (2 * k + 1)
  end.

(** Explicit values for first four shells. *)
Theorem degen_n1 : angular_states 1 = 1%nat.
Proof. reflexivity. Qed.

Theorem degen_n2 : angular_states 2 = 4%nat.
Proof. reflexivity. Qed.

Theorem degen_n3 : angular_states 3 = 9%nat.
Proof. reflexivity. Qed.

Theorem degen_n4 : angular_states 4 = 16%nat.
Proof. reflexivity. Qed.

(** THE GENERAL THEOREM: angular_states n = n^2.

    Proof: induction.
      Base:  angular_states 0 = 0 = 0 * 0.
      Step:  angular_states (S k) = angular_states k + (2k + 1)
                                  = k^2 + 2k + 1
                                  = (k + 1)^2. *)
Theorem degeneracy_is_n_squared : forall n : nat,
  angular_states n = (n * n)%nat.
Proof.
  induction n as [|k IHk].
  - reflexivity.
  - simpl. rewrite IHk. lia.
Qed.

(** Corollary: n=10 has 100 states (ignoring spin). *)
Theorem degen_n10 : angular_states 10 = 100%nat.
Proof. rewrite degeneracy_is_n_squared. reflexivity. Qed.

(** Including spin, each shell has 2*n^2 states. *)
Definition total_states_with_spin (n : nat) : nat :=
  (2 * angular_states n)%nat.

Theorem total_states_n2 : total_states_with_spin 2 = 8%nat.
Proof. unfold total_states_with_spin. rewrite degeneracy_is_n_squared. reflexivity. Qed.

Theorem total_states_n3 : total_states_with_spin 3 = 18%nat.
Proof. unfold total_states_with_spin. rewrite degeneracy_is_n_squared. reflexivity. Qed.

(** Prediction: the periodic-table row lengths are 2, 8, 8, 18, 18, 32, 32,
    i.e. 2*n^2 for n = 1, 2, 3, 4 repeated twice. Our theorem gives the
    inner numbers 2, 8, 18, 32. *)
Theorem periodic_row_4 : total_states_with_spin 4 = 32%nat.
Proof. unfold total_states_with_spin. rewrite degeneracy_is_n_squared. reflexivity. Qed.

(* ================================================================ *)
(*  SECTION 3: SELECTION RULES (Delta l = +/- 1)                    *)
(* ================================================================ *)

(** Electric dipole transition is allowed iff |l1 - l2| = 1. *)
Definition allowed_transition (l1 l2 : nat) : bool :=
  orb (Nat.eqb (S l1) l2) (Nat.eqb (S l2) l1).

Theorem s_to_p_allowed : allowed_transition 0 1 = true.
Proof. reflexivity. Qed.

Theorem p_to_s_allowed : allowed_transition 1 0 = true.
Proof. reflexivity. Qed.

Theorem p_to_d_allowed : allowed_transition 1 2 = true.
Proof. reflexivity. Qed.

Theorem d_to_p_allowed : allowed_transition 2 1 = true.
Proof. reflexivity. Qed.

Theorem s_to_s_forbidden : allowed_transition 0 0 = false.
Proof. reflexivity. Qed.

Theorem s_to_d_forbidden : allowed_transition 0 2 = false.
Proof. reflexivity. Qed.

Theorem p_to_p_forbidden : allowed_transition 1 1 = false.
Proof. reflexivity. Qed.

Theorem s_to_f_forbidden : allowed_transition 0 3 = false.
Proof. reflexivity. Qed.

(** Symmetry of allowed transitions: (l1 -> l2) allowed <-> (l2 -> l1) allowed. *)
Theorem allowed_symmetric : forall l1 l2,
  allowed_transition l1 l2 = allowed_transition l2 l1.
Proof.
  intros l1 l2. unfold allowed_transition.
  rewrite Bool.orb_comm. reflexivity.
Qed.

(* ================================================================ *)
(*  GRAND THEOREM                                                    *)
(* ================================================================ *)

Theorem hydrogen_structure_complete :
  (* Composition: binding energy is emergent *)
  E_bound < E_free /\
  E_binding == 1 # 2 /\
  0 < E_binding /\
  (* Degeneracy: n^2 angular states *)
  angular_states 1 = 1%nat /\
  angular_states 2 = 4%nat /\
  angular_states 3 = 9%nat /\
  (forall n, angular_states n = (n * n)%nat) /\
  total_states_with_spin 4 = 32%nat /\
  (* Selection rules *)
  allowed_transition 0 1 = true /\
  allowed_transition 0 2 = false /\
  (forall l1 l2, allowed_transition l1 l2 = allowed_transition l2 l1).
Proof.
  split. { apply bound_below_free. }
  split. { apply binding_value. }
  split. { apply binding_positive. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { apply degeneracy_is_n_squared. }
  split. { apply periodic_row_4. }
  split. { apply s_to_p_allowed. }
  split. { apply s_to_d_forbidden. }
  apply allowed_symmetric.
Qed.

(**
   ==================================================================
   VERIFIABLE PREDICTIONS
   ==================================================================

   (1) IONIZATION ENERGY.
       Prediction: E_binding = 1/2 Hartree = (1/2) m_e c^2 alpha^2
                 = 13.6057 eV.
       Measured:   13.5984 eV.
       Agreement:  0.05%.

   (2) PERIODIC TABLE ROW LENGTHS.
       Prediction (2 n^2):  2, 8, 18, 32.
       Observed row-shell capacities (period sizes are doubled):
         Period 1: 2  (1s only)
         Period 2: 8  (2s + 2p)
         Period 3: 8  (3s + 3p, 3d in 4th period in reality)
         Period 4: 18 (3d + 4s + 4p)
         Period 5: 18 (4d + 5s + 5p)
         Period 6: 32 (4f + 5d + 6s + 6p)
       The numbers 2, 8, 18, 32 appear exactly as (2 n^2).

   (3) SELECTION RULES IN SPECTRA.
       Prediction: only Delta l = +/- 1 transitions produce observable lines.
       Check: in hydrogen emission, s -> s transitions (e.g. 2s -> 1s)
              are FORBIDDEN. Observed: 2s is metastable, lives ~0.15 s
              vs 2p lifetime ~1.6 ns.
       Agreement: qualitative match (orders of magnitude).

   (4) DEGENERACY-LIFTING BY MAGNETIC FIELD.
       Without field: each l-shell contains 2l+1 degenerate m-states.
       With field: Zeeman effect splits them into 2l+1 separate lines
       (our 2l+1 is the "m multiplicity").
       Check: s-shell doesn't split (2(0)+1 = 1), p-shell splits into 3
       (2(1)+1 = 3), d-shell into 5 (2(2)+1 = 5). Observed in
       every Zeeman experiment since 1896.

   ==================================================================
   REUSABLE PATTERNS FOR FUTURE FILES
   ==================================================================

   PATTERN A: Composition.
     L1 + L1 -> L2 via R-coupling
     Binding energy = emergent info at L2
     Applicable: He, H2, any molecule, nuclei.

   PATTERN B: n^2 degeneracy from hidden symmetry.
     Abstract: Sum_{k=0}^{n-1} (2k+1) = n^2
     Physical: SO(4) of 1/r potential via LRL vector
     Applicable: any Coulomb-like system (ions, excitons, muonium).

   PATTERN C: Selection rules as R-rules.
     Discrete predicate allowed : role x role -> bool
     Captures: "only transitions with specific symmetry properties"
     Applicable: nuclear decay, molecular transitions, beta decay.
*)
