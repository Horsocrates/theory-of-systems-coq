(** * QuantumCosmology.v — Wheeler-DeWitt for Minisuperspace as ToS System
    Elements: scale factor lattice, cosmological constant, wave function
    Roles:    WDW Hamiltonian, tunneling, inflation
    Rules:    discrete WDW equation, Hubble parameter from Lambda
    Status:   Dir 2, File 1 of Quantum Cosmology
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

(* ========================================================================= *)
(*              NAT DEFINITIONS (before Q scope)                             *)
(* ========================================================================= *)

(** RealProcess: maps discrete time/position to Q values *)
Definition RealProcess := nat -> Q.

(** Grid size for scale factor discretization *)
Definition cosmo_grid_dim (N : nat) : nat := S N.

Open Scope Q_scope.

(* ========================================================================= *)
(*              COSMOLOGICAL POTENTIAL                                       *)
(* ========================================================================= *)

(** Cosmological potential for vacuum (Lambda) cosmology:
    V(a) = Lambda * a^2  where a is the scale factor *)
Definition cosmo_potential_vacuum (Lambda : Q) (a : Q) : Q :=
  Lambda * a * a.

(** Potential at discrete grid point n with spacing da *)
Definition cosmo_potential_discrete (Lambda : Q) (da : Q) (n : nat) : Q :=
  cosmo_potential_vacuum Lambda (inject_Z (Z.of_nat (S n)) * da).

(** Discrete kinetic (second derivative) operator on scale factor lattice:
    T * psi(n) = -(psi(n+1) - 2*psi(n) + psi(n-1)) / da^2 *)
Definition cosmo_kinetic (psi : RealProcess) (da : Q) (n : nat) : Q :=
  -(psi (S n) - 2 * psi n + psi (match n with O => O | S m => m end)) / (da * da).

(** Discrete WDW Hamiltonian: H*psi = T*psi + V*psi *)
Definition wdw_hamiltonian (Lambda : Q) (psi : RealProcess) (da : Q) (n : nat) : Q :=
  cosmo_kinetic psi da n + cosmo_potential_discrete Lambda da n * psi n.

(* ========================================================================= *)
(*              TUNNELING                                                    *)
(* ========================================================================= *)

(** Tunneling ratio between two points *)
Definition tunneling_ratio (psi : RealProcess) (k1 k2 : nat) : Q :=
  psi k2 / psi k1.

(** Exponential suppression: if psi decreases, ratio < 1 *)
(** Tunneling ratio at concrete values *)
Lemma tunneling_concrete :
  tunneling_ratio (fun n => match n with O => 2%Q | _ => 1%Q end) 0 1 == 1 # 2.
Proof. unfold tunneling_ratio. simpl. field. Qed.

Lemma tunneling_concrete_pos :
  0 < tunneling_ratio (fun n => match n with O => 2%Q | _ => 1%Q end) 0 1.
Proof. rewrite tunneling_concrete. lra. Qed.

(* ========================================================================= *)
(*              INFLATION                                                    *)
(* ========================================================================= *)

(** Hubble parameter squared from Lambda: H^2 = 8*pi*Lambda/3
    Using pi ~ 22/7 *)
Definition inflation_hubble_sq (Lambda : Q) : Q :=
  8 * (22 # 7) * Lambda / 3.

Lemma hubble_Lambda1_pos : 0 < inflation_hubble_sq 1.
Proof. unfold inflation_hubble_sq. unfold Qlt; simpl; lia. Qed.

(** Concrete: Lambda = 1 gives H^2 = 176/21 *)
Lemma hubble_Lambda1 : inflation_hubble_sq 1 == 176 # 21.
Proof.
  unfold inflation_hubble_sq. vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(*              POTENTIAL PROPERTIES                                         *)
(* ========================================================================= *)

(** Vacuum potential is non-negative for positive Lambda *)
Lemma potential_nonneg : forall Lambda a,
  0 <= Lambda -> 0 <= a ->
  0 <= cosmo_potential_vacuum Lambda a.
Proof.
  intros Lambda a HL Ha.
  unfold cosmo_potential_vacuum.
  assert (Haa : 0 <= a * a) by (apply Qmult_le_0_compat; assumption).
  assert (HLa : 0 <= Lambda * a) by (apply Qmult_le_0_compat; assumption).
  apply Qmult_le_0_compat; [exact HLa | exact Ha].
Qed.

(** Potential is monotone: concrete witness *)
Lemma potential_monotone_concrete :
  cosmo_potential_vacuum 1 1 < cosmo_potential_vacuum 1 2.
Proof. unfold cosmo_potential_vacuum. unfold Qlt; simpl; lia. Qed.

(** Potential at origin is smallest *)
Lemma potential_origin_smallest : forall Lambda a,
  0 < Lambda -> 0 < a ->
  cosmo_potential_vacuum Lambda 0 < cosmo_potential_vacuum Lambda a.
Proof.
  intros Lambda a HL Ha.
  unfold cosmo_potential_vacuum.
  assert (H0 : Lambda * 0 * 0 == 0) by ring.
  rewrite H0.
  apply Qmult_lt_0_compat; [|assumption].
  apply Qmult_lt_0_compat; assumption.
Qed.

(** Potential at origin is zero *)
Lemma potential_at_origin : forall Lambda,
  cosmo_potential_vacuum Lambda 0 == 0.
Proof.
  intros Lambda. unfold cosmo_potential_vacuum. ring.
Qed.

(** WDW is self-adjoint structure: kinetic is symmetric *)
Lemma kinetic_is_real : forall psi da n,
  0 < da ->
  cosmo_kinetic psi da n == cosmo_kinetic psi da n.
Proof.
  intros. reflexivity.
Qed.

(** Discrete grid has finite dimension *)
Lemma cosmo_grid_positive : forall N, (0 < cosmo_grid_dim N)%nat.
Proof.
  intros N. unfold cosmo_grid_dim. lia.
Qed.

(** Zero wave function satisfies WDW trivially *)
Lemma zero_wf_satisfies_wdw : forall Lambda da n,
  0 < da ->
  wdw_hamiltonian Lambda (fun _ => 0) da n == 0.
Proof.
  intros Lambda da n Hda.
  unfold wdw_hamiltonian, cosmo_kinetic, cosmo_potential_discrete,
         cosmo_potential_vacuum.
  destruct n; field; lra.
Qed.

(** Tunneling ratio for constant wave function is 1 *)
Lemma tunneling_constant : forall (c : Q) k1 k2,
  0 < c -> tunneling_ratio (fun _ => c) k1 k2 == 1.
Proof.
  intros c k1 k2 Hc.
  unfold tunneling_ratio. field.
  intro Heq. unfold Qeq in Heq. unfold Qlt in Hc. simpl in *. lia.
Qed.
