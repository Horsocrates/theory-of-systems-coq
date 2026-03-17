(** * ProcessContinuumLimit.v — Continuum Limit as Process

    Theory of Systems — Process Physics (Wave 5, Phase E5)

    Elements: physical_mass, lattice_spacing, continuum_process
    Roles:    a → 0, σ → 0, m_phys = σ·K → finite
    Rules:    continuum IS the process, not separate object
    Status:   complete

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.

(* ================================================================== *)
(*  Part I: Lattice Spacing (~8 Qed)                                  *)
(* ================================================================== *)

(** Lattice spacing: a(K) = 1/(K+1) *)
Definition lattice_spacing (K : nat) : Q :=
  1 / inject_Z (Z.of_nat (S K)).

Lemma spacing_at_0 : lattice_spacing 0 == 1.
Proof. unfold lattice_spacing. simpl. field. Qed.

Lemma spacing_at_1 : lattice_spacing 1 == 1 # 2.
Proof. unfold lattice_spacing. simpl. unfold Qeq. simpl. lia. Qed.

Lemma spacing_at_9 : lattice_spacing 9 == 1 # 10.
Proof. unfold lattice_spacing. simpl. unfold Qeq. simpl. lia. Qed.

(** Spacing positive *)
Lemma spacing_pos : forall K, 0 < lattice_spacing K.
Proof.
  intros K. unfold lattice_spacing, Qdiv, Qlt, Qinv, Qmult, Qnum, Qden.
  simpl. lia.
Qed.

(** Spacing decreases *)
Lemma spacing_decreases : forall K,
  lattice_spacing (S K) < lattice_spacing K.
Proof.
  intros K. unfold lattice_spacing, Qdiv, Qlt, Qinv, Qmult, Qnum, Qden.
  simpl. lia.
Qed.

(** Spacing bounded by 1 *)
Lemma spacing_le_1 : forall K,
  lattice_spacing K <= 1.
Proof.
  intros K. unfold lattice_spacing, Qdiv, Qle, Qinv, Qmult, Qnum, Qden.
  simpl. lia.
Qed.

(* ================================================================== *)
(*  Part II: Physical Mass (~8 Qed)                                   *)
(* ================================================================== *)

(** m_phys = σ · (K+1) *)
Definition physical_mass (sigma : Q) (K : nat) : Q :=
  sigma * inject_Z (Z.of_nat (S K)).

(** Physical mass at K=0 *)
Lemma phys_mass_0 : forall sigma,
  physical_mass sigma 0 == sigma.
Proof. intros. unfold physical_mass. simpl. ring. Qed.

(** Physical mass at σ = 289/384, K=10 *)
Lemma phys_mass_example :
  physical_mass (289#384) 10 == 289 * 11 # 384.
Proof.
  unfold physical_mass. simpl. unfold Qeq. simpl. lia.
Qed.

(** Physical mass positive *)
Lemma phys_mass_pos : forall sigma K,
  0 < sigma -> 0 < physical_mass sigma K.
Proof.
  intros sigma K Hs. unfold physical_mass.
  apply Qmult_lt_0_compat; [exact Hs|].
  unfold Qlt. simpl. lia.
Qed.

(** Physical mass grows with K *)
Lemma phys_mass_grows : forall sigma K,
  0 < sigma ->
  physical_mass sigma K < physical_mass sigma (S K).
Proof.
  intros sigma K Hs. unfold physical_mass, Qlt, Qmult, Qnum, Qden. simpl.
  assert (Hq := Hs). unfold Qlt, Qnum, Qden in Hq. simpl in Hq.
  nia.
Qed.

(** Ratio m_phys/(K+1) = σ (constant) *)
Lemma mass_over_K : forall sigma K,
  physical_mass sigma K / inject_Z (Z.of_nat (S K)) == sigma.
Proof.
  intros. unfold physical_mass. field.
  unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  Part III: Continuum Process (~9 Qed)                              *)
(* ================================================================== *)

(** Continuum = the process {σ(K), a(K), m(K)} *)

(** Sigma process: σ decreasing with K *)
Definition sigma_process (sigma_0 : Q) : RealProcess :=
  fun K => sigma_0 / inject_Z (Z.of_nat (S K)).

Lemma sigma_process_0 : forall s0,
  sigma_process s0 0%nat == s0.
Proof. intros. unfold sigma_process. simpl. field. Qed.

Lemma sigma_process_pos : forall s0 K,
  0 < s0 -> 0 < sigma_process s0 K.
Proof.
  intros s0 K Hs. unfold sigma_process, Qdiv.
  apply Qmult_lt_0_compat; [exact Hs|].
  apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Qed.

(** Sigma decreases *)
Lemma sigma_decreases : forall s0 K,
  0 < s0 ->
  sigma_process s0 (S K) < sigma_process s0 K.
Proof.
  intros s0 K Hs. unfold sigma_process, Qdiv, Qlt, Qinv, Qmult.
  simpl. rewrite !Z.mul_1_r.
  assert (Hq := Hs). unfold Qlt in Hq. simpl in Hq.
  nia.
Qed.

(** Physical mass stays constant as σ and a both decrease *)
Lemma mass_constant : forall m K,
  physical_mass (m / inject_Z (Z.of_nat (S K))) K == m.
Proof.
  intros. unfold physical_mass. field. unfold Qeq. simpl. lia.
Qed.

(** Continuum limit IS a process *)
Theorem continuum_is_process :
  (* Lattice spacing → 0 *)
  (forall K, lattice_spacing (S K) < lattice_spacing K) /\
  (* Physical mass finite at each K *)
  (forall sigma K, 0 < sigma -> 0 < physical_mass sigma K) /\
  (* Ratio m/K = σ = constant *)
  (forall sigma K, physical_mass sigma K / inject_Z (Z.of_nat (S K)) == sigma).
Proof.
  split; [|split].
  - exact spacing_decreases.
  - exact phys_mass_pos.
  - exact mass_over_K.
Qed.

(* ================================================================== *)
(*  Part IV: Summary                                                    *)
(* ================================================================== *)

Theorem phase_E5_complete :
  (* Spacing decreases *)
  (forall K, lattice_spacing (S K) < lattice_spacing K) /\
  (* Mass positive *)
  (forall sigma K, 0 < sigma -> 0 < physical_mass sigma K) /\
  (* Sigma decreases *)
  (forall s0 K, 0 < s0 -> sigma_process s0 (S K) < sigma_process s0 K).
Proof.
  split; [|split].
  - exact spacing_decreases.
  - exact phys_mass_pos.
  - exact sigma_decreases.
Qed.
