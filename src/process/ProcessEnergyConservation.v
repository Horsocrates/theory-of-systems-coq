(** * ProcessEnergyConservation.v — Energy conservation under discrete evolution
      (Tier 2, Part VI → physics)

    Elements: rational amplitudes ψ_k; diagonal Hamiltonian Ĥ (levels e_i); time steps n
    Roles:    Ĥ = Hamiltonian (energy operator); E(ψ) = energy (observable);
              an energy-preserving U = symmetry (commutes with Ĥ); ψ_n = state in time
    Rules:    E(ψ) = ⟨ψ|Ĥ|ψ⟩; an energy-preserving step ⟹ E(ψ_n) = E(ψ_0) for all n;
              the sign-flip diag(1,−1) preserves the energy of a diagonal Ĥ (and the norm)

    The second conservation law of quantum mechanics (after probability): the energy
    E(ψ) = ⟨ψ|Ĥ|ψ⟩ is conserved under Schrödinger evolution because the propagator
    commutes with Ĥ. The constructive P4 core: when a discrete step U preserves the
    energy functional (⟨Uψ|Ĥ|Uψ⟩ = ⟨ψ|Ĥ|ψ⟩ — the discrete analogue of [U,Ĥ] = 0 with
    unitarity), the energy is conserved at every step, E(ψ_n) = E(ψ_0), by induction.
    We exhibit a concrete witness: the sign-flip diag(1,−1) preserves the energy of any
    diagonal Hamiltonian Hdiag(e0,e1) for ALL states (and is also an isometry), so the
    evolution it generates conserves both probability and energy for all n. Over ℚ, 0 axioms.

    HONEST FRONTIER (P4 boundary): the continuous symmetry / exact Noether statement for
    e^{−iĤt} is a role-limit; the general "isometry + commutes-with-Ĥ ⟹ energy conserved"
    (via the transpose adjoint and UᵀĤU = Ĥ) and a Hamiltonian-derived unitary are next.

    ============ E/R/R разбор ============
      Rules (L5): E(ψ)=⟨ψ|Ĥ|ψ⟩; шаг сохраняет энергию ⟹ E(ψ_n)=E(ψ_0) ∀n; sign-flip
                  diag(1,−1) сохраняет энергию диагонального Ĥ (и норму) ∀ψ.
      Roles (L4): Ĥ=роль-гамильтониан; E(ψ)=роль-энергия (наблюдаемая); U сохраняющий E =
                  роль-симметрия (коммутирует с Ĥ); ψ_n=роль-состояние во времени.
      Elements  : рациональные ψ_k, диагональный Ĥ (уровни e_i), шаги n, унитарный U (L1+P4).
    ДИАГНОСТИКА: дискретное энергосохранение — процессный факт (0 акс); непрерывная
    симметрия / теорема Нётер для e^{−iĤt} = роль-предел, P4-граница.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessSchrodingerEvolution. (* evolve, Isometry *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Energy functional E(ψ) = ⟨ψ | Ĥ | ψ⟩ and energy-preserving steps.     *)
(* ===================================================================== *)

Definition energy (H : nat -> nat -> Q) (psi : nat -> Q) (N : nat) : Q :=
  seq_inner psi (op_apply H psi N) N.

Definition EnergyPreserving (U H : nat -> nat -> Q) (N : nat) : Prop :=
  forall w, energy H (op_apply U w N) N == energy H w N.

(** Energy is conserved at every step of an energy-preserving evolution. *)
Theorem evolution_conserves_energy : forall (U H : nat -> nat -> Q) (N : nat),
  EnergyPreserving U H N ->
  forall (v : nat -> Q) (n : nat),
  energy H (evolve U N v n) N == energy H v N.
Proof.
  intros U H N HU v n. induction n as [|k IH].
  - cbn [evolve]. reflexivity.
  - cbn [evolve]. rewrite (HU (evolve U N v k)). exact IH.
Qed.

(* ===================================================================== *)
(*  Concrete witness: a diagonal Hamiltonian and the sign-flip diag(1,−1). *)
(* ===================================================================== *)

Definition Hdiag (e0 e1 : Q) : nat -> nat -> Q :=
  fun i j => match i, j with
             | O, O     => e0
             | S O, S O => e1
             | _, _     => 0
             end.

Definition signflip : nat -> nat -> Q :=
  fun i j => match i, j with
             | O, O     => 1
             | S O, S O => - (1)
             | _, _     => 0
             end.

(** The sign-flip is unitary (an isometry): it preserves the norm. *)
Lemma signflip_isometry : Isometry signflip 2.
Proof.
  intro w. unfold seq_inner, op_apply, signflip. cbn [q_sum]. ring.
Qed.

(** The sign-flip preserves the energy of ANY diagonal Hamiltonian, for all states
    (a diagonal operator commutes with a diagonal Hamiltonian). *)
Lemma signflip_preserves_energy : forall (e0 e1 : Q),
  EnergyPreserving signflip (Hdiag e0 e1) 2.
Proof.
  intros e0 e1 w. unfold energy, seq_inner, op_apply, signflip, Hdiag.
  cbn [q_sum]. ring.
Qed.

(** Payoff: the sign-flip evolution conserves energy for ALL time steps. *)
Corollary evolution_signflip_conserves_energy : forall (e0 e1 : Q) (v : nat -> Q) (n : nat),
  energy (Hdiag e0 e1) (evolve signflip 2 v n) 2 == energy (Hdiag e0 e1) v 2.
Proof.
  intros e0 e1 v n.
  apply evolution_conserves_energy. apply signflip_preserves_energy.
Qed.

(* Concrete sanity: Ĥ = diag(2,3), ψ = (1,1). Energy = 2·1 + 3·1 = 5, preserved by
   the sign-flip (which sends ψ to (1,−1), energy 2·1 + 3·1 = 5). *)
Example energy_signflip_concrete :
  let H := Hdiag 2 3 in
  let psi := fun _ : nat => 1 in
  energy H (op_apply signflip psi 2%nat) 2%nat == 5 /\ energy H psi 2%nat == 5.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions evolution_conserves_energy.
Print Assumptions evolution_signflip_conserves_energy.
