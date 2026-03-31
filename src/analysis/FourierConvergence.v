(** * FourierConvergence.v — Parseval's Theorem and L² Convergence

    Theory of Systems — Step 4: Fourier Series

    Parseval's identity: energy in time domain = energy in frequency domain.
    Verified concretely for N=4 cycle with specific test functions.

    Elements: time energy, frequency energy, Parseval sum
    Roles:    energy -> conserved quantity, DFT -> isometry, modes -> basis
    Rules:    energy conservation (L5: total energy preserved)
    Status:   verified | concrete_checked

    Strategy: All computations concrete with vm_compute on Q.

    STATUS: 15 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ========================================================================= *)
(* Reproduce definitions from FourierBasis (standalone)                       *)
(* ========================================================================= *)

Definition phi_0 (j : nat) : Q :=
  match j with O => 1 | S O => 1 | S (S O) => 1 | S (S (S O)) => 1 | _ => 0 end.

Definition phi_1 (j : nat) : Q :=
  match j with O => 1 | S O => 0 | S (S O) => -(1) | S (S (S O)) => 0 | _ => 0 end.

Definition phi_2 (j : nat) : Q :=
  match j with O => 1 | S O => -(1) | S (S O) => 1 | S (S (S O)) => -(1) | _ => 0 end.

Definition phi_3 (j : nat) : Q :=
  match j with O => 0 | S O => 1 | S (S O) => 0 | S (S (S O)) => -(1) | _ => 0 end.

Definition inner4 (f g : nat -> Q) : Q :=
  f 0%nat * g 0%nat + f 1%nat * g 1%nat + f 2%nat * g 2%nat + f 3%nat * g 3%nat.

Definition dft_4 (f : nat -> Q) (k : nat) : Q :=
  match k with
  | O => inner4 f phi_0 / 4
  | S O => inner4 f phi_1 / 2
  | S (S O) => inner4 f phi_2 / 4
  | S (S (S O)) => inner4 f phi_3 / 2
  | _ => 0
  end.

(* ========================================================================= *)
(* Energy definitions                                                         *)
(* ========================================================================= *)

(* Time-domain energy: Σ|f(j)|² *)
Definition time_energy_4 (f : nat -> Q) : Q :=
  f 0%nat * f 0%nat + f 1%nat * f 1%nat +
  f 2%nat * f 2%nat + f 3%nat * f 3%nat.

(* Frequency-domain energy (Parseval form):
   4|f̂₀|² + 2|f̂₁|² + 4|f̂₂|² + 2|f̂₃|²
   = Σ ‖φ_k‖² · |f̂_k|² *)
Definition freq_energy_4 (f : nat -> Q) : Q :=
  let fh0 := dft_4 f 0%nat in
  let fh1 := dft_4 f 1%nat in
  let fh2 := dft_4 f 2%nat in
  let fh3 := dft_4 f 3%nat in
  4 * (fh0 * fh0) + 2 * (fh1 * fh1) + 4 * (fh2 * fh2) + 2 * (fh3 * fh3).

(* ========================================================================= *)
(* Test functions                                                             *)
(* ========================================================================= *)

Definition f_const (j : nat) : Q := 1.

Definition f_impulse (j : nat) : Q :=
  match j with O => 1 | _ => 0 end.

Definition f_alt (j : nat) : Q :=
  match j with O => 1 | S O => -(1) | S (S O) => 1 | S (S (S O)) => -(1) | _ => 0 end.

Definition f_ramp (j : nat) : Q :=
  match j with O => 0 | S O => 1 | S (S O) => 2 | S (S (S O)) => 3 | _ => 0 end.

Definition f_mixed (j : nat) : Q :=
  match j with O => 2 | S O => -(1) | S (S O) => 3 | S (S (S O)) => 0 | _ => 0 end.

(* ========================================================================= *)
(* Parseval for specific functions                                            *)
(* ========================================================================= *)

(* 1. Parseval for constant: f=(1,1,1,1) *)
Lemma parseval_constant :
  time_energy_4 f_const == freq_energy_4 f_const.
Proof. vm_compute. reflexivity. Qed.

(* 2. Parseval for impulse: f=(1,0,0,0) *)
Lemma parseval_impulse :
  time_energy_4 f_impulse == freq_energy_4 f_impulse.
Proof. vm_compute. reflexivity. Qed.

(* 3. Parseval for alternating: f=(1,-1,1,-1) *)
Lemma parseval_alternating :
  time_energy_4 f_alt == freq_energy_4 f_alt.
Proof. vm_compute. reflexivity. Qed.

(* 4. Parseval for ramp: f=(0,1,2,3) *)
Lemma parseval_ramp :
  time_energy_4 f_ramp == freq_energy_4 f_ramp.
Proof. vm_compute. reflexivity. Qed.

(* 5. Parseval for mixed: f=(2,-1,3,0) *)
Lemma parseval_mixed :
  time_energy_4 f_mixed == freq_energy_4 f_mixed.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(* Bessel inequality: partial frequency sum ≤ total energy                   *)
(* ========================================================================= *)

(* Partial energy using only first k+1 modes *)
Definition partial_freq_1 (f : nat -> Q) : Q :=
  let fh0 := dft_4 f 0%nat in
  4 * (fh0 * fh0).

Definition partial_freq_2 (f : nat -> Q) : Q :=
  let fh0 := dft_4 f 0%nat in
  let fh1 := dft_4 f 1%nat in
  4 * (fh0 * fh0) + 2 * (fh1 * fh1).

(* 6. Bessel for impulse: 1-mode partial ≤ total *)
Lemma bessel_impulse_1 :
  partial_freq_1 f_impulse <= time_energy_4 f_impulse.
Proof. vm_compute. discriminate. Qed.

(* 7. Bessel for ramp: 2-mode partial ≤ total *)
Lemma bessel_ramp_2 :
  partial_freq_2 f_ramp <= time_energy_4 f_ramp.
Proof. vm_compute. discriminate. Qed.

(* ========================================================================= *)
(* Energy of specific DFT coefficients                                       *)
(* ========================================================================= *)

(* 8. DFT of impulse: all coefficients = 1/4 or 1/2 *)
Lemma dft_impulse_0 : dft_4 f_impulse 0%nat == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma dft_impulse_1 : dft_4 f_impulse 1%nat == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

(* 9. DFT of ramp: verify mode 0 = average *)
Lemma dft_ramp_0 : dft_4 f_ramp 0%nat == 3 # 2.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(* Non-negativity of energy                                                   *)
(* ========================================================================= *)

(* 10. Time energy is sum of squares *)
Lemma time_energy_nonneg_const : 0 <= time_energy_4 f_const.
Proof. vm_compute. discriminate. Qed.

Lemma time_energy_nonneg_impulse : 0 <= time_energy_4 f_impulse.
Proof. vm_compute. discriminate. Qed.

(* ========================================================================= *)
(* L² convergence: reconstruction error                                      *)
(* ========================================================================= *)

(* Reconstruct from DFT coefficients *)
Definition reconstruct_4 (f : nat -> Q) (j : nat) : Q :=
  dft_4 f 0%nat * phi_0 j + dft_4 f 1%nat * phi_1 j +
  dft_4 f 2%nat * phi_2 j + dft_4 f 3%nat * phi_3 j.

(* 12. Perfect reconstruction for impulse *)
Lemma reconstruct_impulse : forall j, (j < 4)%nat ->
  reconstruct_4 f_impulse j == f_impulse j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia; vm_compute; reflexivity.
Qed.

(* 13. Perfect reconstruction for ramp *)
Lemma reconstruct_ramp : forall j, (j < 4)%nat ->
  reconstruct_4 f_ramp j == f_ramp j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia; vm_compute; reflexivity.
Qed.

(* 14. Perfect reconstruction for mixed *)
Lemma reconstruct_mixed : forall j, (j < 4)%nat ->
  reconstruct_4 f_mixed j == f_mixed j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia; vm_compute; reflexivity.
Qed.

(* ========================================================================= *)
(* Linearity of DFT                                                          *)
(* ========================================================================= *)

(* 15. DFT(f + g)(k) = DFT(f)(k) + DFT(g)(k) for specific f,g *)
Definition f_sum (j : nat) : Q := f_impulse j + f_alt j.

Lemma dft_linearity_mode0 :
  dft_4 f_sum 0%nat == dft_4 f_impulse 0%nat + dft_4 f_alt 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** Summary:
    - 5 Parseval verifications (const, impulse, alt, ramp, mixed)
    - 2 Bessel inequalities
    - 3 DFT coefficient values
    - 2 energy non-negativity
    - 3 perfect reconstruction (impulse, ramp, mixed)
    - 1 linearity check
    Total: 15 Qed, 0 Admitted *)
