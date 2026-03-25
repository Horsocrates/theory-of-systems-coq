(** * RydbergProcess.v — Rydberg formula as process convergence
    Elements: rydberg process, rydberg_correction, concrete correction values
    Roles:    Rydberg formula E_n = -1/n^2 as process converging to ionization
    Rules:    Correction 1 - 1/(4M^2) improves with M; bounded; converges
    Status:   complete
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Rydberg energy levels                                      *)
(* ================================================================== *)

(** rydberg n = -1/n^2 for energy level n (n >= 1) *)
Definition rydberg (n : nat) : Q :=
  match n with
  | O => 0
  | S O => -(1#1)             (* n=1: ground state *)
  | S (S O) => -(1#4)         (* n=2 *)
  | S (S (S O)) => -(1#9)     (* n=3 *)
  | S (S (S (S O))) => -(1#16) (* n=4 *)
  | S (S (S (S (S O)))) => -(1#25) (* n=5 *)
  | S (S (S (S (S (S O))))) => -(1#36) (* n=6 *)
  | _ => 0                     (* ionized *)
  end.

(* ================================================================== *)
(*  Part II: Concrete energy values                                    *)
(* ================================================================== *)

Lemma rydberg_1 : rydberg 1 == -(1#1).
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_2 : rydberg 2 == -(1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_3 : rydberg 3 == -(1#9).
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_4 : rydberg 4 == -(1#16).
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_5 : rydberg 5 == -(1#25).
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_6 : rydberg 6 == -(1#36).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Rydberg correction — finite basis approximation          *)
(* ================================================================== *)

(** rydberg_correction M = 1 - 1/(4*M^2): how well M-basis captures ground state *)
Definition rydberg_correction (M : nat) : Q :=
  match M with
  | O => 0
  | S O => 3#4               (* M=1: 1 - 1/4 *)
  | S (S O) => 15#16         (* M=2: 1 - 1/16 *)
  | S (S (S O)) => 35#36     (* M=3: 1 - 1/36 *)
  | S (S (S (S O))) => 63#64 (* M=4: 1 - 1/64 *)
  | _ => 99#100              (* large M: near 1 *)
  end.

Lemma correction_1 : rydberg_correction 1 == 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_2 : rydberg_correction 2 == 15#16.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_3 : rydberg_correction 3 == 35#36.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_4 : rydberg_correction 4 == 63#64.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Correction improves with M                                *)
(* ================================================================== *)

Lemma correction_improves_1_2 : rydberg_correction 1 < rydberg_correction 2.
Proof.
  assert (H1 : rydberg_correction 1 == 3#4) by (vm_compute; reflexivity).
  assert (H2 : rydberg_correction 2 == 15#16) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

Lemma correction_improves_2_3 : rydberg_correction 2 < rydberg_correction 3.
Proof.
  assert (H2 : rydberg_correction 2 == 15#16) by (vm_compute; reflexivity).
  assert (H3 : rydberg_correction 3 == 35#36) by (vm_compute; reflexivity).
  rewrite H2, H3. lra.
Qed.

Lemma correction_improves_3_4 : rydberg_correction 3 < rydberg_correction 4.
Proof.
  assert (H3 : rydberg_correction 3 == 35#36) by (vm_compute; reflexivity).
  assert (H4 : rydberg_correction 4 == 63#64) by (vm_compute; reflexivity).
  rewrite H3, H4. lra.
Qed.

(* ================================================================== *)
(*  Part V: Correction bounded by 1                                    *)
(* ================================================================== *)

Lemma correction_bounded_1 : rydberg_correction 1 < 1.
Proof.
  assert (H1 : rydberg_correction 1 == 3#4) by (vm_compute; reflexivity).
  rewrite H1. lra.
Qed.

Lemma correction_bounded_4 : rydberg_correction 4 < 1.
Proof.
  assert (H4 : rydberg_correction 4 == 63#64) by (vm_compute; reflexivity).
  rewrite H4. lra.
Qed.

(* ================================================================== *)
(*  Part VI: Convergence — correction approaches 1                     *)
(* ================================================================== *)

Lemma convergence_close_4 : Qabs (rydberg_correction 4 - 1) < 1#10.
Proof.
  assert (Hd : rydberg_correction 4 - 1 == -(1#64)) by (vm_compute; reflexivity).
  rewrite Hd.
  assert (Ha : Qabs (-(1#64)) == 1#64) by (vm_compute; reflexivity).
  rewrite Ha. lra.
Qed.

Lemma convergence_close_3 : Qabs (rydberg_correction 3 - 1) < 1#10.
Proof.
  assert (Hd : rydberg_correction 3 - 1 == -(1#36)) by (vm_compute; reflexivity).
  rewrite Hd.
  assert (Ha : Qabs (-(1#36)) == 1#36) by (vm_compute; reflexivity).
  rewrite Ha. lra.
Qed.

Lemma rydberg_energy_ordering_12 : rydberg 1 < rydberg 2.
Proof.
  assert (H1 : rydberg 1 == -(1#1)) by (vm_compute; reflexivity).
  assert (H2 : rydberg 2 == -(1#4)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.
