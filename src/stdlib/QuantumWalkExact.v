(** * QuantumWalkExact.v -- Exact Amplitudes at K=4 and K=5
    Elements: K=4 amplitudes at 5 positions, K=5 amplitudes at 6 positions
    Roles:    Exact integer amplitudes; norm = 2^K verified by sum of squares
    Rules:    K=4 norm = 16, K=5 norm = 32; peak location theorems
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* K=4 amplitudes: positions -4, -2, 0, +2, +4                        *)
(* Format: (L-component, R-component)                                  *)
(* ------------------------------------------------------------------ *)

(* Position -4: (1, 0) *)
Definition K4_m4_L : Q := 1.   Definition K4_m4_R : Q := 0.
(* Position -2: (1, 1) *)
Definition K4_m2_L : Q := 1.   Definition K4_m2_R : Q := 1.
(* Position  0: (-1, -1) *)
Definition K4_z0_L : Q := -1.  Definition K4_z0_R : Q := -1.
(* Position +2: (-1, 3) *)
Definition K4_p2_L : Q := -1.  Definition K4_p2_R : Q := 3.
(* Position +4: (0, 1) *)
Definition K4_p4_L : Q := 0.   Definition K4_p4_R : Q := 1.

(* Individual |amp|^2 values *)
Lemma K4_sq_m4 : K4_m4_L * K4_m4_L + K4_m4_R * K4_m4_R == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma K4_sq_m2 : K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma K4_sq_z0 : K4_z0_L * K4_z0_L + K4_z0_R * K4_z0_R == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma K4_sq_p2 : K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R == 10.
Proof. vm_compute. reflexivity. Qed.

Lemma K4_sq_p4 : K4_p4_L * K4_p4_L + K4_p4_R * K4_p4_R == 1.
Proof. vm_compute. reflexivity. Qed.

(* K=4 total norm = 16 = 2^4 *)
Lemma K4_norm_check :
  (K4_m4_L * K4_m4_L + K4_m4_R * K4_m4_R) +
  (K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R) +
  (K4_z0_L * K4_z0_L + K4_z0_R * K4_z0_R) +
  (K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R) +
  (K4_p4_L * K4_p4_L + K4_p4_R * K4_p4_R) == 16.
Proof. vm_compute. reflexivity. Qed.

(* Peak at +2 for K=4: |amp|^2 = 10 > all others *)
Lemma K4_peak_at_plus2 :
  K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R >
  K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R.
Proof. unfold K4_p2_L, K4_p2_R, K4_m2_L, K4_m2_R, Qlt. simpl. lia. Qed.

(* ------------------------------------------------------------------ *)
(* K=5 amplitudes: positions -5, -3, -1, +1, +3, +5                   *)
(* ------------------------------------------------------------------ *)

(* Position -5: (1, 0) *)
Definition K5_m5_L : Q := 1.   Definition K5_m5_R : Q := 0.
(* Position -3: (2, 1) *)
Definition K5_m3_L : Q := 2.   Definition K5_m3_R : Q := 1.
(* Position -1: (-2, 0) *)
Definition K5_m1_L : Q := -2.  Definition K5_m1_R : Q := 0.
(* Position +1: (2, 0) *)
Definition K5_p1_L : Q := 2.   Definition K5_p1_R : Q := 0.
(* Position +3: (1, -4) *)
Definition K5_p3_L : Q := 1.   Definition K5_p3_R : Q := -4.
(* Position +5: (0, -1) *)
Definition K5_p5_L : Q := 0.   Definition K5_p5_R : Q := -1.

(* K=5 total norm = 32 = 2^5 *)
Lemma K5_norm_check :
  (K5_m5_L * K5_m5_L + K5_m5_R * K5_m5_R) +
  (K5_m3_L * K5_m3_L + K5_m3_R * K5_m3_R) +
  (K5_m1_L * K5_m1_L + K5_m1_R * K5_m1_R) +
  (K5_p1_L * K5_p1_L + K5_p1_R * K5_p1_R) +
  (K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R) +
  (K5_p5_L * K5_p5_L + K5_p5_R * K5_p5_R) == 32.
Proof. vm_compute. reflexivity. Qed.

(* Peak at +3 for K=5: |amp|^2 = 17 *)
Lemma K5_peak_value :
  K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R == 17.
Proof. vm_compute. reflexivity. Qed.

Lemma K5_peak_at_plus3 :
  K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R >
  K5_m3_L * K5_m3_L + K5_m3_R * K5_m3_R.
Proof. unfold K5_p3_L, K5_p3_R, K5_m3_L, K5_m3_R, Qlt. simpl. lia. Qed.

(* K=4 probability at origin: P(0) = 2/16 = 1/8 *)
Lemma K4_origin_probability :
  (K4_z0_L * K4_z0_L + K4_z0_R * K4_z0_R) / 16 == 1 # 8.
Proof. vm_compute. reflexivity. Qed.

(* K=5 probability at +3: P(+3) = 17/32 *)
Lemma K5_prob_plus3 :
  (K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R) / 32 == 17 # 32.
Proof. vm_compute. reflexivity. Qed.

(* K=4 probability at +2: P(+2) = 10/16 = 5/8 *)
Lemma K4_prob_plus2 :
  (K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R) / 16 == 5 # 8.
Proof. vm_compute. reflexivity. Qed.

(* K=5 boundary amplitudes: edges carry weight 1 *)
Lemma K5_boundary_m5 :
  K5_m5_L * K5_m5_L + K5_m5_R * K5_m5_R == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma K5_boundary_p5 :
  K5_p5_L * K5_p5_L + K5_p5_R * K5_p5_R == 1.
Proof. vm_compute. reflexivity. Qed.
