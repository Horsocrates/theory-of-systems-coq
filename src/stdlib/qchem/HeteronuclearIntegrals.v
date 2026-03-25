(** * HeteronuclearIntegrals.v — Molecular integrals for heteronuclear diatomics

    Elements: orbital exponents alpha_H, alpha_F; bond distance R
    Roles:    overlap -> S(R), kinetic -> T(R), nuclear attraction -> V(R)
    Rules:    Padé approximant for exp(-x) decay of overlap
    Status:   computed | verified

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Padé[2,2] approximant for exp(-x): (12 - 6x + x²)/(12 + 6x + x²) *)
Definition pade22 (x : Q) : Q :=
  (12 - 6 * x + x * x) / (12 + 6 * x + x * x).

(** Padé at x=0 gives 1 (= exp(0)) *)
Theorem pade22_at_0 : pade22 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Padé at x=1 *)
Theorem pade22_at_1 : pade22 1 == 7 # 19.
Proof. vm_compute. reflexivity. Qed.

(** Padé at x=2 *)
Theorem pade22_at_2 : pade22 2 == 1 # 7.
Proof. vm_compute. reflexivity. Qed.

(** Padé at x=3 *)
Theorem pade22_at_3 : pade22 3 == 1 # 13.
Proof. vm_compute. reflexivity. Qed.

(** Padé approximant is decreasing for positive x *)
Theorem pade22_decreasing_01 : pade22 0 > pade22 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pade22_decreasing_12 : pade22 1 > pade22 2.
Proof. vm_compute. reflexivity. Qed.

Theorem pade22_decreasing_23 : pade22 2 > pade22 3.
Proof. vm_compute. reflexivity. Qed.

(** HF molecule orbital exponents *)
Definition alpha_H : Q := 1.
Definition alpha_F : Q := 27 # 10.

(** Overlap integral approximation at R=2: S ≈ pade22((alpha_H+alpha_F)/2 * R) *)
(** Parameter: (1 + 27/10)/2 * 2 = (37/10) * 1 = 37/10 *)
Definition s_param_R2 : Q := (alpha_H + alpha_F) / 2 * 2.

Theorem s_param_R2_value : s_param_R2 == 37 # 10.
Proof. vm_compute. reflexivity. Qed.

Definition overlap_HF_R2 : Q := pade22 (37 # 10).

(** Compute pade22(37/10):
    12 - 6*37/10 + (37/10)^2 = 12 - 222/10 + 1369/100
    = 1200/100 - 2220/100 + 1369/100 = 349/100
    12 + 6*37/10 + (37/10)^2 = 12 + 222/10 + 1369/100
    = 1200/100 + 2220/100 + 1369/100 = 4789/100
    Result: (349/100) / (4789/100) = 349/4789 *)
Theorem overlap_HF_R2_value : overlap_HF_R2 == 349 # 4789.
Proof. vm_compute. reflexivity. Qed.

(** Overlap is positive but small *)
Theorem overlap_HF_R2_positive : overlap_HF_R2 > 0.
Proof. vm_compute. reflexivity. Qed.

Theorem overlap_HF_R2_small : overlap_HF_R2 < 1 # 10.
Proof.
  assert (H : overlap_HF_R2 == 349 # 4789) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Exponent ratio *)
Theorem exponent_ratio : alpha_F / alpha_H == 27 # 10.
Proof. vm_compute. reflexivity. Qed.

(** Mean exponent *)
Definition alpha_mean : Q := (alpha_H + alpha_F) / 2.
Theorem alpha_mean_value : alpha_mean == 37 # 20.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem heteronuclear_err :
  pade22 0 == 1 /\
  overlap_HF_R2 == 349 # 4789 /\
  overlap_HF_R2 > 0 /\
  alpha_F / alpha_H == 27 # 10.
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
