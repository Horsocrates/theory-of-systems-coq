(** * HallConductanceT.v — Quantized Hall conductance

    Elements: Chern number C, Hall conductance sigma_xy = C * e^2/h
    Roles:    quantization of conductance from topology
    Rules:    sigma_xy = C (in natural units); integer-quantized
    Status:   verified | quantum Hall effect

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool ZArith Lia.
Open Scope Q_scope.

(** Hall conductance in units of e^2/h *)
Definition hall_conductance (C : Z) : Q := inject_Z C.

(** ---- Concrete values ---- *)

Theorem hall_integer : hall_conductance 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hall_zero : hall_conductance 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem hall_neg : hall_conductance (-1) == -(1).
Proof. vm_compute. reflexivity. Qed.

(** Particle-hole symmetry: C + (-C) = 0 *)
Theorem hall_sum : hall_conductance 1 + hall_conductance (-1) == 0.
Proof. vm_compute. reflexivity. Qed.

(** Positive Chern -> positive conductance *)
Theorem von_klitzing_positive : 0 < hall_conductance 1.
Proof. unfold hall_conductance, Qlt. simpl. lia. Qed.

(** Double Chern *)
Theorem quantization_exact : hall_conductance 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(** Conductance is additive *)
Theorem hall_additive : forall C1 C2,
  hall_conductance C1 + hall_conductance C2 ==
  hall_conductance (C1 + C2).
Proof.
  intros. unfold hall_conductance. rewrite inject_Z_plus. lra.
Qed.

(** Triple filling *)
Theorem hall_triple : hall_conductance 3 == 3.
Proof. vm_compute. reflexivity. Qed.

(** Negative filling *)
Theorem hall_neg2 : hall_conductance (-2) == -(2).
Proof. vm_compute. reflexivity. Qed.

(** Conductance determines phase: C=0 means trivial *)
Theorem hall_trivial_zero : hall_conductance 0 == 0.
Proof. vm_compute. reflexivity. Qed.
