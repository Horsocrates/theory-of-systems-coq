(** * JCrossTerms.v — Cross-exponent Coulomb J-integrals

    Elements: orbital exponent pairs (alpha_a, alpha_b)
    Roles:    J_cross -> cross Coulomb integral
    Rules:    J_cross(a,b) = 5ab/(4(a+b)), reduces to J_same when a=b
    Status:   verified | symmetric

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Cross-exponent Coulomb integral between 1s orbitals *)
Definition J_cross (alpha_a alpha_b : Q) : Q :=
  5 * alpha_a * alpha_b / (4 * (alpha_a + alpha_b)).

(** Concrete evaluations *)
Theorem J_cross_11 : J_cross 1 1 == 5 # 8.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_12 : J_cross 1 2 == 5 # 6.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_21 : J_cross 2 1 == 5 # 6.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_1_5_2 : J_cross 1 (5 # 2) == 25 # 28.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_22 : J_cross 2 2 == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_13 : J_cross 1 3 == 15 # 16.
Proof. vm_compute. reflexivity. Qed.

(** Symmetry: J_cross(a,b) = J_cross(b,a) at concrete points *)
Theorem J_cross_symmetric_12 : J_cross 1 2 == J_cross 2 1.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_symmetric_13 : J_cross 1 3 == J_cross 3 1.
Proof. vm_compute. reflexivity. Qed.

(** Positivity *)
Theorem J_cross_positive_12 : J_cross 1 2 > 0.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_positive_1_5_2 : J_cross 1 (5 # 2) > 0.
Proof. vm_compute. reflexivity. Qed.

(** J_cross < J_same(max) — cross term is smaller than same-exponent *)
(** J_cross(1,2) = 5/6, J_same(2) = 5/4: 5/6 < 5/4 *)
Theorem J_cross_less_max : J_cross 1 2 < 5 # 4.
Proof. vm_compute. reflexivity. Qed.

(** When a=b, J_cross reduces to J_same = 5a/8 *)
(** J_cross(a,a) = 5a²/(4*2a) = 5a/8 *)
Theorem J_cross_same_at_1 : J_cross 1 1 == 5 # 8.
Proof. vm_compute. reflexivity. Qed.

Theorem J_cross_same_at_2 : J_cross 2 2 == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

(** Ordering: J_cross(1,2) < J_cross(2,2) *)
Theorem J_cross_ordering : J_cross 1 2 < J_cross 2 2.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem j_cross_err :
  J_cross 1 2 == 5 # 6 /\
  J_cross 1 (5 # 2) == 25 # 28 /\
  J_cross 1 2 == J_cross 2 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
