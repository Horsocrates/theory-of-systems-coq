(** * RationalSO3.v — rational orthogonal 3×3 matrices: SO(3,Q) elements
    Elements: rational 3×3 matrices (9 entries in Q)
    Roles:    rotation as role-symmetry; orthogonality RᵀR=I as the well-formedness rule
    Rules:    RᵀR = I and det R = 1 define a rotation; rot_z embeds SO(2,Q) ⊂ SO(3,Q)
    STATUS:   5 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The Lie-group (Element) side, in 3D: concrete rational rotation matrices.
    (a) The z-axis family rot_z(c,s) is orthogonal with det 1 whenever (c,s) is on
        the unit circle — i.e. the rational SO(2) of stdlib/RationalRotationGroup.v
        embeds into SO(3,Q).
    (b) A genuinely 3-dimensional rational rotation: the cyclic permutation matrix
        is the 120° rotation about the (1,1,1) axis (the rotation of the rational
        unit quaternion (½,½,½,½) from QuaternionRotation.v — the SAME element); it is orthogonal,
        has det 1, and has ORDER 3 (cyc³ = I) — a finite-order element of SO(3,Q).

    HONEST SCOPE: concrete rational rotations + the SO(2)⊂SO(3) family. The full Lie
    GROUP SO(3) as a smooth manifold is a continuum role-limit; general
    orthogonal-times-orthogonal closure (matrix algebra) is buildable but not assembled
    here. on_circle is replicated locally (trivial).

    RELATED (existing repo): SO(2,Q) group laws (composition closure, inverse, the
    Cayley chart) live in stdlib/RationalRotationGroup.v; the order-3 element here is
    the matrix form of `qhalf` in QuaternionRotation.v.
*)

From Stdlib Require Import QArith.
Open Scope Q_scope.

(* ===================== minimal 3×3 rational matrices ===================== *)
Record M3 : Set := mkM3 {
  a11 : Q; a12 : Q; a13 : Q;
  a21 : Q; a22 : Q; a23 : Q;
  a31 : Q; a32 : Q; a33 : Q }.

Definition Meq (A B : M3) : Prop :=
  a11 A == a11 B /\ a12 A == a12 B /\ a13 A == a13 B /\
  a21 A == a21 B /\ a22 A == a22 B /\ a23 A == a23 B /\
  a31 A == a31 B /\ a32 A == a32 B /\ a33 A == a33 B.

Definition Mtrans (A : M3) : M3 :=
  mkM3 (a11 A) (a21 A) (a31 A)
       (a12 A) (a22 A) (a32 A)
       (a13 A) (a23 A) (a33 A).

Definition Mmul (A B : M3) : M3 :=
  mkM3 (a11 A*a11 B + a12 A*a21 B + a13 A*a31 B)
       (a11 A*a12 B + a12 A*a22 B + a13 A*a32 B)
       (a11 A*a13 B + a12 A*a23 B + a13 A*a33 B)
       (a21 A*a11 B + a22 A*a21 B + a23 A*a31 B)
       (a21 A*a12 B + a22 A*a22 B + a23 A*a32 B)
       (a21 A*a13 B + a22 A*a23 B + a23 A*a33 B)
       (a31 A*a11 B + a32 A*a21 B + a33 A*a31 B)
       (a31 A*a12 B + a32 A*a22 B + a33 A*a32 B)
       (a31 A*a13 B + a32 A*a23 B + a33 A*a33 B).

Definition Mid : M3 := mkM3 1 0 0  0 1 0  0 0 1.

Definition Mdet (A : M3) : Q :=
  a11 A*(a22 A*a33 A - a23 A*a32 A)
  - a12 A*(a21 A*a33 A - a23 A*a31 A)
  + a13 A*(a21 A*a32 A - a22 A*a31 A).

Definition orthogonal (A : M3) : Prop := Meq (Mmul (Mtrans A) A) Mid.

(* on_circle replicated locally (same as CayleyMap.v) *)
Definition on_circle (c s : Q) : Prop := c * c + s * s == 1.

(* ===================== (a) the z-axis family rot_z ⊂ SO(3,Q) ============= *)
Definition rot_z (c s : Q) : M3 := mkM3 c (- s) 0  s c 0  0 0 1.

(* rot_z(c,s) is orthogonal whenever (c,s) is on the unit circle *)
Theorem rot_z_orthogonal : forall c s, on_circle c s -> orthogonal (rot_z c s).
Proof.
  intros c s H. unfold orthogonal, Meq, Mmul, Mtrans, rot_z, Mid; simpl.
  repeat split; try ring; (transitivity (c * c + s * s); [ ring | exact H ]).
Qed.

(* and has determinant 1 on the circle *)
Theorem rot_z_det : forall c s, on_circle c s -> Mdet (rot_z c s) == 1.
Proof.
  intros c s H. unfold Mdet, rot_z; simpl. transitivity (c * c + s * s); [ ring | exact H ].
Qed.

(* ===================== (b) a genuine 3D rational rotation (order 3) ======= *)
(* the cyclic permutation = 120° rotation about (1,1,1); from quaternion (½,½,½,½) *)
Definition cyc : M3 := mkM3 0 0 1  1 0 0  0 1 0.

Theorem cyc_orthogonal : orthogonal cyc.
Proof. unfold orthogonal, Meq, Mmul, Mtrans, cyc, Mid. repeat split; vm_compute; reflexivity. Qed.

Theorem cyc_det : Mdet cyc == 1.
Proof. vm_compute. reflexivity. Qed.

(* ★ order 3: three 120° rotations return to the identity *)
Theorem cyc_order3 : Meq (Mmul (Mmul cyc cyc) cyc) Mid.
Proof. unfold Meq, Mmul, cyc, Mid. repeat split; vm_compute; reflexivity. Qed.
