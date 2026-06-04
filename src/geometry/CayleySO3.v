(** * CayleySO3.v — the Cayley transform so(3) → SO(3,Q): rational 3D rotations
    Elements: a rational vector v=(x,y,z) ∈ Q³ (an so(3) element, via the hat map)
    Roles:    the Cayley transform as the RATIONAL exp: 𝔤 → G in 3 dimensions
    Rules:    R = (I−K)(I+K)⁻¹ with K = hat(v) skew; RᵀR = I, det R = 1
    STATUS:   6 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The 3D analogue of the 2D rational rotations in stdlib/RationalRotationGroup.v,
    and the bridge LieAlgebraSO3.v (the algebra) → RationalSO3.v (the group). The
    exponential exp: so(3) → SO(3) over ℝ is a continuum role-limit (it needs
    cos/sin); the CAYLEY TRANSFORM is its RATIONAL substitute. For the skew matrix
    K = hat(v) of a rational vector v=(x,y,z) ∈ Q³ (an element of the Lie algebra
    of G1), the Cayley transform R = (I−K)(I+K)⁻¹ is a rational rotation matrix.

    To stay purely in ring arithmetic (no matrix inverse / division in the proofs),
    we work with the NUMERATOR N := (1+|v|²)·R (the adjugate form). The headline is
    a PURE RING IDENTITY:
        Nᵀ·N = (1+|v|²)²·I        and        det N = (1+|v|²)³,
    so R = N/(1+|v|²) satisfies RᵀR = I and det R = +1 — i.e. R ∈ SO(3,Q). The
    normalization is the rational denominator (1+|v|²) > 0; we exhibit it concretely
    for the 90° rotation about the x-axis (v=(1,0,0)).

    HONEST SCOPE: the genuine exp: so(3)→SO(3) over ℝ is a continuum role-limit;
    Cayley is the rational replacement (it misses rotations by π — the antipodal
    points where 1+|v|²→∞). Same spirit as stdlib/RationalRotationGroup.v (2D).
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

Definition Mscale (c : Q) (A : M3) : M3 :=
  mkM3 (c*a11 A) (c*a12 A) (c*a13 A)
       (c*a21 A) (c*a22 A) (c*a23 A)
       (c*a31 A) (c*a32 A) (c*a33 A).

Definition Mid : M3 := mkM3 1 0 0  0 1 0  0 0 1.

Definition Mdet (A : M3) : Q :=
  a11 A*(a22 A*a33 A - a23 A*a32 A)
  - a12 A*(a21 A*a33 A - a23 A*a31 A)
  + a13 A*(a21 A*a32 A - a22 A*a31 A).

Definition orthogonal (A : M3) : Prop := Meq (Mmul (Mtrans A) A) Mid.

(* ===================== the Cayley numerator N = (1+|v|²)·R ================= *)
(* K = hat(v) = [0 -z y; z 0 -x; -y x 0]; N = (1+|v|²)·(I-K)(I+K)^{-1} *)
Definition cay_num (x y z : Q) : M3 :=
  mkM3 (1 + x*x - y*y - z*z)  (2*(x*y - z))        (2*(x*z + y))
       (2*(x*y + z))          (1 - x*x + y*y - z*z) (2*(y*z - x))
       (2*(x*z - y))          (2*(y*z + x))         (1 - x*x - y*y + z*z).

(* ★ THE CAYLEY ORTHOGONALITY IDENTITY (pure ring): Nᵀ·N = (1+|v|²)²·I *)
Theorem cay_orthogonal_scaled : forall x y z,
  Meq (Mmul (Mtrans (cay_num x y z)) (cay_num x y z))
      (Mscale ((1 + (x*x+y*y+z*z)) * (1 + (x*x+y*y+z*z))) Mid).
Proof.
  intros x y z. unfold Meq, Mmul, Mtrans, cay_num, Mscale, Mid; simpl.
  repeat split; ring.
Qed.

(* det N = (1+|v|²)³ > 0, so R = N/(1+|v|²) is a ROTATION (det +1), not a reflection *)
Theorem cay_det_scaled : forall x y z,
  Mdet (cay_num x y z)
    == (1 + (x*x+y*y+z*z)) * ((1 + (x*x+y*y+z*z)) * (1 + (x*x+y*y+z*z))).
Proof.
  intros x y z. unfold Mdet, cay_num; simpl. ring.
Qed.

(* the Cayley transform of 0 (the zero Lie-algebra element) is the identity *)
Theorem cay_identity : Meq (cay_num 0 0 0) Mid.
Proof. unfold Meq, cay_num, Mid; simpl. repeat split; ring. Qed.

(* ===================== concrete: 90° rotation about the x-axis =========== *)
(* v=(1,0,0) ⇒ tan(θ/2)=1 ⇒ θ=90°; here 1+|v|²=2, so N = 2·R *)
Definition rot90x : M3 := mkM3 1 0 0  0 0 (-(1))  0 1 0.

(* the Cayley numerator at v=(1,0,0) is exactly 2·rot90x: the normalization is /2 *)
Theorem cay_num_90x : Meq (cay_num 1 0 0) (Mscale 2 rot90x).
Proof. unfold Meq, cay_num, Mscale, rot90x; simpl. repeat split; ring. Qed.

(* and the normalized matrix really is in SO(3,Q): orthogonal with det 1 *)
Theorem rot90x_orthogonal : orthogonal rot90x.
Proof.
  unfold orthogonal, Meq, Mmul, Mtrans, rot90x, Mid; simpl.
  repeat split; ring.
Qed.

Theorem rot90x_det : Mdet rot90x == 1.
Proof. unfold Mdet, rot90x; simpl. ring. Qed.
