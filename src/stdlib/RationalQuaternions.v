(** * RationalQuaternions.v — the Element-side 3D rotation group via Euler's
      four-square identity: rational unit quaternions are CLOSED under multiplication
      (the norm a²+b²+c²+d² is multiplicative), giving rational 3D rotations.  The
      order-5 / icosahedral rotation is a role-limit (it needs φ = 2cos36° = √5).

    Elements: the rational components a,b,c,d; the unit quaternion; the order-3
              rotation (½,½,½,½); the norm 1 (L1 + P4)
    Roles:    rational unit quaternions = the Element-side 3D rotation group (closed
              via the multiplicative norm — the 3D analogue of ℚ[i] for 2D rotations
              and of the conic norm forms in `ConicDuality.v`); the order-3 quaternion
              = an allowed rational rotation (④); the order-5/icosahedral rotation =
              a role-limit (its quaternion needs φ = 2cos36°, the same √5 as ④)
    Rules:    quaternion multiplication; the norm N(a,b,c,d) = a²+b²+c²+d²; Euler's
              four-square identity N(pq) = N(p)·N(q) (the norm is multiplicative); the
              double cover SU(2)→SO(3); the half-angle cosine 2cos(θ/2)

    THE DEEP POINT — the Element-side symmetry groups in 1, 2 and 3 dimensions all
    come from MULTIPLICATIVE norm forms.  In 2D, rational rotations are the norm-1
    elements of ℚ[i] (norm a²+b², the two-square identity) and rational boosts the
    norm-1 elements of the split algebra (norm γ²−s²), unified in `ConicDuality.v`.
    In 3D, rational rotations are the norm-1 rational QUATERNIONS (the double cover
    Spin(3)=SU(2)→SO(3)), and the norm a²+b²+c²+d² is multiplicative by EULER'S
    FOUR-SQUARE IDENTITY (`euler_four_square`).  So rational unit quaternions are
    closed under multiplication (`unit_quaternion_closed`) — the Element-side 3D
    rotation group.  A concrete witness: (½,½,½,½) is a rational unit quaternion
    (`order3_rational_quaternion`), the 120° rotation about (1,1,1) — an order-3
    rotation, allowed by the crystallographic restriction (④).

    THE ROLE-LIMIT IS ORDER 5.  A unit quaternion for a rotation by angle θ has real
    part cos(θ/2).  For the order-5 / icosahedral rotation (θ = 72°), 2cos36° = φ, the
    golden ratio, a root of x²−x−1 — irrational (`order5_rotation_role_limit`, = the
    golden-ratio role-limit from `GoldenFibonacci.v`, the SAME √5 that excludes the
    icosahedron in ④).  So no rational quaternion realises the order-5 rotation: the
    Element/role-limit boundary in 3D rotations is the rational quaternion vs the
    √5-quaternion, exactly as the multiplicative norm form predicts.

    ============ E/R/R разбор ============
      Rules (L5): умножение кватернионов; норма N=a²+b²+c²+d²; тождество Эйлера
                  N(pq)=N(p)N(q); двойное накрытие SU(2)→SO(3); 2cos(θ/2).
      Roles (L4): рациональные единичные кватернионы = Element-группа 3D-вращений
                  (замкнута через мультипликативную норму); (½,½,½,½) = порядок 3 (④);
                  порядок 5/икосаэдр = role-limit (φ=2cos36°, √5).
      Elements  : рациональные компоненты; единичный кватернион; порядок 3; норма 1 (L1+P4).
    ДИАГНОСТИКА (P4): 3D-вращения Element-сторонни при рациональном единичном кватернионе —
    группа замкнута через мультипликативную норм-форму Эйлера (3D-аналог 2D ℚ[i]/коник). Порядок
    5/икосаэдр = role-limit (φ=√5, та же, что ④). Граница = рациональный кватернион vs √5-кватернион.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia Lqa.
From ToS Require Import stdlib.GoldenFibonacci.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Quaternions over ℚ: norm and (the components of) the product          *)
(* ===================================================================== *)

Definition qnorm4 (a b c d : Q) : Q := a*a + b*b + c*c + d*d.

(** ★ Euler's four-square identity: the quaternion norm is MULTIPLICATIVE.  This is
    what makes the rational unit quaternions a group — the Element-side double cover
    of the rational 3D rotation group. *)
Theorem euler_four_square : forall a1 b1 c1 d1 a2 b2 c2 d2 : Q,
  qnorm4 (a1*a2 - b1*b2 - c1*c2 - d1*d2)
         (a1*b2 + b1*a2 + c1*d2 - d1*c2)
         (a1*c2 - b1*d2 + c1*a2 + d1*b2)
         (a1*d2 + b1*c2 - c1*b2 + d1*a2)
  == qnorm4 a1 b1 c1 d1 * qnorm4 a2 b2 c2 d2.
Proof. intros. unfold qnorm4. ring. Qed.

(** ★ Rational UNIT quaternions are closed under multiplication: if N(p)=N(q)=1 then
    N(pq)=1.  This is the Element-side 3D rotation group (Spin(3) over ℚ). *)
Theorem unit_quaternion_closed : forall a1 b1 c1 d1 a2 b2 c2 d2 : Q,
  qnorm4 a1 b1 c1 d1 == 1 -> qnorm4 a2 b2 c2 d2 == 1 ->
  qnorm4 (a1*a2 - b1*b2 - c1*c2 - d1*d2)
         (a1*b2 + b1*a2 + c1*d2 - d1*c2)
         (a1*c2 - b1*d2 + c1*a2 + d1*b2)
         (a1*d2 + b1*c2 - c1*b2 + d1*a2) == 1.
Proof.
  intros a1 b1 c1 d1 a2 b2 c2 d2 H1 H2.
  rewrite euler_four_square, H1, H2. ring.
Qed.

(* ===================================================================== *)
(*  A concrete rational unit quaternion: the order-3 (120°) rotation      *)
(* ===================================================================== *)

(** (½,½,½,½) is a rational unit quaternion — the 120° rotation about (1,1,1), an
    order-3 rotation (allowed by the crystallographic restriction ④). *)
Theorem order3_rational_quaternion : qnorm4 (1#2) (1#2) (1#2) (1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The role-limit: the order-5 / icosahedral rotation needs φ = 2cos36°  *)
(* ===================================================================== *)

(** The order-5 / icosahedral rotation has half-angle cosine 2cos36° = φ, the golden
    ratio (a root of x²−x−1) — irrational, the SAME √5 that excludes the icosahedron
    in ④.  So no rational quaternion realises it: order 5 is a role-limit. *)
Theorem order5_rotation_role_limit : ~ (exists q : Q, q * q == q + 1).
Proof. exact no_rational_golden. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** 3D rotations split by the finitization boundary:
      (a) Euler's four-square identity — the quaternion norm is multiplicative;
      (b) hence rational unit quaternions are CLOSED under multiplication (the
          Element-side 3D rotation group);
      (c) (½,½,½,½) is a concrete rational unit quaternion (the order-3 rotation);
      (d) the order-5/icosahedral rotation is a role-limit — 2cos36°=φ is irrational
          (the same √5 as ④). *)
Theorem quaternion_synthesis :
  (forall a1 b1 c1 d1 a2 b2 c2 d2 : Q,
     qnorm4 (a1*a2 - b1*b2 - c1*c2 - d1*d2) (a1*b2 + b1*a2 + c1*d2 - d1*c2)
            (a1*c2 - b1*d2 + c1*a2 + d1*b2) (a1*d2 + b1*c2 - c1*b2 + d1*a2)
     == qnorm4 a1 b1 c1 d1 * qnorm4 a2 b2 c2 d2)
  /\ (forall a1 b1 c1 d1 a2 b2 c2 d2 : Q,
        qnorm4 a1 b1 c1 d1 == 1 -> qnorm4 a2 b2 c2 d2 == 1 ->
        qnorm4 (a1*a2 - b1*b2 - c1*c2 - d1*d2) (a1*b2 + b1*a2 + c1*d2 - d1*c2)
               (a1*c2 - b1*d2 + c1*a2 + d1*b2) (a1*d2 + b1*c2 - c1*b2 + d1*a2) == 1)
  /\ (qnorm4 (1#2) (1#2) (1#2) (1#2) == 1)
  /\ ~ (exists q : Q, q * q == q + 1).
Proof.
  split; [ exact euler_four_square | ].
  split; [ exact unit_quaternion_closed | ].
  split; [ exact order3_rational_quaternion | exact order5_rotation_role_limit ].
Qed.
