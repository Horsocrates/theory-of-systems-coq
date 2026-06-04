(** * QuaternionRotation.v — the rational quaternions ℍ_ℚ and the SU(2)→SO(3) cover
    Elements: rational quaternions (w,x,y,z) ∈ Q⁴ — finite data, a division algebra
    Roles:    unit quaternion as a rotation; conjugation q·v·q̄ as the rotation action
    Rules:    Hamilton product; |ab|²=|a|²·|b|² (Euler four-square identity); q,−q ↦ same rotation
    STATUS:   24 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Companion to LieAlgebraSO3.v (G1) and RationalSO3.v (G4). The unit quaternions
    form SU(2); they act on pure quaternions (= Q³) by conjugation q·v·q̄, giving
    the 2:1 cover SU(2) → SO(3). EVERYTHING here is rational and finite:
      • the norm is MULTIPLICATIVE — |a·b|² = |a|²·|b|² — which is exactly the
        EULER FOUR-SQUARE IDENTITY, a pure ring identity over Q;
      • hence the conjugation action is an ISOMETRY (scales the norm by |q|², =1 for
        a unit quaternion) — Element-side proof that a unit quaternion rotates;
      • q and −q give the SAME rotation: the DOUBLE COVER;
      • the unit quaternion (½,½,½,½) is the 120° rotation about (1,1,1) — its cube
        is −1, and its conjugation action has ORDER 3 (it is the `cyc` of G4).
    The imaginary units satisfy i²=j²=k²=−1, ij=k, jk=i, ki=j (the so(3)≅su(2)
    structure constants of G1, group-level).

    PRIOR ART: the scalar four-square identity (euler_four_square) and the order-5
    role-limit already live in stdlib/RationalQuaternions.v. This file is the
    GEOMETRY-layer extension: it builds the full quaternion algebra as a Record,
    the conjugation rotation ACTION, the isometry property, and the SU(2)→SO(3)
    DOUBLE COVER — none of which are in the stdlib scalar file.

    HONEST SCOPE: the rotation action is shown via the quaternion algebra (no matrix
    type needed): conjugation preserves the norm and sends pure→pure. The smooth Lie
    group SU(2) over ℝ is a continuum role-limit; this is its rational core.
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================== quaternions over Q ===================== *)
Record H : Set := mkH { hw : Q ; hx : Q ; hy : Q ; hz : Q }.

Definition Heq (a b : H) : Prop :=
  hw a == hw b /\ hx a == hx b /\ hy a == hy b /\ hz a == hz b.

Definition Hadd (a b : H) : H :=
  mkH (hw a + hw b) (hx a + hx b) (hy a + hy b) (hz a + hz b).
Definition Hneg (a : H) : H := mkH (- hw a) (- hx a) (- hy a) (- hz a).
Definition Hzero : H := mkH 0 0 0 0.
Definition Hone  : H := mkH 1 0 0 0.

(* the Hamilton product *)
Definition Hmul (a b : H) : H :=
  mkH (hw a*hw b - hx a*hx b - hy a*hy b - hz a*hz b)
      (hw a*hx b + hx a*hw b + hy a*hz b - hz a*hy b)
      (hw a*hy b - hx a*hz b + hy a*hw b + hz a*hx b)
      (hw a*hz b + hx a*hy b - hy a*hx b + hz a*hw b).

Definition Hconj (a : H) : H := mkH (hw a) (- hx a) (- hy a) (- hz a).

(* squared norm — a single rational number *)
Definition Hnorm2 (a : H) : Q := hw a*hw a + hx a*hx a + hy a*hy a + hz a*hz a.

(* a pure (imaginary) quaternion = an element of Q³ *)
Definition pureH (x y z : Q) : H := mkH 0 x y z.

(* the imaginary units *)
Definition qi : H := mkH 0 1 0 0.
Definition qj : H := mkH 0 0 1 0.
Definition qk : H := mkH 0 0 0 1.

(* ===================== Heq is an equivalence ===================== *)
Lemma Heq_refl : forall a, Heq a a.
Proof. intro a. unfold Heq. repeat split; reflexivity. Qed.

Lemma Heq_sym : forall a b, Heq a b -> Heq b a.
Proof. intros a b [H1 [H2 [H3 H4]]]. unfold Heq. repeat split; symmetry; assumption. Qed.

Lemma Heq_trans : forall a b c, Heq a b -> Heq b c -> Heq a c.
Proof.
  intros a b c [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]]. unfold Heq.
  repeat split; eapply Qeq_trans; eassumption.
Qed.

(* ===================== ★ norm is multiplicative (four-square identity) ==== *)
Theorem Hnorm2_mult : forall a b, Hnorm2 (Hmul a b) == Hnorm2 a * Hnorm2 b.
Proof. intros a b. unfold Hnorm2, Hmul; simpl. ring. Qed.

Theorem Hnorm2_conj : forall a, Hnorm2 (Hconj a) == Hnorm2 a.
Proof. intro a. unfold Hnorm2, Hconj; simpl. ring. Qed.

(* conjugation is an anti-homomorphism, and a·ā = |a|² *)
Theorem Hconj_mul : forall a b, Heq (Hconj (Hmul a b)) (Hmul (Hconj b) (Hconj a)).
Proof. intros a b. unfold Heq, Hconj, Hmul; simpl. repeat split; ring. Qed.

Theorem Hmul_conj_eq_norm : forall a, Heq (Hmul a (Hconj a)) (mkH (Hnorm2 a) 0 0 0).
Proof. intro a. unfold Heq, Hmul, Hconj, Hnorm2; simpl. repeat split; ring. Qed.

(* associativity and the unit *)
Theorem Hmul_assoc : forall a b c, Heq (Hmul (Hmul a b) c) (Hmul a (Hmul b c)).
Proof. intros a b c. unfold Heq, Hmul; simpl. repeat split; ring. Qed.

Theorem Hmul_one_l : forall a, Heq (Hmul Hone a) a.
Proof. intro a. unfold Heq, Hmul, Hone; simpl. repeat split; ring. Qed.

Theorem Hmul_one_r : forall a, Heq (Hmul a Hone) a.
Proof. intro a. unfold Heq, Hmul, Hone; simpl. repeat split; ring. Qed.

(* ===================== imaginary-unit relations (group-level so(3)) ======= *)
Theorem qi_squared : Heq (Hmul qi qi) (Hneg Hone).
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

Theorem qj_squared : Heq (Hmul qj qj) (Hneg Hone).
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

Theorem qk_squared : Heq (Hmul qk qk) (Hneg Hone).
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

Theorem qij : Heq (Hmul qi qj) qk.
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

Theorem qjk : Heq (Hmul qj qk) qi.
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

Theorem qki : Heq (Hmul qk qi) qj.
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

(* genuinely non-commutative: ij = k but ji = -k *)
Theorem quaternion_not_commutative : ~ Heq (Hmul qi qj) (Hmul qj qi).
Proof.
  unfold Heq, Hmul, qi, qj; simpl. intros [_ [_ [_ H]]]. lra.
Qed.

(* ===================== the conjugation action (rotation) ===================== *)
Definition conjugate_action (q v : H) : H := Hmul (Hmul q v) (Hconj q).

(* the action of any q on a pure quaternion is again pure (real part 0) *)
Theorem conjugate_action_pure : forall q x y z,
  hw (conjugate_action q (pureH x y z)) == 0.
Proof. intros q x y z. unfold conjugate_action, pureH, Hmul, Hconj; simpl. ring. Qed.

(* ★ the action scales the squared norm by |q|² on each side (ring identity) *)
Theorem rotation_scales_norm : forall q v,
  Hnorm2 (conjugate_action q v) == Hnorm2 q * (Hnorm2 q * Hnorm2 v).
Proof. intros q v. unfold conjugate_action, Hnorm2, Hmul, Hconj; simpl. ring. Qed.

(* hence a UNIT quaternion acts as an ISOMETRY: it is a rotation *)
Theorem rotation_preserves_norm : forall q v,
  Hnorm2 q == 1 -> Hnorm2 (conjugate_action q v) == Hnorm2 v.
Proof.
  intros q v H. rewrite rotation_scales_norm. rewrite H. ring.
Qed.

(* ★ THE DOUBLE COVER: q and −q give exactly the same rotation *)
Theorem double_cover : forall q v,
  Heq (conjugate_action (Hneg q) v) (conjugate_action q v).
Proof.
  intros q v. unfold conjugate_action, Heq, Hneg, Hmul, Hconj; simpl.
  repeat split; ring.
Qed.

(* ===================== (½,½,½,½): the 120° rotation about (1,1,1) ========= *)
Definition qhalf : H := mkH (1#2) (1#2) (1#2) (1#2).

(* a genuine unit quaternion *)
Theorem qhalf_unit : Hnorm2 qhalf == 1.
Proof. vm_compute. reflexivity. Qed.

(* ★ its cube is −1 (so the rotation it induces has order 3) *)
Theorem qhalf_cube : Heq (Hmul (Hmul qhalf qhalf) qhalf) (Hneg Hone).
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.

(* ★ the conjugation action has ORDER 3: three turns return the axis to itself
   (this is the `cyc` order-3 rotation of RationalSO3.v, quaternion-side) *)
Theorem rotation_order3 :
  Heq (conjugate_action qhalf
        (conjugate_action qhalf
          (conjugate_action qhalf (pureH 1 0 0))))
      (pureH 1 0 0).
Proof. unfold Heq. repeat split; vm_compute; reflexivity. Qed.
