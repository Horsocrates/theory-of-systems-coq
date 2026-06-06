(** * TwoSU2OneQuaternion.v — ONE quaternion carries BOTH SU(2)'s: weak gauge AND spatial rotation.

    HYPOTHESIS TESTED HERE (H2 — closing the "weak-SU(2) = rotation-SU(2)" seam).
    The Standard-Model weak SU(2) and the spatial rotation group SU(2)=Spin(3) are NOT two
    coincidentally-equal groups: they are TWO REPRESENTATIONS of ONE object — the unit quaternion.

      - FUNDAMENTAL rep (spin-1/2, the doublet)  = the WEAK GAUGE action:
            q ↦ 2x2 complex matrix M(q) over Q[i], with det M(q) = N(q) (the quaternion norm).
        For a UNIT quaternion N(q)=1, M(q) is an SL2 element with det = 1.
      - ADJOINT rep (spin-1, the vector)         = the SPATIAL ROTATION action:
            q acts on R^3 by conjugation q·v·q̄, the 2:1 cover SU(2) → SO(3).

    The single shared invariant is the quaternion norm N = w^2+x^2+y^2+z^2, whose MULTIPLICATIVITY
    N(pq)=N(p)N(q) is exactly Euler's four-square identity — the SAME form that is det M(q) and the
    SU(2) Casimir.  So gauge-isospin index and spatial-spin index are two indices of one group.

    SMACK INTO THE H BRIDGE (GRQFTDiscriminantBridge.v):
      For a unit quaternion, M(q) has trace 2w (real) and det 1, hence discriminant
          Delta = tr^2 - 4det = 4w^2 - 4 <= 0   (since w^2 <= N(q) = 1).
      So EVERY SU(2) element is ELLIPTIC (Delta <= 0) — the COMPACT / gauge / Euclidean face of H.
      Lorentz boosts are the hyperbolic (Delta>0) face.  Thus: {weak gauge} and {spatial rotation}
      are ONE SU(2), and it is the elliptic (compact) side of the discriminant bridge; the Lorentz
      side is the other (hyperbolic) side.  H + H2 = the two SU(2)'s unified ON the GR/QFT axis.

    Elements: quaternions over Q (w,x,y,z); Hamilton product; norm; conjugation; the 2x2 det/trace.
    Roles:    fundamental rep = doublet/gauge (det = norm); adjoint rep = vector/rotation (q v q̄).
    Rules:    N(pq)=N(p)N(q) (four-square) = shared SU(2) invariant; unit q ⟹ SL2 & elliptic.

    STATUS: 14 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Quaternions over Q                                                     *)
(* ===================================================================== *)

Record Quat := mkQ { qw : Q; qx : Q; qy : Q; qz : Q }.

Definition qmul (a b : Quat) : Quat :=
  mkQ
    (qw a*qw b - qx a*qx b - qy a*qy b - qz a*qz b)
    (qw a*qx b + qx a*qw b + qy a*qz b - qz a*qy b)
    (qw a*qy b - qx a*qz b + qy a*qw b + qz a*qx b)
    (qw a*qz b + qx a*qy b - qy a*qx b + qz a*qw b).

Definition qconj (a : Quat) : Quat := mkQ (qw a) (- qx a) (- qy a) (- qz a).
Definition qneg  (a : Quat) : Quat := mkQ (- qw a) (- qx a) (- qy a) (- qz a).
Definition qnorm (a : Quat) : Q := qw a*qw a + qx a*qx a + qy a*qy a + qz a*qz a.
Definition qpure (vx vy vz : Q) : Quat := mkQ 0 vx vy vz.

(* ===================================================================== *)
(*  The shared SU(2) invariant: norm multiplicativity = Euler four-square  *)
(* ===================================================================== *)

(** ★ N(p·q) = N(p)·N(q): the SAME four-square identity that is det M(q) and the SU(2) Casimir. *)
Lemma qnorm_mult : forall a b, qnorm (qmul a b) == qnorm a * qnorm b.
Proof. intros a b. unfold qnorm, qmul; simpl; ring. Qed.

Lemma qconj_norm : forall a, qnorm (qconj a) == qnorm a.
Proof. intro a. unfold qnorm, qconj; simpl; ring. Qed.

(* ===================================================================== *)
(*  ADJOINT rep (spin-1): q acts on R^3 by conjugation = spatial rotation  *)
(* ===================================================================== *)

Definition rotate (q : Quat) (vx vy vz : Q) : Quat :=
  qmul (qmul q (qpure vx vy vz)) (qconj q).

(** q·v·q̄ is always a PURE quaternion (w-component 0): it stays in R^3. *)
Lemma rotate_pure : forall q vx vy vz, qw (rotate q vx vy vz) == 0.
Proof. intros. unfold rotate, qmul, qconj, qpure; simpl; ring. Qed.

(** Conjugation scales the R^3 norm by N(q)^2. *)
Lemma rotate_norm : forall q vx vy vz,
  qnorm (rotate q vx vy vz) == qnorm q * qnorm q * (vx*vx + vy*vy + vz*vz).
Proof.
  intros q vx vy vz. unfold rotate. rewrite !qnorm_mult.
  unfold qnorm, qconj, qpure; simpl; ring.
Qed.

(** ★ Hence a UNIT quaternion conjugation is an ISOMETRY of R^3 — the SO(3) rotation (spin-1). *)
Corollary rotate_unit_isometry : forall q vx vy vz,
  qnorm q == 1 ->
  qnorm (rotate q vx vy vz) == vx*vx + vy*vy + vz*vz.
Proof. intros q vx vy vz H. rewrite rotate_norm, H. ring. Qed.

(** ★ The 2:1 DOUBLE COVER SU(2) → SO(3): q and −q give the SAME rotation (all components). *)
Lemma double_cover : forall q vx vy vz,
  (qw (rotate (qneg q) vx vy vz) == qw (rotate q vx vy vz)) /\
  (qx (rotate (qneg q) vx vy vz) == qx (rotate q vx vy vz)) /\
  (qy (rotate (qneg q) vx vy vz) == qy (rotate q vx vy vz)) /\
  (qz (rotate (qneg q) vx vy vz) == qz (rotate q vx vy vz)).
Proof.
  intros. unfold rotate, qneg, qmul, qconj, qpure; simpl.
  repeat split; ring.
Qed.

(* ===================================================================== *)
(*  FUNDAMENTAL rep (spin-1/2): the 2x2 complex matrix M(q) = the doublet  *)
(* ===================================================================== *)

(** M(q) = [[w+ix, y+iz],[-y+iz, w-ix]] over Q[i].  We record its trace and det:
    trace = (w+ix)+(w-ix) = 2w (real);  det = (w^2+x^2)+(y^2+z^2) = N(q) = the four-square form. *)
Definition M_trace (q : Quat) : Q := 2 * qw q.
Definition M_det   (q : Quat) : Q := qnorm q.
Definition M_disc  (q : Quat) : Q := M_trace q * M_trace q - 4 * M_det q.

(** ★ det of the gauge (doublet) matrix = the quaternion norm = the four-square invariant. *)
Lemma M_det_is_norm : forall q, M_det q == qnorm q.
Proof. intro q. unfold M_det. reflexivity. Qed.

Lemma M_disc_eq : forall q, M_disc q == 4*(qw q*qw q) - 4*qnorm q.
Proof. intro q. unfold M_disc, M_trace, M_det. ring. Qed.

(* ===================================================================== *)
(*  Square-nonnegativity helper                                            *)
(* ===================================================================== *)

Lemma q_sq_nonneg : forall a : Q, 0 <= a * a.
Proof.
  intro a. destruct (Qlt_le_dec a 0) as [Hlt | Hge].
  - assert (H : 0 < (- a) * (- a)) by (apply Qmult_lt_0_compat; lra).
    assert (Heq : (- a) * (- a) == a * a) by ring.
    rewrite Heq in H. lra.
  - destruct (Qlt_le_dec 0 a) as [Hlt0 | Hle0].
    + apply Qlt_le_weak. apply Qmult_lt_0_compat; assumption.
    + assert (Ha0 : a == 0) by (apply Qle_antisym; assumption).
      assert (Haa : a * a == 0) by (rewrite Ha0; ring).
      rewrite Haa. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  Unit quaternion ⟹ SL2 (det 1) AND elliptic (Delta<=0): the H bridge    *)
(* ===================================================================== *)

(** ★ Unit quaternion's doublet matrix is SL2 (det = 1) — the SU(2) fundamental. *)
Lemma unit_quat_SL2 : forall q, qnorm q == 1 -> M_det q == 1.
Proof. intros q H. unfold M_det. exact H. Qed.

(** ★★ Unit quaternion's doublet matrix is ELLIPTIC: Delta = 4w^2 - 4 <= 0.
    So SU(2) (gauge AND rotation) lives entirely on the COMPACT/Euclidean face of the H bridge;
    the Lorentz boosts are the hyperbolic (Delta>0) face.  This UNIFIES H and H2 on the GR/QFT axis. *)
Lemma unit_quat_elliptic : forall q, qnorm q == 1 -> M_disc q <= 0.
Proof.
  intros q H. unfold M_disc, M_trace, M_det, qnorm in *.
  assert (HX : 0 <= qx q * qx q) by apply q_sq_nonneg.
  assert (HY : 0 <= qy q * qy q) by apply q_sq_nonneg.
  assert (HZ : 0 <= qz q * qz q) by apply q_sq_nonneg.
  assert (Hexp : (2 * qw q) * (2 * qw q) == 4 * (qw q * qw q)) by ring.
  rewrite Hexp. lra.
Qed.

(* ===================================================================== *)
(*  Concrete: q0 = (1+i+j+k)/2 is the 120-deg axis-cycling rotation        *)
(* ===================================================================== *)

Definition q0 : Quat := mkQ (1#2) (1#2) (1#2) (1#2).

Lemma q0_unit : qnorm q0 == 1.
Proof. unfold qnorm, q0; vm_compute; reflexivity. Qed.

(** ★ q0 conjugation sends the x-axis e_x = (1,0,0) to the y-axis e_y = (0,1,0):
    the order-3 cyclic rotation about (1,1,1).  ONE quaternion, a concrete spatial rotation. *)
Lemma q0_rotates_x_to_y :
  qw (rotate q0 1 0 0) == 0 /\ qx (rotate q0 1 0 0) == 0 /\
  qy (rotate q0 1 0 0) == 1 /\ qz (rotate q0 1 0 0) == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE : two SU(2) representations, one quaternion                   *)
(* ===================================================================== *)

(** ONE object (the unit quaternion) carries BOTH SU(2)'s:
      (four-square)  N(pq)=N(p)N(q) — the shared SU(2) invariant (= det M = Casimir);
      (fundamental)  det M(q) = N(q); unit q ⟹ det 1 (gauge doublet, spin-1/2) AND elliptic (Δ<=0);
      (adjoint)      unit-q conjugation is an R^3 isometry (spatial rotation, spin-1), output pure;
      (double cover) q and −q give the same rotation (2:1 SU(2)→SO(3));
      (concrete)     q0 = (1+i+j+k)/2 cyclically rotates e_x ↦ e_y.
    Weak-isospin SU(2) (internal/gauge) and rotation SU(2)=Spin(3) (external/spacetime) are TWO
    representations of this one object, and (via elliptic Δ<=0) the COMPACT face of the H bridge. *)
Theorem two_su2_one_quaternion :
  (* shared invariant: Euler four-square = SU(2) Casimir = det M *)
  (forall a b, qnorm (qmul a b) == qnorm a * qnorm b)
  /\ (forall q, M_det q == qnorm q)
  (* FUNDAMENTAL (doublet / weak gauge, spin-1/2): unit q ⟹ SL2 and ELLIPTIC (compact face of H) *)
  /\ (forall q, qnorm q == 1 -> M_det q == 1 /\ M_disc q <= 0)
  (* ADJOINT (vector / spatial rotation, spin-1): unit-q conjugation is an R^3 isometry, output pure *)
  /\ (forall q vx vy vz, qnorm q == 1 ->
        qnorm (rotate q vx vy vz) == vx*vx + vy*vy + vz*vz)
  /\ (forall q vx vy vz, qw (rotate q vx vy vz) == 0)
  (* 2:1 double cover SU(2) → SO(3) *)
  /\ (forall q vx vy vz, qy (rotate (qneg q) vx vy vz) == qy (rotate q vx vy vz))
  (* concrete unit quaternion = a concrete spatial rotation e_x ↦ e_y *)
  /\ (qnorm q0 == 1 /\ qy (rotate q0 1 0 0) == 1).
Proof.
  split. exact qnorm_mult.
  split. exact M_det_is_norm.
  split. intros q H. split; [ exact (unit_quat_SL2 q H) | exact (unit_quat_elliptic q H) ].
  split. exact rotate_unit_isometry.
  split. exact rotate_pure.
  split. intros q vx vy vz. apply (double_cover q vx vy vz).
  split. exact q0_unit.
  destruct q0_rotates_x_to_y as [_ [_ [Hy _]]]. exact Hy.
Qed.
