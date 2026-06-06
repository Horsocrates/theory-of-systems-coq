(** * GRQFTDiscriminantBridge.v — ONE 2x2 discriminant carries BOTH the GR datum
      (causal type / metric signature) AND the QFT datum (compact gauge; Element/role-limit).

    HYPOTHESIS TESTED HERE.
    For a 2x2 SL2 element M = [[a,b],[c,d]] with det M = 1, the discriminant
        Delta = tr^2 - 4*det = (a-d)^2 + 4*b*c
    is a TWO-BIT master valve unifying the two faces of the base:

      BIT 1 — sign(Delta) selects the SIGNATURE / causal type (the GR datum):
         Delta < 0  -> elliptic   -> rotation  -> preserves x^2 + y^2  (Euclidean (+,+))
                                                  = COMPACT / gauge / internal
         Delta = 0  -> parabolic  -> null      -> the lightcone boundary
         Delta > 0  -> hyperbolic -> boost     -> preserves x^2 - y^2  (Lorentzian (+,-))
                                                  = NON-COMPACT / Lorentz / spacetime

      BIT 2 — (within Delta >= 0) Delta a perfect square selects FINITIZATION (the QFT/atlas datum):
         Delta a perfect square -> rational eigenvalue -> Element    (3-4-5 boost: Delta=9/4, eigs 2,1/2)
         Delta not a square     -> irrational eigenvalue -> role-limit (sqrt2 Pell boost: Delta=32)

    So ONE rational 2x2 matrix simultaneously fixes the GR causal type (sign of Delta) and the
    QFT Element/role-limit status (square-ness of Delta).  This MERGES three previously separate
    threads of the codebase into one valve:
      - ConicDuality.v        (circle c^2+s^2=1 vs hyperbola g^2-s^2=1),
      - ReductionAtlas*.v     (Delta perfect-square = Element vs role-limit master dial),
      - CausalSignature.v     (the single minus sign of the (-,+,+,+) Lorentzian signature).
    The sign of Delta IS the sign of the norm form D in x^2 - D*y^2 IS the metric signature.

    Elements: rational 2x2 matrices; tr, det, Delta; the preserved quadratic forms x^2+-y^2.
    Roles:    Delta<0 = rotation/gauge/Euclidean; Delta>0 = boost/Lorentz; Delta=0 = null/lightcone.
    Rules:    sign(Delta) = signature selector; perfect-square(Delta) = Element/role-limit selector.

    STATUS: 27 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The 2x2 invariants                                                     *)
(* ===================================================================== *)

Definition mtr   (a d : Q)         : Q := a + d.
Definition mdet  (a b c d : Q)     : Q := a*d - b*c.
Definition mdisc (a b c d : Q)     : Q := (a - d)*(a - d) + 4*(b*c).

(** Delta = tr^2 - 4*det (the characteristic-polynomial discriminant). *)
Lemma disc_is_tr2_minus_4det : forall a b c d,
  mdisc a b c d == (mtr a d)*(mtr a d) - 4*(mdet a b c d).
Proof. intros. unfold mdisc, mtr, mdet. ring. Qed.

(* ===================================================================== *)
(*  Five concrete SL2 elements (det = 1)                                   *)
(* ===================================================================== *)

(* Rotation at the 3-4-5 circle point: [[3/5,-4/5],[4/5,3/5]] (Delta<0, elliptic) *)
Definition r_a := 3#5.  Definition r_b := -(4#5).
Definition r_c := 4#5.  Definition r_d := 3#5.

(* Rotation by 90 deg: [[0,-1],[1,0]] (order 4, Delta<0) *)
Definition q_a : Q := 0.  Definition q_b := -(1).
Definition q_c : Q := 1.  Definition q_d : Q := 0.

(* Boost at the 3-4-5 hyperbola point: [[5/4,3/4],[3/4,5/4]] (Delta>0, Element) *)
Definition b_a := 5#4.  Definition b_b := 3#4.
Definition b_c := 3#4.  Definition b_d := 5#4.

(* Pell boost for sqrt2: [[3,4],[2,3]] (Delta>0, role-limit) *)
Definition p_a := 3#1.  Definition p_b := 4#1.
Definition p_c := 2#1.  Definition p_d := 3#1.

(* Parabolic / null shear: [[1,1],[0,1]] (Delta=0, lightcone) *)
Definition n_a : Q := 1.  Definition n_b : Q := 1.
Definition n_c : Q := 0.  Definition n_d : Q := 1.

Lemma rot345_sl2  : mdet r_a r_b r_c r_d == 1.
Proof. unfold mdet, r_a, r_b, r_c, r_d. vm_compute. reflexivity. Qed.
Lemma rot90_sl2   : mdet q_a q_b q_c q_d == 1.
Proof. unfold mdet, q_a, q_b, q_c, q_d. vm_compute. reflexivity. Qed.
Lemma boost345_sl2: mdet b_a b_b b_c b_d == 1.
Proof. unfold mdet, b_a, b_b, b_c, b_d. vm_compute. reflexivity. Qed.
Lemma boostP_sl2  : mdet p_a p_b p_c p_d == 1.
Proof. unfold mdet, p_a, p_b, p_c, p_d. vm_compute. reflexivity. Qed.
Lemma par_sl2     : mdet n_a n_b n_c n_d == 1.
Proof. unfold mdet, n_a, n_b, n_c, n_d. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  BIT 1 : sign(Delta) = signature / causal type                          *)
(* ===================================================================== *)

(** Rotations are ELLIPTIC: Delta < 0  (compact / gauge / Euclidean side). *)
Lemma rot345_elliptic : mdisc r_a r_b r_c r_d < 0.
Proof. unfold mdisc, r_a, r_b, r_c, r_d. lra. Qed.

Lemma rot90_elliptic : mdisc q_a q_b q_c q_d < 0.
Proof. unfold mdisc, q_a, q_b, q_c, q_d. lra. Qed.

(** Boosts are HYPERBOLIC: Delta > 0  (non-compact / Lorentz / spacetime side). *)
Lemma boost345_hyperbolic : 0 < mdisc b_a b_b b_c b_d.
Proof. unfold mdisc, b_a, b_b, b_c, b_d. lra. Qed.

Lemma boostP_hyperbolic : 0 < mdisc p_a p_b p_c p_d.
Proof. unfold mdisc, p_a, p_b, p_c, p_d. lra. Qed.

(** The shear is PARABOLIC: Delta = 0  (the null / lightcone boundary). *)
Lemma par_parabolic : mdisc n_a n_b n_c n_d == 0.
Proof. unfold mdisc, n_a, n_b, n_c, n_d. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The two preserved quadratic forms = the two signatures                 *)
(* ===================================================================== *)

(** A rotation [[c,-s],[s,c]] preserves x^2 + y^2 up to the factor c^2+s^2.
    With c^2+s^2 = 1 (circle) it is an isometry of the EUCLIDEAN (+,+) form. *)
Lemma rotation_preserves_euclid : forall c s x y,
  (c*x - s*y)*(c*x - s*y) + (s*x + c*y)*(s*x + c*y)
  == (c*c + s*s) * (x*x + y*y).
Proof. intros. ring. Qed.

(** A boost [[g,s],[s,g]] preserves x^2 - y^2 up to the factor g^2-s^2.
    With g^2-s^2 = 1 (hyperbola) it is an isometry of the LORENTZIAN (+,-) form. *)
Lemma boost_preserves_mink : forall g s x y,
  (g*x + s*y)*(g*x + s*y) - (s*x + g*y)*(s*x + g*y)
  == (g*g - s*s) * (x*x - y*y).
Proof. intros. ring. Qed.

(** The unit conditions for our two concrete elements. *)
Lemma rot345_on_circle      : r_a*r_a + r_c*r_c == 1.
Proof. unfold r_a, r_c. vm_compute. reflexivity. Qed.
Lemma boost345_on_hyperbola : b_a*b_a - b_b*b_b == 1.
Proof. unfold b_a, b_b. vm_compute. reflexivity. Qed.

(** Hence: the 3-4-5 rotation is an exact isometry of x^2+y^2 (Euclidean / gauge). *)
Corollary rot345_euclid_isometry : forall x y,
  (r_a*x + r_b*y)*(r_a*x + r_b*y) + (r_c*x + r_d*y)*(r_c*x + r_d*y) == x*x + y*y.
Proof.
  intros x y.
  (* r_a=c, r_b=-s, r_c=s, r_d=c with c=3/5, s=4/5 *)
  assert (Hrw : (r_a*x + r_b*y)*(r_a*x + r_b*y) + (r_c*x + r_d*y)*(r_c*x + r_d*y)
             == (r_a*r_a + r_c*r_c) * (x*x + y*y)).
  { unfold r_a, r_b, r_c, r_d. ring. }
  rewrite Hrw, rot345_on_circle. ring.
Qed.

(** And: the 3-4-5 boost is an exact isometry of x^2-y^2 (Lorentzian / spacetime). *)
Corollary boost345_mink_isometry : forall x y,
  (b_a*x + b_b*y)*(b_a*x + b_b*y) - (b_c*x + b_d*y)*(b_c*x + b_d*y) == x*x - y*y.
Proof.
  intros x y.
  assert (Hrw : (b_a*x + b_b*y)*(b_a*x + b_b*y) - (b_c*x + b_d*y)*(b_c*x + b_d*y)
             == (b_a*b_a - b_b*b_b) * (x*x - y*y)).
  { unfold b_a, b_b, b_c, b_d. ring. }
  rewrite Hrw, boost345_on_hyperbola. ring.
Qed.

(* ===================================================================== *)
(*  BIT 2 : perfect-square(Delta) = Element vs role-limit (boost world)    *)
(* ===================================================================== *)

(** The 3-4-5 boost has Delta = 9/4 = (3/2)^2 : a PERFECT (rational) square. *)
Lemma boost345_disc        : mdisc b_a b_b b_c b_d == 9#4.
Proof. unfold mdisc, b_a, b_b, b_c, b_d. vm_compute. reflexivity. Qed.

Lemma boost345_disc_square : (3#2)*(3#2) == mdisc b_a b_b b_c b_d.
Proof. unfold mdisc, b_a, b_b, b_c, b_d. vm_compute. reflexivity. Qed.

(** ...hence rational eigenvalues 2 and 1/2 (sum = tr = 5/2, product = det = 1) : ELEMENT. *)
Lemma boost345_eigs :
  (2 + (1#2) == mtr b_a b_d) /\ (2 * (1#2) == mdet b_a b_b b_c b_d).
Proof.
  split; unfold mtr, mdet, b_a, b_b, b_c, b_d; vm_compute; reflexivity.
Qed.

(** The Pell sqrt2 boost has Delta = 32 : NOT a perfect square. *)
Lemma boostP_disc : mdisc p_a p_b p_c p_d == 32.
Proof. unfold mdisc, p_a, p_b, p_c, p_d. vm_compute. reflexivity. Qed.

Lemma thirtytwo_not_square : forall m : Z, (m * m <> 32)%Z.
Proof.
  intros m H.
  assert (HM : (Z.abs m * Z.abs m = 32)%Z).
  { rewrite <- Z.abs_mul. rewrite H. reflexivity. }
  assert (HA : (0 <= Z.abs m)%Z) by apply Z.abs_nonneg.
  assert (Hcase : (Z.abs m <= 5 \/ 6 <= Z.abs m)%Z) by lia.
  destruct Hcase as [Hle | Hge]; nia.
Qed.

(** ...hence eigenvalues 3 +- 2*sqrt2 are irrational : ROLE-LIMIT (continuum boost). *)

(* ===================================================================== *)
(*  The null cone lives only in the Lorentzian (boost / Delta>0) world     *)
(* ===================================================================== *)

Definition mink   (x y : Q) : Q := x*x - y*y.   (* boost-invariant: signature (+,-) *)
Definition euclid (x y : Q) : Q := x*x + y*y.   (* rotation-invariant: signature (+,+) *)

(** Lorentzian form: genuine causal trichotomy (timelike / null / spacelike). *)
Lemma timelike_345  : 0 < mink 5 3.   (* 25 - 9 = 16 > 0, proper time^2 = 16 = 4^2 *)
Proof. unfold mink. lra. Qed.
Lemma null_on_cone  : mink 1 1 == 0.  (* (1,1) <> origin yet on the lightcone *)
Proof. unfold mink. vm_compute. reflexivity. Qed.
Lemma spacelike_345 : mink 3 5 < 0.   (* 9 - 25 = -16 < 0 *)
Proof. unfold mink. lra. Qed.

(** Euclidean (gauge) form: NO null cone off the origin — definite, no causal structure. *)
Lemma euclid_no_null_offorigin : 0 < euclid 1 1.   (* 1 + 1 = 2 > 0 *)
Proof. unfold euclid. lra. Qed.

(* ===================================================================== *)
(*  CAPSTONE : one discriminant, both datums                               *)
(* ===================================================================== *)

(** ONE 2x2 discriminant Delta = tr^2 - 4det, read two ways, carries simultaneously:
      (sign)    the GR datum  — elliptic/parabolic/hyperbolic = gauge-Euclid / null / Lorentz,
                with the two preserved forms x^2+y^2 (+,+) and x^2-y^2 (+,-);
      (square)  the QFT datum — Element (rational eigenvalue) vs role-limit (irrational).
    sign(Delta) = sign of D in the norm form x^2 - D*y^2 = the metric signature. *)
Theorem gr_qft_one_discriminant :
  (* all three are SL2 (det = 1) *)
  (mdet r_a r_b r_c r_d == 1)
  /\ (mdet b_a b_b b_c b_d == 1)
  /\ (mdet p_a p_b p_c p_d == 1)
  (* BIT 1 — sign(Delta) = signature / causal type *)
  /\ (mdisc r_a r_b r_c r_d < 0)        (* rotation : elliptic  / compact / gauge / Euclidean *)
  /\ (0 < mdisc b_a b_b b_c b_d)        (* boost    : hyperbolic / non-compact / Lorentz       *)
  /\ (mdisc n_a n_b n_c n_d == 0)       (* shear    : parabolic  / null / lightcone            *)
  (* the two preserved forms = the two signatures *)
  /\ (forall c s x y, (c*x - s*y)*(c*x - s*y) + (s*x + c*y)*(s*x + c*y)
        == (c*c + s*s)*(x*x + y*y))     (* rotation <-> x^2 + y^2  (+,+)  Euclidean / gauge     *)
  /\ (forall g s x y, (g*x + s*y)*(g*x + s*y) - (s*x + g*y)*(s*x + g*y)
        == (g*g - s*s)*(x*x - y*y))     (* boost    <-> x^2 - y^2  (+,-)  Lorentzian / spacetime *)
  (* BIT 2 — perfect-square(Delta) = Element vs role-limit, within the boost (Delta>0) world *)
  /\ ((3#2)*(3#2) == mdisc b_a b_b b_c b_d)               (* 3-4-5 boost : Delta=9/4 square -> Element *)
  /\ (mdisc p_a p_b p_c p_d == 32)                        (* sqrt2 Pell boost : Delta=32 ...          *)
  /\ (forall m : Z, (m*m <> 32)%Z).                       (* ...not a square -> role-limit            *)
Proof.
  split. exact rot345_sl2.
  split. exact boost345_sl2.
  split. exact boostP_sl2.
  split. exact rot345_elliptic.
  split. exact boost345_hyperbolic.
  split. exact par_parabolic.
  split. exact rotation_preserves_euclid.
  split. exact boost_preserves_mink.
  split. exact boost345_disc_square.
  split. exact boostP_disc.
  exact thirtytwo_not_square.
Qed.
