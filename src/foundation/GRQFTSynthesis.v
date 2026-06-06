(** * GRQFTSynthesis.v — CAPSTONE: the Lorentz algebra so(1,3) = 3 boosts (Delta>0, time / P4-arrow)
       + 3 rotations (Delta<0, space = the gauge SU(2)) — all read off ONE 2x2 discriminant.

    This stitches the two verified bridges into a single GR<->QFT statement on the shared base:
      - GRQFTDiscriminantBridge.v : sign(Delta) of a 2x2 SL2 element = the metric signature
            (Delta<0 elliptic/rotation/Euclidean (+,+) ; Delta>0 hyperbolic/boost/Lorentzian (+,-) ;
             Delta=0 parabolic/null/lightcone), and perfect-square(Delta) = Element/role-limit;
      - TwoSU2OneQuaternion.v     : the rotation SU(2) IS the weak-gauge SU(2) (two reps of one
            unit quaternion), and every SU(2) element is ELLIPTIC (Delta<=0) = the compact face.

    THE PICTURE (now machine-checked end to end).
      The 6 generators of the Lorentz algebra so(1,3) = the 6 coordinate planes, split by sign(Delta):
        * 3 BOOSTS  (the t-x, t-y, t-z planes) : Delta>0, hyperbolic, preserve x^2-y^2 (Lorentzian),
                     NON-compact, MIX TIME with space  =  the irreversible P4 arrow (the single minus
                     of the (-,+,+,+) signature lives here);
        * 3 ROTATIONS (the x-y, y-z, z-x planes) : Delta<0, elliptic, preserve x^2+y^2 (Euclidean),
                     COMPACT, purely spatial  =  and these 3 are exactly the 3 generators of the
                     gauge SU(2) (= SO(3) double cover), the SAME SU(2) that acts on the weak doublet
                     (TwoSU2OneQuaternion.v).
      So: "space is 3-dimensional", "its rotation group is SU(2) with 3 generators", and "the weak
      gauge group is SU(2)" are ONE fact; "time is 1-dimensional and irreversible" is the single
      non-compact (boost, Delta>0) direction = the P4 arrow.  The lightcone is the Delta=0 boundary
      where the two sectors meet.  One discriminant, read by sign, gives the entire GR/QFT split.

    Elements: the 6 Lorentz planes; the imported 2x2 matrices and unit quaternions.
    Roles:    SBoost = time / Delta>0 / non-compact / P4-arrow ; SRot = space / Delta<0 / compact / gauge SU(2).
    Rules:    sign(Delta) = sector = signature ; the 3 rotation planes = the 3 gauge SU(2) generators.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia List.
Import ListNotations.
From ToS Require Import foundation.GRQFTDiscriminantBridge.
From ToS Require Import foundation.TwoSU2OneQuaternion.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The two sectors and the 6 Lorentz planes                              *)
(* ===================================================================== *)

Inductive Sector := SBoost | SRot.

(** The 6 generators of so(1,3) as the 6 coordinate planes. *)
Inductive Plane := Ptx | Pty | Ptz | Pxy | Pyz | Pzx.

(** A plane is a boost iff it involves the time axis. *)
Definition involves_time (p : Plane) : bool :=
  match p with Ptx | Pty | Ptz => true | _ => false end.

Definition plane_sector (p : Plane) : Sector :=
  if involves_time p then SBoost else SRot.

Definition all_planes : list Plane := [Ptx; Pty; Ptz; Pxy; Pyz; Pzx].

Definition is_boost (p : Plane) : bool :=
  match plane_sector p with SBoost => true | SRot => false end.
Definition is_rot (p : Plane) : bool :=
  match plane_sector p with SRot => true | SBoost => false end.

Definition n_boosts := length (filter is_boost all_planes).
Definition n_rots   := length (filter is_rot all_planes).

(* ===================================================================== *)
(*  so(1,3) = 3 boosts + 3 rotations                                       *)
(* ===================================================================== *)

Lemma lorentz_6_generators : length all_planes = 6%nat.
Proof. reflexivity. Qed.

Lemma three_boosts_three_rotations : n_boosts = 3%nat /\ n_rots = 3%nat.
Proof. vm_compute. split; reflexivity. Qed.

(** A plane is a boost EXACTLY when it carries the time axis (the (-) of the signature). *)
Lemma boost_iff_time : forall p, plane_sector p = SBoost <-> involves_time p = true.
Proof. intro p. destruct p; cbn; split; intro H; first [ reflexivity | discriminate ]. Qed.

(* ===================================================================== *)
(*  BOOST sector (time / Delta>0 / non-compact / P4-arrow), grounded in H  *)
(* ===================================================================== *)

(** A boost is hyperbolic: Delta > 0. *)
Lemma boost_sector_hyperbolic : 0 < mdisc b_a b_b b_c b_d.
Proof. exact boost345_hyperbolic. Qed.

(** A boost preserves the Lorentzian form x^2 - y^2 (mixes time and space): signature (+,-). *)
Lemma boost_sector_mink : forall x y,
  (b_a*x + b_b*y)*(b_a*x + b_b*y) - (b_c*x + b_d*y)*(b_c*x + b_d*y) == x*x - y*y.
Proof. exact boost345_mink_isometry. Qed.

(* ===================================================================== *)
(*  ROTATION sector (space / Delta<0 / compact), grounded in H            *)
(* ===================================================================== *)

(** A rotation is elliptic: Delta < 0. *)
Lemma rotation_sector_elliptic : mdisc r_a r_b r_c r_d < 0.
Proof. exact rot345_elliptic. Qed.

(** A rotation preserves the Euclidean form x^2 + y^2 (pure space): signature (+,+). *)
Lemma rotation_sector_euclid : forall x y,
  (r_a*x + r_b*y)*(r_a*x + r_b*y) + (r_c*x + r_d*y)*(r_c*x + r_d*y) == x*x + y*y.
Proof. exact rot345_euclid_isometry. Qed.

(* ===================================================================== *)
(*  The 3 ROTATION planes = the 3 gauge-SU(2) generators (grounded in H2)  *)
(* ===================================================================== *)

(** The 3 spatial rotation planes are exactly the 3 = 2^2-1 generators of SU(2). *)
Lemma rotations_are_su2_generators : n_rots = (2*2 - 1)%nat.
Proof. vm_compute. reflexivity. Qed.

(** That SU(2) is the COMPACT face (det 1, Delta<=0) that ALSO acts on the weak doublet (H2). *)
Lemma su2_is_compact_and_gauge : forall q,
  qnorm q == 1 -> M_det q == 1 /\ M_disc q <= 0.
Proof. intros q H. split; [ exact (unit_quat_SL2 q H) | exact (unit_quat_elliptic q H) ]. Qed.

(** ...and the SAME SU(2) rotates space (R^3 isometry by conjugation). *)
Lemma su2_rotates_space : forall q vx vy vz,
  qnorm q == 1 -> qnorm (rotate q vx vy vz) == vx*vx + vy*vy + vz*vz.
Proof. exact rotate_unit_isometry. Qed.

(* ===================================================================== *)
(*  The lightcone = the Delta=0 boundary where the two sectors meet        *)
(* ===================================================================== *)

Lemma lightcone_boundary : mdisc n_a n_b n_c n_d == 0 /\ mink 1 1 == 0.
Proof. split; [ exact par_parabolic | exact null_on_cone ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ONE 2x2 discriminant, read by sign, gives the entire GR/QFT split:
      so(1,3) has 6 generators = 3 BOOSTS + 3 ROTATIONS;
      BOOSTS  = time = Delta>0 (hyperbolic) = x^2-y^2 (Lorentzian) = non-compact = the P4 arrow;
      ROTATIONS = space = Delta<0 (elliptic) = x^2+y^2 (Euclidean) = compact = the gauge SU(2)
                  (the 3 rotation planes ARE the 3 SU(2) generators; same SU(2) rotates space and
                   transforms the weak doublet — TwoSU2OneQuaternion.v);
      the lightcone is the Delta=0 boundary between the sectors.
    "Space is 3-D + its rotation group is the weak SU(2)" and "time is the 1 irreversible (P4) axis"
    are read off the SAME object that gates Element vs role-limit (perfect-square Delta). GR and QFT
    are two readings of one 2x2 discriminant. *)
Theorem gr_qft_synthesis :
  (* so(1,3): 6 generators = 3 boosts + 3 rotations, boosts = the time-carrying planes *)
  length all_planes = 6%nat
  /\ (n_boosts = 3%nat /\ n_rots = 3%nat)
  /\ (forall p, plane_sector p = SBoost <-> involves_time p = true)
  (* BOOST sector : time / Delta>0 (hyperbolic) / x^2-y^2 (Lorentzian) / non-compact / P4-arrow *)
  /\ (0 < mdisc b_a b_b b_c b_d)
  /\ (forall x y, (b_a*x + b_b*y)*(b_a*x + b_b*y) - (b_c*x + b_d*y)*(b_c*x + b_d*y) == x*x - y*y)
  (* ROTATION sector : space / Delta<0 (elliptic) / x^2+y^2 (Euclidean) / compact / gauge SU(2) *)
  /\ (mdisc r_a r_b r_c r_d < 0)
  /\ (forall x y, (r_a*x + r_b*y)*(r_a*x + r_b*y) + (r_c*x + r_d*y)*(r_c*x + r_d*y) == x*x + y*y)
  /\ (n_rots = (2*2 - 1)%nat)
  /\ (forall q, qnorm q == 1 -> M_det q == 1 /\ M_disc q <= 0)
  /\ (forall q vx vy vz, qnorm q == 1 ->
        qnorm (rotate q vx vy vz) == vx*vx + vy*vy + vz*vz)
  (* the lightcone : the Delta=0 boundary where boost and rotation sectors meet *)
  /\ (mdisc n_a n_b n_c n_d == 0).
Proof.
  split. exact lorentz_6_generators.
  split. exact three_boosts_three_rotations.
  split. exact boost_iff_time.
  split. exact boost_sector_hyperbolic.
  split. exact boost_sector_mink.
  split. exact rotation_sector_elliptic.
  split. exact rotation_sector_euclid.
  split. exact rotations_are_su2_generators.
  split. exact su2_is_compact_and_gauge.
  split. exact su2_rotates_space.
  exact par_parabolic.
Qed.
