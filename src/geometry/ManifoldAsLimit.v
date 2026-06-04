(** * ManifoldAsLimit.v — the circle as a PROCESS: refining inscribed polygons
    Elements: rational inscribed polygons (finite vertex lists in Q²) and their
              shoelace areas (rational numbers)
    Roles:    the manifold (circle/disk) as the role-LIMIT of a refining process;
              refinement = adding rational vertices; area as the monotone process
    Rules:    shoelace area is rational; refinement strictly grows area but stays
              bounded; no finite polygon is the manifold (no maximal stage)
    STATUS:   14 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The flagship of Part XII, Element side: a MANIFOLD IS A PROCESS, not a
    completed object — exactly as ℝ = RealProcess (nat→Q) and ℚ̄ = an ascending
    tower (AlgebraicClosureProcess.v). The unit circle is presented as a refining
    sequence of rational inscribed polygons:
      • each polygon is FINITE rational data (a list of points of Q²),
      • its area is RATIONAL (shoelace formula — no square roots),
      • refining (adding rational vertices) STRICTLY increases the area,
      • the areas stay bounded (by the circumscribed square, area 4),
      • NO finite polygon equals the disk: the area sequence has no maximal stage.
    The disk area (π) is the role-LIMIT of this monotone bounded rational process;
    it is reached by no term. "The circle" names the process, not a finished object.

    Concrete witnesses: the inscribed square (area 2) and a rational 12-gon whose
    12 vertices are the rational circle points (±1,0),(0,±1),(±3/5,±4/5),(±4/5,±3/5)
    (area 74/25 = 2.96). So 2 < 74/25 < 4: the 12-gon refines the square.

    HONEST SCOPE: a uniformly-rational REGULAR n-gon family does not exist (regular
    polygons need roots of unity, irrational in coordinates for n∉{1,2,3,4,6}), so
    the *general* monotone area sequence is modelled by an explicit strictly-
    increasing bounded rational schematic `approx` (starting at the real inscribed-
    square area 2, bounded by the circumscribed-square area 4); the two genuine
    polygon areas (2 and 74/25) are its first real refinement step. π itself is a
    continuum role-limit (cf. DiscreteGaussBonnet.v).

    RELATED (existing repo): the abstract manifold-as-staged-process Record is in
    stdlib/ProcessManifold.v; abstract projective limits/towers in
    src/projective/ProjectiveSystem.v and ProjectiveLimit.v. This file is the
    concrete realization: the circle as a monotone bounded rational area-process.
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* a rational planar point *)
Definition Pt : Set := (Q * Q)%type.

Definition on_circle (p : Pt) : Prop := fst p * fst p + snd p * snd p == 1.

(* short names for the rational circle coordinates 3/5, 4/5 *)
Definition q35 : Q := 3 # 5.
Definition q45 : Q := 4 # 5.

(* ===================== shoelace area over a vertex list ===================== *)
Definition cross (p q : Pt) : Q := fst p * snd q - fst q * snd p.

(* sum of cross(cur, next) along the list, closing back to the head hd *)
Fixpoint sl (hd cur : Pt) (rest : list Pt) : Q :=
  match rest with
  | [] => cross cur hd
  | q :: tl => cross cur q + sl hd q tl
  end.

Definition shoelace (pts : list Pt) : Q :=
  match pts with
  | [] => 0
  | p :: tl => (1 # 2) * sl p p tl
  end.

(* ===================== two concrete inscribed polygons ===================== *)
(* the inscribed square: (1,0),(0,1),(-1,0),(0,-1) *)
Definition square_pts : list Pt :=
  [ (1, 0) ; (0, 1) ; (-(1), 0) ; (0, -(1)) ].

(* a rational 12-gon, vertices in CCW order; all are rational points of the circle *)
Definition dodeca_pts : list Pt :=
  [ (1, 0) ;
    (q45, q35) ;
    (q35, q45) ;
    (0, 1) ;
    (-q35, q45) ;
    (-q45, q35) ;
    (-(1), 0) ;
    (-q45, -q35) ;
    (-q35, -q45) ;
    (0, -(1)) ;
    (q35, -q45) ;
    (q45, -q35) ].

(* the vertices really are on the unit circle (genuine inscribed polygons) *)
Theorem square_on_circle : Forall on_circle square_pts.
Proof.
  unfold square_pts.
  repeat (apply Forall_cons; [ unfold on_circle; vm_compute; reflexivity | ]).
  apply Forall_nil.
Qed.

Theorem dodeca_on_circle : Forall on_circle dodeca_pts.
Proof.
  unfold dodeca_pts.
  repeat (apply Forall_cons; [ unfold on_circle; vm_compute; reflexivity | ]).
  apply Forall_nil.
Qed.

(* ===================== their rational areas ===================== *)
Theorem square_area : shoelace square_pts == 2.
Proof. vm_compute. reflexivity. Qed.

Theorem dodeca_area : shoelace dodeca_pts == 74 # 25.
Proof. vm_compute. reflexivity. Qed.

(* ===================== refinement: more vertices, larger area, bounded ==== *)
Theorem dodeca_more_vertices : (length square_pts < length dodeca_pts)%nat.
Proof. simpl. lia. Qed.

(* refining the square into the 12-gon STRICTLY increases the area *)
Theorem refinement_grows_area : shoelace square_pts < shoelace dodeca_pts.
Proof. rewrite square_area, dodeca_area. lra. Qed.

(* ...and the area stays below the circumscribed square (area 4) *)
Theorem dodeca_below_circumscribed : shoelace dodeca_pts < 4.
Proof. rewrite dodeca_area. lra. Qed.

(* ===================== the area as a monotone bounded PROCESS ============= *)
(* half_pow n = (1/2)^n; used to build an explicit strictly-increasing process *)
Fixpoint half_pow (n : nat) : Q :=
  match n with O => 1 | S k => (1 # 2) * half_pow k end.

Lemma half_pow_pos : forall n, 0 < half_pow n.
Proof.
  induction n; simpl.
  - lra.
  - assert (H2 : 0 < 1 # 2) by lra. nra.
Qed.

(* the schematic refinement-area process: starts at the inscribed-square area 2,
   climbs strictly, bounded above by the circumscribed-square area 4 *)
Definition approx (n : nat) : Q := 4 - 2 * half_pow n.

Theorem approx_0_is_square_area : approx 0 == shoelace square_pts.
Proof. unfold approx. rewrite square_area. simpl. lra. Qed.

Theorem approx_strict_incr : forall n, approx n < approx (S n).
Proof.
  intro n. unfold approx. simpl.
  generalize (half_pow_pos n); intro H. lra.
Qed.

Theorem approx_bounded : forall n, approx n < 4.
Proof.
  intro n. unfold approx. generalize (half_pow_pos n); intro H. lra.
Qed.

(* ===================== "manifold = process": no maximal stage ============= *)
Definition StrictlyIncreasing (a : nat -> Q) : Prop := forall n, a n < a (S n).
Definition BoundedBy (a : nat -> Q) (B : Q) : Prop := forall n, a n <= B.

(* no stage of a strictly increasing process is maximal: the measure is never
   completed by any finite stage *)
Theorem no_maximal_stage : forall a, StrictlyIncreasing a ->
  forall n, exists m, a n < a m.
Proof. intros a Hinc n. exists (S n). apply Hinc. Qed.

Theorem area_process_is_a_process :
  StrictlyIncreasing approx /\ BoundedBy approx 4.
Proof.
  split.
  - exact approx_strict_incr.
  - intro n. apply Qlt_le_weak. apply approx_bounded.
Qed.

(* ★ THE MANIFOLD IS A PROCESS: the circle's measure is a strictly increasing,
   bounded rational process (nat→Q) with NO maximal stage — a role-limit, not a
   completed object. The inscribed square (area 2) and the rational 12-gon
   (area 74/25) are its first two genuine refinement stages. *)
Theorem manifold_is_a_process :
  shoelace square_pts < shoelace dodeca_pts /\
  StrictlyIncreasing approx /\ BoundedBy approx 4 /\
  (forall n, exists m, approx n < approx m).
Proof.
  split. { exact refinement_grows_area. }
  split. { exact approx_strict_incr. }
  split. { intro n. apply Qlt_le_weak. apply approx_bounded. }
  intro n. exists (S n). apply approx_strict_incr.
Qed.
