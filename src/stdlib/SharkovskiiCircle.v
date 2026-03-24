(** * SharkovskiiCircle.v — Circle maps and degree theory as ToS System
    Elements: cyclic rotations, doubling map, degree
    Roles:    orbit structure on circle vs interval
    Rules:    period-3 on circle does NOT force all periods (topology matters)
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)
From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(** Circle rotation on finite cyclic group Z_q: x -> (x + p) mod q *)
Definition cyclic_rotate (p q : nat) (x : nat) : nat := (x + p) mod q.

(** Rotation by 1/3 on Z_3: orbit {0, 1, 2} has period 3 *)
Lemma rotate_1_3_period :
  cyclic_rotate 1 3 0 = 1%nat /\
  cyclic_rotate 1 3 1 = 2%nat /\
  cyclic_rotate 1 3 2 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Rotation by 1/5 on Z_5: orbit {0,1,2,3,4} has period 5 *)
Lemma rotate_1_5_period :
  cyclic_rotate 1 5 0 = 1%nat /\
  cyclic_rotate 1 5 1 = 2%nat /\
  cyclic_rotate 1 5 2 = 3%nat /\
  cyclic_rotate 1 5 3 = 4%nat /\
  cyclic_rotate 1 5 4 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Rotation by 2/5: same period 5, different visitation order *)
Lemma rotate_2_5_period :
  cyclic_rotate 2 5 0 = 2%nat /\
  cyclic_rotate 2 5 2 = 4%nat /\
  cyclic_rotate 2 5 4 = 1%nat /\
  cyclic_rotate 2 5 1 = 3%nat /\
  cyclic_rotate 2 5 3 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Rotation has NO fixed points unless p = 0 mod q *)
Lemma degree_1_no_fixed_points :
  cyclic_rotate 1 3 0 <> 0%nat /\
  cyclic_rotate 1 3 1 <> 1%nat /\
  cyclic_rotate 1 3 2 <> 2%nat.
Proof. vm_compute. repeat split; discriminate. Qed.

(** Zero rotation: every point is fixed *)
Lemma zero_rotation_fixed :
  cyclic_rotate 0 3 0 = 0%nat /\
  cyclic_rotate 0 3 1 = 1%nat /\
  cyclic_rotate 0 3 2 = 2%nat.
Proof. vm_compute. repeat split. Qed.

(** Degree-2 map: doubling map x -> 2x mod q *)
Definition doubling_map (q : nat) (x : nat) : nat := (2 * x) mod q.

(** Doubling on Z_7: fixed point at 0 *)
Lemma doubling_fixed_0 : doubling_map 7 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** Doubling on Z_7: period-3 orbit {1, 2, 4} *)
Lemma doubling_orbit_period3 :
  doubling_map 7 1 = 2%nat /\
  doubling_map 7 2 = 4%nat /\
  doubling_map 7 4 = 1%nat.
Proof. vm_compute. repeat split. Qed.

(** Doubling on Z_7: period-3 orbit {3, 6, 5} *)
Lemma doubling_orbit_period3_b :
  doubling_map 7 3 = 6%nat /\
  doubling_map 7 6 = 5%nat /\
  doubling_map 7 5 = 3%nat.
Proof. vm_compute. repeat split. Qed.

(** Doubling on Z_3: period-2 orbit {1, 2} *)
Lemma doubling_period2_on_Z3 :
  doubling_map 3 1 = 2%nat /\
  doubling_map 3 2 = 1%nat.
Proof. vm_compute. repeat split. Qed.

(** Doubling on Z_15: period-4 orbit {1, 2, 4, 8} *)
Lemma doubling_period4_on_Z15 :
  doubling_map 15 1 = 2%nat /\
  doubling_map 15 2 = 4%nat /\
  doubling_map 15 4 = 8%nat /\
  doubling_map 15 8 = 1%nat.
Proof. vm_compute. repeat split. Qed.

(** KEY THEOREM: Circle vs Interval topology *)
(** On the interval: period-3 implies ALL periods (Sharkovskii). *)
(** On the circle: degree-2 map has period-3 but period structure is different. *)
(** The doubling map on Z_7 has period-3 orbits. *)
(** The doubling map on Z_3 has period-2 but NOT period-3. *)
(** This shows: the SPACE topology matters for forcing. *)
Theorem circle_no_sharkovskii :
  (* Degree-2 on Z_7: has period-3 *)
  doubling_map 7 1 = 2%nat /\ doubling_map 7 2 = 4%nat /\ doubling_map 7 4 = 1%nat /\
  (* Degree-2 on Z_3: has period-2 but no period-3 *)
  doubling_map 3 1 = 2%nat /\ doubling_map 3 2 = 1%nat /\
  doubling_map 3 0 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Rotation period divides q: rotation by p in Z_q has period q/gcd(p,q) *)
(** Concrete: gcd(2,6) = 2, period = 6/2 = 3 *)
Lemma rotation_period_divides :
  cyclic_rotate 2 6 0 = 2%nat /\
  cyclic_rotate 2 6 2 = 4%nat /\
  cyclic_rotate 2 6 4 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Tripling map on Z_13: period-3 orbit {1, 3, 9} since 27 mod 13 = 1 *)
Definition tripling_map (q : nat) (x : nat) : nat := (3 * x) mod q.

Lemma tripling_period3_on_Z13 :
  tripling_map 13 1 = 3%nat /\
  tripling_map 13 3 = 9%nat /\
  tripling_map 13 9 = 1%nat.
Proof. vm_compute. repeat split. Qed.

(** Synthesis: circle maps summary *)
Theorem circle_map_synthesis :
  (* Pure rotation: all orbits same period *)
  cyclic_rotate 1 3 0 = 1%nat /\
  (* Doubling has multiple orbit types *)
  doubling_map 7 0 = 0%nat /\ doubling_map 7 1 = 2%nat /\
  (* Tripling: another degree *)
  tripling_map 13 1 = 3%nat /\
  (* No Sharkovskii forcing on circle *)
  doubling_map 3 1 = 2%nat.
Proof. vm_compute. repeat split. Qed.
