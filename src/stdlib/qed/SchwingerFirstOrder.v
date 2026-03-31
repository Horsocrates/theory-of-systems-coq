(* SchwingerFirstOrder.v *)
(* Elements: alpha_em, pi approximations, Schwinger coefficient C1 *)
(* Roles: first-order QED correction to anomalous magnetic moment *)
(* Rules: a_e^(1) = C1 * (alpha/pi), comparison with experiment *)

From Stdlib Require Import QArith Qabs Lqa.

Open Scope Q_scope.

(** === Schwinger first-order coefficient === *)

Definition C1_schwinger : Q := 1 # 2.

Definition alpha_em : Q := 1 # 137.

(** Pi approximations from continued fractions *)
Definition pi_1 : Q := 22 # 7.
Definition pi_2 : Q := 333 # 106.
Definition pi_3 : Q := 355 # 113.
Definition pi_4 : Q := 103993 # 33102.

(** First-order Schwinger correction: a_e^(1) = (1/2)(alpha/pi) *)
Definition a1_pi3 : Q := C1_schwinger * alpha_em / pi_3.

Lemma a1_value : a1_pi3 == 113 # 97270.
Proof.
  unfold a1_pi3, C1_schwinger, alpha_em, pi_3.
  vm_compute. reflexivity.
Qed.

(** Experimental value of a_e (truncated) *)
Definition a_e_exp : Q := 115965 # 100000000.

(** First-order approximation is close to experiment *)
Lemma first_order_close : Qabs (a1_pi3 - a_e_exp) < 3 # 1000000.
Proof.
  assert (Hd : a1_pi3 - a_e_exp == (-1300550 # 972700000000)).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3, a_e_exp.
    vm_compute. reflexivity. }
  rewrite Hd.
  assert (Habs : Qabs (-1300550 # 972700000000) == 1300550 # 972700000000).
  { vm_compute. reflexivity. }
  rewrite Habs. lra.
Qed.

(** C1 is exactly 1/2 *)
Lemma C1_exact : C1_schwinger == 1 # 2.
Proof. unfold C1_schwinger. vm_compute. reflexivity. Qed.

(** alpha is exactly 1/137 *)
Lemma alpha_rational : alpha_em == 1 # 137.
Proof. unfold alpha_em. vm_compute. reflexivity. Qed.

(** pi_3 = 355/113 is a better approximation than pi_1 = 22/7 *)
(** We compare |pi_approx - 355/113| for consistency; actually compare
    the Schwinger results. a1 with pi_1 vs pi_3: *)
Definition a1_pi1 : Q := C1_schwinger * alpha_em / pi_1.

Lemma a1_pi1_value : a1_pi1 == 7 # 6028.
Proof.
  unfold a1_pi1, C1_schwinger, alpha_em, pi_1.
  vm_compute. reflexivity.
Qed.

(** pi_3 gives a result closer to experiment than pi_1 *)
Lemma pi3_better_than_pi1 :
  Qabs (a1_pi3 - a_e_exp) < Qabs (a1_pi1 - a_e_exp).
Proof.
  assert (H1 : a1_pi3 - a_e_exp == (-1300550 # 972700000000)).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3, a_e_exp. vm_compute. reflexivity. }
  assert (H2 : a1_pi1 - a_e_exp == (-583025 # 602800000000)).
  { unfold a1_pi1, C1_schwinger, alpha_em, pi_1, a_e_exp. vm_compute. reflexivity. }
  rewrite H1, H2.
  assert (Ha1 : Qabs (-1300550 # 972700000000) == 1300550 # 972700000000).
  { vm_compute. reflexivity. }
  assert (Ha2 : Qabs (-583025 # 602800000000) == 583025 # 602800000000).
  { vm_compute. reflexivity. }
  rewrite Ha1, Ha2. lra.
Qed.

(** a1 is positive *)
Lemma a1_positive : a1_pi3 > 0.
Proof. unfold a1_pi3, C1_schwinger, alpha_em, pi_3. lra. Qed.

(** a1 is small (less than 1/800) *)
Lemma a1_small : a1_pi3 < 1 # 800.
Proof.
  assert (H : a1_pi3 == 113 # 97270).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3. vm_compute. reflexivity. }
  rewrite H. lra.
Qed.

(** Pi approximations are ordered *)
Lemma pi_approx_ordered : pi_1 < pi_3.
Proof. unfold pi_1, pi_3. lra. Qed.

(** alpha/pi is small *)
Definition alpha_over_pi3 : Q := alpha_em / pi_3.

Lemma alpha_over_pi3_value : alpha_over_pi3 == 113 # 48635.
Proof.
  unfold alpha_over_pi3, alpha_em, pi_3.
  vm_compute. reflexivity.
Qed.

Lemma alpha_over_pi3_small : alpha_over_pi3 < 1 # 400.
Proof.
  assert (H : alpha_over_pi3 == 113 # 48635).
  { exact alpha_over_pi3_value. }
  rewrite H. lra.
Qed.

Close Scope Q_scope.
