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
  (* a1_pi3 - a_e_exp = 113/97270 - 115965/10^8 = 2008445/972700000000
     (~ 2.0648e-6, POSITIVE: the first-order value overshoots experiment). *)
  assert (Hd : a1_pi3 - a_e_exp == (2008445 # 972700000000)).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3, a_e_exp.
    vm_compute. reflexivity. }
  rewrite Hd.
  assert (Habs : Qabs (2008445 # 972700000000) == 2008445 # 972700000000).
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

(** pi_3 gives a Schwinger result closer than pi_1 to the SAME first-order
    formula evaluated at the finer convergent pi_4 = 103993/33102 (quality of
    the pi-convergents carried over to a1):
      a1_pi3 - a1(pi_4) = -1/10115399110  (~ -9.9e-11)
      a1_pi1 - a1(pi_4) = -293/626869804  (~ -4.7e-7).
    NOTE (2026-11-12): the earlier statement measured against EXPERIMENT,
      Qabs (a1_pi3 - a_e_exp) < Qabs (a1_pi1 - a_e_exp),
    and was FALSE (never compiled):
      a1_pi3 - a_e_exp = 2008445/972700000000 (~ 2.065e-6),
      a1_pi1 - a_e_exp =  962980/602800000000 (~ 1.598e-6).
    The first-order value with alpha = 1/137 overshoots experiment, so the
    cruder (larger) 22/7 lands closer by accidental compensation of the
    omitted higher-order terms; a better pi does NOT improve the first-order
    agreement with experiment. *)
Lemma pi3_better_than_pi1 :
  Qabs (a1_pi3 - C1_schwinger * alpha_em / pi_4) <
  Qabs (a1_pi1 - C1_schwinger * alpha_em / pi_4).
Proof.
  assert (H1 : a1_pi3 - C1_schwinger * alpha_em / pi_4 == (-1 # 10115399110)).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3, pi_4. vm_compute. reflexivity. }
  assert (H2 : a1_pi1 - C1_schwinger * alpha_em / pi_4 == (-293 # 626869804)).
  { unfold a1_pi1, C1_schwinger, alpha_em, pi_1, pi_4. vm_compute. reflexivity. }
  rewrite H1, H2.
  assert (Ha1 : Qabs (-1 # 10115399110) == 1 # 10115399110).
  { vm_compute. reflexivity. }
  assert (Ha2 : Qabs (-293 # 626869804) == 293 # 626869804).
  { vm_compute. reflexivity. }
  rewrite Ha1, Ha2. lra.
Qed.

(** a1 is positive *)
Lemma a1_positive : a1_pi3 > 0.
Proof.
  (* lra cannot divide by the literal 355 # 113; go through a1_value *)
  assert (H : a1_pi3 == 113 # 97270) by exact a1_value.
  rewrite H. lra.
Qed.

(** a1 is small (less than 1/800) *)
Lemma a1_small : a1_pi3 < 1 # 800.
Proof.
  assert (H : a1_pi3 == 113 # 97270).
  { unfold a1_pi3, C1_schwinger, alpha_em, pi_3. vm_compute. reflexivity. }
  rewrite H. lra.
Qed.

(** Pi approximations are ordered: 355/113 < 22/7 (22/7 - 355/113 = 1/791).
    NOTE (2026-11-12): the earlier statement [pi_1 < pi_3] had the order
    reversed and was false (22/7 ~ 3.142857 > 355/113 ~ 3.141593). *)
Lemma pi_approx_ordered : pi_3 < pi_1.
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
