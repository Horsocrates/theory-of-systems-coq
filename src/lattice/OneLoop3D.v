(* ========================================================================= *)
(*                     ONE-LOOP 3D                                          *)
(*           One-loop self-energy and Weinberg angle correction in 3D       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 12 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  One-loop corrections in 3D give quantum mass shift:                    *)
(*                                                                          *)
(*    Elements = self-energy Sigma_3D, one-loop delta to sin^2 theta       *)
(*    Roles    = tree-level sin^2(theta_W) = 3/13, corrected value         *)
(*    Rules    = Sigma positive and small (perturbative),                   *)
(*               b_diff < 0 (metric runs faster than gauge),               *)
(*               delta_raw < 0 (raw correction negative at this order)     *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Replicated from Lattice3DPropagator.v ---- *)
Definition lap3D_N2 : list (Q * nat) :=
  [(0, 1%nat); (4, 3%nat); (8, 3%nat); (12, 1%nat)].

Definition self_prop_3D (eigs : list (Q * nat)) (m_sq : Q) : Q :=
  let total := fold_left (fun a p => (a + inject_Z (Z.of_nat (snd p)))) eigs 0 in
  fold_left (fun a p =>
    a + inject_Z (Z.of_nat (snd p)) / (fst p + m_sq)
  ) eigs 0 / total.

(* ---- One-loop self-energy on Z^3 ---- *)
(* Sigma = (1/8) * G(0,0) where 1/8 = lambda_4 / (4*pi) approximation *)
Definition sigma_3D (eigs : list (Q * nat)) (m_sq : Q) : Q :=
  (1#8) * self_prop_3D eigs m_sq.

(* ---- Weinberg angle one-loop corrections ---- *)
Definition sin2_tree : Q := 3 # 13.
Definition cos2_tree : Q := 10 # 13.
(* beta coefficients: b_gauge = dim(SU(2)) * lambda_4, b_metric = n_metric * lambda_4 *)
Definition b_gauge : Q := 3 # 8.
Definition b_metric : Q := 10 # 8.
Definition b_diff : Q := b_gauge - b_metric.

(* Raw one-loop correction to sin^2(theta_W) *)
Definition delta_raw (G00 : Q) : Q :=
  sin2_tree * cos2_tree * b_diff * G00.

(* ---- Lemma 1: sigma_3D at N=2, m^2=1 ---- *)
(* sigma = (1/8) * (49/195) = 49/1560 *)
Lemma sigma_3D_N2 : sigma_3D lap3D_N2 1 == 49 # 1560.
Proof. unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 2: sigma is positive ---- *)
Lemma sigma_3D_positive : 0 < sigma_3D lap3D_N2 1.
Proof. unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 3: sigma is small (< 1/10) ---- *)
Lemma sigma_3D_small : sigma_3D lap3D_N2 1 < 1#10.
Proof. unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 4: b_diff = -7/8 ---- *)
Lemma b_diff_value : b_diff == -(7#8).
Proof. unfold b_diff, b_gauge, b_metric. vm_compute. reflexivity. Qed.

(* ---- Lemma 5: b_diff < 0 (metric runs faster than gauge) ---- *)
Lemma b_diff_negative : b_diff < 0.
Proof. unfold b_diff, b_gauge, b_metric. vm_compute. reflexivity. Qed.

(* ---- Lemma 6: delta_raw exact value ---- *)
(* sin2 * cos2 * b_diff * G00 *)
(* = (3/13) * (10/13) * (-7/8) * (49/195) *)
(* = (30/169) * (-7/8) * (49/195) *)
(* = (-210/1352) * (49/195) *)
(* = -10290/263640 *)
(* GCD(10290, 263640) = 30, so -343/8788 *)
(* 343 = 7^3, 8788 = 4 * 13^3 *)
Lemma delta_raw_value : delta_raw (49#195) == -(343 # 8788).
Proof.
  unfold delta_raw, sin2_tree, cos2_tree, b_diff, b_gauge, b_metric.
  vm_compute. reflexivity.
Qed.

(* ---- Lemma 7: delta_raw is negative ---- *)
Lemma delta_raw_negative : delta_raw (49#195) < 0.
Proof.
  unfold delta_raw, sin2_tree, cos2_tree, b_diff, b_gauge, b_metric.
  vm_compute. reflexivity.
Qed.

(* ---- Lemma 8: physical mass > bare mass ---- *)
Lemma phys_mass_3D : 1 + sigma_3D lap3D_N2 1 > 1.
Proof.
  assert (H : 0 < sigma_3D lap3D_N2 1).
  { unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. }
  lra.
Qed.

(* ---- Lemma 9: |delta_raw| < 1/10 (perturbative) ---- *)
(* 343/8788 < 1/10 iff 3430 < 8788, which is true *)
Lemma delta_order_of_magnitude : -(343#8788) > -(1#10).
Proof. vm_compute. reflexivity. Qed.

(* ---- Lemma 10: sigma small relative to bare mass ---- *)
Lemma sigma_less_than_bare : sigma_3D lap3D_N2 1 < 1.
Proof. unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 11: sigma_3D is exactly 49/1560 ---- *)
Lemma sigma_3D_exact : sigma_3D lap3D_N2 1 == 49 # 1560.
Proof. unfold sigma_3D, self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 12: Synthesis ---- *)
Lemma one_loop_3D_synthesis :
  sigma_3D lap3D_N2 1 == 49 # 1560 /\
  0 < sigma_3D lap3D_N2 1 /\
  b_diff < 0 /\
  delta_raw (49#195) == -(343 # 8788) /\
  delta_raw (49#195) < 0.
Proof.
  split. { unfold sigma_3D, self_prop_3D; simpl; vm_compute; reflexivity. }
  split. { unfold sigma_3D, self_prop_3D; simpl; vm_compute; reflexivity. }
  split. { unfold b_diff, b_gauge, b_metric; vm_compute; reflexivity. }
  split. { unfold delta_raw, sin2_tree, cos2_tree, b_diff, b_gauge, b_metric;
           vm_compute; reflexivity. }
  unfold delta_raw, sin2_tree, cos2_tree, b_diff, b_gauge, b_metric;
    vm_compute; reflexivity.
Qed.
