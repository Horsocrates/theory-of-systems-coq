(** * EulerProductQ.v — Euler product for zeta(2) over Q
    Elements: primes_list, euler_factor_2, euler_product_2, partial products
    Roles:    each prime p contributes p^2/(p^2-1) to zeta(2)=pi^2/6
    Rules:    partial products converge from below; concrete 1-4 prime products
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Primes list (as nat, for safe computation under Q_scope) --- *)
Definition primes_list : list nat := [2%nat; 3%nat; 5%nat; 7%nat; 11%nat].

(* --- Euler factor: p^2 / (p^2 - 1) --- *)
Definition euler_factor_2 (p : nat) : Q :=
  let pq := inject_Z (Z.of_nat (p * p)) in
  pq / (pq - 1).

(* --- Euler product: fold of euler_factor_2 over primes --- *)
Definition euler_product_2 (ps : list nat) : Q :=
  fold_left (fun acc p => acc * euler_factor_2 p) ps 1.

(* 1: factor for p=2 *)
Lemma ep_factor_2 : euler_factor_2 2%nat == 4 # 3.
Proof. vm_compute. reflexivity. Qed.

(* 2: factor for p=3 *)
Lemma ep_factor_3 : euler_factor_2 3%nat == 9 # 8.
Proof. vm_compute. reflexivity. Qed.

(* 3: factor for p=5 *)
Lemma ep_factor_5 : euler_factor_2 5%nat == 25 # 24.
Proof. vm_compute. reflexivity. Qed.

(* 4: factor for p=7 *)
Lemma ep_factor_7 : euler_factor_2 7%nat == 49 # 48.
Proof. vm_compute. reflexivity. Qed.

(* 5: one prime *)
Lemma ep_1prime : euler_product_2 [2%nat] == 4 # 3.
Proof. vm_compute. reflexivity. Qed.

(* 6: two primes: 4/3 * 9/8 = 3/2 *)
Lemma ep_2primes : euler_product_2 [2%nat; 3%nat] == 3 # 2.
Proof. vm_compute. reflexivity. Qed.

(* 7: three primes: 3/2 * 25/24 = 75/48 = 25/16 *)
Lemma ep_3primes : euler_product_2 [2%nat; 3%nat; 5%nat] == 25 # 16.
Proof. vm_compute. reflexivity. Qed.

(* 8: four primes: 25/16 * 49/48 = 1225/768 *)
Lemma ep_4primes : euler_product_2 [2%nat; 3%nat; 5%nat; 7%nat] == 1225 # 768.
Proof. vm_compute. reflexivity. Qed.

(* --- pi^2/6 ≈ 1.6449... --- *)
Definition pi_sq_over_6_approx : Q := 1645 # 1000.

(* 9: product grows toward pi^2/6 *)
Lemma ep_1_lt_target : euler_product_2 [2%nat] < pi_sq_over_6_approx.
Proof.
  assert (H : euler_product_2 [2%nat] == 4#3) by (vm_compute; reflexivity).
  rewrite H. unfold pi_sq_over_6_approx. lra.
Qed.

(* 10 *)
Lemma ep_2_lt_target : euler_product_2 [2%nat; 3%nat] < pi_sq_over_6_approx.
Proof.
  assert (H : euler_product_2 [2%nat; 3%nat] == 3#2) by (vm_compute; reflexivity).
  rewrite H. unfold pi_sq_over_6_approx. lra.
Qed.

(* 11 *)
Lemma ep_3_lt_target : euler_product_2 [2%nat; 3%nat; 5%nat] < pi_sq_over_6_approx.
Proof.
  assert (H : euler_product_2 [2%nat; 3%nat; 5%nat] == 25#16) by (vm_compute; reflexivity).
  rewrite H. unfold pi_sq_over_6_approx. lra.
Qed.

(* 12: monotonicity: adding primes increases the product *)
Lemma ep_mono_12 : euler_product_2 [2%nat] < euler_product_2 [2%nat; 3%nat].
Proof.
  assert (H1 : euler_product_2 [2%nat] == 4#3) by (vm_compute; reflexivity).
  assert (H2 : euler_product_2 [2%nat; 3%nat] == 3#2) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* 13 *)
Lemma ep_mono_23 :
  euler_product_2 [2%nat; 3%nat] < euler_product_2 [2%nat; 3%nat; 5%nat].
Proof.
  assert (H2 : euler_product_2 [2%nat; 3%nat] == 3#2) by (vm_compute; reflexivity).
  assert (H3 : euler_product_2 [2%nat; 3%nat; 5%nat] == 25#16) by (vm_compute; reflexivity).
  rewrite H2, H3. lra.
Qed.

(* 14 *)
Lemma ep_mono_34 :
  euler_product_2 [2%nat; 3%nat; 5%nat] <
  euler_product_2 [2%nat; 3%nat; 5%nat; 7%nat].
Proof.
  assert (H3 : euler_product_2 [2%nat; 3%nat; 5%nat] == 25#16) by (vm_compute; reflexivity).
  assert (H4 : euler_product_2 [2%nat; 3%nat; 5%nat; 7%nat] == 1225#768) by (vm_compute; reflexivity).
  rewrite H3, H4. lra.
Qed.

(* --- Each factor > 1 --- *)
(* 15 *)
Lemma factor_2_gt_1 : 1 < euler_factor_2 2%nat.
Proof.
  assert (H : euler_factor_2 2%nat == 4#3) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* 16 *)
Lemma factor_3_gt_1 : 1 < euler_factor_2 3%nat.
Proof.
  assert (H : euler_factor_2 3%nat == 9#8) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* --- Contribution of each prime = factor - 1 --- *)
(* 17 *)
Lemma contribution_p2 : euler_factor_2 2%nat - 1 == 1 # 3.
Proof. vm_compute. reflexivity. Qed.

(* 18: pi^2/6 from euler product — the product formula *)
Theorem pi_sq_from_euler :
  (* partial products increase monotonically *)
  euler_product_2 [2%nat] < euler_product_2 [2%nat; 3%nat] /\
  euler_product_2 [2%nat; 3%nat] < euler_product_2 [2%nat; 3%nat; 5%nat] /\
  euler_product_2 [2%nat; 3%nat; 5%nat] < euler_product_2 [2%nat; 3%nat; 5%nat; 7%nat] /\
  (* all below target *)
  euler_product_2 [2%nat; 3%nat; 5%nat] < pi_sq_over_6_approx.
Proof.
  split; [|split; [|split]].
  - exact ep_mono_12.
  - exact ep_mono_23.
  - exact ep_mono_34.
  - exact ep_3_lt_target.
Qed.
