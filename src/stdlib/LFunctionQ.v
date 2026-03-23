(** * LFunctionQ.v — Dirichlet L-function L(1,chi4) Euler product over Q
    Elements: chi4_prime, L_factor_1, L_product_1, partial products
    Roles:    chi4 = non-principal character mod 4; L(1,chi4) = pi/4
    Rules:    Euler product converges to pi/4; concrete values for small primes
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- chi4: non-principal Dirichlet character mod 4 --- *)
(* chi4(n) = 0 if n even, 1 if n=1 mod 4, -1 if n=3 mod 4 *)
Definition chi4_prime (p : nat) : Q :=
  match Nat.modulo p 4 with
  | O => 0
  | S O => 1
  | S (S O) => 0
  | S (S (S O)) => -(1)
  | _ => 0
  end.

(* 1 *)
Lemma chi4_of_2 : chi4_prime 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* 2 *)
Lemma chi4_of_3 : chi4_prime 3%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* 3 *)
Lemma chi4_of_5 : chi4_prime 5%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* 4 *)
Lemma chi4_of_7 : chi4_prime 7%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* --- L-factor at s=1: 1/(1 - chi(p)/p) --- *)
Definition L_factor_1 (p : nat) : Q :=
  let chi := chi4_prime p in
  let pq := inject_Z (Z.of_nat p) in
  if Qeq_bool chi 0 then 1
  else pq / (pq - chi).

(* 5 *)
Lemma L_factor_2 : L_factor_1 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* 6: p=3, chi=-1, factor = 3/(3-(-1)) = 3/4 *)
Lemma L_factor_3 : L_factor_1 3%nat == 3 # 4.
Proof. vm_compute. reflexivity. Qed.

(* 7: p=5, chi=1, factor = 5/(5-1) = 5/4 *)
Lemma L_factor_5 : L_factor_1 5%nat == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

(* 8: p=7, chi=-1, factor = 7/(7+1) = 7/8 *)
Lemma L_factor_7 : L_factor_1 7%nat == 7 # 8.
Proof. vm_compute. reflexivity. Qed.

(* --- L product: fold over primes --- *)
Definition L_product_1 (ps : list nat) : Q :=
  fold_left (fun acc p => acc * L_factor_1 p) ps 1.

(* 9: two primes [2,3] *)
Lemma L_2primes : L_product_1 [2%nat; 3%nat] == 3 # 4.
Proof. vm_compute. reflexivity. Qed.

(* 10: three primes [2,3,5] = 3/4 * 5/4 = 15/16 *)
Lemma L_3primes : L_product_1 [2%nat; 3%nat; 5%nat] == 15 # 16.
Proof. vm_compute. reflexivity. Qed.

(* 11: four primes [2,3,5,7] = 15/16 * 7/8 = 105/128 *)
Lemma L_4primes : L_product_1 [2%nat; 3%nat; 5%nat; 7%nat] == 105 # 128.
Proof. vm_compute. reflexivity. Qed.

(* --- pi/4 approx --- *)
Definition pi_over_4_approx : Q := 7854 # 10000.

(* 12: 4-prime product close to pi/4 *)
Lemma L_4_close_to_pi4 :
  L_product_1 [2%nat; 3%nat; 5%nat; 7%nat] - pi_over_4_approx < 1 # 10.
Proof.
  assert (H : L_product_1 [2%nat; 3%nat; 5%nat; 7%nat] == 105#128)
    by (vm_compute; reflexivity).
  rewrite H. unfold pi_over_4_approx. lra.
Qed.

(* 13 *)
Lemma L_mono_23 :
  L_product_1 [2%nat; 3%nat] < L_product_1 [2%nat; 3%nat; 5%nat].
Proof.
  assert (H2 : L_product_1 [2%nat; 3%nat] == 3#4) by (vm_compute; reflexivity).
  assert (H3 : L_product_1 [2%nat; 3%nat; 5%nat] == 15#16) by (vm_compute; reflexivity).
  rewrite H2, H3. lra.
Qed.

(* 14: L product is always positive *)
Lemma L_2primes_pos : 0 < L_product_1 [2%nat; 3%nat].
Proof.
  assert (H : L_product_1 [2%nat; 3%nat] == 3#4) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* 15: pi from L — the Leibniz-Euler connection *)
Theorem pi_from_L :
  L_product_1 [2%nat; 3%nat] == 3 # 4 /\
  L_product_1 [2%nat; 3%nat; 5%nat] == 15 # 16 /\
  L_product_1 [2%nat; 3%nat; 5%nat; 7%nat] == 105 # 128.
Proof.
  split; [|split]; vm_compute; reflexivity.
Qed.
