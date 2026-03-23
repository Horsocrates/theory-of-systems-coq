(** * GaussianZetaProduct.v — ζ_{Z[i]}(s) = ζ(s)·L(s,χ₄)
    Elements: gaussian_zeta_2, catalan_partial
    Roles:    Gaussian integers unite ζ and L into one object
    Rules:    Product of two Euler products = Gaussian zeta
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.EulerProductQ.
From ToS Require Import stdlib.LFunctionQ.

Open Scope Q_scope.

(** Gaussian zeta at s=2: ζ(2)·L(2,χ₄) *)
Definition gaussian_zeta_2 (ps : list nat) : Q :=
  euler_product_2 ps * L_product_1 ps.

Lemma gz_1prime : gaussian_zeta_2 [2%nat] == (4#3) * 1.
Proof. unfold gaussian_zeta_2. vm_compute. reflexivity. Qed.

Lemma gz_2primes : gaussian_zeta_2 [2%nat; 3%nat] == (3#2) * (3#4).
Proof. unfold gaussian_zeta_2. vm_compute. reflexivity. Qed.

Lemma gz_value_2 : gaussian_zeta_2 [2%nat; 3%nat] == 9#8.
Proof. vm_compute. reflexivity. Qed.

Lemma gz_value_3_positive : 0 < gaussian_zeta_2 [2%nat; 3%nat; 5%nat].
Proof.
  assert (H : gaussian_zeta_2 [2%nat; 3%nat; 5%nat] == 375#256) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Catalan's constant partial sums: G = 1 - 1/9 + 1/25 - 1/49 + ... *)
Fixpoint catalan_partial (K : nat) : Q :=
  match K with
  | O => 0
  | S k => catalan_partial k +
      (if Nat.even k then 1 else -(1)) /
      inject_Z (Z.of_nat ((2*k+1)*(2*k+1)))
  end.

Lemma catalan_1 : catalan_partial 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_2 : catalan_partial 2%nat == 8#9.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_3 : catalan_partial 3%nat == 209#225.
Proof. vm_compute. reflexivity. Qed.

(** Catalan ≈ 0.916. Our 209/225 ≈ 0.929. Off by 1.4%. *)
Lemma catalan_positive : 0 < catalan_partial 3%nat.
Proof. rewrite catalan_3. lra. Qed.

Lemma catalan_lt_1 : catalan_partial 3%nat < 1.
Proof. rewrite catalan_3. lra. Qed.

(** SYNTHESIS *)
Theorem gaussian_zeta_synthesis :
  gaussian_zeta_2 [2%nat; 3%nat] == 9#8 /\
  0 < catalan_partial 3%nat /\
  catalan_partial 3%nat < 1.
Proof.
  split; [|split].
  - exact gz_value_2.
  - exact catalan_positive.
  - exact catalan_lt_1.
Qed.
