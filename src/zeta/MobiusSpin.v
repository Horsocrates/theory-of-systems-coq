(* MobiusSpin.v *)
(* Arithmetic Heisenberg: Mobius function as spin system *)
(* E/R/R: Elements = natural numbers, Roles = squarefree/non-squarefree,
   Rules = mobius values {-1, 0, +1} as spin states *)

From Coq Require Import QArith.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Arith.

(* === Mobius function values for n = 1..30 === *)

Definition mobius_val (n : nat) : Z :=
  if Nat.eqb n 1%nat then 1
  else if Nat.eqb n 2%nat then (-1)
  else if Nat.eqb n 3%nat then (-1)
  else if Nat.eqb n 4%nat then 0    (* 2^2 *)
  else if Nat.eqb n 5%nat then (-1)
  else if Nat.eqb n 6%nat then 1    (* 2*3, squarefree, 2 factors *)
  else if Nat.eqb n 7%nat then (-1)
  else if Nat.eqb n 8%nat then 0    (* 2^3 *)
  else if Nat.eqb n 9%nat then 0    (* 3^2 *)
  else if Nat.eqb n 10%nat then 1   (* 2*5 *)
  else if Nat.eqb n 11%nat then (-1)
  else if Nat.eqb n 12%nat then 0   (* 2^2*3 *)
  else if Nat.eqb n 13%nat then (-1)
  else if Nat.eqb n 14%nat then 1   (* 2*7 *)
  else if Nat.eqb n 15%nat then 1   (* 3*5 *)
  else if Nat.eqb n 16%nat then 0   (* 2^4 *)
  else if Nat.eqb n 17%nat then (-1)
  else if Nat.eqb n 18%nat then 0   (* 2*3^2 *)
  else if Nat.eqb n 19%nat then (-1)
  else if Nat.eqb n 20%nat then 0   (* 2^2*5 *)
  else if Nat.eqb n 21%nat then 1   (* 3*7 *)
  else if Nat.eqb n 22%nat then 1   (* 2*11 *)
  else if Nat.eqb n 23%nat then (-1)
  else if Nat.eqb n 24%nat then 0   (* 2^3*3 *)
  else if Nat.eqb n 25%nat then 0   (* 5^2 *)
  else if Nat.eqb n 26%nat then 1   (* 2*13 *)
  else if Nat.eqb n 27%nat then 0   (* 3^3 *)
  else if Nat.eqb n 28%nat then 0   (* 2^2*7 *)
  else if Nat.eqb n 29%nat then (-1)
  else if Nat.eqb n 30%nat then (-1) (* 2*3*5, 3 factors *)
  else 0.

(* === Mertens function: cumulative sum of mobius === *)

Fixpoint mertens (x : nat) : Z :=
  match x with
  | O => 0
  | S n => (mertens n + mobius_val (S n))
  end.

Open Scope Z_scope.

(* === Concrete mobius values === *)

Lemma mobius_1 : mobius_val 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mobius_2 : mobius_val 2 = (-1).
Proof. vm_compute. reflexivity. Qed.

Lemma mobius_4 : mobius_val 4 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mobius_6 : mobius_val 6 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mobius_30 : mobius_val 30 = (-1).
Proof. vm_compute. reflexivity. Qed.

(* === Mertens function values === *)

Lemma mertens_10 : mertens 10 = (-1).
Proof. vm_compute. reflexivity. Qed.

Lemma mertens_20 : mertens 20 = (-3).
Proof. vm_compute. reflexivity. Qed.

Lemma mertens_30 : mertens 30 = (-3).
Proof. vm_compute. reflexivity. Qed.

(* === Mertens bounded (|M(x)| <= sqrt(x) conjecture data) === *)

Lemma mertens_abs_10 : Z.abs (mertens 10) <= 3.
Proof.
  assert (H: mertens 10 = (-1)) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

Lemma mertens_abs_20 : Z.abs (mertens 20) <= 4.
Proof.
  assert (H: mertens 20 = (-3)) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

Lemma mertens_abs_30 : Z.abs (mertens 30) <= 5.
Proof.
  assert (H: mertens 30 = (-3)) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

(* === Mobius bounded: |mu(n)| <= 1 for concrete values === *)

Lemma mobius_bounded_1 : Z.abs (mobius_val 1) <= 1.
Proof.
  assert (H: mobius_val 1 = 1) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

Lemma mobius_bounded_6 : Z.abs (mobius_val 6) <= 1.
Proof.
  assert (H: mobius_val 6 = 1) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

Lemma mobius_bounded_4 : Z.abs (mobius_val 4) <= 1.
Proof.
  assert (H: mobius_val 4 = 0) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

Lemma mobius_bounded_2 : Z.abs (mobius_val 2) <= 1.
Proof.
  assert (H: mobius_val 2 = (-1)) by (vm_compute; reflexivity).
  rewrite H. unfold Z.abs. lia.
Qed.

(* === Spin counting: +1 spins among 1..10 === *)
(* mu(n) = +1 for n = 1, 6, 10 → 3 up-spins *)

Definition count_up (lo hi : nat) : nat :=
  let fix aux (n : nat) (acc : nat) :=
    match n with
    | O => acc
    | S k => let idx := (lo + k)%nat in
             let v := mobius_val idx in
             if Z.eqb v 1 then aux k (S acc) else aux k acc
    end
  in aux (hi - lo)%nat O.

Lemma count_up_10 : count_up 1 11 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* Count of down-spins (-1) among 1..10: n=2,3,5,7 → 4 *)

Definition count_down (lo hi : nat) : nat :=
  let fix aux (n : nat) (acc : nat) :=
    match n with
    | O => acc
    | S k => let idx := (lo + k)%nat in
             let v := mobius_val idx in
             if Z.eqb v (-1) then aux k (S acc) else aux k acc
    end
  in aux (hi - lo)%nat O.

Lemma count_down_10 : count_down 1 11 = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(* Zero-spins among 1..10: n=4,8,9 → 3 *)

Definition count_zero (lo hi : nat) : nat :=
  let fix aux (n : nat) (acc : nat) :=
    match n with
    | O => acc
    | S k => let idx := (lo + k)%nat in
             let v := mobius_val idx in
             if Z.eqb v 0 then aux k (S acc) else aux k acc
    end
  in aux (hi - lo)%nat O.

Lemma count_zero_10 : count_zero 1 11 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* Total check: 3 + 4 + 3 = 10 *)
Lemma spin_partition_10 :
  (count_up 1 11 + count_down 1 11 + count_zero 1 11 = 10)%nat.
Proof. vm_compute. reflexivity. Qed.

(* === Mertens oscillation: changes sign === *)

Lemma mertens_sign_change :
  (mertens 1 > 0)%Z /\ (mertens 10 < 0)%Z.
Proof.
  assert (H1: mertens 1 = 1) by (vm_compute; reflexivity).
  assert (H2: mertens 10 = (-1)) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.
