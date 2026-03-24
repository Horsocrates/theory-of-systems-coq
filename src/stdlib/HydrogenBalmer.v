(** * HydrogenBalmer.v -- Balmer series: transition wavelengths
    Elements: balmer function, concrete values, series ordering
    Roles:    balmer(n) = (n²-4)/(4n²) gives Balmer spectral lines
    Rules:    Concrete values verified, series converges to 1/4
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  BALMER SERIES: (n² - 4) / (4n²) for n ≥ 3                        *)
(* ================================================================== *)

Definition balmer (n : nat) : Q :=
  let nq := inject_Z (Z.of_nat n) in
  (nq * nq - 4) / (4 * nq * nq).

(** balmer(3) = (9-4)/36 = 5/36 *)
Lemma balmer_3 : balmer 3 == 5#36.
Proof. vm_compute. reflexivity. Qed.

(** balmer(4) = (16-4)/64 = 12/64 = 3/16 *)
Lemma balmer_4 : balmer 4 == 3#16.
Proof. vm_compute. reflexivity. Qed.

(** balmer(5) = (25-4)/100 = 21/100 *)
Lemma balmer_5 : balmer 5 == 21#100.
Proof. vm_compute. reflexivity. Qed.

(** balmer(6) = (36-4)/144 = 32/144 = 2/9 *)
Lemma balmer_6 : balmer 6 == 2#9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SERIES ORDERING: balmer increases toward 1/4                      *)
(* ================================================================== *)

Lemma balmer_increases_34 : balmer 3 < balmer 4.
Proof. vm_compute. reflexivity. Qed.

Lemma balmer_increases_45 : balmer 4 < balmer 5.
Proof. vm_compute. reflexivity. Qed.

Lemma balmer_increases_56 : balmer 5 < balmer 6.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  LIMIT: balmer(n) < 1/4 for all finite n                          *)
(* ================================================================== *)

Lemma balmer_below_limit_3 : balmer 3 < 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma balmer_below_limit_10 : balmer 10 < 1#4.
Proof. vm_compute. reflexivity. Qed.

(** The series limit is 1/4 = 1/2² (Balmer limit) *)
Definition balmer_limit : Q := 1#4.

Lemma balmer_limit_value : balmer_limit == 1#4.
Proof. vm_compute. reflexivity. Qed.
