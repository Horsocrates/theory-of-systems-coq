(* ========================================================================= *)
(*                     INTERACTION FROM GRAPH                               *)
(*           Cayley expansion yields interaction vertices                    *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  The Cayley expansion of the transfer matrix generates interaction       *)
(*  vertices with coupling constants lambda_n = 1/2^{n-1}:                 *)
(*                                                                          *)
(*    Elements = coupling constants lambda_n for n-point vertices           *)
(*    Roles    = cubic (lambda_3), quartic (lambda_4), etc.                 *)
(*    Rules    = lambda_{n+1}/lambda_n = 1/2 (geometric decay)             *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* Cayley coefficient: lambda_n = 1 / 2^{n-1} *)
Definition cayley_coeff (n : nat) : Q :=
  match n with
  | O => 1
  | S n' => 1 / inject_Z (Z.pow 2 (Z.of_nat n'))
  end.

Definition lambda_3 : Q := cayley_coeff 3.
Definition lambda_4 : Q := cayley_coeff 4.

Lemma cayley_0 : cayley_coeff 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_1 : cayley_coeff 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_2 : cayley_coeff 2 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_3 : cayley_coeff 3 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_4 : cayley_coeff 4 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_5 : cayley_coeff 5 == 1#16.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda_3_val : lambda_3 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda_4_val : lambda_4 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda_ratio : lambda_4 / lambda_3 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma couplings_synthesis :
  lambda_3 == 1#4 /\
  lambda_4 == 1#8 /\
  lambda_4 / lambda_3 == 1#2.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
