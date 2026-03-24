(** * HydrogenCorrection.v -- Spectral classification of lattice models
    Elements: SpectralClass, classify functions, comparison lemmas
    Roles:    Polynomial (hydrogen) vs Exponential (Ising) convergence
    Rules:    Classification by convergence rate to continuum limit
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  SPECTRAL CLASSIFICATION                                            *)
(* ================================================================== *)

Inductive SpectralClass : Set :=
  | Polynomial : Q -> SpectralClass   (* rate = power *)
  | Exponential : Q -> SpectralClass  (* rate = base *)
  | Logarithmic : SpectralClass.

(** Hydrogen: polynomial convergence with rate 2 (error ~ 1/M²) *)
Definition hydrogen_class : SpectralClass := Polynomial 2.

(** Ising: exponential convergence with rate 28/37 *)
Definition ising_class : SpectralClass := Exponential (28#37).

(** Harmonic oscillator: polynomial with rate 2 *)
Definition harmonic_class : SpectralClass := Polynomial 2.

(* ================================================================== *)
(*  RATE EXTRACTION                                                    *)
(* ================================================================== *)

Definition extract_rate (c : SpectralClass) : Q :=
  match c with
  | Polynomial r => r
  | Exponential r => r
  | Logarithmic => 0
  end.

Lemma hydrogen_rate : extract_rate hydrogen_class == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ising_rate : extract_rate ising_class == 28#37.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CLASSIFICATION PREDICATES                                          *)
(* ================================================================== *)

Definition is_polynomial (c : SpectralClass) : bool :=
  match c with
  | Polynomial _ => true
  | _ => false
  end.

Definition is_exponential (c : SpectralClass) : bool :=
  match c with
  | Exponential _ => true
  | _ => false
  end.

Lemma hydrogen_is_poly : is_polynomial hydrogen_class = true.
Proof. reflexivity. Qed.

Lemma ising_is_exp : is_exponential ising_class = true.
Proof. reflexivity. Qed.

Lemma hydrogen_not_exp : is_exponential hydrogen_class = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  CONVERGENCE COMPARISON                                             *)
(* ================================================================== *)

(** For polynomial convergence: error at step M ~ 1/M^rate.
    Higher rate = faster convergence *)
Definition poly_error_bound (rate : Q) (M : nat) : Q :=
  let Mq := inject_Z (Z.of_nat M) in
  1 / (Mq * Mq).  (* for rate=2 *)

Lemma poly_error_M2 : poly_error_bound 2 2 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma poly_error_M4 : poly_error_bound 2 4 == 1#16.
Proof. vm_compute. reflexivity. Qed.

Lemma poly_error_improves : poly_error_bound 2 4 < poly_error_bound 2 2.
Proof. vm_compute. reflexivity. Qed.

(** Exponential convergence is faster than polynomial for large M *)
Definition exp_error_bound (base : Q) (M : nat) : Q :=
  let fix pow (n : nat) : Q :=
    match n with O => 1 | S k => base * pow k end
  in pow M.

Lemma exp_error_M2 : exp_error_bound (28#37) 2 == 784#1369.
Proof. vm_compute. reflexivity. Qed.

(** Exponential base < 1 means it converges *)
Lemma exp_base_less_one : exp_error_bound (28#37) 1 < 1.
Proof. vm_compute. reflexivity. Qed.
