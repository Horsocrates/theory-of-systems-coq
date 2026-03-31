(* ========================================================================= *)
(*                     LATTICE 3D PROPAGATOR                                *)
(*           3D lattice eigenvalues and self-propagator for N=2             *)
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
(*  3D lattice propagator captures spatial structure:                       *)
(*                                                                          *)
(*    Elements = 3D Laplacian eigenvalues with multiplicities               *)
(*    Roles    = propagator G(lambda,m^2), self-propagator G(0,0)           *)
(*    Rules    = total modes = N^3, G positive, G < 1 for massive case     *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- 3D Laplacian eigenvalues for N=2 periodic lattice ---- *)
(* Eigenvalues: lambda = 2*(3 - cos(2*pi*n1/N) - cos(2*pi*n2/N) - cos(2*pi*n3/N)) *)
(* For N=2, cos values are +1 or -1, giving lambda in {0,4,8,12} *)
(* Multiplicities: (0,0,0)->0; one nonzero->4 x3=12 split as (4,3),(8,3); all nonzero->12 x1 *)

Definition lap3D_N2 : list (Q * nat) :=
  [(0, 1%nat); (4, 3%nat); (8, 3%nat); (12, 1%nat)].

(* Green's function: G(lambda, m^2) = 1 / (lambda + m^2) *)
Definition G_3D (lambda m_sq : Q) : Q := 1 / (lambda + m_sq).

(* Self-propagator: G(0,0) = (1/N^3) * sum_k mult_k / (lambda_k + m^2) *)
Definition self_prop_3D (eigs : list (Q * nat)) (m_sq : Q) : Q :=
  let total := fold_left (fun a p => (a + inject_Z (Z.of_nat (snd p)))) eigs 0 in
  fold_left (fun a p =>
    a + inject_Z (Z.of_nat (snd p)) / (fst p + m_sq)
  ) eigs 0 / total.

(* ---- Lemma 1: Total modes = 8 = 2^3 ---- *)
Lemma total_modes_N2 :
  fold_left (fun a p => a + inject_Z (Z.of_nat (snd p))) lap3D_N2 0 == 8.
Proof. vm_compute. reflexivity. Qed.

(* ---- Lemma 2: G at zero mode ---- *)
Lemma G_3D_zero : G_3D 0 1 == 1.
Proof. unfold G_3D. vm_compute. reflexivity. Qed.

(* ---- Lemma 3: G at lambda=4 ---- *)
Lemma G_3D_four : G_3D 4 1 == 1#5.
Proof. unfold G_3D. vm_compute. reflexivity. Qed.

(* ---- Lemma 4: G at lambda=8 ---- *)
Lemma G_3D_eight : G_3D 8 1 == 1#9.
Proof. unfold G_3D. vm_compute. reflexivity. Qed.

(* ---- Lemma 5: G at lambda=12 ---- *)
Lemma G_3D_twelve : G_3D 12 1 == 1#13.
Proof. unfold G_3D. vm_compute. reflexivity. Qed.

(* ---- Lemma 6: Weighted sum = 392/195 ---- *)
(* 1/1 + 3/5 + 3/9 + 1/13 = 1 + 3/5 + 1/3 + 1/13 *)
(* = 195/195 + 117/195 + 65/195 + 15/195 = 392/195 *)
Lemma weighted_sum_N2 :
  fold_left (fun a p =>
    a + inject_Z (Z.of_nat (snd p)) / (fst p + 1)
  ) lap3D_N2 0 == 392 # 195.
Proof. vm_compute. reflexivity. Qed.

(* ---- Lemma 7: Self-propagator G(0,0) = 49/195 ---- *)
(* 392/195 / 8 = 392/1560 = 49/195 *)
Lemma self_prop_N2_m1 : self_prop_3D lap3D_N2 1 == 49 # 195.
Proof. unfold self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 8: Self-propagator is positive ---- *)
Lemma self_prop_positive : 0 < self_prop_3D lap3D_N2 1.
Proof. unfold self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 9: Self-propagator < 1 (massive suppression) ---- *)
Lemma self_prop_less_than_1 : self_prop_3D lap3D_N2 1 < 1.
Proof. unfold self_prop_3D. simpl. vm_compute. reflexivity. Qed.

(* ---- Lemma 10: Synthesis ---- *)
Lemma lattice_3D_propagator_synthesis :
  fold_left (fun a p => a + inject_Z (Z.of_nat (snd p))) lap3D_N2 0 == 8 /\
  self_prop_3D lap3D_N2 1 == 49 # 195 /\
  0 < self_prop_3D lap3D_N2 1 /\
  self_prop_3D lap3D_N2 1 < 1.
Proof.
  repeat split; unfold self_prop_3D; simpl; vm_compute; reflexivity.
Qed.
