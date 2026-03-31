(* ========================================================================= *)
(*                     ONE-LOOP SCALAR                                      *)
(*           One-loop self-energy corrections for chain-2 and chain-4       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 7 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  One-loop corrections renormalize the physical mass:                    *)
(*                                                                          *)
(*    Elements = self-energy Sigma for each lattice size                    *)
(*    Roles    = bare mass m^2, physical mass m^2 + Sigma                   *)
(*    Rules    = Sigma decreases with lattice size (convergent),            *)
(*               Sigma positive (mass increases), Sigma < bare mass        *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* Self-energy: Sigma = (1/8) * (1/N) * sum_k 1/(lambda_k + m^2) *)
Definition sigma_chain (eigs : list Q) (m_sq : Q) : Q :=
  let N := inject_Z (Z.of_nat (length eigs)) in
  (1#8) * fold_left (fun acc lam => acc + 1/(lam + m_sq)) eigs 0 / N.

(* Physical mass = bare mass + self-energy *)
Definition phys_mass (m_sq sigma : Q) : Q := m_sq + sigma.

Lemma sigma_chain2_m1 : sigma_chain [0; 2] 1 == 1#12.
Proof. unfold sigma_chain. simpl. vm_compute. reflexivity. Qed.

Lemma sigma_chain4_m1 : sigma_chain [0; 2; 4; 2] 1 == 7#120.
Proof. unfold sigma_chain. simpl. vm_compute. reflexivity. Qed.

Lemma phys_mass_chain2 : phys_mass 1 (1#12) == 13#12.
Proof. unfold phys_mass. vm_compute. reflexivity. Qed.

(* Self-energy DECREASES with lattice size: convergent *)
Lemma sigma_decreases : sigma_chain [0; 2] 1 > sigma_chain [0; 2; 4; 2] 1.
Proof. unfold sigma_chain. simpl. vm_compute. reflexivity. Qed.

(* Self-energy is small: < 10% of bare mass *)
Lemma mass_shift_small : sigma_chain [0; 2] 1 < 1#10.
Proof. unfold sigma_chain. simpl. vm_compute. reflexivity. Qed.

(* Self-energy is positive *)
Lemma sigma_positive_chain2 : 0 < sigma_chain [0; 2] 1.
Proof. unfold sigma_chain. simpl. vm_compute. reflexivity. Qed.

Lemma one_loop_synthesis :
  sigma_chain [0; 2] 1 == 1#12 /\
  sigma_chain [0; 2; 4; 2] 1 == 7#120 /\
  sigma_chain [0; 2] 1 > sigma_chain [0; 2; 4; 2] 1 /\
  0 < sigma_chain [0; 2] 1.
Proof.
  repeat split; unfold sigma_chain; simpl; vm_compute; reflexivity.
Qed.
