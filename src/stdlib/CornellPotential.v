(** * CornellPotential.v -- Cornell V(r) = -Z/r + sigma*r on lattice
    Elements: cornell_potential, cornell_sigma0, cornell_confining
    Roles:    Lattice discretization of Cornell potential; crossover physics
    Rules:    All Q arithmetic, no Admitted
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.

(** Cornell potential on a lattice: V(r_i) = -2Z/r_i + sigma * r_i
    where r_i = (i+1)/M *)
Definition cornell_potential (Z sigma : Q) (M : nat) (i : nat) : Q :=
  let r := inject_Z (Z.of_nat (S i)) / inject_Z (Z.of_nat M) in
  -(2) * Z / r + sigma * r.

Definition nat99 : nat := 99.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONCRETE VALUES: PURE COULOMB (sigma=0)                            *)
(* ================================================================== *)

(** Z=1, sigma=0, M=10, i=0: r=1/10, V = -2/r = -20 *)
Lemma cornell_sigma0 : cornell_potential 1 0 10 O == -(20).
Proof. vm_compute. reflexivity. Qed.

(** Z=1, sigma=0, M=10, i=1: r=2/10, V = -2/r = -10 *)
Lemma cornell_sigma0_i1 : cornell_potential 1 0 10 (S O) == -(10).
Proof. vm_compute. reflexivity. Qed.

(** Z=1, sigma=0, M=10, i=4: r=5/10=1/2, V = -2/r = -4 *)
Lemma cornell_sigma0_i4 : cornell_potential 1 0 10 (S (S (S (S O)))) == -(4).
Proof. vm_compute. reflexivity. Qed.

(** Z=1, sigma=0, M=10, i=9: r=10/10=1, V = -2/r = -2 *)
Lemma cornell_sigma0_i9 :
  cornell_potential 1 0 10 (S (S (S (S (S (S (S (S (S O))))))))) == -(2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONCRETE VALUES: WITH CONFINEMENT (sigma=1/10)                     *)
(* ================================================================== *)

(** Z=1, sigma=1/10, M=10, i=0: r=1/10, V = -20 + 1/100 = -1999/100 *)
Lemma cornell_sigma_small :
  cornell_potential 1 (1#10) 10 O == -(1999#100).
Proof. vm_compute. reflexivity. Qed.

(** Z=1, sigma=1/10, M=10, i=4: r=1/2, V = -4 + 1/20 = -79/20 *)
Lemma cornell_sigma_i4 :
  cornell_potential 1 (1#10) 10 (S (S (S (S O)))) == -(79#20).
Proof. vm_compute. reflexivity. Qed.

(** Z=1, sigma=1/10, M=10, i=9: r=1, V = -2 + 1/10 = -19/10 *)
Lemma cornell_sigma_i9 :
  cornell_potential 1 (1#10) 10 (S (S (S (S (S (S (S (S (S O))))))))) == -(19#10).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONFINING BEHAVIOR: large r with sigma > 0                         *)
(* ================================================================== *)

(** At large r (i=99, M=10 => r=10), sigma=1/10: V = -2/10 + 1 = 4/5 > 0 *)
Lemma cornell_confining_val :
  cornell_potential 1 (1#10) 10 nat99 == (4#5).
Proof. unfold cornell_potential, nat99. vm_compute. reflexivity. Qed.

Lemma cornell_confining :
  cornell_potential 1 (1#10) 10 nat99 > 0.
Proof. rewrite cornell_confining_val. lra. Qed.

(** At large r with sigma=0, V = -1/5 *)
Lemma cornell_coulomb_large :
  cornell_potential 1 0 10 nat99 == -(1#5).
Proof. unfold cornell_potential, nat99. vm_compute. reflexivity. Qed.

(** Coulomb is always negative *)
Lemma cornell_coulomb_negative_i0 :
  cornell_potential 1 0 10 O < 0.
Proof. rewrite cornell_sigma0. lra. Qed.

Lemma cornell_coulomb_negative_i9 :
  cornell_potential 1 0 10 (S (S (S (S (S (S (S (S (S O))))))))) < 0.
Proof. rewrite cornell_sigma0_i9. lra. Qed.

(* ================================================================== *)
(*  SIGMA CROSSOVER: V changes sign                                    *)
(* ================================================================== *)

(** At i=9 (r=1), V = -19/10 < 0 *)
Lemma crossover_negative :
  cornell_potential 1 (1#10) 10 (S (S (S (S (S (S (S (S (S O))))))))) < 0.
Proof. rewrite cornell_sigma_i9. lra. Qed.

(** At i=99 (r=10), V = 4/5 > 0 *)
Lemma crossover_positive :
  cornell_potential 1 (1#10) 10 nat99 > 0.
Proof. rewrite cornell_confining_val. lra. Qed.

(** Therefore there exists a crossover: V negative at small r, positive at large r *)
Theorem sigma_crossover :
  exists i_neg i_pos : nat,
    cornell_potential 1 (1#10) 10 i_neg < 0 /\
    cornell_potential 1 (1#10) 10 i_pos > 0.
Proof.
  exists (S (S (S (S (S (S (S (S (S O))))))))), nat99.
  split.
  - rewrite cornell_sigma_i9. lra.
  - rewrite cornell_confining_val. lra.
Qed.

(** Summary: confinement = sigma makes V grow at large r *)
Theorem confinement_summary :
  cornell_potential 1 0 10 O == -(20) /\
  cornell_potential 1 (1#10) 10 O == -(1999#100) /\
  cornell_potential 1 (1#10) 10 nat99 > 0.
Proof.
  split; [| split].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - rewrite cornell_confining_val. lra.
Qed.
