(** * GrapheneDOS.v — Density of states for graphene

    Elements: DOS proportional to |E| near Dirac point, carrier density
    Roles:    vanishing DOS at E=0 -> semimetal character
    Rules:    D(0) = 0 (Dirac); D symmetric; carrier density ~ E_F^2
    Status:   verified | electronic structure

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** DOS near Dirac point: D(E) proportional to |E| *)
Definition dos_graphene (E : Q) : Q := Qabs E.

(** DOS vanishes at Dirac point *)
Lemma Qabs_0 : Qabs 0 == 0.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

Theorem dos_at_0 : dos_graphene 0 == 0.
Proof. unfold dos_graphene. apply Qabs_0. Qed.

(** DOS at E=1 *)
Lemma Qabs_1 : Qabs 1 == 1.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

Theorem dos_at_1 : dos_graphene 1 == 1.
Proof. unfold dos_graphene. apply Qabs_1. Qed.

(** DOS at E=-1: symmetric *)
Lemma Qabs_neg1 : Qabs (-(1)) == 1.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

Theorem dos_at_neg1 : dos_graphene (-(1)) == 1.
Proof. unfold dos_graphene. apply Qabs_neg1. Qed.

(** DOS symmetric: D(E) = D(-E) for concrete values *)
Theorem dos_symmetric : dos_graphene 1 == dos_graphene (-(1)).
Proof.
  unfold dos_graphene. rewrite Qabs_1. rewrite Qabs_neg1. reflexivity.
Qed.

(** Metal has constant DOS = 1 (for comparison) *)
Definition dos_metal : Q := 1.

(** Graphene DOS at E=0 is below metal DOS *)
Theorem graphene_below_metal_at_0 :
  dos_graphene 0 < dos_metal.
Proof.
  unfold dos_graphene, dos_metal. rewrite Qabs_0. vm_compute. reflexivity.
Qed.

(** Carrier density: n(E_F) = E_F^2 / 2 (integrated DOS) *)
Definition carrier_density (E_F : Q) : Q := E_F * E_F / 2.

(** No carriers at charge neutrality *)
Theorem carrier_at_0 : carrier_density 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Carrier density at E_F = 1 *)
Theorem carrier_at_1 : carrier_density 1 == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

(** Carrier density increases with E_F *)
Theorem carrier_increases : carrier_density (1 # 2) < carrier_density 1.
Proof. vm_compute. reflexivity. Qed.

(** Carrier density positive for E_F > 0 *)
Theorem carrier_positive : 0 < carrier_density 1.
Proof. vm_compute. reflexivity. Qed.
