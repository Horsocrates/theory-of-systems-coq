(** * IonizationThreshold.v -- Bound vs free state classification
    Elements: threshold, bound/free predicates, ionization energy
    Roles:    energy sign determines bound (< 0) vs free (>= 0)
    Rules:    threshold separates; ionization requires |E_ground| energy
    STATUS:   8 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: April 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  DEFINITIONS                                                      *)
(* ================================================================ *)

Definition threshold : Q := 0.

Definition is_bound (e : Q) : Prop := e < 0.
Definition is_free (e : Q) : Prop := 0 <= e.

Definition is_bound_dec (e : Q) : bool :=
  if Qlt_le_dec e 0 then true else false.

Definition ionization_cost (e_ground : Q) : Q := Qabs e_ground.

(* ================================================================ *)
(*  THEOREM 1: Threshold separates bound and free                    *)
(* ================================================================ *)

Theorem threshold_separates :
  is_bound (-(1#2)) /\ is_free (1#4).
Proof.
  unfold is_bound, is_free. split; lra.
Qed.

(* ================================================================ *)
(*  THEOREM 2: Bound needs ionization energy                         *)
(* ================================================================ *)

Theorem bound_needs_energy :
  forall e : Q, is_bound e -> ionization_cost e > 0.
Proof.
  intros e Hb. unfold is_bound in Hb. unfold ionization_cost.
  destruct e as [n d]. unfold Qabs, Qlt in *. simpl in *.
  lia.
Qed.

(* ================================================================ *)
(*  THEOREM 3: Concrete ionization cost                              *)
(* ================================================================ *)

Theorem concrete_ionization :
  ionization_cost (-(1#2)) == 1 # 2.
Proof.
  unfold ionization_cost, Qabs. simpl. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 4: Free states have zero ionization cost conceptually    *)
(* ================================================================ *)

Theorem free_already_ionized :
  forall e : Q, is_free e -> e >= threshold.
Proof.
  intros e Hf. unfold is_free in Hf. unfold threshold. lra.
Qed.

(* ================================================================ *)
(*  THEOREM 5: Bound and free are complementary                      *)
(* ================================================================ *)

Theorem bound_free_complement :
  forall e : Q, is_bound e \/ is_free e.
Proof.
  intro e. unfold is_bound, is_free.
  destruct (Qlt_le_dec e 0); [left | right]; lra.
Qed.

(* ================================================================ *)
(*  THEOREM 6: Bound and free are exclusive                          *)
(* ================================================================ *)

Theorem bound_free_exclusive :
  forall e : Q, is_bound e -> ~ is_free e.
Proof.
  intros e Hb Hf. unfold is_bound in Hb. unfold is_free in Hf. lra.
Qed.

(* ================================================================ *)
(*  THEOREM 7: Deeper bound = more ionization energy                 *)
(* ================================================================ *)

Theorem deeper_more_energy :
  ionization_cost (-(1#1)) > ionization_cost (-(1#2)).
Proof.
  unfold ionization_cost, Qabs. simpl. reflexivity.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem ionization_threshold_synthesis :
  (* Threshold separates *)
  is_bound (-(1#2)) /\ is_free (1#4) /\
  (* Bound needs energy *)
  ionization_cost (-(1#2)) == 1 # 2 /\
  (* Classification is total *)
  (forall e : Q, is_bound e \/ is_free e) /\
  (* Deeper bound = more energy *)
  ionization_cost (-(1#1)) > ionization_cost (-(1#2)).
Proof.
  split. { exact (proj1 threshold_separates). }
  split. { exact (proj2 threshold_separates). }
  split. { exact concrete_ionization. }
  split. { exact bound_free_complement. }
  exact deeper_more_energy.
Qed.
