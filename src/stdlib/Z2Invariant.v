(** * Z2Invariant.v — Z2 Topological Invariant from Pfaffian Signs
    Elements: Sign products at TRIM points, Z2 parity
    Roles:    Classify time-reversal invariant insulators
    Rules:    Product of signs = +1 → trivial, -1 → topological
    Status:   Stdlib — Six Directions Phase 2, Section E8
    STATUS: 11 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================== *)
(*  PART I: Z2 INVARIANT AS SIGN PRODUCT                               *)
(*  delta_i = ±1 at each TRIM point                                   *)
(*  Z2 = product of all delta_i                                       *)
(* ================================================================== *)

Definition Z2_invariant (delta : list Z) : Z :=
  fold_left Z.mul delta 1.

(* ================================================================== *)
(*  PART II: CONCRETE SIGN PATTERNS                                    *)
(* ================================================================== *)

(* All positive: trivial insulator *)
Lemma trivial_all_plus : Z2_invariant [1; 1; 1; 1] = 1.
Proof. vm_compute. reflexivity. Qed.

(* One negative: topological insulator *)
Lemma topological_one_minus : Z2_invariant [1; 1; 1; (-1)] = (-1).
Proof. vm_compute. reflexivity. Qed.

(* Two negatives: trivial (product = +1) *)
Lemma trivial_two_minus : Z2_invariant [1; 1; (-1); (-1)] = 1.
Proof. vm_compute. reflexivity. Qed.

(* Three negatives: topological *)
Lemma topological_three_minus : Z2_invariant [1; (-1); (-1); (-1)] = (-1).
Proof. vm_compute. reflexivity. Qed.

(* All negative: trivial (4 sign flips = even) *)
Lemma trivial_all_minus : Z2_invariant [(-1); (-1); (-1); (-1)] = 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: Z2 CLASSIFICATION                                        *)
(* ================================================================== *)

Definition is_Z2_topological (delta : list Z) : bool :=
  Z.eqb (Z2_invariant delta) (-1).

Lemma z2_topo_one_flip : is_Z2_topological [1; 1; 1; (-1)] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma z2_trivial_no_flip : is_Z2_topological [1; 1; 1; 1] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma z2_trivial_two_flips : is_Z2_topological [1; 1; (-1); (-1)] = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: PARITY PRINCIPLE                                           *)
(*  Z2 is determined by parity of negative count                      *)
(* ================================================================== *)

Definition count_neg_Z (l : list Z) : nat :=
  fold_left (fun acc x => if Z.ltb x 0 then S acc else acc) l 0%nat.

Lemma parity_one_minus : count_neg_Z [1; 1; 1; (-1)] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma parity_two_minus : count_neg_Z [1; 1; (-1); (-1)] = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem z2_invariant_synthesis :
  Z2_invariant [1; 1; 1; 1] = 1 /\
  Z2_invariant [1; 1; 1; (-1)] = (-1) /\
  Z2_invariant [1; 1; (-1); (-1)] = 1 /\
  Z2_invariant [(-1); (-1); (-1); (-1)] = 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
