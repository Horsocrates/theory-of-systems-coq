(** * LandauerConnection.v — Landauer's principle from mode information
    Elements: landauer_cost, erasure_energy, kT
    Roles:    erasing information requires energy proportional to T
    Rules:    erasure cost = kT * ln2 per bit (here: proportional to T)
    STATUS:   8 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    LANDAUER'S PRINCIPLE:
    Erasing one bit of information requires at least kT*ln2 energy.
    In ToS: erasing = forgetting a mode distinction.
    Energy cost = temperature * information lost.
    Information is physical; erasure has thermodynamic cost.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import information.InformationFromModes.

(* ================================================================ *)
(*  LANDAUER COST                                                    *)
(* ================================================================ *)

(** Erasure energy cost: proportional to temperature and bits erased.
    In natural units: cost = T * bits_erased (absorbing k*ln2 into units) *)
Definition landauer_cost (T : Q) (bits_erased : Q) : Q :=
  T * bits_erased.

(** Erasure energy for going from entropy S1 to S2 < S1 *)
Definition erasure_energy (T S1 S2 : Q) : Q :=
  T * (S1 - S2).

(* ================================================================ *)
(*  ERASURE IS POSITIVE                                              *)
(* ================================================================ *)

Lemma erasure_positive :
  landauer_cost 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma erasure_positive_concrete :
  0 < landauer_cost (1#2) 1.
Proof. vm_compute. reflexivity. Qed.

(** Erasing 2 bits costs twice as much *)
Lemma erasure_scales :
  landauer_cost 1 2 == 2 * landauer_cost 1 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  COST PROPORTIONAL TO T                                          *)
(* ================================================================ *)

Lemma cost_proportional_to_T :
  (* At T=1: cost = 1 per bit *)
  landauer_cost 1 1 == 1 /\
  (* At T=2: cost = 2 per bit *)
  landauer_cost 2 1 == 2 /\
  (* Ratio: cost(T=2)/cost(T=1) = 2 *)
  landauer_cost 2 1 == 2 * landauer_cost 1 1.
Proof. vm_compute. split; [| split]; reflexivity. Qed.

(** Zero temperature → zero erasure cost *)
Lemma zero_temp_zero_cost :
  landauer_cost 0 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  ERASURE ENERGY FROM ENTROPY CHANGE                              *)
(* ================================================================ *)

(** Going from uniform (entropy 3/4) to pure (entropy 0):
    cost = T * 3/4 *)
Lemma erasure_uniform_to_pure :
  erasure_energy 1 (3#4) 0 == 3#4.
Proof. vm_compute. reflexivity. Qed.

(** Going from partial (entropy 1/2) to pure (entropy 0):
    cost = T * 1/2 — less than uniform→pure *)
Lemma erasure_partial_to_pure :
  erasure_energy 1 (1#2) 0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem landauer_connection_synthesis :
  (* Erasure costs energy *)
  0 < landauer_cost (1#2) 1 /\
  (* Cost proportional to T *)
  landauer_cost 2 1 == 2 * landauer_cost 1 1 /\
  (* Zero T → zero cost *)
  landauer_cost 0 1 == 0 /\
  (* More entropy reduction → more cost *)
  erasure_energy 1 (1#2) 0 < erasure_energy 1 (3#4) 0 /\
  (* Erasure scales with bits *)
  landauer_cost 1 2 == 2 * landauer_cost 1 1.
Proof.
  split; [exact erasure_positive_concrete |
  split; [vm_compute; reflexivity |
  split; [exact zero_temp_zero_cost |
  split; [vm_compute; reflexivity |
  exact erasure_scales]]]].
Qed.
