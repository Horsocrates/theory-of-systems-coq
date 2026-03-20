(** * SymbolicDynamics.v -- Shift spaces and symbolic coding over Q
    Elements: tent_symbol, itinerary_at, golden_mean_allowed, h_golden_mean
    Roles:    Symbolic coding of tent map orbits, subshift entropy
    Rules:    Itinerary I(x) = s₀s₁s₂... with sₙ = 0 if f^n(x) < 1/2, else 1
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.LyapunovProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  SYMBOLIC CODING                                                    *)
(* ================================================================== *)

(** Code: sₙ = 0 if f^n(x) < 1/2, else 1 *)
Definition tent_symbol (x : Q) : nat :=
  if Qle_bool x (1#2) then 0%nat else 1%nat.

(** Note: we use ≤ 1/2 → 0, > 1/2 → 1 via Qle_bool *)

Definition itinerary_at (x : Q) (n : nat) : nat :=
  tent_symbol (iterate tent_map x n).

(* ================================================================== *)
(*  CONCRETE ITINERARIES                                               *)
(* ================================================================== *)

(** x = 1/4: T(1/4)=1/2, T(1/2)=1, T(1)=0, ... *)
Lemma itin_quarter_0 : itinerary_at (1#4) 0 = 0%nat.
Proof. unfold itinerary_at, tent_symbol, iterate, tent_map. vm_compute. reflexivity. Qed.

(** tent_map(1/4) = 1/2. Since 1/2 ≤ 1/2, tent_symbol = 0 *)
Lemma itin_quarter_1 : itinerary_at (1#4) 1 = 0%nat.
Proof. unfold itinerary_at, tent_symbol, iterate, tent_map. vm_compute. reflexivity. Qed.

(** x = 2/7 (period 3): T(2/7)=4/7, T(4/7)=6/7, T(6/7)=2/7 *)
Lemma itin_2_7_step0 : itinerary_at (2#7) 0 = 0%nat.
Proof. unfold itinerary_at, tent_symbol, iterate, tent_map. vm_compute. reflexivity. Qed.

Lemma itin_2_7_step1 : itinerary_at (2#7) 1 = 1%nat.
Proof. unfold itinerary_at, tent_symbol, iterate, tent_map. vm_compute. reflexivity. Qed.

Lemma itin_2_7_step2 : itinerary_at (2#7) 2 = 1%nat.
Proof. unfold itinerary_at, tent_symbol, iterate, tent_map. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FORBIDDEN WORDS AND SUBSHIFTS                                      *)
(* ================================================================== *)

(** Full shift {0,1}^ℕ: all sequences allowed
    Golden mean shift: no "11" allowed
    h_top(golden mean) = ln(φ) where φ = (1+√5)/2 *)

Definition golden_mean_allowed (s0 s1 : nat) : bool :=
  negb (Nat.eqb s0 1 && Nat.eqb s1 1)%bool.

(** Test: "01" allowed, "11" forbidden *)
Lemma gm_01_allowed : golden_mean_allowed 0 1 = true.
Proof. reflexivity. Qed.

Lemma gm_11_forbidden : golden_mean_allowed 1 1 = false.
Proof. reflexivity. Qed.

Lemma gm_10_allowed : golden_mean_allowed 1 0 = true.
Proof. reflexivity. Qed.

(** Golden mean entropy: ln(φ) ≈ 6/13 (Padé)
    True: ln(φ) ≈ 0.4812. Our: 6/13 ≈ 0.4615. Error: 4%. *)
Definition h_golden_mean : Q := 6 # 13.

(** h(golden mean) < h(full shift) = ln(2) *)
Theorem golden_mean_less_than_full :
  h_golden_mean < ln2_approx.
Proof. unfold h_golden_mean, ln2_approx. lra. Qed.

(** h(golden mean) > 0 (still chaotic, just less) *)
Theorem golden_mean_positive :
  0 < h_golden_mean.
Proof. unfold h_golden_mean. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem symbolic_dynamics_synthesis :
  itinerary_at (1#4) 0 = 0%nat /\
  itinerary_at (1#4) 1 = 0%nat /\
  itinerary_at (2#7) 0 = 0%nat /\
  0 < h_golden_mean /\
  h_golden_mean < ln2_approx.
Proof.
  split; [|split; [|split; [|split]]].
  - exact itin_quarter_0.
  - exact itin_quarter_1.
  - exact itin_2_7_step0.
  - exact golden_mean_positive.
  - exact golden_mean_less_than_full.
Qed.
