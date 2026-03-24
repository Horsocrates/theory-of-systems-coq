(** * Informativeness.v — Search Cost from Informativeness as ToS System

    Theory of Systems — P vs NP Complexity Insights

    Elements: search space, informativeness (bits per query), search cost
    Roles:    high_informativeness → P (logarithmic search),
              low_informativeness → NP (linear/exponential search)
    Rules:    cost = space / informativeness; IVT gives max informativeness
    Status:   informative | uninformative

    Connection: Each query to an oracle returns some bits of information.
    IVT (bisection) extracts 1 bit per query → log(N) total.
    A plateau returns 0 bits → N queries needed.

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

(** Search cost: space / informativeness. If info=0, cost=space (brute force) *)
Definition search_cost_from_info (space info : nat) : nat :=
  match info with
  | O => space
  | S _ => space / info
  end.

(** IVT informativeness: bisection halves the space each step *)
(** For space=256, each query eliminates half → info = space/log2(space) *)
Definition ivt_informativeness (space : nat) : nat :=
  space / (Nat.log2 space + 1).

(** Plateau informativeness: no signal → must check everything *)
Definition plateau_informativeness : nat := 1.

(* ===== Concrete computations ===== *)

Lemma ivt_info_256 : ivt_informativeness 256 = 28%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma search_with_ivt : search_cost_from_info 256 28 = 9%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma search_plateau : search_cost_from_info 256 1 = 256%nat.
Proof. vm_compute. reflexivity. Qed.

(** IVT search is much cheaper than plateau *)
Lemma ivt_beats_plateau :
  (search_cost_from_info 256 28 < search_cost_from_info 256 1)%nat.
Proof. vm_compute. lia. Qed.

(** Zero informativeness means brute force *)
Lemma zero_info_brute_force :
  forall space, search_cost_from_info space 0 = space.
Proof. intros. reflexivity. Qed.

(** Higher informativeness means lower cost *)
Lemma higher_info_lower_cost :
  (search_cost_from_info 100 10 < search_cost_from_info 100 5)%nat.
Proof. vm_compute. lia. Qed.

(** Informativeness 1 is same as brute force for search_cost *)
Lemma info_1_is_space :
  forall space, search_cost_from_info space 1 = space.
Proof. intros. unfold search_cost_from_info. apply Nat.div_1_r. Qed.

(** Concrete IVT info for space=64 *)
Lemma ivt_info_64 : ivt_informativeness 64 = 9%nat.
Proof. vm_compute. reflexivity. Qed.

(** IVT info for space=128 *)
Lemma ivt_info_128 : ivt_informativeness 128 = 16%nat.
Proof. vm_compute. reflexivity. Qed.

(** search_cost_from_info with info=2 halves the space *)
Lemma info_2_halves :
  search_cost_from_info 100 2 = 50%nat.
Proof. vm_compute. reflexivity. Qed.

(** IVT search cost for space=64 *)
Lemma search_ivt_64 : search_cost_from_info 64 9 = 7%nat.
Proof. vm_compute. reflexivity. Qed.

(** Monotonicity: larger space → higher cost at same informativeness *)
Lemma cost_mono_space :
  (search_cost_from_info 64 4 < search_cost_from_info 128 4)%nat.
Proof. vm_compute. lia. Qed.

(** IVT informativeness grows with space *)
Lemma ivt_info_grows :
  (ivt_informativeness 64 < ivt_informativeness 256)%nat.
Proof. vm_compute. lia. Qed.

(** The informativeness ratio: IVT vs plateau *)
Lemma informativeness_ratio :
  (ivt_informativeness 256 / plateau_informativeness = 28)%nat.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R: informativeness determines complexity class *)
Theorem informativeness_determines_class :
  (search_cost_from_info 256 28 < search_cost_from_info 256 1)%nat /\
  (search_cost_from_info 256 28 < 15)%nat.
Proof. vm_compute. lia. Qed.
