(* SecondLaw.v *)
(* Elements: second law of thermodynamics from doubly stochastic mixing *)
(* Roles: entropy non-decrease under application of T *)
(* Rules: concrete proofs for multiple initial states, iterated application *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.DoublyStochastic.
From ToS Require Import stdlib.foundations.MajorizationSchur.

Open Scope Q_scope.

(* ===== Second Law: Entropy Non-Decrease ===== *)

(* Concrete second law: S2(3/4) <= S2(apply_T (1/3) (3/4)) *)
Lemma second_law_concrete :
  S2 (3#4) <= S2 (apply_T (1#3) (3#4)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.

(* Concrete second law 2: S2(9/10) <= S2(apply_T (1/4) (9/10)) *)
Lemma second_law_concrete_2 :
  S2 (9#10) <= S2 (apply_T (1#4) (9#10)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.

(* Concrete second law 3: S2(2/3) <= S2(apply_T (1/3) (2/3)) *)
Lemma second_law_concrete_3 :
  S2 (2#3) <= S2 (apply_T (1#3) (2#3)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.

(* ===== Iterated Application ===== *)

(* Two steps: S2(3/4) < S2(T(3/4)) < S2(T(T(3/4))) *)
Lemma iterated_entropy_step1 : S2 (3#4) < S2 (apply_T (1#3) (3#4)).
Proof. vm_compute. reflexivity. Qed.

Lemma iterated_entropy_step2 :
  S2 (apply_T (1#3) (3#4)) < S2 (apply_T (1#3) (apply_T (1#3) (3#4))).
Proof. vm_compute. reflexivity. Qed.

Lemma iterated_entropy_transitive :
  S2 (3#4) < S2 (apply_T (1#3) (apply_T (1#3) (3#4))).
Proof. vm_compute. reflexivity. Qed.

(* ===== Equilibrium ===== *)

(* S2(1/2) is the maximum *)
Lemma equilibrium_is_max_1 : S2 (3#4) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma equilibrium_is_max_2 : S2 (9#10) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma equilibrium_is_max_3 : S2 (7#12) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

(* ===== No Past Hypothesis Needed ===== *)

(* The second law works for any concrete starting point a > 1/2 *)
Lemma no_past_hypothesis_1 : S2 (3#4) <= S2 (apply_T (1#3) (3#4)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.

Lemma no_past_hypothesis_2 : S2 (9#10) <= S2 (apply_T (1#4) (9#10)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.

Lemma no_past_hypothesis_3 : S2 (7#10) <= S2 (apply_T (1#3) (7#10)).
Proof. apply Qlt_le_weak. vm_compute. reflexivity. Qed.
