(** * UncertaintySynthesis.v -- Grand Synthesis of Uncertainty Bounds as ToS System
    Elements: Tridiag expectation values, bound_uniform formula
    Roles:    Unification of adjacency expectation with (K-1)/K formula
    Rules:    K=2 gives standard 1/2, K >= 3 exceeds 1/2, growth with K
    Status:   Stdlib
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.UncertaintyBounds.
From ToS Require Import stdlib.UncertaintyTable.
Open Scope Q_scope.

(* ================================================================== *)
(*  ADJACENCY EXPECTATION MATCHES (K-1)/K FOR UNIFORM STATES           *)
(* ================================================================== *)

(** K=2: uniform gives 2#2 == 1#2 = bound_uniform 2 *)
Lemma match_K2 : tridiag_expectation 2 [1;1] == bound_uniform 2 * 2.
Proof. vm_compute. reflexivity. Qed.

(** K=3: uniform gives 4#3 and bound = 2#3 *)
Lemma match_K3 : tridiag_expectation 3 [1;1;1] == bound_uniform 3 * 2.
Proof. vm_compute. reflexivity. Qed.

(** K=4: uniform gives 6#4 and bound = 3#4 *)
Lemma match_K4 : tridiag_expectation 4 [1;1;1;1] == bound_uniform 4 * 2.
Proof. vm_compute. reflexivity. Qed.

(** K=5: uniform gives 8#5 and bound = 4#5 *)
Lemma match_K5 : tridiag_expectation 5 [1;1;1;1;1] == bound_uniform 5 * 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  LOCALIZED VS DELOCALIZED CONTRAST                                   *)
(* ================================================================== *)

Lemma localized_K3 : tridiag_expectation 3 [0;1;0] == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma delocalized_K3 : tridiag_expectation 3 [1;1;1] == 4#3.
Proof. vm_compute. reflexivity. Qed.

(** K=2: ground state = delocalized = standard bound *)
Lemma K2_standard : tridiag_expectation 2 [1;1] == 1.
Proof. vm_compute. reflexivity. Qed.

(** K=3 uniform exceeds K=2 ground *)
Lemma K3_exceeds_K2 : tridiag_expectation 2 [1;1] < tridiag_expectation 3 [1;1;1].
Proof.
  change (tridiag_expectation 2 [1;1]) with (2#2).
  change (tridiag_expectation 3 [1;1;1]) with (4#3).
  unfold Qlt. simpl. lia.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem uncertainty_grand_synthesis :
  (* Uniform expectation = 2 * (K-1)/K verified for K=2..5 *)
  tridiag_expectation 2 [1;1] == bound_uniform 2 * 2 /\
  tridiag_expectation 3 [1;1;1] == bound_uniform 3 * 2 /\
  tridiag_expectation 4 [1;1;1;1] == bound_uniform 4 * 2 /\
  tridiag_expectation 5 [1;1;1;1;1] == bound_uniform 5 * 2 /\
  (* Standard bound at K=2 *)
  tridiag_expectation 2 [1;1] == 1 /\
  (* Localized = zero *)
  tridiag_expectation 3 [0;1;0] == 0 /\
  (* (K-1)/K exceeds 1/2 for K >= 3 *)
  (1#2) < (2#3) /\
  (1#2) < (4#5) /\
  (* bound_uniform formula values *)
  bound_uniform 2 == 1#2 /\
  bound_uniform 10 == 9#10.
Proof.
  split. { exact match_K2. }
  split. { exact match_K3. }
  split. { exact match_K4. }
  split. { exact match_K5. }
  split. { exact K2_standard. }
  split. { exact localized_K3. }
  split. { exact bound_exceeds_K3. }
  split. { exact bound_exceeds_K5. }
  split. { exact bound_uniform_2. }
  exact bound_uniform_10.
Qed.
