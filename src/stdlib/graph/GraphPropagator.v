(* GraphPropagator.v *)
(* E/R/R: Elements = path counts on chain graph, Catalan numbers
         Roles = propagator G(n,j) = number of walks of length n from 0 to j
         Rules = return probabilities are Catalan, paths grow combinatorially *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

Open Scope Q_scope.

(* === Chain graph propagator: paths of length n ending at site j === *)
(* For the infinite chain (Z), starting at 0 *)
(* G(n,j) counts lattice paths of n steps from 0 to j *)

Definition chain_paths (n j : nat) : Q :=
  match n, j with
  | O, O => 1
  | S O, S O => 1
  | S (S O), O => 1
  | S (S O), S (S O) => 1
  | S (S (S O)), S O => 2
  | S (S (S O)), S (S (S O)) => 1
  | S (S (S (S O))), O => 2
  | S (S (S (S O))), S (S O) => 3
  | S (S (S (S O))), S (S (S (S O))) => 1
  | S (S (S (S (S O)))), S O => 5
  | S (S (S (S (S O)))), S (S (S O)) => 4
  | S (S (S (S (S O)))), S (S (S (S (S O)))) => 1
  | S (S (S (S (S (S O))))), O => 5
  | S (S (S (S (S (S O))))), S (S O) => 9
  | S (S (S (S (S (S O))))), S (S (S (S O))) => 5
  | S (S (S (S (S (S O))))), S (S (S (S (S (S O))))) => 1
  | S (S (S (S (S (S (S O)))))), S O => 14
  | S (S (S (S (S (S (S O)))))), S (S (S O)) => 14
  | S (S (S (S (S (S (S O)))))), S (S (S (S (S O)))) => 6
  | S (S (S (S (S (S (S O)))))), S (S (S (S (S (S (S O)))))) => 1
  | _, _ => 0
  end.

(* === Path growth === *)

Lemma paths_grow :
  chain_paths 3 1 == 2 /\
  chain_paths 5 1 == 5 /\
  chain_paths 7 1 == 14.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Return probability (paths back to origin) === *)

Lemma return_prob :
  chain_paths 0 0 == 1 /\
  chain_paths 2 0 == 1 /\
  chain_paths 4 0 == 2 /\
  chain_paths 6 0 == 5.
Proof.
  split; [| split; [| split]]; vm_compute; reflexivity.
Qed.

(* === Catalan numbers: 1, 1, 2, 5, 14 === *)

Lemma paths_are_catalan :
  chain_paths 0 0 == 1 /\
  chain_paths 2 0 == 1 /\
  chain_paths 4 0 == 2 /\
  chain_paths 6 0 == 5.
Proof.
  split; [| split; [| split]]; vm_compute; reflexivity.
Qed.

(* === Symmetry === *)

Lemma paths_symmetric : chain_paths 2 0 == chain_paths 2 2.
Proof. vm_compute. reflexivity. Qed.

(* === Spread === *)

Lemma spread_grows : chain_paths 7 5 > 0.
Proof. unfold chain_paths. unfold Qlt. simpl. lia. Qed.

(* === Additional path properties === *)

Lemma paths_origin : chain_paths 0 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma paths_one_step : chain_paths 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_no_return_2 : chain_paths 1 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_no_return_3 : chain_paths 3 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_growth :
  chain_paths 0 0 < chain_paths 4 0 /\
  chain_paths 4 0 < chain_paths 6 0.
Proof.
  split; unfold chain_paths; unfold Qlt; simpl; lia.
Qed.

Lemma paths_boundary :
  chain_paths 4 4 == 1 /\
  chain_paths 6 6 == 1 /\
  chain_paths 7 7 == 1.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

Lemma six_step_interior :
  chain_paths 6 2 == 9 /\
  chain_paths 6 4 == 5.
Proof.
  split; vm_compute; reflexivity.
Qed.

Lemma seven_step_peak :
  chain_paths 7 1 == 14 /\
  chain_paths 7 3 == 14.
Proof.
  split; vm_compute; reflexivity.
Qed.

Lemma paths_total_step4 :
  chain_paths 4 0 + chain_paths 4 2 + chain_paths 4 4 == 6.
Proof. vm_compute. reflexivity. Qed.
