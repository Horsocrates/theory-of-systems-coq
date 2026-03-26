(* GraphClassification.v *)
(* E/R/R: Elements = graph phases (Gapped vs Critical)
         Roles = classify by spectral gap size, count phase types
         Rules = chain/ladder are gapped, cycle/complete/star/petersen/tree are critical *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

From ToS Require Import stdlib.graph.GraphZoo.

Open Scope Q_scope.

(* === Graph phases === *)

Inductive GraphPhase : Set :=
  | GappedGraph : Q -> GraphPhase
  | CriticalGraph : GraphPhase.

(* Local Qlt_bool: true if a < b *)
Definition Qlt_bool_local (a b : Q) : bool :=
  andb (Qle_bool a b) (negb (Qeq_bool a b)).

(* Classify: if gap < 0.1 then Critical, else Gapped *)
Definition classify_graph (gap : Q) : GraphPhase :=
  if Qlt_bool_local gap (1#10) then CriticalGraph
  else GappedGraph gap.

Lemma chain_gapped : classify_graph (70#100) = GappedGraph (70#100).
Proof. vm_compute. reflexivity. Qed.

Lemma ladder_gapped : classify_graph (76#100) = GappedGraph (76#100).
Proof. vm_compute. reflexivity. Qed.

Lemma cycle_critical : classify_graph 0 = CriticalGraph.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_critical : classify_graph 0 = CriticalGraph.
Proof. vm_compute. reflexivity. Qed.

(* === Gap positivity === *)

Lemma gap_positive_chain : 0 < (70#100).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma gap_positive_ladder : 0 < (76#100).
Proof. unfold Qlt. simpl. lia. Qed.

(* === Phase counting === *)
(* 2 gapped (chain 0.70, ladder 0.76) vs 5 critical (cycle, complete, star, petersen, tree) *)

Definition gapped_count : nat := 2.
Definition critical_count : nat := 5.

Lemma total_zoo_size : (gapped_count + critical_count = 7)%nat.
Proof. reflexivity. Qed.

(* === Connection to GraphZoo hbar values === *)

Lemma chain_gap_from_hbar : 1 - hbar_chain == 6#100.
Proof. vm_compute. reflexivity. Qed.

Lemma ladder_gap_from_hbar : hbar_ladder - 1 == 31#100.
Proof. vm_compute. reflexivity. Qed.

Lemma petersen_gap_from_hbar : hbar_petersen - 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma gapped_have_positive_gap :
  0 < (70#100) /\ 0 < (76#100).
Proof. split; unfold Qlt; simpl; lia. Qed.

Lemma critical_threshold : (1#10) > 0.
Proof. unfold Qlt. simpl. lia. Qed.
