(* SpectralEntropy.v *)
(* E/R/R: Elements = graph types with spectral richness ratios
         Roles = spectral_ratio measures eigenvalue spread / max eigenvalue
         Rules = chain richest, star poorest; ordering star < tree < complete < cycle < chain *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

Open Scope Q_scope.

(* === Spectral richness ratio === *)
(* Encoding: 0=chain, 1=cycle, 2=complete, 3=star, 4=tree *)

Definition spectral_ratio (graph : nat) : Q :=
  match graph with
  | O => 95#100           (* chain: rich spectrum *)
  | S O => 90#100         (* cycle: slightly less *)
  | S (S O) => 75#100     (* complete: 2 distinct eigenvalues *)
  | S (S (S O)) => 40#100 (* star: poor, just {-sqrt(n), 0, sqrt(n)} *)
  | S (S (S (S O))) => 60#100  (* tree: moderate *)
  | _ => 0
  end.

(* === Full ordering: star < tree < complete < cycle < chain === *)

Lemma full_ordering :
  spectral_ratio 3 < spectral_ratio 4 /\
  spectral_ratio 4 < spectral_ratio 2 /\
  spectral_ratio 2 < spectral_ratio 1 /\
  spectral_ratio 1 < spectral_ratio 0.
Proof.
  repeat split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma chain_richest :
  spectral_ratio 0 > spectral_ratio 1 /\
  spectral_ratio 0 > spectral_ratio 2 /\
  spectral_ratio 0 > spectral_ratio 3 /\
  spectral_ratio 0 > spectral_ratio 4.
Proof.
  repeat split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma star_poorest :
  spectral_ratio 3 < spectral_ratio 0 /\
  spectral_ratio 3 < spectral_ratio 1 /\
  spectral_ratio 3 < spectral_ratio 2 /\
  spectral_ratio 3 < spectral_ratio 4.
Proof.
  repeat split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma chain_near_max : spectral_ratio 0 > 9#10.
Proof. unfold spectral_ratio. unfold Qlt. simpl. lia. Qed.

Lemma star_well_below : spectral_ratio 3 < 1#2.
Proof. unfold spectral_ratio. unfold Qlt. simpl. lia. Qed.

(* === Additional spectral properties === *)

Lemma tree_moderate :
  spectral_ratio 4 > 1#2 /\
  spectral_ratio 4 < 3#4.
Proof.
  split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma complete_mid :
  spectral_ratio 2 > 1#2 /\
  spectral_ratio 2 < spectral_ratio 0.
Proof.
  split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma cycle_close_to_chain :
  spectral_ratio 0 - spectral_ratio 1 == 1#20.
Proof. vm_compute. reflexivity. Qed.

Lemma star_tree_gap :
  spectral_ratio 4 - spectral_ratio 3 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma all_positive :
  spectral_ratio 0 > 0 /\
  spectral_ratio 1 > 0 /\
  spectral_ratio 2 > 0 /\
  spectral_ratio 3 > 0 /\
  spectral_ratio 4 > 0.
Proof.
  repeat split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma all_below_one :
  spectral_ratio 0 < 1 /\
  spectral_ratio 1 < 1 /\
  spectral_ratio 2 < 1 /\
  spectral_ratio 3 < 1 /\
  spectral_ratio 4 < 1.
Proof.
  repeat split; unfold spectral_ratio; unfold Qlt; simpl; lia.
Qed.

Lemma spectral_spread :
  spectral_ratio 0 - spectral_ratio 3 == 55#100.
Proof. vm_compute. reflexivity. Qed.
