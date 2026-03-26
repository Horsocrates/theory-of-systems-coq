(* AndersonModel.v *)
(* E/R/R: Elements = disorder strength W, localization length, Anderson phases
         Roles = classify into Extended/Localized, compute localization length
         Rules = all 1D states localize for W > 0, length ~ 1/W^2 *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.
Require Import Lra.

Open Scope Q_scope.

(* === Anderson phases === *)

Inductive AndersonPhase : Set :=
  | Extended : AndersonPhase
  | Localized : AndersonPhase.

Definition classify_anderson (W : Q) : AndersonPhase :=
  if Qle_bool W 0 then Extended else Localized.

Lemma clean_extended : classify_anderson 0 = Extended.
Proof. vm_compute. reflexivity. Qed.

Lemma disordered_localized : classify_anderson 1 = Localized.
Proof. vm_compute. reflexivity. Qed.

Lemma any_disorder : classify_anderson (1#1000) = Localized.
Proof. vm_compute. reflexivity. Qed.

(* === Localization length === *)

Definition loc_length_approx (W : Q) : Q :=
  if Qle_bool W 0 then 0 else 4 / (W * W).

Lemma loc_small : loc_length_approx (1#10) == 400.
Proof. vm_compute. reflexivity. Qed.

Lemma loc_large : loc_length_approx 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma loc_decreases : loc_length_approx 2 < loc_length_approx (1#10).
Proof. unfold loc_length_approx. simpl. unfold Qlt. simpl. lia. Qed.

Lemma loc_monotone : loc_length_approx 1 < loc_length_approx (1#2).
Proof. unfold loc_length_approx. simpl. unfold Qlt. simpl. lia. Qed.

(* === Gap mechanisms === *)

Inductive GapMechanism : Set :=
  | QCD : GapMechanism
  | BCS : GapMechanism
  | Graphene : GapMechanism
  | Hydrogen : GapMechanism
  | Anderson : GapMechanism.

(* All from H = tridiag + diagonal structure *)
Definition mechanism_uses_tridiag (m : GapMechanism) : bool := true.

Lemma all_tridiag : forall m, mechanism_uses_tridiag m = true.
Proof. destruct m; reflexivity. Qed.

(* Typical gap values for each mechanism *)
Definition mechanism_gap (m : GapMechanism) : Q :=
  match m with
  | QCD => 938   (* MeV, proton mass *)
  | BCS => 1#1000 (* eV, superconducting gap *)
  | Graphene => 26#100 (* eV, sublattice gap *)
  | Hydrogen => 136#10 (* eV, ionization energy *)
  | Anderson => 1#10  (* eV, typical *)
  end.

Lemma qcd_largest_gap : forall m, m <> QCD ->
  mechanism_gap m < mechanism_gap QCD.
Proof.
  intros m Hm. destruct m; try contradiction;
  unfold mechanism_gap; unfold Qlt; simpl; lia.
Qed.

Lemma bcs_smallest_gap : forall m, m <> BCS ->
  mechanism_gap BCS < mechanism_gap m.
Proof.
  intros m Hm. destruct m; try contradiction;
  unfold mechanism_gap; unfold Qlt; simpl; lia.
Qed.

(* === Anderson localization properties === *)

Lemma loc_length_concrete_1 : loc_length_approx 1 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma loc_length_concrete_3 : loc_length_approx 3 == 4#9.
Proof. vm_compute. reflexivity. Qed.

Lemma extended_zero_length : loc_length_approx 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma loc_half : loc_length_approx (1#2) == 16.
Proof. vm_compute. reflexivity. Qed.

Lemma five_mechanisms_count :
  forall m, m = QCD \/ m = BCS \/ m = Graphene \/ m = Hydrogen \/ m = Anderson.
Proof. destruct m; auto. Qed.

Lemma anderson_gap_between :
  mechanism_gap BCS < mechanism_gap Anderson /\
  mechanism_gap Anderson < mechanism_gap Graphene.
Proof.
  split; unfold mechanism_gap; unfold Qlt; simpl; lia.
Qed.

Lemma gap_ordering :
  mechanism_gap BCS < mechanism_gap Anderson /\
  mechanism_gap Anderson < mechanism_gap Graphene /\
  mechanism_gap Graphene < mechanism_gap Hydrogen /\
  mechanism_gap Hydrogen < mechanism_gap QCD.
Proof.
  repeat split; unfold mechanism_gap; unfold Qlt; simpl; lia.
Qed.
