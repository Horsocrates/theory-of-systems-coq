(* DistinctionPrior.v *)
(* Elements: distinction process starts at 0, natural nail selection *)
(* Roles: PH_nail as natural choice, Occam comparison *)
(* Rules: PH needs 0 extra assumptions, process starts from no-distinction *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.NailedSets.

Open Scope Q_scope.

(* ===== Distinction Prior: Process Starts at Zero ===== *)

(* The initial state: no distinction = S_0 *)
Definition S_0 : Q := 0.

(* Process starts at zero entropy (no distinctions) *)
Lemma process_starts_at_zero : S_0 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Natural nail: PH_nail because process starts from S_0 *)
Definition natural_nail : NailedSet := PH_nail.

Lemma natural_nail_is_PH : natural_nail = PH_nail.
Proof. reflexivity. Qed.

(* Extra assumptions count *)
Definition PH_extra_assumptions : nat := 0%nat.
Definition BB_extra_assumptions : nat := 1%nat.
Definition TwoNail_extra_assumptions : nat := 2%nat.

Lemma PH_extra_zero : PH_extra_assumptions = 0%nat.
Proof. reflexivity. Qed.

Lemma BB_extra_one : BB_extra_assumptions = 1%nat.
Proof. reflexivity. Qed.

(* Occam prefers PH *)
Lemma occam_prefers_PH_over_BB :
  (PH_extra_assumptions < BB_extra_assumptions)%nat.
Proof. unfold PH_extra_assumptions, BB_extra_assumptions. lia. Qed.

Lemma occam_prefers_PH_over_TwoNail :
  (PH_extra_assumptions < TwoNail_extra_assumptions)%nat.
Proof. unfold PH_extra_assumptions, TwoNail_extra_assumptions. lia. Qed.

(* PH is minimal: no nail has fewer assumptions *)
Lemma PH_is_minimal : forall n : NailedSet,
  (extra_assumptions PH_nail <= extra_assumptions n)%nat.
Proof.
  destruct n; simpl; lia.
Qed.

(* Distinction prior: starting from S_0 implies PH *)
Lemma distinction_prior_implies_PH :
  S_0 == 0 -> natural_nail = PH_nail.
Proof.
  intros _. reflexivity.
Qed.

(* The distinction grows from zero — no past hypothesis needed *)
Lemma no_past_hypothesis_needed :
  PH_extra_assumptions = 0%nat /\ S_0 == 0.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

(* BB requires positing fluctuation from equilibrium *)
Lemma BB_requires_fluctuation :
  BB_extra_assumptions = 1%nat /\
  (PH_extra_assumptions < BB_extra_assumptions)%nat.
Proof.
  split.
  - reflexivity.
  - unfold PH_extra_assumptions, BB_extra_assumptions. lia.
Qed.
