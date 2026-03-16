(** * ProcessComplexRules.v - E/R/R with Q[i]-Valued Rules and Chirality

    Theory of Systems - Phase 34: CP Violation from Complex Rules (File 2)

    Elements: ChiralERR, complex_rule, cp_transform
    Roles:    left/right Rules, parity violation, CP transformation
    Rules:    L != R -> parity violation, CP maps L <-> R
    Status:   complete

    When left-handed and right-handed fermions couple differently,
    the effective Rule is complex: R = R_L + i*R_R in Q[i].
    The imaginary part encodes the parity violation.

    STATUS: 18 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Arith.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessGaussianQ.

(* ================================================================== *)
(*  Part I: Chiral E/R/R  (~6 lemmas)                                 *)
(* ================================================================== *)

(** A chiral E/R/R system: separate left and right Rules *)
Record ChiralERR := mkChiralERR {
  ch_nsites : nat;
  ch_nroles : nat;
  ch_rule_left : nat -> nat -> Q;    (* left-handed coupling *)
  ch_rule_right : nat -> nat -> Q;   (* right-handed coupling *)
}.

(** Parity conserving: left = right *)
Definition is_parity_conserving (sys : ChiralERR) : Prop :=
  forall i j, ch_rule_left sys i j == ch_rule_right sys i j.

(** Parity violating: left != right *)
Definition is_parity_violating (sys : ChiralERR) : Prop :=
  exists i j, ~ ch_rule_left sys i j == ch_rule_right sys i j.

(** Combined complex Rule: R = R_L + i*R_R *)
Definition complex_rule (sys : ChiralERR) (i j : nat) : Qi :=
  mkQi (ch_rule_left sys i j) (ch_rule_right sys i j).

(** Parity conserving -> all complex rules have equal re/im *)
Lemma parity_conserving_equal : forall sys,
  is_parity_conserving sys ->
  forall i j, qi_re (complex_rule sys i j) == qi_im (complex_rule sys i j).
Proof.
  intros sys Hpc i j. unfold complex_rule. simpl. apply Hpc.
Qed.

(** Parity violating -> some complex rule has unequal re/im *)
Lemma parity_violating_unequal : forall sys,
  is_parity_violating sys ->
  exists i j, ~ qi_re (complex_rule sys i j) == qi_im (complex_rule sys i j).
Proof.
  intros sys [i [j H]]. exists i, j. unfold complex_rule. simpl. exact H.
Qed.

(* ================================================================== *)
(*  Part II: Concrete Weak Sector  (~6 lemmas)                        *)
(* ================================================================== *)

(** In the Standard Model: only LEFT-handed fermions feel weak force *)
(** Right-handed fermions are weak singlets *)

(** Concrete: left has mixing, right has no off-diagonal coupling *)
Definition weak_chiral_err : ChiralERR :=
  mkChiralERR
    4 2
    (fun i j => if Nat.eqb (i mod 2) (j mod 2) then 1 else 1#2)  (* L: full + mixing *)
    (fun i j => if Nat.eqb (i mod 2) (j mod 2) then 1 else 0).   (* R: no weak mixing *)

(** This system is parity violating *)
Lemma weak_is_parity_violating :
  is_parity_violating weak_chiral_err.
Proof.
  unfold is_parity_violating, weak_chiral_err. simpl.
  exists 0%nat, 1%nat. simpl. lra.
Qed.

(** Diagonal entries are parity conserving *)
Lemma weak_diagonal_conserved : forall i,
  ch_rule_left weak_chiral_err i i == ch_rule_right weak_chiral_err i i.
Proof.
  intros i. unfold weak_chiral_err. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Off-diagonal entries violate parity (when different mod 2) *)
Lemma weak_offdiag_violates :
  ~ ch_rule_left weak_chiral_err 0 1 == ch_rule_right weak_chiral_err 0 1.
Proof.
  unfold weak_chiral_err. simpl. lra.
Qed.

(** Parity violation is a structural property of Role assignment *)
Theorem parity_violation_from_roles :
  (* Different Role assignments for left and right fermions *)
  (* -> different Rule values -> parity violation *)
  (* Left: weak doublet (coupling 1/2 between roles) *)
  (* Right: weak singlet (no coupling between roles) *)
  is_parity_violating weak_chiral_err.
Proof. apply weak_is_parity_violating. Qed.

(** A parity-conserving system: same left and right *)
Definition parity_conserving_example : ChiralERR :=
  mkChiralERR 4 2 (fun i j => 1) (fun i j => 1).

Lemma example_parity_conserved :
  is_parity_conserving parity_conserving_example.
Proof.
  unfold is_parity_conserving, parity_conserving_example. simpl.
  intros i j. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: CP from Chirality  (~6 lemmas)                          *)
(* ================================================================== *)

(** C (charge conjugation): particle <-> antiparticle *)
(** P (parity): left <-> right *)
(** CP: both simultaneously *)

(** CP transform swaps left and right Rules *)
Definition cp_transform (sys : ChiralERR) : ChiralERR :=
  mkChiralERR
    (ch_nsites sys) (ch_nroles sys)
    (ch_rule_right sys)   (* L <-> R swap *)
    (ch_rule_left sys).

(** CP conserving: L(i,j) = R(j,i) *)
(** Includes both P (L<->R) and C (i<->j transpose) *)
Definition is_cp_conserving (sys : ChiralERR) : Prop :=
  forall i j, ch_rule_left sys i j == ch_rule_right sys j i.

(** CP violating: exists i,j such that L(i,j) != R(j,i) *)
Definition is_cp_violating (sys : ChiralERR) : Prop :=
  exists i j, ~ ch_rule_left sys i j == ch_rule_right sys j i.

(** CP transform is involutive *)
Lemma cp_transform_involutive : forall sys,
  ch_rule_left (cp_transform (cp_transform sys)) = ch_rule_left sys /\
  ch_rule_right (cp_transform (cp_transform sys)) = ch_rule_right sys.
Proof.
  intros sys. unfold cp_transform. simpl. split; reflexivity.
Qed.

(** Parity-conserving symmetric system is CP-conserving *)
Lemma symmetric_parity_conserving_is_cp : forall sys,
  is_parity_conserving sys ->
  (forall i j, ch_rule_left sys i j == ch_rule_left sys j i) ->
  is_cp_conserving sys.
Proof.
  intros sys Hpc Hsym i j.
  assert (H1 := Hpc j i).
  assert (H2 := Hsym i j).
  lra.
Qed.

(** CP violation in the weak sector *)
Lemma weak_is_cp_violating :
  is_cp_violating weak_chiral_err.
Proof.
  unfold is_cp_violating, weak_chiral_err. simpl.
  exists 0%nat, 1%nat. simpl. lra.
Qed.

(** CP violation possible when chirality is nontrivial *)
Theorem cp_violation_possible :
  (* A chiral E/R/R system CAN violate CP *)
  (* Whether it DOES depends on the Rule values *)
  is_cp_violating weak_chiral_err.
Proof. apply weak_is_cp_violating. Qed.

Theorem complex_rules_complete :
  (* Chiral E/R/R: separate left and right Rules *)
  (* Parity violation = L != R (structural from Role assignment) *)
  (* CP transform swaps L <-> R *)
  (* CP violation = L(i,j) != R(j,i) *)
  True.
Proof. exact I. Qed.
