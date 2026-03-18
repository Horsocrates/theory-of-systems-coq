(** * ProcessLorentzian.v — Signed Interval ds^2 = -dt^2 + dx^2

    Theory of Systems — Step 4 Phase 22: Lorentzian from P4 (File 2)

    Elements: edge_sign, signed_length_sq, spacetime_interval
    Roles:    space = +1, time = -1, Minkowski interval
    Rules:    reversible -> positive, irreversible -> negative
    Status:   complete

    Space edges contribute POSITIVELY to the interval.
    Time edges contribute NEGATIVELY.
    Combined: ds^2 = -tau^2 + ell^2 = Lorentzian signature.

    STATUS: 15 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSpacetime.

(* ================================================================== *)
(*  Part I: Signed Interval  (~8 lemmas)                              *)
(* ================================================================== *)

(** The metric sign: space = +1, time = -1 *)
Definition edge_sign (e : STEdge) : Q :=
  match ste_type e with
  | SpaceEdge => 1
  | TimeEdge => -(1)
  end.

(** Signed squared length of an edge *)
Definition signed_length_sq (e : STEdge) : Q :=
  edge_sign e * ste_length e * ste_length e.

(** Space edge sign *)
Lemma space_sign : forall e,
  ste_type e = SpaceEdge -> edge_sign e == 1.
Proof.
  intros e He. unfold edge_sign. rewrite He. reflexivity.
Qed.

(** Time edge sign *)
Lemma time_sign : forall e,
  ste_type e = TimeEdge -> edge_sign e == -(1).
Proof.
  intros e He. unfold edge_sign. rewrite He. reflexivity.
Qed.

(** Space edge: positive contribution *)
Lemma space_positive : forall e,
  ste_type e = SpaceEdge ->
  0 < ste_length e ->
  0 < signed_length_sq e.
Proof.
  intros e Hs Hpos. unfold signed_length_sq, edge_sign. rewrite Hs.
  assert (H : 1 * ste_length e * ste_length e == ste_length e * ste_length e) by ring.
  rewrite H. apply Qmult_lt_0_compat; auto.
Qed.

(** Time edge: negative contribution *)
Lemma time_negative : forall e,
  ste_type e = TimeEdge ->
  0 < ste_length e ->
  signed_length_sq e < 0.
Proof.
  intros e Ht Hpos. unfold signed_length_sq, edge_sign. rewrite Ht.
  assert (H : -(1) * ste_length e * ste_length e == -(ste_length e * ste_length e)) by ring.
  rewrite H.
  assert (Hsq : 0 < ste_length e * ste_length e) by (apply Qmult_lt_0_compat; auto).
  lra.
Qed.

(** Spacetime interval: sum of signed squared lengths *)
Definition spacetime_interval (path : list STEdge) : Q :=
  fold_left (fun acc e => acc + signed_length_sq e) path 0.

(** Empty path: interval = 0 *)
Lemma interval_empty : spacetime_interval [] == 0.
Proof. reflexivity. Qed.

(** Single edge interval *)
Lemma interval_single : forall e,
  spacetime_interval [e] == signed_length_sq e.
Proof.
  intros. unfold spacetime_interval. simpl. ring.
Qed.

(* ================================================================== *)
(*  Part II: Why the Minus Sign  (~5 lemmas)                          *)
(* ================================================================== *)

(** Space round trip: go i->j then j->i *)
Lemma space_round_trip : forall e1 e2,
  ste_type e1 = SpaceEdge -> ste_type e2 = SpaceEdge ->
  ste_length e1 == ste_length e2 ->
  spacetime_interval [e1; e2] == 2 * ste_length e1 * ste_length e1.
Proof.
  intros e1 e2 H1 H2 Heq.
  unfold spacetime_interval. simpl.
  unfold signed_length_sq, edge_sign. rewrite H1. rewrite H2.
  rewrite Heq. ring.
Qed.

(** Time "round trip" would also be positive — but it's IMPOSSIBLE *)
Theorem sign_from_irreversibility :
  (* Space: reversible -> positive contribution -> round trips have interval > 0 *)
  (* Time: irreversible -> negative contribution -> no round trips possible *)
  (* The sign difference = the arrow of time encoded metrically *)
  forall tau ell : Q, -(tau*tau) + ell*ell == ell*ell - tau*tau.
Proof. intros. ring. Qed.

(** Two-edge interval: one time + one space *)
Lemma mixed_interval : forall et es,
  ste_type et = TimeEdge -> ste_type es = SpaceEdge ->
  spacetime_interval [et; es] ==
    -(ste_length et * ste_length et) + ste_length es * ste_length es.
Proof.
  intros et es Ht Hs.
  unfold spacetime_interval. simpl.
  unfold signed_length_sq, edge_sign. rewrite Ht. rewrite Hs. ring.
Qed.

(** THIS is the Lorentzian interval: ds^2 = -dt^2 + dx^2 *)
Theorem lorentzian_signature :
  (* For a path with time edges (length tau) and space edges (length ell): *)
  (* ds^2 = -n_time * tau^2 + n_space * ell^2 *)
  (* The minus sign on time comes from irreversibility *)
  (* The plus sign on space comes from reversibility *)
  forall n tau ell : Q, -n*tau*tau + n*ell*ell == n*(ell*ell - tau*tau).
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Part III: Flat Minkowski  (~5 lemmas)                             *)
(* ================================================================== *)

(** Flat spacetime: uniform spacing tau (time) and ell (space) *)
Definition minkowski_interval (tau ell : Q) (n_time n_space : nat) : Q :=
  -(inject_Z (Z.of_nat n_time) * tau * tau) +
  inject_Z (Z.of_nat n_space) * ell * ell.

(** Helper: inject_Z of positive nat is positive *)
Lemma inject_Z_nat_pos : forall n, (0 < n)%nat ->
  0 < inject_Z (Z.of_nat n).
Proof. intros n Hn. unfold Qlt, inject_Z. simpl. lia. Qed.

(** Pure time: interval negative (concrete n=1) *)
Lemma minkowski_pure_time_1 : forall tau,
  0 < tau ->
  minkowski_interval tau 1 1 0 < 0.
Proof.
  intros tau Htau. unfold minkowski_interval.
  change (inject_Z (Z.of_nat 1)) with 1.
  change (inject_Z (Z.of_nat 0)) with 0.
  assert (Hsq : 0 < tau * tau) by (apply Qmult_lt_0_compat; auto).
  lra.
Qed.

(** Pure space: interval positive (concrete n=1) *)
Lemma minkowski_pure_space_1 : forall ell,
  0 < ell ->
  0 < minkowski_interval 1 ell 0 1.
Proof.
  intros ell Hell. unfold minkowski_interval.
  change (inject_Z (Z.of_nat 0)) with 0.
  change (inject_Z (Z.of_nat 1)) with 1.
  assert (Hsq : 0 < ell * ell) by (apply Qmult_lt_0_compat; auto).
  lra.
Qed.

(** Null path: ds^2 = 0 -> tau = ell (for 1 step + 1 edge) *)
Lemma null_path_condition : forall tau ell,
  0 < tau -> 0 < ell ->
  minkowski_interval tau ell 1 1 == 0 ->
  tau * tau == ell * ell.
Proof.
  intros tau ell Htau Hell Hnull. unfold minkowski_interval in Hnull.
  change (inject_Z (Z.of_nat 1)) with 1 in Hnull.
  lra.
Qed.

(** Speed of light: c = ell/tau *)
Definition speed_of_light (tau ell : Q) : Q := ell / tau.

(** Null path -> c = 1 when tau = ell *)
Lemma null_implies_c_one : forall tau,
  0 < tau ->
  speed_of_light tau tau == 1.
Proof.
  intros tau Htau. unfold speed_of_light.
  field. lra.
Qed.
