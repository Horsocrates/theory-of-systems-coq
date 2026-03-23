(** * KellyOptimal.v — Kelly criterion as ToS System
    Elements: win probability p, odds b, fraction f, growth rate
    Roles:    optimal sizing (Kelly), conservative sizing (half-Kelly)
    Rules:    kelly = (p*b - (1-p)) / b, growth positive at optimal,
              overbetting hurts, zero-edge gives zero fraction
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Kelly fraction: f* = (p*b - q) / b  where q = 1 - p             *)
(* ================================================================ *)

Definition kelly (p b : Q) : Q :=
  (p * b - (1 - p)) / b.

Definition half_kelly (p b : Q) : Q :=
  kelly p b / 2.

(* Approximate growth rate: g(f) = f*(p*b - q) - f^2*(p*b^2 + q)/2 *)
Definition growth_rate_approx (p b f : Q) : Q :=
  let q := 1 - p in
  f * (p * b - q) - f * f * (p * b * b + q) / 2.

(* ================================================================ *)
(* Concrete Kelly computations                                      *)
(* ================================================================ *)

(* p=55%, b=1 (even money): kelly = (0.55*1 - 0.45)/1 = 0.10 = 1/10 *)
Lemma kelly_55 : kelly (55#100) 1 == 1#10.
Proof. unfold kelly. vm_compute. reflexivity. Qed.

(* Half-Kelly: 1/20 *)
Lemma half_kelly_55 : half_kelly (55#100) 1 == 1#20.
Proof. unfold half_kelly, kelly. vm_compute. reflexivity. Qed.

(* Crypto bet: p=60%, b=2 → kelly = (0.6*2 - 0.4)/2 = 0.8/2 = 0.4 = 2/5 *)
Lemma kelly_crypto : kelly (60#100) 2 == 2#5.
Proof. unfold kelly. vm_compute. reflexivity. Qed.

(* Negative edge: p=40%, b=1 → kelly = (0.4 - 0.6)/1 = -0.2 = -1/5 *)
Lemma kelly_negative : kelly (40#100) 1 == -(1#5).
Proof. unfold kelly. vm_compute. reflexivity. Qed.

(* Fair coin, even money: p=1/2, b=1 → kelly = 0 *)
Lemma kelly_even : kelly (1#2) 1 == 0.
Proof. unfold kelly. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Growth rate properties                                           *)
(* ================================================================ *)

(* Growth rate at kelly fraction for p=55%, b=1 is positive *)
Lemma growth_positive_at_kelly_55 :
  growth_rate_approx (55#100) 1 (1#10) > 0.
Proof. unfold growth_rate_approx. unfold Qgt, Qlt. vm_compute. reflexivity. Qed.

(* Overbetting: growth at f=1/5 < growth at f=1/10 for p=55%,b=1 *)
Lemma overbetting_hurts_55 :
  growth_rate_approx (55#100) 1 (1#5) < growth_rate_approx (55#100) 1 (1#10).
Proof. unfold growth_rate_approx, Qlt. vm_compute. reflexivity. Qed.

(* Zero edge: p*b = 1-p implies kelly = 0 *)
Lemma kelly_zero_edge : forall p b : Q,
  b > 0 ->
  p * b == 1 - p ->
  kelly p b == 0.
Proof.
  intros p b Hb Hedge.
  unfold kelly.
  assert (Hnum : p * b - (1 - p) == 0).
  { rewrite Hedge. ring. }
  rewrite Hnum. unfold Qdiv. ring.
Qed.

(* Half-kelly is always half of kelly *)
Lemma half_kelly_is_half : forall p b : Q,
  half_kelly p b == kelly p b / 2.
Proof.
  intros. unfold half_kelly. reflexivity.
Qed.

(* Growth at f=0 is 0 *)
Lemma growth_at_zero : forall p b : Q,
  growth_rate_approx p b 0 == 0.
Proof.
  intros p b. unfold growth_rate_approx, Qdiv.
  ring.
Qed.

(* ================================================================ *)
(* Large overbetting: full Kelly vs 3x Kelly                        *)
(* ================================================================ *)

(* Extreme overbetting: 3x Kelly (f=3/10) worse than Kelly (f=1/10) *)
Lemma extreme_overbetting_55 :
  growth_rate_approx (55#100) 1 (3#10) < growth_rate_approx (55#100) 1 (1#10).
Proof. unfold growth_rate_approx, Qlt. vm_compute. reflexivity. Qed.

(* Half-Kelly growth is positive but less than full Kelly *)
Lemma half_kelly_growth_positive_55 :
  growth_rate_approx (55#100) 1 (1#20) > 0.
Proof. unfold growth_rate_approx, Qgt, Qlt. vm_compute. reflexivity. Qed.

Lemma half_kelly_less_than_full_55 :
  growth_rate_approx (55#100) 1 (1#20) < growth_rate_approx (55#100) 1 (1#10).
Proof. unfold growth_rate_approx, Qlt. vm_compute. reflexivity. Qed.

(* High odds: p=30%, b=5 → kelly = (1.5 - 0.7)/5 = 0.8/5 = 4/25 *)
Lemma kelly_high_odds : kelly (30#100) 5 == 4#25.
Proof. unfold kelly. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition kelly_synthesis : Prop :=
  kelly (55#100) 1 == 1#10 /\
  half_kelly (55#100) 1 == 1#20 /\
  growth_rate_approx (55#100) 1 (1#10) > 0 /\
  kelly (1#2) 1 == 0.

Lemma kelly_synthesis_holds : kelly_synthesis.
Proof.
  split. exact kelly_55.
  split. exact half_kelly_55.
  split. exact growth_positive_at_kelly_55.
  exact kelly_even.
Qed.
