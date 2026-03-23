(** SpectralFlowMarket.v — Spectral flow and regime classification.
    E/R/R: Elements = regimes, spectral convergence values;
           Roles = regime classification, transition detection;
           Rules = stress/convergence thresholds, regime change logic.
    STATUS: 25 Qed, 0 Admitted, 0 axioms *)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List Bool.
From ToS Require Import stdlib.trading.CorrMatrix.
From ToS Require Import stdlib.trading.EigenvalueProcess.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Market regime classification                                     *)
(* ================================================================ *)

Inductive MarketRegime : Set :=
  | Trending
  | Volatile
  | MeanReverting
  | Transitioning.

Definition regime_eq_dec (r1 r2 : MarketRegime) : {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

Definition regime_eqb (r1 r2 : MarketRegime) : bool :=
  if regime_eq_dec r1 r2 then true else false.

Definition regime_changed (r1 r2 : MarketRegime) : bool :=
  negb (regime_eqb r1 r2).

(* classify_regime: stress < 1/5 and convergence < 1/2 => Trending
                    stress >= 7/10 => Volatile
                    convergence < 1/10 => MeanReverting
                    otherwise => Transitioning *)
Definition classify_regime (stress convergence : Q) : MarketRegime :=
  if Qlt_le_dec stress (1#5) then
    if Qlt_le_dec convergence (1#2) then Trending
    else Transitioning
  else if Qlt_le_dec (7#10) stress then Volatile
  else if Qlt_le_dec convergence (1#10) then MeanReverting
  else Transitioning.

(* Spectral convergence: |s1 - s2| *)
Definition spectral_convergence (s1 s2 : Q) : Q :=
  Qabs (s1 - s2).

(* Regime signal strength *)
Definition signal_strength (stress convergence : Q) : Q :=
  stress + convergence.

(* ================================================================ *)
(* Regime classification lemmas                                     *)
(* ================================================================ *)

Lemma classify_trending : classify_regime (1#10) (1#4) = Trending.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#10) (1#5)) as [H1|H1].
  - destruct (Qlt_le_dec (1#4) (1#2)) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
  - exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

Lemma classify_volatile : classify_regime (4#5) (1#2) = Volatile.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (4#5) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (7#10) (4#5)) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
Qed.

Lemma classify_mean_reverting : classify_regime (1#2) (1#20) = MeanReverting.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#2) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (7#10) (1#2)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec (1#20) (1#10)) as [H3|H3]. reflexivity.
      exfalso. unfold Qle in H3. simpl in H3. lia.
Qed.

Lemma classify_transitioning : classify_regime (1#2) (1#2) = Transitioning.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#2) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (7#10) (1#2)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec (1#2) (1#10)) as [H3|H3].
      * exfalso. unfold Qlt in H3. simpl in H3. lia.
      * reflexivity.
Qed.

Lemma classify_low_stress_high_conv : classify_regime (1#10) (3#4) = Transitioning.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#10) (1#5)) as [H1|H1].
  - destruct (Qlt_le_dec (3#4) (1#2)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + reflexivity.
  - exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

(* ================================================================ *)
(* Regime change detection                                          *)
(* ================================================================ *)

Lemma regime_changed_diff : regime_changed Trending Volatile = true.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_same : regime_changed Trending Trending = false.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_mr_vol : regime_changed MeanReverting Volatile = true.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_trans : regime_changed Transitioning Trending = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Spectral convergence                                             *)
(* ================================================================ *)

Lemma spectral_conv_same : spectral_convergence 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma spectral_conv_sym :
  spectral_convergence (3#2) 1 == spectral_convergence 1 (3#2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Integration with CorrMatrix and EigenvalueProcess                *)
(* ================================================================ *)

Lemma stress_regime :
  classify_regime (stress_index 5 3) (rayleigh O) = Transitioning.
Proof.
  unfold stress_index, rayleigh, ex_tr.
  unfold classify_regime.
  destruct (Qlt_le_dec (5#9) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (7#10) (5#9)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec 1 (1#10)) as [H3|H3].
      * exfalso. unfold Qlt in H3. simpl in H3. lia.
      * reflexivity.
Qed.

Lemma signal_strength_example : signal_strength (1#4) (1#3) == 7#12.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Decidability                                                     *)
(* ================================================================ *)

Lemma regime_eq_refl : forall r, regime_eqb r r = true.
Proof. destruct r; vm_compute; reflexivity. Qed.

Lemma regime_neq_trending_volatile :
  regime_eqb Trending Volatile = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis: spectral flow detects regime transitions              *)
(* ================================================================ *)

Lemma regime_transition_detected :
  let r1 := classify_regime (1#10) (1#4) in
  let r2 := classify_regime (4#5) (1#2) in
  regime_changed r1 r2 = true.
Proof.
  simpl.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#10) (1#5)) as [H1|H1].
  - destruct (Qlt_le_dec (1#4) (1#2)) as [H2|H2].
    + destruct (Qlt_le_dec (4#5) (1#5)) as [H3|H3].
      * exfalso. unfold Qlt in H3. simpl in H3. lia.
      * destruct (Qlt_le_dec (7#10) (4#5)) as [H4|H4].
        -- vm_compute. reflexivity.
        -- exfalso. unfold Qle in H4. simpl in H4. lia.
    + exfalso. unfold Qle in H2. simpl in H2. lia.
  - exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

Lemma regime_stable_no_change :
  let r1 := classify_regime (1#10) (1#4) in
  let r2 := classify_regime (1#10) (1#3) in
  regime_changed r1 r2 = false.
Proof.
  simpl.
  unfold classify_regime.
  destruct (Qlt_le_dec (1#10) (1#5)) as [H1|H1].
  - destruct (Qlt_le_dec (1#4) (1#2)) as [H2|H2].
    + destruct (Qlt_le_dec (1#10) (1#5)) as [H3|H3].
      * destruct (Qlt_le_dec (1#3) (1#2)) as [H4|H4].
        -- vm_compute. reflexivity.
        -- exfalso. unfold Qle in H4. simpl in H4. lia.
      * exfalso. unfold Qle in H3. simpl in H3. lia.
    + exfalso. unfold Qle in H2. simpl in H2. lia.
  - exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

(* Additional regime classification *)
Lemma classify_edge_transitioning : classify_regime (7#10) (1#2) = Transitioning.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec (7#10) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (7#10) (7#10)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec (1#2) (1#10)) as [H3|H3].
      * exfalso. unfold Qlt in H3. simpl in H3. lia.
      * reflexivity.
Qed.

Lemma classify_edge_trending : classify_regime 0 0 = Trending.
Proof.
  unfold classify_regime.
  destruct (Qlt_le_dec 0 (1#5)) as [H1|H1].
  - destruct (Qlt_le_dec 0 (1#2)) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
  - exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

(* More regime_changed *)
Lemma regime_changed_vol_mr : regime_changed Volatile MeanReverting = true.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_mr_mr : regime_changed MeanReverting MeanReverting = false.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_vol_vol : regime_changed Volatile Volatile = false.
Proof. vm_compute. reflexivity. Qed.

Lemma regime_changed_trans_trans : regime_changed Transitioning Transitioning = false.
Proof. vm_compute. reflexivity. Qed.

(* Signal strength *)
Lemma signal_strength_zero : signal_strength 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma signal_strength_high : signal_strength (3#4) (3#4) == 3#2.
Proof. vm_compute. reflexivity. Qed.
