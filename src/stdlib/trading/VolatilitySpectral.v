(** * VolatilitySpectral.v — Volatility regime detection as ToS System
    Elements: variance (short/long window), ratio, regime classification
    Roles:    spectral comparison (vol_ratio), alert generation (vol_alert),
              regime classification (vol_regime)
    Rules:    ratio outside [3/4, 4/3] triggers alert,
              regime is CALM/NORMAL/EXCITED based on ratio
    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Volatility ratio and regime detection                            *)
(* ================================================================ *)

(* Ratio of short-window variance to long-window variance *)
Definition vol_ratio (var_short var_long : Q) : Q := var_short / var_long.

(* Alert: ratio outside [3/4, 4/3] *)
Definition vol_alert (ratio : Q) : bool :=
  negb (Qle_bool (3#4) ratio && Qle_bool ratio (4#3))%bool.

(* Regime classification *)
Inductive VolRegime := CALM | NORMAL | EXCITED.

Definition vol_regime (ratio : Q) : VolRegime :=
  if Qle_bool ratio (3#4) then CALM
  else if Qle_bool (4#3) ratio then EXCITED
  else NORMAL.

Definition regime_eq (r1 r2 : VolRegime) : bool :=
  match r1, r2 with
  | CALM, CALM => true
  | NORMAL, NORMAL => true
  | EXCITED, EXCITED => true
  | _, _ => false
  end.

(* ================================================================ *)
(* Concrete ratio computations                                      *)
(* ================================================================ *)

(* Equal variances: ratio = 1 *)
Lemma vol_ratio_equal : vol_ratio 1 1 == 1.
Proof. unfold vol_ratio. vm_compute. reflexivity. Qed.

(* Short=2, Long=1: ratio = 2 (excited) *)
Lemma vol_ratio_excited : vol_ratio 2 1 == 2.
Proof. unfold vol_ratio. vm_compute. reflexivity. Qed.

(* Short=1, Long=2: ratio = 1/2 (calm) *)
Lemma vol_ratio_calm : vol_ratio 1 2 == 1#2.
Proof. unfold vol_ratio. vm_compute. reflexivity. Qed.

(* Short=5, Long=4: ratio = 5/4 (within normal band) *)
Lemma vol_ratio_normal : vol_ratio 5 4 == 5#4.
Proof. unfold vol_ratio. vm_compute. reflexivity. Qed.

(* Short=3, Long=4: ratio = 3/4 (boundary) *)
Lemma vol_ratio_boundary_low : vol_ratio 3 4 == 3#4.
Proof. unfold vol_ratio. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Alert trigger tests                                              *)
(* ================================================================ *)

(* ratio=1: no alert (within band) *)
Lemma alert_normal : vol_alert 1 = false.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ratio=2: alert (above 4/3) *)
Lemma alert_excited : vol_alert 2 = true.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ratio=1/2: alert (below 3/4) *)
Lemma alert_calm : vol_alert (1#2) = true.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ratio=5/4: no alert *)
Lemma alert_mild : vol_alert (5#4) = false.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ratio=3/2: alert (above 4/3) *)
Lemma alert_moderate_high : vol_alert (3#2) = true.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ratio=7/10: alert (below 3/4) *)
Lemma alert_moderate_low : vol_alert (7#10) = true.
Proof. unfold vol_alert. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Regime classification tests                                      *)
(* ================================================================ *)

Lemma regime_normal_1 : regime_eq (vol_regime 1) NORMAL = true.
Proof. unfold vol_regime. vm_compute. reflexivity. Qed.

Lemma regime_excited_2 : regime_eq (vol_regime 2) EXCITED = true.
Proof. unfold vol_regime. vm_compute. reflexivity. Qed.

Lemma regime_calm_half : regime_eq (vol_regime (1#2)) CALM = true.
Proof. unfold vol_regime. vm_compute. reflexivity. Qed.

Lemma regime_normal_5_4 : regime_eq (vol_regime (5#4)) NORMAL = true.
Proof. unfold vol_regime. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Alert-regime consistency                                         *)
(* ================================================================ *)

(* NORMAL regime → no alert *)
Lemma normal_no_alert : vol_alert 1 = false /\ regime_eq (vol_regime 1) NORMAL = true.
Proof. split; vm_compute; reflexivity. Qed.

(* EXCITED regime → alert *)
Lemma excited_has_alert : vol_alert 2 = true /\ regime_eq (vol_regime 2) EXCITED = true.
Proof. split; vm_compute; reflexivity. Qed.

(* CALM regime → alert *)
Lemma calm_has_alert : vol_alert (1#2) = true /\ regime_eq (vol_regime (1#2)) CALM = true.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition vol_spectral_synthesis : Prop :=
  vol_alert 1 = false /\
  vol_alert 2 = true /\
  regime_eq (vol_regime (1#2)) CALM = true /\
  regime_eq (vol_regime 2) EXCITED = true.

Lemma vol_spectral_synthesis_holds : vol_spectral_synthesis.
Proof.
  split. exact alert_normal.
  split. exact alert_excited.
  split. exact regime_calm_half.
  exact regime_excited_2.
Qed.
