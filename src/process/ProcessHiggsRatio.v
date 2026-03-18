(* ProcessHiggsRatio.v — Higgs/W mass ratio analysis *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore. From ToS Require Import process.ProcessWeinbergAngle.
Open Scope Q_scope.
Definition mH_sq_over_mW_sq (lambda g_sq : Q) : Q := 8 * lambda / g_sq.
Lemma higgs_ratio_formula : forall l g, 0 < g -> mH_sq_over_mW_sq l g == 8 * l / g.
Proof. intros. unfold mH_sq_over_mW_sq. reflexivity. Qed.
Definition physical_higgs_ratio : Q := 15625 # 6459. (* (125.25/80.37)^2 ≈ 2.428 *)
Lemma physical_ratio_pos : 0 < physical_higgs_ratio.
Proof. unfold physical_higgs_ratio. lra. Qed.
(** HONEST: λ is FREE → m_H/m_W not predicted. E/R/R gives Higgs EXISTS, not mass. *)
Definition lambda_from_ratio (ratio g_sq : Q) : Q := ratio * g_sq / 8.
Lemma lambda_roundtrip : forall r g, 0 < g -> mH_sq_over_mW_sq (lambda_from_ratio r g) g == r.
Proof. intros. unfold mH_sq_over_mW_sq, lambda_from_ratio. field. lra. Qed.
Lemma ratio_at_lambda_half : mH_sq_over_mW_sq (1#2) 1 == 4.
Proof. unfold mH_sq_over_mW_sq. field. Qed.
Lemma ratio_at_lambda_quarter : mH_sq_over_mW_sq (1#4) 1 == 2.
Proof. unfold mH_sq_over_mW_sq. field. Qed.
Theorem higgs_analysis :
  mH_sq_over_mW_sq (1#2) 1 == 4 /\ mH_sq_over_mW_sq (1#4) 1 == 2 /\ 0 < physical_higgs_ratio.
Proof. split; [|split]; [exact ratio_at_lambda_half|exact ratio_at_lambda_quarter|exact physical_ratio_pos]. Qed.
Definition higgs_ratio_count := 7%nat.
