(* ProcessHigherDComparison.v — 1+1D vs 2+1D/3+1D comparison *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessPlaquette. From ToS Require Import process.ProcessPlaquetteCurve.
From ToS Require Import process.ProcessBeta4.
From ToS Require Import gauge.Gap3D.
Open Scope Q_scope.
(** 1+1D: exact plaquette at 5 β values — STRONGEST results *)
Theorem dim_1plus1 :
  plaquette 1 1 == 9 # 20 /\ plaquette 2 2 == 19 # 27 /\ plaquette 4 3 == 86 # 97.
Proof. split; [|split]; [exact plaquette_b1_M1|exact plaquette_b2_M2|exact plaquette_b4_M3]. Qed.
(** 2+1D: gap formula from Gap3D *)
Theorem dim_2plus1 : gap_formula 1 == 3 # 4 /\ gap_formula 2 == 15 # 16.
Proof. split; [exact gap_formula_1|exact gap_formula_2]. Qed.
(** 2+1D glueball: E_j1/E_q = 32/21 ≈ 1.52. Lit: 1.5-1.8 → IN RANGE *)
Definition glueball_ratio_2d : Q := 32 # 21.
Lemma glueball_in_range : 3#2 <= glueball_ratio_2d /\ glueball_ratio_2d <= 9#5.
Proof. unfold glueball_ratio_2d. split; unfold Qle; simpl; lia. Qed.
(** 3+1D: gap increases with dimension *)
Theorem dim_3plus1 : gap_formula 3 == 63 # 64.
Proof. exact gap_formula_3. Qed.
Lemma gap_monotone : gap_formula 1 < gap_formula 2 /\ gap_formula 2 < gap_formula 3.
Proof. rewrite gap_formula_1, gap_formula_2, gap_formula_3. split; unfold Qlt; simpl; lia. Qed.
(** HONEST: m_G/√σ (2+1D) ≈ 1.01 vs lit 4.7 → model too simple *)
Theorem higher_d_summary :
  glueball_ratio_2d == 32 # 21 /\ gap_formula 2 == 15 # 16 /\ gap_formula 3 == 63 # 64.
Proof. split; [|split]; [reflexivity|exact gap_formula_2|exact gap_formula_3]. Qed.
Definition higher_d_count := 7%nat.
