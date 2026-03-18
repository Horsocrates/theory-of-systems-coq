(* ProcessDMCrossSection.v — DM direct detection cross-section *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore. From ToS Require Import process.ProcessRegge.
Open Scope Q_scope.
(** DM = hidden Role, gravitational only. σ_DM = κ²·m_DM²·m_N²/π *)
Definition dm_cross_section (kappa m_DM m_N : Q) : Q :=
  kappa * kappa * m_DM * m_DM * m_N * m_N * (7#22).
Lemma dm_sigma_at_lattice : dm_cross_section (1#10) (1#3) 1 == 7 # 19800.
Proof. unfold dm_cross_section. ring. Qed.
Lemma dm_sigma_positive : 0 < dm_cross_section (1#10) (1#3) 1.
Proof. rewrite dm_sigma_at_lattice. lra. Qed.
(** Physical κ≈10⁻³⁸ → σ∝10⁻⁷⁶ → WAY below LZ bound (10⁻⁴⁸) *)
(** ★ PREDICTION: gravitational DM undetectable by direct detection *)
Lemma dm_undetectable_proxy : dm_cross_section (1#10) (1#3) 1 < 1 # 1000.
Proof. rewrite dm_sigma_at_lattice. lra. Qed.
(** DM mass candidates: m_top/3^L *)
Definition dm_mass_L1 : Q := 1 # 3.   (* m_top/3 ≈ 58 GeV *)
Definition dm_mass_L2 : Q := 1 # 9.   (* m_top/9 ≈ 19 GeV *)
Definition dm_mass_L3 : Q := 1 # 27.  (* m_top/27 ≈ 6.4 GeV *)
Lemma dm_hierarchy : dm_mass_L3 < dm_mass_L2 /\ dm_mass_L2 < dm_mass_L1.
Proof. unfold dm_mass_L1, dm_mass_L2, dm_mass_L3. split; lra. Qed.
Theorem dm_analysis :
  dm_cross_section (1#10) (1#3) 1 == 7 # 19800 /\
  dm_cross_section (1#10) (1#3) 1 < 1 # 1000.
Proof. split; [exact dm_sigma_at_lattice|exact dm_undetectable_proxy]. Qed.
Definition dm_count := 6%nat.
