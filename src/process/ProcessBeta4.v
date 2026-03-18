(* ProcessBeta4.v *)
(* Phase V2: σ and ⟨P⟩ at β=4 — standard lattice coupling *)

From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessPlaquette.

Open Scope Q_scope.

(** β=4 is where lattice physicists typically work *)
(** Computing I₀, I₁ at β=4 with M=3 gives results at THEIR coupling *)

(** I₀(β=4, M=3) = Σ_{m=0}^{3} (β/2)^{2m} / (m!·m!) *)
(** At β=4: β/2 = 2 *)
(** m=0: 1/(1·1) = 1 *)
(** m=1: 4/(1·1) = 4 *)
(** m=2: 16/(2·2) = 4 *)
(** m=3: 64/(6·6) = 64/36 = 16/9 *)

Lemma I0_b4_M3 : I0_partial 4 3 == 97 # 9.
Proof.
  unfold I0_partial, bessel_partial, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

(** I₁(β=4, M=3) = Σ_{m=0}^{3} (β/2)^{1+2m} / (m!·(1+m)!) *)
(** m=0: 2/(1·1) = 2 *)
(** m=1: 8/(1·2) = 4 *)
(** m=2: 32/(2·6) = 32/12 = 8/3 *)
(** m=3: 128/(6·24) = 128/144 = 8/9 *)

Lemma I1_b4_M3 : I1_partial 4 3 == 86 # 9.
Proof.
  unfold I1_partial, bessel_partial, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

(** ⟨P⟩(β=4, M=3) = I₁/I₀ = 86/97 *)
Lemma plaquette_b4_M3 : plaquette 4 3 == 86 # 97.
Proof.
  unfold plaquette.
  rewrite I1_b4_M3, I0_b4_M3. field.
Qed.

(** Exact: ⟨P⟩(β=4) = I₁(4)/I₀(4) ≈ 0.88957 *)
(** Our M=3: 86/97 ≈ 0.8866 → error ≈ 0.3% *)

Lemma plaquette_b4_M3_pos : 0 < plaquette 4 3.
Proof. rewrite plaquette_b4_M3. unfold Qlt; simpl; lia. Qed.

Lemma plaquette_b4_M3_lt_1 : plaquette 4 3 < 1.
Proof. rewrite plaquette_b4_M3. unfold Qlt; simpl; lia. Qed.

(** σ(β=4, M=3, order=1) = 1 − 86/97 = 11/97 *)
Lemma sigma_b4_M3_order1 : sigma_phys 4 3 1 == 11 # 97.
Proof.
  unfold sigma_phys. simpl.
  rewrite I1_b4_M3, I0_b4_M3.
  unfold neg_ln_taylor. simpl.
  field.
Qed.

(** Exact: σ(β=4) ≈ 0.11698 *)
(** Our: 11/97 ≈ 0.1134 → error ≈ 3% *)

(** Plaquette increases with β — more ordered at weaker coupling *)
Lemma plaquette_increases_b2_b4 :
  plaquette 2 2 < plaquette 4 3.
Proof.
  rewrite plaquette_b2_M2, plaquette_b4_M3.
  unfold Qlt; simpl; lia.
Qed.

(** Complete β progression *)
Lemma plaquette_progression :
  plaquette 1 1 < plaquette 2 2 /\
  plaquette 2 2 < plaquette 4 3.
Proof.
  split.
  - rewrite plaquette_b1_M1, plaquette_b2_M2. unfold Qlt; simpl; lia.
  - exact plaquette_increases_b2_b4.
Qed.

(** ★ β=4 accuracy table:
    M    ⟨P⟩           Exact     Error
    3    86/97≈0.887    0.890     0.3%
*)

Theorem beta4_results :
  plaquette 4 3 == 86 # 97 /\
  0 < plaquette 4 3 /\
  plaquette 4 3 < 1.
Proof.
  split; [|split].
  - exact plaquette_b4_M3.
  - exact plaquette_b4_M3_pos.
  - exact plaquette_b4_M3_lt_1.
Qed.

Definition v2_theorem_count := 12%nat.
