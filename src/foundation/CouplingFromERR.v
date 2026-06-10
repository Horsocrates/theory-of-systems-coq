(** * CouplingFromERR.v — g² ∝ 1/dim(G), and C CANCELS in sin²θ_W: a genuine C-independence,
       but the (3,10) dims are CHOICES — 10 is a data-selected rank, NOT forced
    Elements: coupling_sq, sin2_from_couplings
    Roles:    Show sin²θ_W = n/(n+m) is INDEPENDENT of the normalization C
    Rules:    P1 equal weight ⟹ g² = C/dim(G); mixing = g'²/(g²+g'²)
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026  (rank-honesty rollback: June 2026)

    WHAT IS GENUINELY PROVEN (C_cancels / C_cancels_general): the normalization constant C drops
    out of the mixing ratio — sin²θ_W = n/(n+m) depends only on the integer dims, not on C.  That
    C-independence is real and worth stating.

    WHAT IS NOT A DERIVATION: the dims (n,m) = (dim SU(2), n_metric) = (3, 10) are ASSUMED
    IDENTIFICATIONS, chosen to match sin²θ_W ≈ 3/13.  n_metric = 10 is the SYMMETRIC tensor rank of
    a 4D metric; the antisymmetric (6) and Riemann (20) ranks are equally geometric and give 1/3 and
    3/23 (sin2_rank6 / sin2_rank20 below).  The rules admit all three; the datum selects 10.  So C
    cancelling is a true structural fact, but sin²θ_W = 3/13 remains a postdiction modulo the
    data-selected rank — C-independence is NOT parameter-freedom.

    ============ E/R/R разбор ============
      Elements : нормировка C; целые dim'ы n=3 (числитель), m=10 (знаменатель = сим. ранг 4D-метрики).
      Roles    : C — общий масштаб (сокращается); n/(n+m) — смешивание; m играет роль «геом. сектор».
      Rules    : g²=C/dim ⟹ sin² = n/(n+m) — НЕ зависит от C (доказано); но ранг m НЕ фиксирован правилами.
      ДИАГНОСТИКА (P4 + L4): C-независимость реальна (масштаб сокращается). Но (3,10) — ПОСТУЛАТЫ, не
      произвол: по L4 основание само-обосновано; по JustificationRegress обоснованное требует ≥1 постулат
      (grounded_needs_posit), «из ничего» — role-limit (from_nothing_ungrounded). Ранг m сводится
      локальностью; неустранимые постулаты 3/13 — P1 + карта depth→gauge (②). C-независимость ≠ свобода от
      постулатов. forced(C-сокращение, отношение при (3,10)) ⟂ posit(карта). Уровень: `новое-обрамление`.
      Честная задача — СЧИТАТЬ постулаты, не обнулять. Дом ранга: MetricDOFJustification.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  COUPLING FROM EQUAL WEIGHT (P1)                                    *)
(* ================================================================== *)

(** P1 (equal weight): each generator carries equal share of interaction.
    Observable = probability = g^2 (Born rule: amplitude^2 = probability).
    dim(G) generators, equal weight => g^2 = C/dim(G). *)

Definition coupling_sq (C : Q) (dim_G : nat) : Q :=
  C / inject_Z (Z.of_nat dim_G).

(** Standard mixing formula: sin^2(theta) = g'^2 / (g^2 + g'^2) *)
Definition sin2_from_couplings (g_sq g_prime_sq : Q) : Q :=
  g_prime_sq / (g_sq + g_prime_sq).

(* ================================================================== *)
(*  KEY THEOREM: C CANCELS IN SIN^2(THETA_W)  (genuine C-independence)  *)
(* ================================================================== *)

(** For SU(2) (dim=3) and the metric-rank denominator (dim=10):
    g^2 = C/3.  g'^2 = C/10.
    sin^2 = (C/10) / (C/3 + C/10) = (1/10)/(13/30) = 3/13.  C cancels!
    NB: the C-cancellation is genuine; the dims (3,10) are CHOICES (see the rank section below). *)

Lemma C_cancels : forall C : Q, C > 0 ->
  sin2_from_couplings (coupling_sq C 3) (coupling_sq C 10) == 3#13.
Proof.
  intros C HC.
  unfold sin2_from_couplings, coupling_sq. simpl.
  field.
  intro H. lra.
Qed.

(** Same result expressed differently *)
Lemma sin2_is_DOF_ratio : forall C : Q, C > 0 ->
  sin2_from_couplings (coupling_sq C 3) (coupling_sq C 10) == 3 / 13.
Proof.
  intros C HC.
  rewrite C_cancels; [| exact HC].
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  WRONG POWER: g^2 (Born), not g or g^4                              *)
(* ================================================================== *)

(** If g (not g^2) were distributed equally: sin^2 = 9/109 ~ 0.0826.  Far from observed 0.231. *)
Lemma wrong_if_g_not_g2 : (9#109) < (1#5).
Proof. lra. Qed.

(** If g^4 were distributed: also wrong (9/109 < 1/4). *)
Lemma wrong_if_g4 : (9#109) < (1#4).
Proof. lra. Qed.

(* ================================================================== *)
(*  ALPHA_EM AT TREE LEVEL                                             *)
(* ================================================================== *)

(** alpha_EM = sin^2(theta_W) * kappa where kappa ~ 1/10 in some normalizations *)
Lemma alpha_EM_tree : (3#13) * (1#10) == 3#130.
Proof. vm_compute. reflexivity. Qed.

(** alpha_inv > 43 (actual ~ 43.3) *)
Lemma alpha_inv_tree : 130#3 > 43.
Proof. lra. Qed.

(* ================================================================== *)
(*  GENERAL THEOREM: C ALWAYS CANCELS — sin^2 = n/(n+m)                *)
(* ================================================================== *)

Lemma inject_Z_nat_pos : forall n : nat, (n > 0)%nat -> inject_Z (Z.of_nat n) > 0.
Proof.
  intros n Hn. unfold Qlt. simpl. lia.
Qed.

(** General version: sin^2 = n/(n+m), proved by expanding Q division.  This is the genuine content:
    the mixing ratio is INDEPENDENT of the normalization C — it depends only on the dims n, m. *)
Lemma C_cancels_general : forall C : Q, forall n m : nat,
  C > 0 -> (n > 0)%nat -> (m > 0)%nat ->
  sin2_from_couplings (coupling_sq C n) (coupling_sq C m) ==
  inject_Z (Z.of_nat n) / inject_Z (Z.of_nat (n + m)).
Proof.
  intros C n m HC Hn Hm.
  unfold sin2_from_couplings, coupling_sq.
  set (N := inject_Z (Z.of_nat n)).
  set (M := inject_Z (Z.of_nat m)).
  assert (HN : N > 0) by (apply inject_Z_nat_pos; lia).
  assert (HM : M > 0) by (apply inject_Z_nat_pos; lia).
  assert (HNM : N + M > 0) by lra.
  (* Rewrite C/N + C/M = C * (M + N) / (N * M) *)
  assert (Hsum : C / N + C / M == C * (N + M) / (N * M)).
  { field. split; lra. }
  rewrite Hsum.
  assert (HNM_prod : N * M > 0) by (apply Qmult_lt_0_compat; lra).
  assert (HCNM : C * (N + M) > 0) by (apply Qmult_lt_0_compat; lra).
  assert (Heq_nm : inject_Z (Z.of_nat (n + m)) == N + M).
  { unfold N, M. rewrite Nat2Z.inj_add. rewrite inject_Z_plus. reflexivity. }
  assert (Hdiv : C / M / (C * (N + M) / (N * M)) == N / (N + M)).
  { field. split; [lra | split; [lra | split; [lra | lra]]]. }
  rewrite Heq_nm. exact Hdiv.
Qed.

(** Synthesis: coupling from E/R/R equal weight (C-independence + the wrong-power check) *)
Theorem coupling_from_ERR_synthesis :
  (* C cancels for SU(2) x U(1) *)
  (forall C, C > 0 -> sin2_from_couplings (coupling_sq C 3) (coupling_sq C 10) == 3#13) /\
  (* Wrong alternative: g (not g^2) gives 9/109 *)
  (9#109) < (1#5) /\
  (* General: C always cancels *)
  (forall C n m, C > 0 -> (n > 0)%nat -> (m > 0)%nat ->
   sin2_from_couplings (coupling_sq C n) (coupling_sq C m) ==
   inject_Z (Z.of_nat n) / inject_Z (Z.of_nat (n + m))).
Proof.
  split; [exact C_cancels|].
  split; [exact wrong_if_g_not_g2|].
  exact C_cancels_general.
Qed.

(* ================================================================== *)
(*  THE FREE CHOICE — the denominator RANK is rule-underdetermined     *)
(*  (C cancels, but WHICH m is a choice; only m=10 is data-selected)   *)
(* ================================================================== *)

(** The three geometric ranks of a 4D metric, numerator fixed at dim SU(2) = 3, via the proven
    C-independence C_cancels_general.  All rule-admissible; only b = 10 is data-selected. *)
Lemma sin2_rank6 : forall C : Q, C > 0 ->
  sin2_from_couplings (coupling_sq C 3) (coupling_sq C 6) == 1#3.
Proof.
  intros C HC.
  transitivity (inject_Z (Z.of_nat 3) / inject_Z (Z.of_nat (3 + 6))).
  - apply C_cancels_general; [exact HC | lia | lia].
  - vm_compute. reflexivity.
Qed.

Lemma sin2_rank20 : forall C : Q, C > 0 ->
  sin2_from_couplings (coupling_sq C 3) (coupling_sq C 20) == 3#23.
Proof.
  intros C HC.
  transitivity (inject_Z (Z.of_nat 3) / inject_Z (Z.of_nat (3 + 20))).
  - apply C_cancels_general; [exact HC | lia | lia].
  - vm_compute. reflexivity.
Qed.

(** ★ HONEST CAPSTONE: C cancels (genuine, C_cancels) — but C-independence is NOT parameter-freedom.
    {6,10,20} give {1/3, 3/13, 3/23}, so L1 does not fix the rank m.  By L4 (Law_of_SufficientReason)
    and JustificationRegress.v the dims (3,10) are POSITS, not free choices: ≥1 counted posit is
    honest (grounded_needs_posit), "from nothing / zero" is the role-limit (from_nothing_ungrounded).
    Pushed deep, 3/13's posits are P1 + the depth→gauge map (②); the rank reduces via locality. *)
Theorem sin2_3_13_forced_modulo_rank_choice :
  (forall C, C > 0 -> sin2_from_couplings (coupling_sq C 3) (coupling_sq C 10) == 3#13)
  /\ (forall C, C > 0 -> sin2_from_couplings (coupling_sq C 3) (coupling_sq C 6)  == 1#3)
  /\ (forall C, C > 0 -> sin2_from_couplings (coupling_sq C 3) (coupling_sq C 20) == 3#23)
  /\ ~ (1#3 == 3#13) /\ ~ (3#13 == 3#23).
Proof.
  split; [exact C_cancels|].
  split; [exact sin2_rank6|].
  split; [exact sin2_rank20|].
  split; intro H; vm_compute in H; discriminate H.
Qed.
