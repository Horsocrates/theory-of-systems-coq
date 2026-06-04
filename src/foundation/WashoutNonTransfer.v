(** * WashoutNonTransfer.v — Baryogenesis Phase 4 (core): the SM washout argument does NOT transfer to
      ToS, because its PREMISE (thermal equilibrium) is structurally FALSE in ToS (P4 / the arrow).  So
      ToS does NOT inherit the SM ~10⁹ baryogenesis failure: η does NOT wash out (η ≠ 0).  HONEST: the
      arrow grounds only fwd ≠ bwd (direction / nonzero departure), NOT the sign or the magnitude — the
      number stays an open box.  The result DIFFERS from the SM (η ≠ 0 vs η = 0), because the INPUT
      differs (irreversibility vs equilibrium), but it is not a derived value.

    This answers the question "do we get a different result if our inputs differ from the SM?".  The SM
    electroweak-baryogenesis FAILURE (the ~10⁹ shortfall) is, at its core, a WASHOUT: sphalerons in
    thermal EQUILIBRIUM (a crossover, for m_H = 125 GeV) transition both ways at equal rates (detailed
    balance), so any asymmetry is erased.  The washout is a LOGICAL IMPLICATION:

        equilibrium  →  detailed balance (fwd = bwd)  →  net departure = 0  →  η = 0.

    The conclusion (η = 0) FOLLOWS FROM the premise (equilibrium).  ToS's process is NEVER static — it is
    intrinsically irreversible (ThermodynamicArrow: decoherence monotone, ℕ-indexed, never at a fixed
    point), so fwd ≠ bwd.  Therefore the washout's PREMISE is false in ToS, and its conclusion does NOT
    transfer: η is NOT forced to 0.

    ── The dichotomy (machine-checked) ──
      SM input  (equilibrium, fwd = bwd):   η = 0           — the washout failure;
      ToS input (arrow, fwd ≠ bwd):         η ≠ 0           — no washout (the asymmetry survives);
      the two inputs are MUTUALLY EXCLUSIVE (a positive net departure precludes equilibrium).

    ── HONEST (both directions) ──
      • PRO different result: the SM washout (the mechanism of its failure) rests on equilibrium, which
        ToS does NOT assume; ToS's arrow gives fwd ≠ bwd ⟹ the departure (the L5 face) is nonzero ⟹ the
        triad does not collapse ⟹ η ≠ 0.  We are NOT entitled to inherit the SM value or its gap.
      • AGAINST overclaim: the arrow grounds the DIRECTION (fwd ≠ bwd), NOT the SIGN or the MAGNITUDE of
        (fwd − bwd).  So this gives η ≠ 0 (no washout), NOT a specific η_B.  The magnitude is the open box
        (would need the actual finite-lattice rates — beyond what is derived).  ToS does NOT "solve"
        baryogenesis; it shows the SM failure is not inherited and the number is genuinely open.

    Elements: the rates fwd, bwd; the departure fwd − bwd (the L5 face); η = eta_triad cp b (fwd − bwd)
    Roles:    equilibrium (SM) ⟹ departure 0 ⟹ η = 0; irreversibility (ToS) ⟹ departure ≠ 0 ⟹ η ≠ 0
    Rules:    the washout is "equilibrium ⟹ η = 0"; its premise is false in ToS ⟹ it does not transfer

    ============ E/R/R разбор ============
      Rules (L5): вымывание = импликация «равновесие ⟹ η=0»; посылка (равновесие) у ToS ложна (стрела)
                  ⟹ не переносится; ToS-вход (fwd≠bwd) ⟹ η≠0 (нет вымывания).
      Roles (L4): грань L5 = departure=fwd−bwd; равновесие⟹0⟹η=0; необратимость⟹≠0⟹η≠0; входы исключают друг друга.
      Elements  : скорости fwd,bwd; departure; η = eta_triad cp b (fwd−bwd).
    ДИАГНОСТИКА (P4): SM-провал (вымывание) НЕ переносится — его посылка (равновесие) ложна в ToS (P4/стрела).
    ToS-результат η≠0 (genuinely иной, чем SM-η=0), потому что ВВОДНЫЕ отличаются. Но стрела даёт лишь
    направление (≠0), не знак/магнитуду — число = открытый ящик. Не «SM-разрыв», а «иной результат + открыто».

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.
From ToS Require Import foundation.SakharovERR.            (* eta_triad, eta_pos_if_all *)
From ToS Require Import foundation.BaryogenesisTransport.   (* cp_factor, bviol_factor, cp_factor_pos, bviol_factor_pos *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  A positive quantity is nonzero (helper)                                *)
(* ===================================================================== *)

Lemma Qpos_nonzero : forall x : Q, 0 < x -> ~ x == 0.
Proof. intros x Hx Heq. lra. Qed.

(* ===================================================================== *)
(*  The washout: equilibrium (fwd = bwd) ⟹ η = 0 (the SM failure)          *)
(* ===================================================================== *)

(** ★ The WASHOUT: if the sphaleron rates are in detailed balance (fwd = bwd) — thermal equilibrium —
    the L5 (out-of-equilibrium) face is 0 and η washes out to 0.  This is the core of the SM failure. *)
Lemma washout :
  forall cp b fwd bwd, fwd == bwd -> eta_triad cp b (fwd - bwd) == 0.
Proof.
  intros cp b fwd bwd H. unfold eta_triad.
  assert (Hd : fwd - bwd == 0) by (rewrite H; ring).
  rewrite Hd. ring.
Qed.

(** ★ A positive net departure (non-equilibrium) ⟹ η > 0 — the asymmetry is generated, not erased. *)
Lemma non_equilibrium_admits_pos :
  forall cp b fwd bwd, 0 < cp -> 0 < b -> 0 < fwd - bwd -> 0 < eta_triad cp b (fwd - bwd).
Proof. intros cp b fwd bwd Hcp Hb Hd. apply eta_pos_if_all; assumption. Qed.

(* ===================================================================== *)
(*  The arrow blocks the washout: fwd ≠ bwd ⟹ η ≠ 0 (no washout)           *)
(* ===================================================================== *)

(** ★ ToS's irreversibility (fwd ≠ bwd, from the arrow) ⟹ η ≠ 0: the asymmetry does NOT wash out.
    (The CP and B-violation faces are nonzero; the departure is nonzero; the triad does not collapse.)
    HONEST: this gives η ≠ 0, NOT its sign or magnitude — fwd ≠ bwd is the direction, not the size. *)
Lemma arrow_no_washout :
  forall cp b fwd bwd, ~ cp == 0 -> ~ b == 0 -> ~ fwd == bwd ->
  ~ eta_triad cp b (fwd - bwd) == 0.
Proof.
  intros cp b fwd bwd Hcp Hb Hfb Hc.
  unfold eta_triad in Hc.
  apply Qmult_integral in Hc. destruct Hc as [Hcb | Hd].
  - apply Qmult_integral in Hcb. destruct Hcb as [H | H].
    + apply Hcp. exact H.
    + apply Hb. exact H.
  - apply Hfb. lra.
Qed.

(** ★ The two inputs are MUTUALLY EXCLUSIVE: a positive net departure (ToS) precludes equilibrium (SM).
    The result differs BECAUSE the input differs. *)
Lemma premises_exclusive :
  forall fwd bwd, 0 < fwd - bwd -> ~ fwd == bwd.
Proof. intros fwd bwd Hd Heq. lra. Qed.

(* ===================================================================== *)
(*  Concrete: with the real CP and B-violation factors                     *)
(* ===================================================================== *)

(** η with the derived CP and B-violation faces, and the out-of-equilibrium face = the net departure. *)
Definition eta_washout (K : nat) (fwd bwd : Q) : Q :=
  eta_triad (cp_factor K) (bviol_factor K) (fwd - bwd).

(** ★ SM branch (equilibrium): η washes out to 0. *)
Lemma eta_washout_equilibrium :
  forall K fwd bwd, fwd == bwd -> eta_washout K fwd bwd == 0.
Proof. intros K fwd bwd H. unfold eta_washout. apply washout. exact H. Qed.

(** ★ ToS branch (arrow / irreversibility): η ≠ 0 — no washout.  (Magnitude open.) *)
Lemma eta_washout_arrow :
  forall K fwd bwd, ~ fwd == bwd -> ~ eta_washout K fwd bwd == 0.
Proof.
  intros K fwd bwd H. unfold eta_washout. apply arrow_no_washout.
  - apply Qpos_nonzero. apply cp_factor_pos.
  - apply Qpos_nonzero. apply bviol_factor_pos.
  - exact H.
Qed.

(* ===================================================================== *)
(*  Capstone: the SM washout does not transfer to ToS                      *)
(* ===================================================================== *)

(** The washout-non-transfer dichotomy:
      (SM)        equilibrium (fwd = bwd) ⟹ η = 0 — the washout, the core of the SM failure;
      (positive)  a positive net departure ⟹ η > 0 — the asymmetry is generated;
      (exclusive) a positive departure precludes equilibrium — the two inputs are mutually exclusive;
      (SM concr.) with the real faces, equilibrium ⟹ η = 0;
      (ToS concr.) with the real faces, the arrow (fwd ≠ bwd) ⟹ η ≠ 0 — NO washout.
    The SM failure rests on equilibrium, which ToS does not assume (P4 / the arrow); so ToS does not
    inherit it — η ≠ 0.  HONEST: this is "no washout", NOT a derived η_B; the magnitude is the open box. *)
Theorem washout_does_not_transfer :
  (forall cp b fwd bwd, fwd == bwd -> eta_triad cp b (fwd - bwd) == 0)
  /\ (forall cp b fwd bwd, 0 < cp -> 0 < b -> 0 < fwd - bwd -> 0 < eta_triad cp b (fwd - bwd))
  /\ (forall fwd bwd, 0 < fwd - bwd -> ~ fwd == bwd)
  /\ (forall K fwd bwd, fwd == bwd -> eta_washout K fwd bwd == 0)
  /\ (forall K fwd bwd, ~ fwd == bwd -> ~ eta_washout K fwd bwd == 0).
Proof.
  split; [ exact washout | ].
  split; [ exact non_equilibrium_admits_pos | ].
  split; [ exact premises_exclusive | ].
  split; [ exact eta_washout_equilibrium | ].
  exact eta_washout_arrow.
Qed.
