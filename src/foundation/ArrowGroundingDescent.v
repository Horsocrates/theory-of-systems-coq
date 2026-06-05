(** * ArrowGroundingDescent.v — the DESCENT INTO Part G's arrow (not a snapshot): does the P4 generative
      arrow GROUND the thermodynamic arrow, or does the low-entropy past stay a boundary posit?

    The Part-G snapshot (ThermoArrowAudit.v) classified: "generative arrow = derived, low-entropy past =
    posited" -- but did not descend into WHY they fail to connect.  This file runs that descent, rung by
    rung, to the honest floor.  Result: the wall does NOT collapse and does NOT stay one block -- it SPLITS.

    -- Rung 1: P4 gives a DIRECTION.  gen_count (the count of actualized distinctions) strictly increases:
       succession LS is irreversible (gen_arrow_monotone).  If time IS succession (ToS identification), P4
       grounds the direction of time -- more than time-symmetric microphysics offers.  But direction
       (before < after) is not entropy-increase along it.

    -- Rung 2: P4 does NOT give the SIGN.  The tempting move "count grows (P4), entropy = count, so entropy
       grows" fails because these are TWO DIFFERENT counts: gen_count (actualized steps, always up) vs W
       (the multiplicity of the current macrostate, = entropy, can go either way).  They DECOUPLE: a concrete
       trajectory has gen_count up (0 < 1) yet W down (6 -> 4).  Monotone generative arrow =/=> monotone
       entropy.  "count grows" is true but it is the WRONG count (direction_not_sign, gen_up_but_entropy_down).

    -- Rung 3: the sign rides on a LOW-ENTROPY START.  Entropy can only rise if the start is BELOW the peak
       (room toward equilibrium); a start AT the peak gives no arrow (peak_start_no_increase).  And P4's
       "minimal actualization at the origin" does NOT disambiguate low- vs high-entropy: few distinctions =
       few constraints = MANY consistent micro-states = HIGH entropy (typical reading) OR a special simple
       origin = LOW entropy (the reading we need).  The identification "minimal actualization = low entropy"
       IS the past hypothesis; P4 does not entail it.

    -- Floor / verdict: the wall SPLITS.
         Direction -> DerivedFromP4   (FRONTIER crossed to Element: P4 grounds the direction).
         Sign      -> PositedBoundary (the low-entropy past = the past hypothesis; P4 buys the direction,
                                       NOT the sign).  The named gap: "minimal actualization =/= low entropy".
       The descent RELOCATES the wall precisely; it does not collapse it.

    -- Honesty about the seam itself: Sign = posited RELATIVE TO P4, NOT a proven necessity.  The low-entropy
       past may be a DEEPER FRONTIER (cosmology: inflation, the Weyl-curvature hypothesis) -- a separate,
       open descent.  Not claimed here as a necessary seam; tagged as "floor relative to current principles".

    Elements: gen_count t = t; W_traj 6,4,6; peak = 6; ArrowAspect (Direction/Sign) / Grounding
    Roles:    gen_count = actualized-step count (P4 direction); W = macrostate multiplicity (entropy sign)
    Rules:    P4 grounds the direction (strict before<after); the sign rides on the low-entropy-start posit

    ============ E/R/R разбор ============
      Rules (L5): P4 даёт НАПРАВЛЕНИЕ (gen_count строго растёт, преемство необратимо); ЗНАК (dS/dt>0)
                  не следует -- держится на низкоэнтроп. старте (гипотеза прошлого).
      Roles (L4): gen_count = счёт актуализированных шагов (направление P4) vs W = кратность макросостояния
                  (знак энтропии) -- ДВА РАЗНЫХ счёта, расцепляются (gen_count вверх, W вниз).
      Elements  : gen_count t=t; W_traj=6,4,6; peak=6; ArrowAspect Direction/Sign -> Grounding.
    ДИАГНОСТИКА (P4): стена РАСЩЕПЛЯЕТСЯ. Direction = DerivedFromP4 (фронтир -> Element, P4 даёт направление,
    больше микрофизики). Sign = PositedBoundary (низкоэнтроп. старт = гипотеза прошлого; P4 не влечёт; «мин.
    актуализация != низкая энтропия»). Спуск не обрушил стену -- ТОЧНО ПЕРЕМЕСТИЛ: P4 покупает направление,
    не знак. ЧЕСТНО: Sign -- посит ОТНОСИТЕЛЬНО P4, не доказанная необходимость; возможно более глубокий
    фронтир (космология) -- отдельный незакрытый спуск.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* ===================================================================== *)
(*  Rung 1 — P4 gives a DIRECTION: the actualized-step count strictly grows *)
(* ===================================================================== *)

(** The P4 generative arrow: the count of actualized distinctions. *)
Definition gen_count (t : nat) : nat := t.

(** ★ Strict direction: before < after, always.  Succession LS is irreversible. *)
Lemma gen_arrow_monotone : forall t, gen_count t < gen_count (S t).
Proof. intro t. unfold gen_count. lia. Qed.

(* ===================================================================== *)
(*  Rung 2 — P4 does NOT give the SIGN: the two counts decouple             *)
(* ===================================================================== *)

(** A thermodynamic trajectory: the multiplicity W of the macrostate at generative time t.
    W goes 6, 4, 6 (down then up) while generative time goes 0, 1, 2 (strictly up). *)
Definition W_traj (t : nat) : nat :=
  match t with O => 6 | S O => 4 | _ => 6 end.

(** ★ DECOUPLING: generative time strictly increases (0 < 1) yet entropy DECREASES (W: 6 -> 4).
    A monotone generative arrow does NOT entail monotone entropy: DIRECTION =/= SIGN. *)
Lemma direction_not_sign :
  gen_count 0 < gen_count 1 /\ W_traj 1 < W_traj 0.
Proof. vm_compute. lia. Qed.

(** The reason: gen_count (actualized steps) and W (macrostate multiplicity) are DIFFERENT counts.
    "count grows" is true of gen_count but false of W -- it is the wrong count for entropy. *)
Lemma gen_up_but_entropy_down :
  gen_count 0 < gen_count 1 /\ ~ (W_traj 0 <= W_traj 1).
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  Rung 3 — the sign rides on a LOW-ENTROPY START (the past hypothesis)    *)
(* ===================================================================== *)

(** Equilibrium multiplicity of the 4-bit system (the peak, from ThermoArrowAudit.v). *)
Definition peak : nat := 6.

(** ★ From a LOW-entropy start (below the peak) there is room to rise toward equilibrium.
    The entropy increase EXISTS only given the low start. *)
Lemma low_start_has_room : forall W0, W0 < peak -> exists W1, W0 < W1 <= peak.
Proof. intros W0 H. exists peak. unfold peak in *. lia. Qed.

(** ★ But nothing forces the start to be low: a start AT the peak has no increase -- no arrow.
    So the sign rides on the low start being ASSUMED (the past hypothesis), not on P4. *)
Lemma peak_start_no_increase : ~ exists W1, peak < W1 <= peak.
Proof. intro H. destruct H as [W1 [H1 H2]]. unfold peak in *. lia. Qed.

(* ===================================================================== *)
(*  Floor — the verdict: the wall SPLITS                                   *)
(* ===================================================================== *)

Inductive ArrowAspect := Direction | Sign.
Inductive Grounding := DerivedFromP4 | PositedBoundary.

Definition aspect_grounding (a : ArrowAspect) : Grounding :=
  match a with
  | Direction => DerivedFromP4    (* P4 succession gives strict before < after (Element) *)
  | Sign      => PositedBoundary  (* entropy LOW-at-origin = the past hypothesis; P4 does not entail it *)
  end.

(** ★ The split: Direction is grounded by P4 (a frontier crossed to Element); Sign remains a posited
    boundary (the low-entropy past).  P4 buys the direction, not the sign. *)
Lemma the_split :
  aspect_grounding Direction = DerivedFromP4
  /\ aspect_grounding Sign = PositedBoundary.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the arrow-grounding descent                                  *)
(* ===================================================================== *)

(** Descent INTO the arrow (Part G), seam-vs-frontier:
      (direction)  the generative arrow IS grounded by P4 -- gen_count strictly increases (FRONTIER crossed
                   to Element; an asset time-symmetric microphysics lacks);
      (decoupling) but a monotone generative arrow does NOT entail monotone entropy -- a concrete trajectory
                   has gen_count up (0<1) yet W down (6>4): DIRECTION =/= SIGN, the two counts differ;
      (lever)      the entropy increase rides on a LOW-entropy start (room toward the peak) = the past
                   hypothesis -- a peak start gives no arrow; P4 does not entail the low start;
      (verdict)    the wall SPLITS: Direction = DerivedFromP4, Sign = PositedBoundary.
    The descent does NOT collapse the wall -- it RELOCATES it precisely: P4 buys the direction, not the
    sign.  "Minimal actualization at the origin" =/= "low entropy" -- that identification is the posit. *)
Theorem arrow_grounding_descent :
  (forall t, gen_count t < gen_count (S t))
  /\ (gen_count 0 < gen_count 1 /\ W_traj 1 < W_traj 0)
  /\ (forall W0, W0 < peak -> exists W1, W0 < W1 <= peak)
  /\ aspect_grounding Direction = DerivedFromP4
  /\ aspect_grounding Sign = PositedBoundary.
Proof.
  split; [ exact gen_arrow_monotone | ].
  split; [ exact direction_not_sign | ].
  split; [ exact low_start_has_room | ].
  split; reflexivity.
Qed.
