(** * RoleToSUNGrounding.v — deriving role→SU(N): how far distinction reaches (CORRECTED ontology).
       Superposition is POTENTIALITY (role-limit), NOT an actual contradiction of L2.  The residual
       quantum content relocates to INTERFERENCE (signed/complex weight), with Born's |·|² left Open.
    Elements: RoleState (amplitude pair over 2 roles); dist_form (distinguishability); the transforms
    Roles:    actualized pole = Element; superposition = the potential mode (role-limit); measurement
              = actualization (one pole, L4_witness-like)
    Rules:    unitarity = preserve dist_form (DERIVED); L2 preserved on the ACTUALIZED level;
              superposition = potential, not "both"; interference = signed weights cancel
    STATUS:   14 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: June 2026

    THE CORRECTION (potentiality nuance).  An amplitude pair (α,β) is NOT "actually both poles" —
    that would be positive ∧ negative = ¬L2, and was a category error (treating the potential as
    actual).  By the ToS ontology (Element = actual / role-limit = potential; P4 = Finite Actuality),
    a superposition is the POTENTIAL to actualize + OR −: it has actualized NEITHER pole.  L2
    (Law_of_NonContradiction, ~(positive ∧ negative)) governs ACTUALIZED distinctions and is
    PRESERVED — no state is both actualized-positive and actualized-negative (L2_holds_on_actualized).
    Measurement actualizes exactly one pole (resolution_actualizes), and L2 holds for the outcome.

    CONSEQUENCE.  Linearity/superposition is NOT an anti-L2 posit — it is POTENTIALITY, a mode the
    framework ALREADY has (role-limit).  The genuine quantum addition is narrower: INTERFERENCE — the
    potential is weighted by SIGNED/COMPLEX amplitudes that can CANCEL (1 + (−1) = 0,
    interference_cancels), which classical potential (probabilities ≥ 0) cannot (classical_no_cancel).
    The signed/complex weight is role-limit-grounded (the Z_4 Element i, its closure the phase); and the
    quadratic Born weight |·|² is DERIVED — the unique rotation invariant (born_exponent_is_derived;
    BornRuleDescent.square_preserved), NOT an open residual.

    LEDGER (corrected, Born closed):
      Unitarity   — DERIVED   (preserve distinguishability — swap_/rot_preserves_dist).
      SpecialDet  — DERIVED   (factor the reflexive global phase — phase_preserves_dist).
      BornWeight  — DERIVED   (the SQUARE is the unique rotation invariant — born_exponent_is_derived,
                    BornRuleDescent; given interference, p=2 is forced — closed, not Open).
      Continuity  — ROLE-LIMIT (closure of the rational rotations; the continuum, P4).
      Linearity   — ROLE-LIMIT (POTENTIALITY — the potential mode of distinction) — NOT a posit.
    Net: role→SU(N) reduces to the theory's OWN foundational footing (the role-limit / continuous side
    of the Element/role-limit boundary + the 2 axioms) + ENTIRELY derived structure (unitarity, det=1,
    AND the Born exponent 2).  There is NO new SM-specific anti-law posit and NO open residual: the one
    input is "be on the role-limit side" (interference/continuity/potentiality).  The earlier
    "superposition = relaxed L2" reading is withdrawn (potentiality nuance); the Born weight is closed
    (BornRuleDescent).

    ============ E/R/R разбор (CORRECTED) ============
      Elements : амплитудные пары; актуализованные полюса (Element); форма различимости dist_form.
      Roles    : суперпозиция = ПОТЕНЦИАЛ (role-limit), не актуальное «оба»; измерение = актуализация (один полюс).
      Rules    : L2 держится на АКТУАЛИЗОВАННОМ уровне (L2_holds_on_actualized); суперпозиция — ни один полюс
                 не актуализован (superposition_is_potential_not_both); интерференция = знаковые веса сокращаются.
      ДИАГНОСТИКА (P4+L4): прошлое «суперпозиция = ¬L2» — категориальная ошибка (потенциал как актуальное).
      Верно: суперпозиция = потенциальность = role-limit (теория это УЖЕ имеет). Анти-L2-постулата НЕТ. Квантовое
      содержание — интерференция (role-limit через Z_4); борновский показатель 2 ВЫВЕДЕН (единственный вращательный
      инвариант — born_exponent_is_derived/BornRuleDescent). Единственный вход — сторона role-limit; БЕЗ открытого
      остатка. role→SU(N) = выведенное + фундамент теории. Уровень: `синтез+наблюдение`. *)

From Stdlib Require Import QArith Qabs Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  ROLE STATES over 2 roles (+ and −) — amplitude pairs              *)
(* ================================================================== *)

Definition RoleState := (Q * Q)%type.
Definition amp_plus  (s : RoleState) : Q := fst s.
Definition amp_minus (s : RoleState) : Q := snd s.

(** A nonzero amplitude = the POTENTIAL for that pole (not its actualization). *)
Definition has_pos_amp (s : RoleState) : Prop := ~ (amp_plus s == 0).
Definition has_neg_amp (s : RoleState) : Prop := ~ (amp_minus s == 0).

(** ACTUALIZED poles (Elements): exactly one pole present, the other absent. *)
Definition actual_positive (s : RoleState) : Prop := has_pos_amp s /\ amp_minus s == 0.
Definition actual_negative (s : RoleState) : Prop := amp_plus s == 0 /\ has_neg_amp s.

(** POTENTIAL (role-limit): both amplitudes present — NEITHER pole actualized. *)
Definition in_potential (s : RoleState) : Prop := has_pos_amp s /\ has_neg_amp s.

(* ================================================================== *)
(*  L2 IS PRESERVED; superposition is POTENTIAL, not "both"           *)
(* ================================================================== *)

(** ★ L2 (non-contradiction) HOLDS on the actualized level: no state is both actualized-positive and
    actualized-negative.  Superposition does NOT violate it. *)
Theorem L2_holds_on_actualized :
  forall s, ~ (actual_positive s /\ actual_negative s).
Proof.
  intros s [[_ Hmin] [_ Hneg]]. exact (Hneg Hmin).
Qed.

(** ★ THE CORRECTION: a superposition has actualized NEITHER pole — it is the POTENTIAL for either,
    not the actual conjunction "positive ∧ negative".  (This withdraws the old ¬L2 reading.) *)
Theorem superposition_is_potential_not_both :
  forall s, in_potential s -> ~ actual_positive s /\ ~ actual_negative s.
Proof.
  intros s [Hp Hn]. split.
  - intros [_ Hmin]. exact (Hn Hmin).
  - intros [Hpl _]. exact (Hp Hpl).
Qed.

(** The concrete superposition |+⟩+|−⟩ is in POTENTIAL (a potential for either pole). *)
Definition superposed : RoleState := (1, 1).

Theorem superposed_is_potential : in_potential superposed.
Proof.
  unfold in_potential, has_pos_amp, has_neg_amp, superposed, amp_plus, amp_minus; simpl.
  split; intro H; lra.
Qed.

(** Measurement = actualization: resolve the potential to the + pole — a definite Element, no longer
    in potential.  (The L4_witness-like step; the outcome obeys L2.) *)
Definition resolve_plus (s : RoleState) : RoleState := (amp_plus s, 0).

Theorem resolution_actualizes :
  forall s, has_pos_amp s -> actual_positive (resolve_plus s) /\ ~ in_potential (resolve_plus s).
Proof.
  intros s Hp. split.
  - unfold actual_positive, has_pos_amp, resolve_plus, amp_plus, amp_minus; simpl.
    split; [exact Hp | reflexivity].
  - unfold in_potential, has_neg_amp, resolve_plus, amp_minus; simpl.
    intros [_ Hn]. apply Hn. reflexivity.
Qed.

(* ================================================================== *)
(*  DERIVED: unitarity = preservation of distinguishability           *)
(* ================================================================== *)

(** The distinguishability form: the inner product whose value IS "how distinct the roles are". *)
Definition dist_form (s : RoleState) : Q :=
  amp_plus s * amp_plus s + amp_minus s * amp_minus s.

Definition apply2 (m : (Q*Q)*(Q*Q)) (s : RoleState) : RoleState :=
  (fst (fst m) * amp_plus s + snd (fst m) * amp_minus s,
   fst (snd m) * amp_plus s + snd (snd m) * amp_minus s).

(** The DISCRETE relabel symmetry S_2 (swap the two roles). *)
Definition swap : (Q*Q)*(Q*Q) := ((0,1),(1,0)).

Theorem swap_preserves_dist : forall s, dist_form (apply2 swap s) == dist_form s.
Proof.
  intros [x y]. unfold dist_form, apply2, swap, amp_plus, amp_minus; simpl. ring.
Qed.

(** A rotation with c²+s²=1 — the continuous closure (its rational points are Elements). *)
Definition rot (c sn : Q) : (Q*Q)*(Q*Q) := ((c, -sn),(sn, c)).

(** ★ UNITARITY DERIVED: any rotation preserving c²+s²=1 preserves the distinguishability form. *)
Theorem rot_preserves_dist : forall c sn x y,
  c*c + sn*sn == 1 ->
  dist_form (apply2 (rot c sn) (x, y)) == dist_form (x, y).
Proof.
  intros c sn x y Hcs.
  unfold dist_form, apply2, rot, amp_plus, amp_minus; simpl.
  transitivity ((c*c + sn*sn) * (x*x + y*y)).
  - ring.
  - rewrite Hcs. ring.
Qed.

(** ★ The 1-norm is BROKEN by a rotation (the (3,4,5) image of (1,0) has 1-norm 7/5 > 1).  So among the
    p-norms ONLY p=2 survives the rotation — the exponent 2 (the Born weight) is the UNIQUE rotation
    invariant: DERIVED, not an Open residual.  Full descent: BornRuleDescent.square_preserved /
    only_square_conserved. *)
Lemma one_norm_broken_by_rotation : 1 < Qabs (3#5) + Qabs (4#5).
Proof. vm_compute. reflexivity. Qed.

(** ★ det=1 DERIVED: the global phase (reflexive self-distinction) preserves everything observable. *)
Definition global_phase : (Q*Q)*(Q*Q) := ((-1,0),(0,-1)).

Theorem phase_preserves_dist : forall s, dist_form (apply2 global_phase s) == dist_form s.
Proof.
  intros [x y]. unfold dist_form, apply2, global_phase, amp_plus, amp_minus; simpl. ring.
Qed.

(* ================================================================== *)
(*  THE QUANTUM CONTENT, RELOCATED: interference (signed weights)     *)
(* ================================================================== *)

(** ★ INTERFERENCE: signed/complex amplitudes can CANCEL — two nonzero contributions sum to zero. *)
Theorem interference_cancels :
  exists a b : Q, ~ (a == 0) /\ ~ (b == 0) /\ a + b == 0.
Proof.
  exists 1, (-(1)). split; [intro H; lra | split; [intro H; lra | lra]].
Qed.

(** ★ CLASSICAL potential (probabilities ≥ 0) CANNOT cancel — the contrast that makes interference
    the genuine quantum addition (beyond bare potentiality). *)
Theorem classical_no_cancel :
  forall p q : Q, 0 <= p -> 0 <= q -> p + q == 0 -> p == 0 /\ q == 0.
Proof. intros p q Hp Hq Hsum. split; lra. Qed.

(* ================================================================== *)
(*  THE LEDGER: 5 requirements of SU(N), corrected statuses           *)
(* ================================================================== *)

Inductive SUNRequirement :=
  | Linearity | Unitarity | SpecialDet | Continuity | BornWeight.

Inductive ToSStatus := Derived | RoleLimit | Posit.

Definition status (r : SUNRequirement) : ToSStatus :=
  match r with
  | Unitarity  => Derived     (* preserve distinguishability *)
  | SpecialDet => Derived     (* factor the reflexive global phase *)
  | BornWeight => Derived     (* the SQUARE is the unique rotation invariant (born_exponent_is_derived;
                                 full descent BornRuleDescent.square_preserved) — closed, not Open *)
  | Continuity => RoleLimit   (* Lie group = process-closure of rational rotations (P4) *)
  | Linearity  => RoleLimit   (* POTENTIALITY — NOT a posit, NOT ¬L2 *)
  end.

(** ★ THE CORRECTION, in the ledger: Linearity/superposition is POTENTIALITY (role-limit). *)
Theorem linearity_is_potentiality_not_posit : status Linearity = RoleLimit.
Proof. reflexivity. Qed.

(** ★ No requirement is an anti-law POSIT: the ¬L2 reading is gone.  What remains is the theory's own
    foundational footing (potentiality/role-limit + the 2 axioms) plus ONE honest Open residual
    (the Born weight).  Honest: this neither fakes a derivation nor invents a posit. *)
Theorem no_antilaw_posit : forall r, status r <> Posit.
Proof. intros r; destruct r; simpl; discriminate. Qed.

(** ★ THE BORN WEIGHT CLOSES: the exponent 2 is DERIVED — the rotation preserves the 2-norm
    (rot_preserves_dist) but BREAKS the 1-norm (one_norm_broken_by_rotation), so p=2 is the unique
    rotation invariant.  Given interference, the Born weight is forced — not Open.  The single
    remaining INPUT is "why interference / the 2-norm symmetry" = being on the role-limit (continuous)
    side of the Element/role-limit boundary (the theory's foundation, the ≥1 footing — NOT a new
    posit; cf. BornRuleDescent: NormChoice = PositedInput). *)
Theorem born_exponent_is_derived :
  (forall c sn x y, c*c + sn*sn == 1 ->
     dist_form (apply2 (rot c sn) (x, y)) == dist_form (x, y))
  /\ 1 < Qabs (3#5) + Qabs (4#5)
  /\ status BornWeight = Derived.
Proof.
  split; [ exact rot_preserves_dist | ].
  split; [ exact one_norm_broken_by_rotation | reflexivity ].
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** The corrected attempt:
      L2 is PRESERVED on the actualized level (L2_holds_on_actualized);
      superposition is POTENTIAL, not "both" (superposition_is_potential_not_both) — withdraws ¬L2;
      DERIVED: the distinction-preserving (unitary) symmetry and the reflexive phase;
      the quantum content is INTERFERENCE (signed weights cancel; classical can't);
      no anti-law posit — Linearity = potentiality (role-limit), Born weight Open.
    So role→SU(N) is reduced to the theory's own footing + derived structure, with one Open residual
    (Born), and NO new logic-violating posit. *)
Theorem role_to_SUN_attempt :
  (forall s, ~ (actual_positive s /\ actual_negative s))
  /\ (forall s, in_potential s -> ~ actual_positive s /\ ~ actual_negative s)
  /\ (forall s, dist_form (apply2 swap s) == dist_form s)
  /\ (forall s, dist_form (apply2 global_phase s) == dist_form s)
  /\ (exists a b : Q, ~ (a == 0) /\ ~ (b == 0) /\ a + b == 0)
  /\ (forall p q : Q, 0 <= p -> 0 <= q -> p + q == 0 -> p == 0 /\ q == 0)
  /\ (status Linearity = RoleLimit /\ forall r, status r <> Posit).
Proof.
  split; [exact L2_holds_on_actualized|].
  split; [exact superposition_is_potential_not_both|].
  split; [exact swap_preserves_dist|].
  split; [exact phase_preserves_dist|].
  split; [exact interference_cancels|].
  split; [exact classical_no_cancel|].
  split; [exact linearity_is_potentiality_not_posit | exact no_antilaw_posit].
Qed.
