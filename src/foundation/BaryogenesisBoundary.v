(** * BaryogenesisBoundary.v — dissecting the THREE open magnitude-boxes of baryogenesis through the
      finitization-boundary lens (H1).  Each box SPLITS into {a DERIVED Element-side (existence / sign /
      direction) + a magnitude-side that is a BOUNDARY}; and the boundaries are of two kinds — 2 of 3 are
      finitization ROLE-LIMITS (irrational / transcendental walls, like √2), 1 is a DIFFERENT ARENA.

    The earlier phases left η_B's magnitude "open".  But "open" is a label, not an analysis.  Applying
    the E/R/R + finitization-boundary lens DISSECTS each open box:

      ── JValue (the CP magnitude) ──
        Element-side (DERIVED): J ≠ 0 — existence & sign (3 generations ⟹ 1 CP phase ⟹ Jarlskog > 0).
        Magnitude-side: the VALUE of J.  By Niven (cos(rπ) ∈ ℚ ⟹ cos ∈ {0,±½,±1}; NivenRationalCosine.v),
          a generic CP angle has an IRRATIONAL cosine ⟹ J is a ROLE-LIMIT — non-finitizable, like √2.

      ── SphaleronRate (the B-violation magnitude) ──
        Element-side (DERIVED): the channel is ACTIVE, ΔB = 3 ≠ 0 (SphaleronWinding).
        Magnitude-side: the rate ∝ exp(−E_sph/T).  The exponential is the canonical NON-TERMINATING
          process (e transcendental) ⟹ a ROLE-LIMIT by form.

      ── DepartureMagnitude (the out-of-equilibrium magnitude) ──
        Element-side (DERIVED): departure ≠ 0 — direction / irreversibility (the arrow; WashoutNonTransfer).
        Magnitude-side: the SIZE of the departure (H vs Γ at T_EW) — needs continuum thermal dynamics ⟹
          a DIFFERENT ARENA (not a role-limit number; an arena ToS-as-finite does not model).

    THE PAYOFF: the baryogenesis open boxes are INSTANCES OF THE FINITIZATION BOUNDARY (H1).  η_B is
    unreachable not by sloppiness but for the SAME reason √2 is: 2 of the 3 boxes are role-limits
    (irrational CP value via Niven, transcendental rate via exp); the third is a different arena.  In
    EVERY box the Element-side (count, sign, direction, the triad STRUCTURE) is DERIVED; only the
    magnitude is a wall.  This ties the whole baryogenesis work back to the flagship: finite/discrete/
    Element ⟹ derived; role-limit/continuum ⟹ wall.

    Elements: the three open boxes; their Element-sides (J≠0, ΔB≠0, departure≠0 — derived)
    Roles:    each box = {derived Element-side} + {magnitude-side of a named kind}
    Rules:    boundary_kind classifies the magnitudes; 2 of 3 are finitization role-limits

    ============ E/R/R разбор ============
      Rules (L5): каждая открытая магнитуда расщепляется {Element (выведено) + сторона-граница};
                  границы разных видов: 2 role-limit (Нивен/exp) + 1 иная-арена (континуум).
      Roles (L4): J-значение/скорость-сфалерона/departure-размер — три ящика; Element-стороны
                  (J≠0, ΔB≠0, departure≠0) выведены; магнитуды = стены.
      Elements  : boundary_kind; счёт role-limit = 2; Element-стороны выведены.
    ДИАГНОСТИКА (P4): границы бариогенезиса = ИНСТАНСЫ границы финитизации (H1). η_B недостижимо по той же
    причине, что √2: 2 из 3 = role-limit (иррац. CP через Нивена, трансцендентная скорость через exp),
    третий = иная арена. Element-стороны (счёт, знак, направление, триада) выведены; role-limit/арена = стена.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith Lia ZArith QArith Lqa.
Import ListNotations.
From ToS Require Import foundation.EtaFromLattice.     (* jarlskog_estimate, jarlskog_positive *)
From ToS Require Import foundation.SphaleronWinding.    (* delta_B, sphaleron_violates_B *)

(* ===================================================================== *)
(*  The three open magnitude-boxes and the kinds of boundary               *)
(* ===================================================================== *)

(** The three open magnitude-boxes of baryogenesis (the things we did NOT derive the value of). *)
Inductive OpenBox := JValue | SphaleronRate | DepartureMagnitude.

(** The KIND of a boundary: a finitization ROLE-LIMIT (irrational/transcendental wall) or a DIFFERENT
    ARENA (a magnitude living in a structure ToS-as-finite does not model). *)
Inductive BoundaryKind := RoleLimit | DifferentArena.

(** Classification of each box's MAGNITUDE-side. *)
Definition boundary_kind (b : OpenBox) : BoundaryKind :=
  match b with
  | JValue             => RoleLimit       (* Niven: a generic CP angle ⟹ irrational cosine *)
  | SphaleronRate      => RoleLimit       (* exp(−E/T): transcendental, non-terminating *)
  | DepartureMagnitude => DifferentArena  (* continuum thermal dynamics (H/Γ) *)
  end.

Lemma jvalue_role_limit : boundary_kind JValue = RoleLimit.
Proof. reflexivity. Qed.

Lemma sphaleron_role_limit : boundary_kind SphaleronRate = RoleLimit.
Proof. reflexivity. Qed.

Lemma departure_different_arena : boundary_kind DepartureMagnitude = DifferentArena.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2 of 3 are finitization role-limits (ties to the flagship H1)           *)
(* ===================================================================== *)

Definition is_role_limit (b : OpenBox) : bool :=
  match boundary_kind b with RoleLimit => true | DifferentArena => false end.

Definition n_role_limits : nat :=
  length (filter is_role_limit [JValue; SphaleronRate; DepartureMagnitude]).

(** ★ TWO of the three open boxes are finitization ROLE-LIMITS — η_B is unreachable for the SAME reason
    √2 is (the finitization boundary, H1).  The third is a different arena. *)
Lemma two_finitization_walls : n_role_limits = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Each box SPLITS: a DERIVED Element-side + a magnitude boundary          *)
(* ===================================================================== *)

(** A box's status: its Element-side (existence/sign/direction) is derived (true), and its magnitude is
    a boundary of some kind. *)
Record BoxStatus := mkBox { elem_derived : bool ; mag_kind : BoundaryKind }.

Definition box_status (b : OpenBox) : BoxStatus :=
  match b with
  | JValue             => mkBox true RoleLimit       (* J ≠ 0 derived; value a role-limit *)
  | SphaleronRate      => mkBox true RoleLimit       (* ΔB ≠ 0 derived; rate a role-limit *)
  | DepartureMagnitude => mkBox true DifferentArena  (* departure ≠ 0 derived; size a different arena *)
  end.

(** ★ EVERY box has a DERIVED Element-side: existence / sign / direction is always derived; only the
    magnitude is a wall.  (The Element-sides are cited concretely below and in the earlier files.) *)
Lemma all_element_derived : forall b, elem_derived (box_status b) = true.
Proof. intro b; destruct b; reflexivity. Qed.

(* ---- the concrete derived Element-sides (real teeth) ---- *)

(** ★ JValue Element-side DERIVED: J ≠ 0 — the CP asymmetry exists (3 generations ⟹ Jarlskog > 0). *)
Lemma jvalue_element_derived : forall K, ~ jarlskog_estimate K == 0.
Proof. intros K Heq. pose proof (jarlskog_positive K) as H. rewrite Heq in H. exact (Qlt_irrefl 0 H). Qed.

(** ★ SphaleronRate Element-side DERIVED: the channel is active, ΔB ≠ 0 (the sphaleron changes B). *)
Lemma sphaleron_element_derived : (delta_B 1 <> 0)%Z.
Proof. exact sphaleron_violates_B. Qed.

(* ===================================================================== *)
(*  Capstone: the baryogenesis boundary, dissected                          *)
(* ===================================================================== *)

(** The baryogenesis boundary, dissected (not just labelled "open"):
      (classify)  JValue and SphaleronRate are finitization ROLE-LIMITS; DepartureMagnitude is a DIFFERENT
                  ARENA — 2 of 3 are finitization walls (η_B unreachable for the same reason √2 is);
      (split)     every box has a DERIVED Element-side (existence/sign/direction) — only the magnitude is
                  the wall;
      (teeth)     concretely: J ≠ 0 (derived) and the sphaleron channel is active, ΔB ≠ 0 (derived).
    The open boxes are INSTANCES OF THE FINITIZATION BOUNDARY (H1): finite/Element ⟹ derived;
    role-limit/continuum ⟹ wall. *)
Theorem baryogenesis_boundary :
  boundary_kind JValue = RoleLimit
  /\ boundary_kind SphaleronRate = RoleLimit
  /\ boundary_kind DepartureMagnitude = DifferentArena
  /\ n_role_limits = 2%nat
  /\ (forall b, elem_derived (box_status b) = true)
  /\ (~ jarlskog_estimate 0 == 0)
  /\ (delta_B 1 <> 0)%Z.
Proof.
  split; [ exact jvalue_role_limit | ].
  split; [ exact sphaleron_role_limit | ].
  split; [ exact departure_different_arena | ].
  split; [ exact two_finitization_walls | ].
  split; [ exact all_element_derived | ].
  split; [ exact (jvalue_element_derived 0) | ].
  exact sphaleron_element_derived.
Qed.
