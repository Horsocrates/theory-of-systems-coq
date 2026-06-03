(** * GaussianMUB.v — ② (Gaussian step): the THIRD mutually-unbiased basis Y over
      ℚ[i], and the state-independent 3-MUB sum rule.  The imaginary unit i is an
      ELEMENT (Z₄), not a role-limit.

    Elements: Gaussian-rational amplitudes ℚ[i] = (re,im); rational Born
              probabilities (½); the imaginary unit i AS the order-4 element of Z₄
              (i⁴=1, terminating — from ①); the rational invariant 2 (L1 + P4)
    Roles:    the Y eigenbasis = the third measurement context; conjugation z̄ =
              the "real structure" making the imaginary observable-as-rational; the
              √2 normalisation = STILL a role-limit (untouched here)
    Rules:    the sesquilinear inner product ⟨u|v⟩ = ū·v; the modulus |z|²=z·z̄
              (ℚ[i]→ℚ, the Born rule one storey down); the 3-MUB sum rule
              coll_Z+coll_X+coll_Y = 2; i⁴ = 1 (Z₄)

    THE DEEP POINT — i is an ELEMENT, not a role-limit.  The amplitude layer carries
    TWO kinds of non-real content with OPPOSITE P4-status: √2 (the normalisation,
    `RationalQInfo.v`) is a role-limit — the non-terminating Pell process; but i (the
    Y-phase here) is an ELEMENT — it is the quarter-turn of Z₄ from ① (i²=−1, i⁴=1, it
    CLOSES — literally the point (0,1) of FinitizationBoundary).  So extending ℚ → ℚ[i]
    does NOT cross the finitization boundary: i stays entirely on the Element side.
    The continuum of QM lives only in the √2 normalisation; ℚ[i] is a finite-actual
    extension, not a step into the continuum.

    CONJUGATION = the Born rule one storey down.  |z|² = z·z̄ : ℚ[i] → ℚ sends a
    Gaussian-rational Element to a rational Element; the sesquilinearity (conjugate on
    the bra) is exactly what guarantees ⟨ψ|ψ⟩ ∈ ℚ (real, an Element).  And the
    completed MUB triad {Z,X,Y} is ①'s WHOLE Pauli/Clifford structure (all three
    axes); the state-independent sum rule coll_Z+coll_X+coll_Y = 2 = 1 + purity is the
    informational statement that a qubit's information is conserved across the
    complementary contexts — rational, Element-valued, state-independent.

    (NB: the constant is 2, not 3/2.  3/2 is the TWO-basis real sum coll_Z+coll_X of
    `RationalQInfo.renyi2_uncertainty`; the FULL three-MUB sum is 2 = 1 + purity.)

    ============ E/R/R разбор ============
      Rules (L5): полуторалинейный ⟨u|v⟩=ū·v; |z|²=z·z̄ (модуль-граница ℚ[i]→ℚ);
                  правило суммы 3-MUB = 2; i⁴=1 (Z₄).
      Roles (L4): Y-базис = третий контекст измерения; сопряжение = вещественная
                  структура; √2-нормировка = по-прежнему role-limit.
      Elements  : гауссовы рациональные амплитуды, вероятности ½, инвариант 2, i как
                  Z₄-Element (L1+P4).
    ДИАГНОСТИКА (P4): ℚ[i] — КОНЕЧНО-АКТУАЛЬНОЕ расширение (i завершается, i⁴=1), НЕ
    континуум; континуум только в √2-нормировке. «Реальна ли амплитуда i/√2» расщепляется:
    i = Element (Z₄), √2 = role-limit. Правило суммы = 2 — рациональный инвариант Element-слоя.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Minimal Gaussian rationals ℚ[i] = (re, im)                            *)
(* ===================================================================== *)

Definition GQ := (Q * Q)%type.
Definition gadd (z w : GQ) : GQ := (fst z + fst w, snd z + snd w).
Definition gmul (z w : GQ) : GQ :=
  (fst z * fst w - snd z * snd w, fst z * snd w + snd z * fst w).
Definition gconj (z : GQ) : GQ := (fst z, - snd z).
Definition cmod2 (z : GQ) : Q := fst z * fst z + snd z * snd z.   (* |z|² ∈ ℚ *)

Definition g0 : GQ := (0, 0).
Definition g1 : GQ := (1, 0).
Definition gi : GQ := (0, 1).        (* the imaginary unit *)
Definition gn1 : GQ := (-1, 0).      (* −1 *)
Definition gni : GQ := (0, -1).      (* −i *)

(* ===================================================================== *)
(*  Qubit states over ℚ[i], sesquilinear inner product, Born rule        *)
(* ===================================================================== *)

Definition qst := (GQ * GQ)%type.

(** Sesquilinear inner product ⟨u|v⟩ = ū₀v₀ + ū₁v₁ ∈ ℚ[i]. *)
Definition hinner (u v : qst) : GQ :=
  gadd (gmul (gconj (fst u)) (fst v)) (gmul (gconj (snd u)) (snd v)).

(** ⟨u|u⟩ = |u₀|² + |u₁|² ∈ ℚ — REAL, an Element (sesquilinearity at work). *)
Definition nrm (u : qst) : Q := cmod2 (fst u) + cmod2 (snd u).

(** Born probability of measuring state u and finding basis vector b. *)
Definition gborn (b u : qst) : Q := cmod2 (hinner b u) / (nrm b * nrm u).

(* The three MUB eigen-bases (entries in ℚ[i]). *)
Definition z0 : qst := (g1, g0).  Definition z1 : qst := (g0, g1).   (* Z / σz *)
Definition x0 : qst := (g1, g1).  Definition x1 : qst := (g1, gn1).  (* X / σx *)
Definition y0 : qst := (g1, gi).  Definition y1 : qst := (g1, gni).  (* Y / σy *)

Definition coll_Z (u : qst) : Q := gborn z0 u * gborn z0 u + gborn z1 u * gborn z1 u.
Definition coll_X (u : qst) : Q := gborn x0 u * gborn x0 u + gborn x1 u * gborn x1 u.
Definition coll_Y (u : qst) : Q := gborn y0 u * gborn y0 u + gborn y1 u * gborn y1 u.

(* ===================================================================== *)
(*  1. i is an ELEMENT (Z₄), not a role-limit                            *)
(* ===================================================================== *)

(** The imaginary unit closes: i² = −1, i⁴ = 1 — it is the order-4 element of
    Z₄ (the quarter-turn of ①), terminating.  CONTRAST: the √2 normalisation
    (RationalQInfo.v) never closes — a role-limit.  So ℚ[i] stays on the Element
    side of the finitization boundary. *)
Theorem imaginary_unit_is_element :
  gmul gi gi = gn1 /\ gmul (gmul (gmul gi gi) gi) gi = g1.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  2. Y is mutually unbiased with both Z and X (all cross-Born = ½)      *)
(* ===================================================================== *)

(** The Y basis is unbiased w.r.t. Z and X: every cross-Born probability is the
    rational ½.  Together with mub_ZX (RationalQInfo.v) this is the complete qubit
    MUB triad {Z,X,Y} — exactly ①'s Pauli eigenbasis structure. *)
Theorem mub_Y_unbiased :
  gborn z0 y0 == 1#2 /\ gborn z0 y1 == 1#2 /\
  gborn z1 y0 == 1#2 /\ gborn z1 y1 == 1#2 /\
  gborn x0 y0 == 1#2 /\ gborn x0 y1 == 1#2 /\
  gborn x1 y0 == 1#2 /\ gborn x1 y1 == 1#2.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  3. ★ The state-independent 3-MUB sum rule: coll_Z+coll_X+coll_Y = 2   *)
(* ===================================================================== *)

(** For ANY nonzero qubit state, the collision probabilities over the three
    mutually-unbiased bases sum to EXACTLY 2 = 1 + purity — a rational,
    state-independent invariant (the qubit MUB sum rule).  `gborn` self-
    normalises, so only ⟨u|u⟩ ≠ 0 is needed.  This is the informational
    conservation law across complementary contexts, fully over ℚ. *)
Theorem mub_sum_rule_3 : forall u : qst,
  ~ (nrm u == 0) -> coll_Z u + coll_X u + coll_Y u == 2.
Proof.
  intros [[a1 a2] [b1 b2]] Hnz.
  unfold nrm, cmod2 in Hnz; simpl in Hnz.
  unfold coll_Z, coll_X, coll_Y, gborn, hinner, nrm, cmod2,
         gadd, gmul, gconj, z0, z1, x0, x1, y0, y1,
         g0, g1, gi, gn1, gni; simpl.
  field. exact Hnz.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Gaussian step of ② in one statement: i is an Element (i⁴=1, Z₄), the Y
    basis completes the MUB triad (cross-Born ½), and the 3-MUB collision sum is
    the rational state-independent invariant 2 — all over ℚ[i], 0 axioms. *)
Theorem gaussian_mub_synthesis :
  gmul (gmul (gmul gi gi) gi) gi = g1
  /\ gborn z0 y0 == 1#2
  /\ (forall u : qst, ~ (nrm u == 0) -> coll_Z u + coll_X u + coll_Y u == 2).
Proof.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  exact mub_sum_rule_3.
Qed.
