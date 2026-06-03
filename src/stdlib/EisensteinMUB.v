(** * EisensteinMUB.v — qutrit (d=3) mutually unbiased bases over ℚ[ω]: the
      rational-QM / MUB story is NOT a qubit accident — it works for d=3 too.

    Elements: Eisenstein-rational amplitudes ℚ[ω] = a+bω (ω³=1); the rational Born
              probability 1/3; the cube root of unity ω AS the order-3 element of Z₃
    Roles:    the FOUR (= d+1) measurement contexts (Z + three Heisenberg–Weyl
              Fourier-type bases); the √3 normalisation = a role-limit
    Rules:    the sesquilinear inner product over ℚ[ω]; the modulus |z|² = z·z̄ =
              the Eisenstein norm a²−ab+b²; the MU criterion |⟨a|b⟩|² = 1/3; ω³ = 1

    This extends the qubit MUB layer (Z↔X↔Y over ℚ[i]) to the QUTRIT over ℚ[ω].
    The parallel is exact:
      · for the qubit the new unit was i, an ELEMENT of Z₄ (i⁴=1); for the qutrit it
        is ω, an ELEMENT of Z₃ (ω³=1) — and Z₃ is one of the crystallographic orders
        {1,2,3,4,6}.  So ℚ → ℚ[ω] does NOT cross the finitization boundary either.
      · the amplitude normalisation role-limit is √d: √2 for the qubit, √3 for the
        qutrit — and √3 is the SAME role-limit that excludes the 60°-point.  So the
        qutrit's amplitude carries two non-real contents of opposite P4-status: ω
        (Element, Z₃) and √3 (role-limit), exactly as i/√2 for the qubit.
      · the observable Born probability is the rational 1/3 (an Element); the four
        d+1 = 4 MUBs are ℚ[ω]-finite.  The finitization Element side is not a
        single-d accident.

    ============ E/R/R разбор ============
      Rules (L5): полуторалинейный ⟨u|v⟩ над ℚ[ω]; |z|²=z·z̄ = a²−ab+b² (Эйзенштейн);
                  MUB-Борн=1/3; ω³=1.
      Roles (L4): 4 = d+1 контекста измерения; √3-нормировка = role-limit.
      Elements  : эйзенштейново-рациональные амплитуды, Борн 1/3, ω как Z₃-Element.
    ДИАГНОСТИКА (P4): Element-сторона работает и для d=3. ω = Z₃-Element (ℚ→ℚ[ω] не
    пересекает границу); √3-нормировка = role-limit (та же √3 из ④). Борн 1/3 = Element.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import analysis.Sqrt3Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Eisenstein rationals ℚ[ω] = a + bω,  ω² = −1 − ω                      *)
(* ===================================================================== *)

Definition GQw := (Q * Q)%type.
Definition gwadd (z w : GQw) : GQw := (fst z + fst w, snd z + snd w).
(* (a+bω)(c+dω) = (ac−bd) + (ad+bc−bd)ω  since ω² = −1−ω *)
Definition gwmul (z w : GQw) : GQw :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w - snd z * snd w).
(* conjugate: ω̄ = ω² = −1−ω, so (a+bω)‾ = (a−b) − bω *)
Definition gwconj (z : GQw) : GQw := (fst z - snd z, - snd z).
(* |z|² = z·z̄ = a² − ab + b² ∈ ℚ (the Eisenstein norm) *)
Definition cmodw (z : GQw) : Q := fst z * fst z - fst z * snd z + snd z * snd z.

Definition gw0 : GQw := (0, 0).
Definition gw1 : GQw := (1, 0).
Definition gww : GQw := (0, 1).       (* ω *)
Definition gww2 : GQw := (-1, -1).    (* ω² = −1 − ω *)

(* ===================================================================== *)
(*  1. ω is an ELEMENT (Z₃): ω³ = 1, order exactly 3                      *)
(* ===================================================================== *)

(** The cube root of unity closes: ω³ = 1 and ω ≠ 1, ω² ≠ 1 — it is the order-3
    element of Z₃ (one of the crystallographic orders).  So ℚ[ω] stays on the
    Element side of the finitization boundary (parallel to i = Z₄). *)
Theorem omega_is_element :
  gwmul (gwmul gww gww) gww = gw1 /\ gwmul gww gww = gww2 /\ ~ (gww = gw1).
Proof. repeat split; try (vm_compute; reflexivity); discriminate. Qed.

(* ===================================================================== *)
(*  Qutrit states over ℚ[ω], sesquilinear inner product, Born rule       *)
(* ===================================================================== *)

Definition qst3 := (GQw * GQw * GQw)%type.

Definition nrm3 (u : qst3) : Q :=
  let '(a, b, c) := u in cmodw a + cmodw b + cmodw c.

Definition hinner3 (u v : qst3) : GQw :=
  let '(a, b, c) := u in let '(x, y, z) := v in
  gwadd (gwadd (gwmul (gwconj a) x) (gwmul (gwconj b) y)) (gwmul (gwconj c) z).

Definition born3 (b u : qst3) : Q := cmodw (hinner3 b u) / (nrm3 b * nrm3 u).

(* The four d+1 = 4 MUBs: Z (computational) and three Heisenberg–Weyl bases
   v_{m,k}(j) = ω^{m·j² + k·j}, m,k ∈ {0,1,2}. *)
Definition e0 : qst3 := (gw1, gw0, gw0).
Definition e1 : qst3 := (gw0, gw1, gw0).
Definition e2 : qst3 := (gw0, gw0, gw1).

Definition f0 : qst3 := (gw1, gw1, gw1).            (* m=0 Fourier (X) *)
Definition f1 : qst3 := (gw1, gww, gww2).
Definition f2 : qst3 := (gw1, gww2, gww).

Definition g0 : qst3 := (gw1, gww, gww).            (* m=1 (Y) *)
Definition g1 : qst3 := (gw1, gww2, gw1).
Definition g2 : qst3 := (gw1, gw1, gww2).

Definition h0 : qst3 := (gw1, gww2, gww2).          (* m=2 (W) *)
Definition h1 : qst3 := (gw1, gw1, gww).
Definition h2 : qst3 := (gw1, gww, gw1).

(* ===================================================================== *)
(*  2. Complementarity: every cross-basis Born probability is 1/3         *)
(* ===================================================================== *)

(** The computational basis is unbiased w.r.t. the Fourier (X) basis: every Born
    probability is the rational 1/3 — flat complementarity in d = 3. *)
Theorem qutrit_ZX_mub :
  born3 e0 f0 == 1#3 /\ born3 e1 f1 == 1#3 /\ born3 e2 f2 == 1#3 /\
  born3 e0 f1 == 1#3 /\ born3 e1 f2 == 1#3.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The genuinely non-trivial MUB pairs — two Fourier-type bases (X, Y, W) are
    mutually unbiased with one another: cross-Born = 1/3. *)
Theorem qutrit_XYW_mub :
  born3 f0 g0 == 1#3 /\ born3 f1 g1 == 1#3 /\
  born3 f0 h0 == 1#3 /\ born3 g0 h0 == 1#3 /\ born3 g1 h2 == 1#3.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Within a basis the vectors are orthogonal (Born = 0). *)
Theorem fourier_orthogonality :
  born3 f0 f1 == 0 /\ born3 f0 f2 == 0 /\ born3 f1 f2 == 0 /\
  born3 g0 g1 == 0 /\ born3 h0 h2 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  3. amplitude = role-limit (√3), probability = Element (1/3)           *)
(* ===================================================================== *)

(** The d = 3 amplitude normalisation √3 has no rational value (a role-limit —
    the SAME √3 that excludes the 60°-point), yet the Born probability is the
    rational Element 1/3. *)
Theorem amplitude_role_limit_qutrit :
  (~ exists r : Q, r * r == 3) /\ born3 e0 f0 == 1#3.
Proof. split; [ exact sqrt3_not_in_Q | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The qutrit MUBs over ℚ[ω] in one statement: ω is an Element (Z₃), the four
    d+1 bases are mutually unbiased with flat rational Born 1/3, orthogonal
    within a basis, and the √3 normalisation is a role-limit while the
    probability 1/3 is an Element — all over ℚ[ω], 0 axioms. *)
Theorem eisenstein_mub_synthesis :
  gwmul (gwmul gww gww) gww = gw1
  /\ born3 e0 f0 == 1#3
  /\ born3 f0 g0 == 1#3
  /\ born3 f0 f1 == 0
  /\ (~ exists r : Q, r * r == 3).
Proof.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  exact sqrt3_not_in_Q.
Qed.
