(** * ReductionAtlasParity.v — the reduction atlas, page V (final discovery engine): the PARITY
      character popcount(i∧j) mod 2 as the cluster's purest Element-side primitive.  The cluster's
      Walsh / Hadamard / Clifford / stabilizer Element-structure — rational QM on the Walsh basis
      (③), the real Hadamard (Palmer), the n-qubit norm 2ⁿ and orthogonality H_nᵀH_n = 2ⁿI, the
      MUBs, Gottesman–Knill — is NOT many facts.  It is ONE engine: the sign character
      χ(p) = (−1)ᵖ, a homomorphism (ℕ,+) → ({±1},·) factoring through parity, applied to the
      mod-2 inner product popcount(i∧j) of bit-vectors.  Where pages I–IV read an integer invariant
      (surd index, determinant, norm form, trace), this page reads the smallest one — a parity bit
      in ℤ/2 — and it is the purest Element engine: every entry ±1, norm a power of 2, no continuum.
      Its only contact with the role-limit is the normalization 1/√(2ⁿ) — the SAME √2 of page I.

    Elements: the parity character χ; the 1-qubit Hadamard [[1,1],[1,−1]] entries and orthogonality;
              the tensor (n-bit) ±1 entry; det H₁ = −2 (L1 + P4)
    Roles:    the parity popcount(i∧j) mod 2 — the single ℤ/2-valued integer fixing the Walsh sign:
              held across all bits it gives orthogonality H_nᵀH_n = 2ⁿI and all entries ±1 (pure
              Element); its only role-limit contact is the normalization 1/√(2ⁿ) (the √2 wall, page I)
    Rules:    one generating rule — χ(p) = (−1)ᵖ is a homomorphism (ℕ,+) → ({±1},·) factoring through
              parity: χ(p+q) = χ(p)·χ(q) (χ_add), χ(p+2k) = χ(p) (χ_parity); the Walsh sign is
              χ(popcount(i∧j)), the character of the group (ℤ/2)ⁿ

    THE DEEP POINT — the fifth and most-Element engine; the atlas's discovery phase closes.  Five
    engines = five integer invariants at five "sizes": surd index m²=n·k² (page I, obstruction);
    determinant ad−bc (II, adjacency |·|=1); norm form x²−Dy² (III, bridge ±1); trace 2cosθ (IV,
    periodicity ∈{−2..2}); parity popcount(i∧j) mod 2 (V, Element, in ℤ/2 — the smallest).  Page V
    is the purest Element engine: the whole Walsh/Clifford/stabilizer/MUB structure runs on ONE
    parity character χ.  The homomorphism χ_add gives the character's bilinearity; χ_sq makes every
    entry ±1 (`w1_pm1`, `w_tensor_pm1` — the entries scale to n bits as a tensor of characters);
    the 1-qubit orthogonality H_1ᵀH_1 = 2I (`w1_orthogonality`) is the atomic character sum whose
    n-fold Kronecker product is H_nᵀH_n = 2ⁿI.  The role-limit appears ONLY at normalization:
    det H_1 = −2 (`hadamard_det_is_power2`, a signed power of 2 = Element), so the orthonormalizing
    factor is √2 — and the characteristic polynomial of [[1,1],[1,−1]] is x²−2 (trace 0, det −2),
    eigenvalues ±√2: the SAME √2 of page I.  So page V (Element) touches page I (surd) exactly at
    the √2 wall (the Hadamard 1/√2 of CliffordCeiling, ①/H7).  Element = the parity character (all
    ±1, norm 2ⁿ); role-limit = the √2 normalization alone.

    ============ E/R/R разбор ============
      Rules (L5): одно правило — характер чётности χ(p)=(−1)ᵖ есть гомоморфизм (ℕ,+)→({±1},·) через
                  чётность: χ(p+q)=χ(p)·χ(q) (chi_add), χ(p+2k)=χ(p) (chi_parity); знак Уолша = χ(popcount(i∧j)).
      Roles (L4): чётность popcount(i∧j) mod 2 — наименьшее (ℤ/2) целое, задающее знак: по всем битам —
                  ортогональность HᵀH=2ⁿI и элементы ±1 (Element); контакт с role-limit только нормировка 1/√(2ⁿ).
      Elements  : характер χ; элементы/ортогональность 1-кубитного Адамара; тензор n-бит ±1; det H₁=−2.
    ДИАГНОСТИКА (P4): пятый и самый ЭЛЕМЕНТНЫЙ движок; фаза открытия атласа замыкается. Пять движков = пять целых
    инвариантов на пяти размерах (сурд/определитель/норм-форма/след/ЧЁТНОСТЬ — наименьший, ℤ/2). Вся структура
    Уолша/Клиффорда/стабилизаторов/MUB = ОДИН характер чётности; элементы ±1, норма 2ⁿ — всё Element. Role-limit
    всплывает только при нормировке: det H₁=−2, χ-многочлен x²−2 ⟹ ±√2 = ТА ЖЕ √2 страницы I. Стр.V касается стр.I у стены √2.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: the parity character χ(p) = (−1)ᵖ, a homomorphism          *)
(* ===================================================================== *)

(** The parity sign character χ(p) = (−1)ᵖ. *)
Fixpoint chi (p : nat) : Z :=
  match p with
  | O => 1
  | S p' => - chi p'
  end.

(** χ on a successor flips sign (clean unfold, no stuck match — used instead of simpl). *)
Lemma chi_S : forall p, chi (S p) = - chi p.
Proof. reflexivity. Qed.

(** ★ Every value is ±1: χ(p)·χ(p) = 1. *)
Lemma chi_sq : forall p, chi p * chi p = 1.
Proof.
  intros p. induction p as [|p IH].
  - reflexivity.
  - rewrite chi_S. replace (- chi p * - chi p) with (chi p * chi p) by ring. exact IH.
Qed.

(** ★ The single rule: χ is a homomorphism (ℕ,+) → ({±1},·): χ(p+q) = χ(p)·χ(q). *)
Lemma chi_add : forall p q, chi (p + q)%nat = chi p * chi q.
Proof.
  intros p q. induction p as [|p IH].
  - rewrite Nat.add_0_l. change (chi 0) with 1. ring.
  - rewrite Nat.add_succ_l, !chi_S, IH. ring.
Qed.

(** χ on an even number is 1 (the homomorphism on a square). *)
Lemma chi_double : forall k, chi (2 * k)%nat = 1.
Proof.
  intros k. replace (2 * k)%nat with (k + k)%nat by lia.
  rewrite chi_add. apply chi_sq.
Qed.

(** ★ χ depends ONLY on parity: χ(p + 2k) = χ(p). *)
Lemma chi_parity : forall p k, chi (p + 2 * k)%nat = chi p.
Proof. intros p k. rewrite chi_add, chi_double. ring. Qed.

(* ===================================================================== *)
(*  The Walsh entry: a single-bit Hadamard value w1 a b = χ(a·b)           *)
(* ===================================================================== *)

(** The single-bit Walsh/Hadamard value w1 a b = χ(a·b): the entry of [[1,1],[1,−1]]
    (w1 0 0 = w1 0 1 = w1 1 0 = 1, w1 1 1 = −1).  The n-qubit entry is the product of w1 over
    bit positions, i.e. χ(popcount(i∧j)). *)
Definition w1 (a b : nat) : Z := chi (a * b)%nat.

(** Every Hadamard entry is ±1 (from χ_sq). *)
Lemma w1_pm1 : forall a b, w1 a b * w1 a b = 1.
Proof. intros a b. unfold w1. apply chi_sq. Qed.

(** ★ The entries scale to n bits as a TENSOR of characters and stay ±1: a 2-bit entry
    w1·w1 squares to 1 (χ_sq twice).  This is why the Element side scales to every n
    (`wval_pm1` in WalshHadamardN): a product of ±1 is ±1. *)
Lemma w_tensor_pm1 : forall a0 b0 a1 b1,
  (w1 a0 b0 * w1 a1 b1) * (w1 a0 b0 * w1 a1 b1) = 1.
Proof.
  intros a0 b0 a1 b1.
  assert (Hr : (w1 a0 b0 * w1 a1 b1) * (w1 a0 b0 * w1 a1 b1)
             = (w1 a0 b0 * w1 a0 b0) * (w1 a1 b1 * w1 a1 b1)) by ring.
  rewrite Hr, (w1_pm1 a0 b0), (w1_pm1 a1 b1). reflexivity.
Qed.

(* ===================================================================== *)
(*  ELEMENT FACE — orthogonality H_1ᵀH_1 = 2I (the atomic character sum)    *)
(* ===================================================================== *)

(** ★ The atomic orthogonality H_1ᵀH_1 = 2I: rows of the 1-qubit Hadamard are orthogonal with
    squared norm 2.  This is the character sum Σ_b χ(a·b)χ(a'·b) = 2·[a=a'] at one bit; its
    n-fold Kronecker product is H_nᵀH_n = 2ⁿI (WalshOrthogonality).  Pure Element: every term ±1,
    every diagonal a power of 2. *)
Lemma w1_orthogonality :
  w1 0 0 * w1 0 0 + w1 0 1 * w1 0 1 = 2
  /\ w1 1 0 * w1 1 0 + w1 1 1 * w1 1 1 = 2
  /\ w1 0 0 * w1 1 0 + w1 0 1 * w1 1 1 = 0.
Proof. unfold w1. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  ROLE-LIMIT CONTACT — the √2 normalization wall (page I)                *)
(* ===================================================================== *)

(** ★ The single role-limit contact: det H_1 = −2, a signed power of 2 (Element).  The
    orthonormalizing factor is therefore √2 (det = ±2 ⟹ normalize by √2), and the characteristic
    polynomial of [[1,1],[1,−1]] is x²−2 (trace 0, det −2) — eigenvalues ±√2, the SAME √2 of
    page I (the Hadamard 1/√2 wall, ①/H7).  Element character, role-limit normalization. *)
Lemma hadamard_det_is_power2 : w1 0 0 * w1 1 1 - w1 0 1 * w1 1 0 = -2.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The atlas page: one parity character, the whole Element-side Walsh      *)
(* ===================================================================== *)

(** The parity atlas page:
      (engine) χ is a homomorphism (ℕ,+) → ({±1},·) (`chi_add`) with every value ±1 (`chi_sq`);
      (Element) the 1-qubit Hadamard is orthogonal with squared norm 2 (`w1_orthogonality`) —
        the atomic character sum whose Kronecker power is H_nᵀH_n = 2ⁿI;
      (role-limit contact) det H_1 = −2, a power of 2 (`hadamard_det_is_power2`), so the
        normalization is √2 — the χ-polynomial x²−2 of page I.
    One parity character carries the whole Element side of the Walsh/Clifford/stabilizer structure;
    the role-limit enters only through the √2 normalization. *)
Theorem parity_atlas :
  (forall p q, chi (p + q)%nat = chi p * chi q)
  /\ (forall p, chi p * chi p = 1)
  /\ (w1 0 0 * w1 0 0 + w1 0 1 * w1 0 1 = 2
      /\ w1 1 0 * w1 1 0 + w1 1 1 * w1 1 1 = 2
      /\ w1 0 0 * w1 1 0 + w1 0 1 * w1 1 1 = 0)
  /\ (w1 0 0 * w1 1 1 - w1 0 1 * w1 1 0 = -2).
Proof.
  split; [ exact chi_add | ].
  split; [ exact chi_sq | ].
  split; [ exact w1_orthogonality | exact hadamard_det_is_power2 ].
Qed.
