(** * NivenRationalCosine.v — Niven's phenomenon, concretely: the 3-4-5 rotation
      is APERIODIC (its angle ∉ πℚ), so a rational cosine generically comes from a
      π-incommensurable angle. Seeds the P4 aperiodic-rational-orbit and Palmer's
      number-theoretic Bell mechanism.

    Elements: the integer coordinates (Xₙ,Yₙ) of the n-fold (3,4,5) rotation,
              scaled by 5ⁿ (so the rational orbit point is (Xₙ/5ⁿ, Yₙ/5ⁿ))
    Roles:    a FINITE-ORDER rational rotation = role of "π-commensurable angle"
              (only the four Z₄ points {±1,±i} have it); every other rational
              rotation is APERIODIC = role of "π-incommensurable angle"
    Rules:    Xₙ₊₁ = 3Xₙ−4Yₙ, Yₙ₊₁ = 4Xₙ+3Yₙ;  Xₙ²+Yₙ² = 25ⁿ (on the circle);
              the mod-5 invariant (Xₙ,Yₙ) ≡ (3,4) (mod 5) for n ≥ 1 ⟹ Xₙ ≠ 5ⁿ
              ⟹ the orbit NEVER returns to (1,0) ⟹ infinite order

    NIVEN'S THEOREM (cos(rπ) ∈ ℚ ⟹ cos ∈ {0,±½,±1}) says rational cosines at
    π-rational angles are SPARSE. Its constructive shadow, proved here over ℤ
    (no cos, no ℝ, no rational-denominator bookkeeping): the rotation with
    cos = 3/5 — a perfectly rational cosine — has an angle that is NOT a rational
    multiple of π, because its orbit of rational points (3/5,4/5),(−7/25,24/25),
    (−117/125,44/125),… never closes. The exact return to (1,0) is the role-limit
    (would require π-commensurability); over ℚ it never actualises. This is the
    P4 aperiodic-rational-orbit seed, and the non-conspiratorial number-theoretic
    constraint behind Palmer's RaQM Bell mechanism (measurement bases cannot be
    simultaneously rational AND π-commensurable, save the Z₄ exceptions).

    ============ E/R/R разбор ============
      Rules (L5): целочисленная рекуррентность поворота; mod-5 инвариант (3,4).
      Roles (L4): конечный порядок = π-соизмеримость (только Z₄); апериодичность =
                  π-несоизмеримость (role-limit «возврат в (1,0)» не актуализируется).
      Elements  : (Xₙ,Yₙ)∈ℤ², рациональные точки орбиты (Xₙ/5ⁿ,Yₙ/5ⁿ) (L1+P4).
    ДИАГНОСТИКА (P4): орбита 3-4-5 = НЕЗАВЕРШАЮЩИЙСЯ процесс (никогда не возвращается
    в (1,0)) = role-limit; «конечный порядок» не актуализуется над ℚ — обструкция mod 5. Точный CCR-аналог: апериодичность
    рационального поворота = бесконечность как процесс, а не объект.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ===== Integer coordinates of the n-fold (3,4,5) rotation (× 5ⁿ) ======== *)

Fixpoint XY (n : nat) : Z * Z :=
  match n with
  | O => (1, 0)
  | S k => let (x, y) := XY k in (3*x - 4*y, 4*x + 3*y)
  end.

Definition Xc (n : nat) : Z := fst (XY n).
Definition Yc (n : nat) : Z := snd (XY n).

Lemma Xc_S : forall n, Xc (S n) = 3 * Xc n - 4 * Yc n.
Proof. intro n. unfold Xc, Yc. simpl. destruct (XY n) as [x y]. reflexivity. Qed.

Lemma Yc_S : forall n, Yc (S n) = 4 * Xc n + 3 * Yc n.
Proof. intro n. unfold Xc, Yc. simpl. destruct (XY n) as [x y]. reflexivity. Qed.

(* ===== Scale factor 5ⁿ: the rational orbit point is (Xₙ/5ⁿ, Yₙ/5ⁿ) ===== *)

Fixpoint pow5 (n : nat) : Z := match n with O => 1 | S k => 5 * pow5 k end.

(* ===== The mod-5 invariant: (Xₙ,Yₙ) ≡ (3,4) (mod 5) for n ≥ 1 =========== *)

Lemma XY_mod5 : forall n, (1 <= n)%nat ->
  Z.divide 5 (Xc n - 3) /\ Z.divide 5 (Yc n - 4).
Proof.
  induction n as [|k IH]; intro Hn.
  - lia.
  - destruct k as [|k'].
    + (* n = 1: XY 1 = (3,4) *)
      split; [exists 0 | exists 0]; vm_compute; reflexivity.
    + assert (Hk : (1 <= S k')%nat) by lia.
      destruct (IH Hk) as [[a Ha] [b Hb]].
      split.
      * rewrite Xc_S. exists (3*a - 4*b - 2). lia.
      * rewrite Yc_S. exists (4*a + 3*b + 4). lia.
Qed.

Lemma pow5_mod5 : forall n, (1 <= n)%nat -> Z.divide 5 (pow5 n).
Proof.
  destruct n as [|k]; intro Hn.
  - lia.
  - exists (pow5 k). change (pow5 (S k)) with (5 * pow5 k). apply Z.mul_comm.
Qed.

(* ===== The 3-4-5 rotation has infinite order (angle ∉ πℚ) =============== *)

(** The orbit never returns to (1,0): for n ≥ 1, Xₙ ≢ 0 (mod 5) while 5ⁿ ≡ 0,
    so Xₙ ≠ 5ⁿ — the rotation power is never the identity. *)
Theorem infinite_order_345 : forall n, (1 <= n)%nat -> Xc n <> pow5 n.
Proof.
  intros n Hn Heq.
  destruct (XY_mod5 n Hn) as [[a Ha] _].
  destruct (pow5_mod5 n Hn) as [c Hc].
  rewrite Heq, Hc in Ha. lia.
Qed.

Corollary orbit_never_returns : forall n, (1 <= n)%nat ->
  ~ (Xc n = pow5 n /\ Yc n = 0).
Proof. intros n Hn [H _]. exact (infinite_order_345 n Hn H). Qed.

(* ===== Concrete aperiodic march of distinct rational points ============= *)
(* (3/5,4/5), (−7/25,24/25), (−117/125,44/125): all on the circle, all ≠ (1,0) *)

Example xy1 : XY 1 = (3, 4).       Proof. vm_compute. reflexivity. Qed.
Example xy2 : XY 2 = (-7, 24).     Proof. vm_compute. reflexivity. Qed.
Example xy3 : XY 3 = (-117, 44).   Proof. vm_compute. reflexivity. Qed.

(* ...each on the circle of radius 5ⁿ (Xₙ²+Yₙ² = 25ⁿ), verified concretely *)
Example xy1_circle : Xc 1 * Xc 1 + Yc 1 * Yc 1 = 25.    Proof. vm_compute. reflexivity. Qed.
Example xy2_circle : Xc 2 * Xc 2 + Yc 2 * Yc 2 = 625.   Proof. vm_compute. reflexivity. Qed.
Example xy3_circle : Xc 3 * Xc 3 + Yc 3 * Yc 3 = 15625. Proof. vm_compute. reflexivity. Qed.
