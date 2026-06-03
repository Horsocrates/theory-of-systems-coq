(** * CrystallographicTrace.v — the integer-trace (lattice) form of the crystallographic
      restriction.  A finite-order integer rotation M (Mⁿ=I, det 1) has trace t with
      |t| ≤ 2, hence t ∈ {−2,−1,0,1,2} and order n ∈ {1,2,3,4,6}.  Pure ℤ, no matrices:
      the trace-of-powers sequence aₖ = tr(Mᵏ) satisfies aₖ₊₂ = t·aₖ₊₁ − aₖ (Cayley–
      Hamilton, det 1), with a₀=2, a₁=t; Mⁿ=I forces aₙ = tr(I) = 2.  For |t| ≥ 3 the
      sequence grows without bound and NEVER returns to 2 — no finite order.  This is the
      general n behind LatticePolygons.v (n≥7 barred by the trace), complementing the
      SO(3,ℚ)/Niven form in CrystallographicRestriction.v.

    Elements: the integer trace sequence cheb t k; the five returning traces {−2,−1,0,1,2}
              at orders {1,2,3,4,6}; the unbounded growth for |t|≥3 (L1 + P4)
    Roles:    Element side = the FINITE set of allowed traces that return to 2 (realizable
              lattice rotations); role-limit/forbidden = |t|≥3 where the trace grows and
              never returns (no finite order — a non-terminating growth); the integer trace
              t = 2cos(2π/n) IS the crystallographic constraint
    Rules:    Cayley–Hamilton M²=tM−I ⟹ aₖ₊₂=t·aₖ₊₁−aₖ; Mⁿ=I ⟹ aₙ=tr(I)=2; the growth law

    THE DEEP POINT — a lattice rotation is finite-actual ⟺ its trace returns to 2 ⟺ |t|≤2.
    The trace of the k-th power, aₖ = tr(Mᵏ), follows the Chebyshev-like recurrence
      cheb t 0 = 2,  cheb t 1 = t,  cheb t (k+2) = t·cheb t (k+1) − cheb t k
    (from M² = t·M − I, det 1).  If Mⁿ = I then cheb t n = tr(I) = 2.
      · ELEMENT / allowed: the five integer traces {−2,−1,0,1,2} DO return to 2, at orders
        n = 2,3,4,6,1 (`cheb_realizable`) — the realizable lattice rotations.
      · FORBIDDEN / role-limit: for |t| ≥ 3 the sequence is strictly increasing in
        magnitude (`cheb_mono`, `cheb_gt2`), so cheb t n ≠ 2 for all n ≥ 1 (`cheb_ne2`) —
        no finite order.  The "forbidden symmetry" (a 5-, 7-, 8-… fold rotation of ℤ²) is
        a non-terminating growth of the trace, never closing onto the identity.
    So the integer trace forces order ∈ {1,2,3,4,6}: the lattice crystallographic
    restriction, the general n behind LatticePolygons.v.

    ============ E/R/R разбор ============
      Rules (L5): Кэли–Гамильтон M²=tM−I ⟹ aₖ₊₂=t·aₖ₊₁−aₖ (a₀=2,a₁=t); Mⁿ=I ⟹ aₙ=2; закон роста.
      Roles (L4): Element = КОНЕЧНОЕ множество следов {−2,−1,0,1,2}, возвращающихся к 2 (порядки
                  {1,2,3,4,6}, реализуемые повороты); role-limit = |t|≥3, след растёт, не возвращается
                  (нет конечного порядка — нетерминирующий рост); целочисл. след = кристалл. ограничение.
      Elements  : целочисл. последовательность cheb t k; пять возвращающихся следов; рост (L1+P4).
    ДИАГНОСТИКА (P4): решёточный поворот конечно-актуален ⟺ след возвращается к 2 ⟺ |t|≤2 ⟺ n∈{1,2,3,4,6};
    |t|≥3 ⟹ след-процесс расходится (запрещённая симметрия = нетерминирующий рост). Решёточная форма
    кристалл. ограничения, дополняет SO(3,ℚ)/Нивен; общее n за LatticePolygons (n≥7 запрещены следом).

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The trace-of-powers sequence: cheb t k = tr(Mᵏ) for trace t, det 1    *)
(* ===================================================================== *)

Fixpoint cheb (t : Z) (k : nat) : Z :=
  match k with
  | O => 2
  | S O => t
  | S (S m as k') => t * cheb t k' - cheb t m
  end.

(** The defining recurrence, definitionally: aₖ₊₂ = t·aₖ₊₁ − aₖ. *)
Lemma cheb_SS : forall t m, cheb t (S (S m)) = t * cheb t (S m) - cheb t m.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Forbidden: |t| ≥ 3 ⟹ the sequence grows, never returns to 2           *)
(* ===================================================================== *)

(** For t ≥ 3 the sequence is ≥ 2 and strictly increasing. *)
Lemma cheb_mono : forall t, 3 <= t ->
  forall k, 2 <= cheb t k /\ cheb t k < cheb t (S k).
Proof.
  intros t Ht. induction k.
  - simpl. split; lia.
  - destruct IHk as [Hlo Hlt]. split.
    + lia.
    + rewrite cheb_SS. nia.
Qed.

(** For t ≥ 3 and k ≥ 1, the trace exceeds 2 — so it never equals tr(I) = 2. *)
Lemma cheb_gt2 : forall t, 3 <= t -> forall k, (1 <= k)%nat -> cheb t k > 2.
Proof.
  intros t Ht k Hk. destruct k as [| j].
  - lia.
  - destruct (cheb_mono t Ht j) as [Hlo Hlt]. lia.
Qed.

(* ===================================================================== *)
(*  The alternating sign, to handle the negative-trace case               *)
(* ===================================================================== *)

Fixpoint altsign (k : nat) : Z := match k with O => 1 | S m => - altsign m end.

Lemma altsign_SS : forall k, altsign (S k) = - altsign k.
Proof. reflexivity. Qed.

Lemma altsign_pm1 : forall k, altsign k = 1 \/ altsign k = -1.
Proof.
  induction k.
  - left. reflexivity.
  - rewrite altsign_SS. destruct IHk as [H | H]; rewrite H.
    + right. reflexivity.
    + left. reflexivity.
Qed.

(** cheb(−t) k = (−1)ᵏ · cheb t k (carried as a consecutive pair). *)
Lemma cheb_neg_pair : forall t k,
  cheb (-t) k = altsign k * cheb t k
  /\ cheb (-t) (S k) = altsign (S k) * cheb t (S k).
Proof.
  intros t. induction k.
  - split.
    + reflexivity.
    + change (cheb (- t) (S 0)) with (- t).
      change (cheb t (S 0)) with t.
      change (altsign (S 0)) with (-1).
      ring.
  - destruct IHk as [H0 H1]. split.
    + exact H1.
    + rewrite (cheb_SS (-t) k), (cheb_SS t k), H1, H0.
      replace (altsign (S (S k))) with (altsign k) by (rewrite !altsign_SS; ring).
      replace (altsign (S k)) with (- altsign k) by (rewrite altsign_SS; ring).
      ring.
Qed.

Lemma cheb_neg : forall t k, cheb (-t) k = altsign k * cheb t k.
Proof. intros t k. destruct (cheb_neg_pair t k) as [H _]. exact H. Qed.

(** ★ |t| ≥ 3 ⟹ cheb t n ≠ 2 for all n ≥ 1: a forbidden trace never returns to the
    identity trace, so the rotation has no finite order. *)
Lemma cheb_ne2 : forall t, (3 <= t \/ t <= -3) ->
  forall k, (1 <= k)%nat -> cheb t k <> 2.
Proof.
  intros t Ht k Hk Hcontra.
  destruct Ht as [Hpos | Hneg].
  - pose proof (cheb_gt2 t Hpos k Hk). lia.
  - assert (Hu : 3 <= - t) by lia.
    pose proof (cheb_gt2 (- t) Hu k Hk) as Hgt.
    pose proof (cheb_neg t k) as Hng.
    rewrite Hcontra in Hng.
    destruct (altsign_pm1 k) as [Ha | Ha]; rewrite Ha in Hng; lia.
Qed.

(* ===================================================================== *)
(*  Element / allowed: the five integer traces DO return to 2             *)
(* ===================================================================== *)

(** ★ The five allowed traces {2,−2,−1,0,1} return to tr(I)=2 at orders n=1,2,3,4,6 —
    the realizable lattice rotations (square n=4 ↔ trace 0, hexagonal n=6 ↔ trace 1, …). *)
Lemma cheb_realizable :
  cheb 2 1 = 2 /\ cheb (-2) 2 = 2 /\ cheb (-1) 3 = 2 /\ cheb 0 4 = 2 /\ cheb 1 6 = 2.
Proof. repeat split; reflexivity. Qed.

(** Concrete forbidden case: trace 3 (a would-be rotation that is too "fast") never
    returns to 2 — no finite order. *)
Lemma cheb_3_never : forall k, (1 <= k)%nat -> cheb 3 k <> 2.
Proof. intros k Hk. apply (cheb_ne2 3); [ left; lia | exact Hk ]. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The lattice crystallographic restriction in trace form:
      (a) FORBIDDEN — |trace| ≥ 3 ⟹ the trace never returns to 2 (no finite order);
      (b) ALLOWED — the five traces {2,−2,−1,0,1} return to 2 at orders {1,2,3,4,6};
      (c) the trace-of-powers recurrence (Cayley–Hamilton, det 1).
    Hence a finite-order integer rotation has trace ∈ {−2,−1,0,1,2}, order ∈ {1,2,3,4,6}. *)
Theorem crystallographic_trace_synthesis :
  (forall t, (3 <= t \/ t <= -3) -> forall k, (1 <= k)%nat -> cheb t k <> 2)
  /\ (cheb 2 1 = 2 /\ cheb (-2) 2 = 2 /\ cheb (-1) 3 = 2 /\ cheb 0 4 = 2 /\ cheb 1 6 = 2)
  /\ (forall t m, cheb t (S (S m)) = t * cheb t (S m) - cheb t m).
Proof.
  split; [ exact cheb_ne2 | ].
  split; [ exact cheb_realizable | exact cheb_SS ].
Qed.
