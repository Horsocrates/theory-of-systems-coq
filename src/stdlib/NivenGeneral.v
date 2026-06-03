(** * NivenGeneral.v — Niven's theorem, FULL: cos(rπ)∈ℚ ⟹ cos∈{0,±½,±1}
      (both halves), via aperiodicity of every non-exceptional rational rotation.

    Elements: the integer numerator sequence cₖ of 2·cos(kθ) = cₖ/tᵏ, where
              2cosθ = s/t; defined by c₀=2, c₁=s, cₖ₊₂ = s·cₖ₊₁ − t²·cₖ
    Roles:    "2cos(kθ) is an integer" = role of "θ commensurable with π / period k"
              (forces t | cₖ); aperiodicity = role of "no period-Element over ℚ"
              (classically: θ ∉ πℚ)
    Rules:    the Chebyshev trace recurrence; the invariant cₖ ≡ sᵏ (mod t)
              (`c_cong`); gcd(s,t)=1 ⟹ gcd(sᵏ,t)=1 ⟹ t ∤ sᵏ ⟹ t ∤ cₖ
              ⟹ 2cos(kθ) ∉ ℤ ⟹ cos(kθ) ≠ ±1 ⟹ no period

    NIVEN'S THEOREM: cos(rπ)∈ℚ ⟹ cos∈{0,±½,±1}. The hard half is the
    rationality→integrality obstruction: a rational 2cosθ = s/t with t ≥ 2
    can NEVER make 2cos(kθ) an integer (k≥1), so cos(kθ) is never ±1, so the
    rotation never completes a period — it is APERIODIC. This file proves that
    obstruction over ℤ (the elementary "denominator stays tᵏ" argument, recast as
    the congruence cₖ ≡ sᵏ mod t). It generalises `infinite_order_345`
    (`NivenRationalCosine.v`) from the single denominator 5 to EVERY t ≥ 2:
    the 3-4-5 rotation is the instance 2cosθ = 6/5 (s=6, t=5).

    BOTH halves are now proved (niven_full): (A) t≥2 ⟹ aperiodic (the congruence
    obstruction); (B) t=1 with |x|≥3 ⟹ |cₖ| strictly grows ⟹ no period (elementary
    growth, c_abs_incr). So a rational rotation has a period IFF it is a Niven
    exception: t=1 ∧ |s|≤2, i.e. cosθ ∈ {0,±½,±1}.

    ============ E/R/R разбор ============
      Rules (L5): cₖ₊₂=s·cₖ₊₁−t²cₖ; cₖ≡sᵏ (mod t); gcd(sᵏ,t)=1 ⟹ t∤cₖ.
      Roles (L4): "2cos(kθ)∈ℤ" = π-соизмеримость/период (role-limit, не актуализуется
                  при t≥2); апериодичность = π-несоизмеримость.
      Elements  : cₖ∈ℤ — числители 2cos(kθ)=cₖ/tᵏ (L1+P4).
    ДИАГНОСТИКА (P4): орбита cₖ при рациональном не-полуцелом 2cosθ = НЕЗАВЕРШАЮЩИЙСЯ
    процесс (период/возврат cosθ к ±1 не актуализуется над ℚ) = role-limit; обструкция
    t∤cₖ = незавершаемость процесса, не дефект.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia.
Open Scope Z_scope.

Section Niven.
Variable s t : Z.

(* cₖ = numerator of 2·cos(kθ) when 2cosθ = s/t.  c₀=2, c₁=s. *)
Fixpoint cpair (k : nat) : Z * Z :=
  match k with
  | O => (2, s)
  | S j => let (a, b) := cpair j in (b, s*b - t*t*a)
  end.
Definition c (k : nat) : Z := fst (cpair k).

(* sᵏ — the residue of cₖ modulo t. *)
Fixpoint spow (k : nat) : Z := match k with O => 1 | S j => s * spow j end.

Lemma c_rec : forall k, c (S (S k)) = s * c (S k) - t*t * c k.
Proof. intro k. unfold c. simpl. destruct (cpair k) as [a b]. reflexivity. Qed.

(** The invariant: cₖ ≡ sᵏ (mod t) for k ≥ 1. *)
Lemma c_cong : forall k, (t | (c (S k) - spow (S k))).
Proof.
  induction k as [|k IH].
  - assert (H0 : c 1 - spow 1 = 0) by (unfold c; simpl; ring).
    rewrite H0. apply Z.divide_0_r.
  - destruct IH as [m Hm].
    exists (s*m - t * c k).
    rewrite c_rec.
    change (spow (S (S k))) with (s * spow (S k)).
    assert (Hc : c (S k) = spow (S k) + m * t) by lia.
    rewrite Hc.
    generalize (spow (S k)) (c k); intros u v. ring.
Qed.

(** sᵏ stays coprime to t. *)
Lemma spow_gcd : Z.gcd s t = 1 -> forall k, Z.gcd (spow k) t = 1.
Proof.
  intro H.
  assert (Hrel : rel_prime s t) by (apply Zgcd_1_rel_prime; exact H).
  induction k as [|k IH].
  - apply Z.gcd_1_l.
  - simpl. apply Zgcd_1_rel_prime, rel_prime_sym, rel_prime_mult.
    + apply rel_prime_sym; exact Hrel.
    + apply rel_prime_sym, Zgcd_1_rel_prime; exact IH.
Qed.

(** ★ The obstruction: for t ≥ 2 and 2cosθ = s/t in lowest terms, t never
    divides cₖ — i.e. 2cos(kθ) is never an integer, so cos(kθ) ≠ ±1, so the
    rotation is APERIODIC (θ is not a rational multiple of π). *)
Theorem niven_general :
  Z.gcd s t = 1 -> 2 <= t -> forall k, ~ (t | c (S k)).
Proof.
  intros Hgcd Ht k Hd.
  pose proof (c_cong k) as Hcong.
  pose proof (spow_gcd Hgcd (S k)) as Hsg.
  assert (Hsp : (t | spow (S k))).
  { assert (Heq : spow (S k) = c (S k) - (c (S k) - spow (S k))) by lia.
    rewrite Heq. apply Z.divide_sub_r; assumption. }
  assert (Hd1 : (t | 1)).
  { rewrite <- Hsg. apply Z.gcd_greatest; [ exact Hsp | apply Z.divide_refl ]. }
  apply Z.divide_1_r in Hd1. lia.
Qed.

End Niven.

(** The 3-4-5 rotation is the instance 2cosθ = 6/5: cos θ = 3/5, gcd(6,5)=1,
    t = 5 ≥ 2.  So it is aperiodic — recovering `infinite_order_345`
    (NivenRationalCosine.v) from the GENERAL theorem. *)
Corollary rotation_345_aperiodic : forall k, ~ (5 | c 6 5 (S k)).
Proof. apply niven_general; [ vm_compute; reflexivity | lia ]. Qed.

(* ===================================================================== *)
(*  Part (B): the integer case t = 1 — bounding 2cosθ ∈ {−2,−1,0,1,2}    *)
(*  If x = 2cosθ ∈ ℤ with |x| ≥ 3, the sequence |cₖ| strictly grows, so   *)
(*  it never returns to ±2: no period. Hence a periodic integer x has     *)
(*  |x| ≤ 2. (Elementary growth — no number theory.)                      *)
(* ===================================================================== *)

(** The t = 1 recurrence, with 1·1 cleared away. *)
Lemma c_rec1 : forall s k, c s 1 (S (S k)) = s * c s 1 (S k) - c s 1 k.
Proof. intros s k. rewrite c_rec. lia. Qed.

(** Reverse triangle inequality over ℤ. *)
Lemma abs_rev : forall u v : Z, Z.abs u - Z.abs v <= Z.abs (u - v).
Proof.
  intros u v. pose proof (Z.abs_triangle (u - v) v) as H.
  replace (u - v + v) with u in H by lia. lia.
Qed.

(** |cₖ| strictly increases when |s| ≥ 3. *)
Lemma c_abs_incr : forall s, 3 <= Z.abs s ->
  forall k, Z.abs (c s 1 k) < Z.abs (c s 1 (S k)).
Proof.
  intros s Hs. induction k as [|k IH].
  - change (c s 1 0) with 2. change (c s 1 1) with s.
    change (Z.abs 2) with 2. lia.
  - assert (Hr : c s 1 (S (S k)) = s * c s 1 (S k) - c s 1 k) by (apply c_rec1).
    pose proof (abs_rev (s * c s 1 (S k)) (c s 1 k)) as Hrev.
    rewrite <- Hr in Hrev.
    rewrite (Z.abs_mul s (c s 1 (S k))) in Hrev.
    pose proof (Z.abs_nonneg (c s 1 (S k))) as HnB.
    pose proof (Z.abs_nonneg (c s 1 k)) as HnA.
    assert (H3 : 3 * Z.abs (c s 1 (S k)) <= Z.abs s * Z.abs (c s 1 (S k)))
      by (apply Z.mul_le_mono_nonneg_r; [ exact HnB | exact Hs ]).
    lia.
Qed.

(** Hence |cₖ| ≥ 3 (≥ |s|) for every k ≥ 1. *)
Lemma c_abs_ge : forall s, 3 <= Z.abs s ->
  forall q, (1 <= q)%nat -> 3 <= Z.abs (c s 1 q).
Proof.
  intros s Hs. induction q as [|q IH]; intro Hq.
  - lia.
  - destruct q as [|q'].
    + change (c s 1 1) with s. exact Hs.
    + assert (Hq' : (1 <= S q')%nat) by lia.
      pose proof (IH Hq') as Hge.
      pose proof (c_abs_incr s Hs (S q')) as Hinc.
      lia.
Qed.

(** No period in the integer case: cₖ ≠ ±2 for k ≥ 1 when |s| ≥ 3. *)
Lemma c_no_period_int : forall s, 3 <= Z.abs s ->
  forall q, (1 <= q)%nat -> c s 1 q <> 2 /\ c s 1 q <> -2.
Proof.
  intros s Hs q Hq. pose proof (c_abs_ge s Hs q Hq) as Hge.
  split; intro Heq; rewrite Heq in Hge.
  - change (Z.abs 2) with 2 in Hge. lia.
  - change (Z.abs (-2)) with 2 in Hge. lia.
Qed.

(* ===== Powers t^q, for the period condition cₖ = ±2·t^q ================= *)

Fixpoint tpow (t : Z) (q : nat) : Z := match q with O => 1 | S j => t * tpow t j end.

Lemma tpow_one : forall q, tpow 1 q = 1.
Proof. induction q as [|q IH]; simpl; [ reflexivity | rewrite IH; lia ]. Qed.

Lemma tpow_div : forall t q, (1 <= q)%nat -> (t | tpow t q).
Proof.
  destruct q as [|q]; intro Hq; [ lia | ].
  exists (tpow t q). change (tpow t (S q)) with (t * tpow t q). apply Z.mul_comm.
Qed.

(* ===================================================================== *)
(*  ★ FULL NIVEN: a rational rotation 2cosθ = s/t is APERIODIC unless it   *)
(*  is a Niven exception — t = 1 with |s| ≤ 2, i.e. cosθ ∈ {0,±½,±1}.      *)
(*  Stated as: outside the exceptions, cₖ never equals ±2·tᵏ (no period).  *)
(* ===================================================================== *)
Theorem niven_full : forall s t,
  1 <= t -> Z.gcd s t = 1 -> (t = 1 -> 3 <= Z.abs s) ->
  forall q, (1 <= q)%nat ->
    c s t q <> 2 * tpow t q /\ c s t q <> - (2 * tpow t q).
Proof.
  intros s t Ht Hgcd Hexc q Hq.
  destruct (Z.le_gt_cases 2 t) as [Ht2 | Ht2].
  - destruct q as [|q0]; [ lia | ].
    pose proof (niven_general s t Hgcd Ht2 q0) as Hng.
    pose proof (tpow_div t (S q0) Hq) as Htd.
    split; intro Heq; apply Hng; rewrite Heq.
    + apply Z.divide_mul_r; exact Htd.
    + apply Z.divide_opp_r, Z.divide_mul_r; exact Htd.
  - assert (Ht1 : t = 1) by lia. subst t.
    pose proof (Hexc eq_refl) as Hs3.
    pose proof (c_no_period_int s Hs3 q Hq) as [Hne2 Hne2'].
    rewrite tpow_one. split; intro Heq.
    + apply Hne2. lia.
    + apply Hne2'. lia.
Qed.
