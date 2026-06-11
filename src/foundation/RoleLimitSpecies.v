(** * RoleLimitSpecies.v — Two species of role-limit (H1 stratified)

    Elements: size-sequences  N : nat -> Q  (the norm at each finite stage —
              enstrophy Omega_K, partial sum, modulus of an iterate). Each N n is
              an actual, computable rational; the limit is never actual (P4).
    Roles:    RegularLimit (bounded, Species I — does not escape) vs
              SingularLimit (unbounded, Species II — escapes). These are the TWO
              strata of the finitization boundary H1.
    Rules:    the partition is EXHAUSTIVE only via L3 (excluded middle on
              boundedness) — species_dichotomy is an instance of `classic`.
              The dial is the per-step growth ratio: c<1 (subcritical) FORCES
              Species I (decay_regular); r>1 (supercritical) FORCES Species II;
              r=1 (critical/marginal) — neither certificate fires, finer structure
              decides (cap is bounded, lin is unbounded, BOTH at the margin).
    P4:       finite stages are actual & bounded; "uniform-over-stages bound" is a
              statement over ALL stages = the role-limit = potential. NS enstrophy
              is the r=1 critical member: classified by L3 (regular-or-singular),
              but WHICH side is the Millennium gap.

    Interlock (no duplication): Species I's strongest certificate IS the project's
    Banach machinery, reused verbatim — is_cauchy (CauchyReal) and iterate_is_cauchy
    (FixedPoint) feed cauchy_regular / contraction_regular. RegularLimit (bounded)
    sits ABOVE Cauchy as the weaker, blow-up-relevant predicate.

    STATUS: 39 Qed, 0 Admitted, 0 axioms beyond `classic` (L3)
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith Arith.
From Stdlib Require Import Lqa.
From ToS Require Import ToS_Axioms.   (* classic = L3 *)
From ToS Require Import CauchyReal.   (* is_cauchy *)
From ToS Require Import FixedPoint.   (* is_contraction, iterate, iterate_is_cauchy *)
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: the two species (genuine predicates, not epistemic)        *)
(* ================================================================== *)

(** Species I: the role-limit does not escape — the size-sequence is bounded. *)
Definition RegularLimit (N : nat -> Q) : Prop :=
  exists M : Q, forall n : nat, N n <= M.

(** Species II: the role-limit escapes — the size-sequence is unbounded. *)
Definition SingularLimit (N : nat -> Q) : Prop :=
  forall M : Q, exists n : nat, M < N n.

(** Mutually exclusive (constructive). *)
Lemma regular_not_singular : forall N, RegularLimit N -> ~ SingularLimit N.
Proof.
  intros N [M HM] Hs. destruct (Hs M) as [n Hn].
  apply (Qlt_irrefl M). apply Qlt_le_trans with (N n); [ exact Hn | exact (HM n) ].
Qed.

(** ~RegularLimit -> SingularLimit (the De Morgan push through forall needs L3). *)
Lemma not_regular_singular : forall N, ~ RegularLimit N -> SingularLimit N.
Proof.
  intros N Hnr M.
  destruct (classic (exists n, M < N n)) as [He | He].
  - exact He.
  - exfalso. apply Hnr. exists M. intro n.
    destruct (Qlt_le_dec M (N n)) as [Hlt | Hle].
    + exfalso. apply He. exists n. exact Hlt.
    + exact Hle.
Qed.

(** ★ The partition {Species I, Species II} is exhaustive — and this IS L3. ★ *)
Theorem species_dichotomy : forall N, RegularLimit N \/ SingularLimit N.
Proof.
  intro N. destruct (classic (RegularLimit N)) as [H | H].
  - left; exact H.
  - right; apply not_regular_singular; exact H.
Qed.

(* ================================================================== *)
(*  Part II: the dial — subcritical certificate (c<1 -> Species I)      *)
(* ================================================================== *)

Definition decays_geometrically (N : nat -> Q) (c : Q) : Prop :=
  0 <= c /\ c < 1 /\ (forall n, 0 <= N n) /\ (forall n, N (S n) <= c * N n).

Lemma decay_monotone : forall N c, decays_geometrically N c ->
  forall n, N (S n) <= N n.
Proof.
  intros N c (Hc0 & Hc1 & Hnn & Hstep) n.
  apply Qle_trans with (c * N n); [ exact (Hstep n) | ].
  apply Qle_trans with (1 * N n).
  - apply Qmult_le_compat_r; [ lra | exact (Hnn n) ].
  - rewrite Qmult_1_l; apply Qle_refl.
Qed.

Lemma decay_regular : forall N c, decays_geometrically N c -> RegularLimit N.
Proof.
  intros N c Hd. exists (N O). intro n. induction n.
  - apply Qle_refl.
  - apply Qle_trans with (N n); [ apply (decay_monotone N c Hd) | exact IHn ].
Qed.

(* ================================================================== *)
(*  Part III: interlock with CauchyReal / FixedPoint (no duplication)  *)
(* ================================================================== *)

(** A self-contained max (avoids name-guessing on Qminmax). *)
Definition qmax (x y : Q) : Q := if Qlt_le_dec x y then y else x.
Lemma qmax_l : forall x y, x <= qmax x y.
Proof. intros x y. unfold qmax. destruct (Qlt_le_dec x y); lra. Qed.
Lemma qmax_r : forall x y, y <= qmax x y.
Proof. intros x y. unfold qmax. destruct (Qlt_le_dec x y); lra. Qed.

Fixpoint maxabs (a : nat -> Q) (N : nat) : Q :=
  match N with
  | O => 0
  | S k => qmax (maxabs a k) (Qabs (a k))
  end.

Lemma maxabs_ge : forall a N n, (n < N)%nat -> Qabs (a n) <= maxabs a N.
Proof.
  intros a N. induction N as [|k IH]; intros n Hn.
  - exfalso; lia.
  - simpl. destruct (Nat.eq_dec n k) as [Heq | Hneq].
    + subst. apply qmax_r.
    + apply Qle_trans with (maxabs a k); [ apply IH; lia | apply qmax_l ].
Qed.

(** ★ Bridge: convergent (Cauchy) ⟹ bounded (RegularLimit). Cauchy is STRONGER. ★ *)
Lemma cauchy_regular : forall a, is_cauchy a -> RegularLimit (fun n => Qabs (a n)).
Proof.
  intros a Hcau.
  assert (H1 : 0 < 1) by lra.
  destruct (Hcau 1 H1) as [N HN].
  exists (qmax (maxabs a N) (Qabs (a N) + 1)).
  intro n. simpl.
  destruct (le_lt_dec N n) as [Hge | Hlt].
  - apply Qle_trans with (Qabs (a N) + 1); [ | apply qmax_r ].
    assert (Hd : Qabs (a n - a N) < 1) by (apply HN; [ exact Hge | apply Nat.le_refl ]).
    assert (Htri := Qabs_triangle_reverse (a n) (a N)).
    lra.
  - apply Qle_trans with (maxabs a N); [ apply maxabs_ge; exact Hlt | apply qmax_l ].
Qed.

(** ★ Contraction ⟹ Species I, factoring through the project's Banach theorem. ★ *)
Theorem contraction_regular : forall f a b c x,
  is_contraction f a b c -> a <= x -> x <= b ->
  RegularLimit (fun n => Qabs (iterate f x n)).
Proof.
  intros f a b c x Hc Hxa Hxb.
  apply cauchy_regular.
  exact (iterate_is_cauchy f a b c x Hc Hxa Hxb).
Qed.

(* ================================================================== *)
(*  Part IV: witnesses — both species inhabited, BOTH at the margin r=1 *)
(* ================================================================== *)

(** Archimedean: nat is unbounded in Q. *)
Lemma Q_unbounded_nat : forall q : Q, exists n : nat, q < inject_Z (Z.of_nat n).
Proof.
  intro q. destruct (Qarchimedean q) as [p Hp].
  exists (Pos.to_nat p). rewrite positive_nat_Z. exact Hp.
Qed.

Lemma injZ_S_pos : forall n : nat, 0 < inject_Z (Z.of_nat (S n)).
Proof.
  intro n. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma injZ_S_succ : forall n : nat,
  inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ. unfold Z.succ.
  rewrite inject_Z_plus. reflexivity.
Qed.

(** Subcritical Species-I witness: halfpow n = (1/2)^n  (dial c = 1/2 < 1). *)
Fixpoint halfpow (n : nat) : Q :=
  match n with O => 1 | S k => (1#2) * halfpow k end.

Lemma halfpow_nonneg : forall n, 0 <= halfpow n.
Proof.
  induction n; simpl; [ lra | apply Qmult_le_0_compat; [ lra | exact IHn ] ].
Qed.

Lemma half_nonneg : 0 <= (1#2).
Proof. rewrite Qle_alt. discriminate. Qed.

Lemma half_lt_one : (1#2) < 1.
Proof. rewrite Qlt_alt. reflexivity. Qed.

Lemma halfpow_step : forall n, halfpow (S n) <= (1#2) * halfpow n.
Proof. intro n. simpl. apply Qle_refl. Qed.

Lemma halfpow_decay : decays_geometrically halfpow (1#2).
Proof.
  unfold decays_geometrically.
  exact (conj half_nonneg (conj half_lt_one (conj halfpow_nonneg halfpow_step))).
Qed.

Lemma halfpow_regular : RegularLimit halfpow.
Proof. apply (decay_regular halfpow (1#2) halfpow_decay). Qed.

(** Marginal (r=1) Species-I witness: cap n = 2 - 1/(n+1) -> 2, bounded by 2. *)
Definition cap (n : nat) : Q := 2 - / inject_Z (Z.of_nat (S n)).

Lemma cap_regular : RegularLimit cap.
Proof.
  exists 2. intro n. unfold cap.
  assert (Hpos : 0 < inject_Z (Z.of_nat (S n))) by apply injZ_S_pos.
  assert (Hinv : 0 < / inject_Z (Z.of_nat (S n))) by (apply Qinv_lt_0_compat; exact Hpos).
  lra.
Qed.

(** Marginal (r=1) Species-II witness: lin n = n, unbounded but sub-geometric. *)
Definition lin (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma lin_singular : SingularLimit lin.
Proof. intro M. destruct (Q_unbounded_nat M) as [n Hn]. exists n. unfold lin. exact Hn. Qed.

(** Supercritical certificate (dial r>1): geometric growth ⟹ Species II. *)
Definition grows_geometrically (N : nat -> Q) (r : Q) : Prop :=
  1 < r /\ 0 < N O /\ (forall n, r * N n <= N (S n)).

Lemma grow_pos : forall N r, grows_geometrically N r -> forall n, 0 < N n.
Proof.
  intros N r (Hr & H0 & Hstep) n. induction n.
  - exact H0.
  - apply Qlt_le_trans with (r * N n);
      [ apply Qmult_lt_0_compat; [ lra | exact IHn ] | exact (Hstep n) ].
Qed.

Lemma grow_ge_init : forall N r, grows_geometrically N r -> forall n, N O <= N n.
Proof.
  intros N r Hg n. assert (Hpos := grow_pos N r Hg).
  destruct Hg as (Hr & H0 & Hstep). induction n.
  - apply Qle_refl.
  - apply Qle_trans with (N n); [ exact IHn | ].
    apply Qle_trans with (r * N n); [ | exact (Hstep n) ].
    rewrite <- (Qmult_1_l (N n)) at 1.
    apply Qmult_le_compat_r; [ lra | apply Qlt_le_weak; apply Hpos ].
Qed.

Lemma grow_additive : forall N r, grows_geometrically N r ->
  forall n, N O + inject_Z (Z.of_nat n) * ((r - 1) * N O) <= N n.
Proof.
  intros N r Hg. assert (Hge := grow_ge_init N r Hg).
  destruct Hg as (Hr & H0 & Hstep).
  set (d := (r - 1) * N O).
  induction n.
  - replace (inject_Z (Z.of_nat 0)) with 0 by reflexivity. lra.
  - rewrite injZ_S_succ.
    assert (Hexp : (inject_Z (Z.of_nat n) + 1) * d ==
                   inject_Z (Z.of_nat n) * d + d) by ring.
    rewrite Hexp.
    assert (Haux : d <= (r - 1) * N n).
    { unfold d. rewrite (Qmult_comm (r-1) (N O)), (Qmult_comm (r-1) (N n)).
      apply Qmult_le_compat_r; [ apply Hge | lra ]. }
    assert (Hring : N n + (r - 1) * N n == r * N n) by ring.
    specialize (Hstep n). lra.
Qed.

Lemma growth_singular : forall N r, grows_geometrically N r -> SingularLimit N.
Proof.
  intros N r Hg M. assert (Hadd := grow_additive N r Hg).
  destruct Hg as (Hr & H0 & Hstep).
  set (d := (r - 1) * N O).
  assert (Hd : 0 < d) by (unfold d; apply Qmult_lt_0_compat; lra).
  assert (Hdne : ~ d == 0) by (intro Hc; rewrite Hc in Hd; exact (Qlt_irrefl 0 Hd)).
  destruct (Q_unbounded_nat ((M - N O) / d)) as [n Hn].
  exists n.
  apply Qlt_le_trans with (N O + inject_Z (Z.of_nat n) * d).
  - assert (Hmul : (M - N O) / d * d < inject_Z (Z.of_nat n) * d).
    { apply (proj2 (Qmult_lt_r _ _ d Hd)). exact Hn. }
    assert (Hsimp : (M - N O) / d * d == M - N O).
    { unfold Qdiv. rewrite <- Qmult_assoc, (Qmult_comm (/d) d), Qmult_inv_r;
        [ ring | exact Hdne ]. }
    lra.
  - unfold d. exact (Hadd n).
Qed.

(** Supercritical Species-II witness: pow2 n = 2^n. *)
Fixpoint pow2 (n : nat) : Q := match n with O => 1 | S k => 2 * pow2 k end.

Lemma pow2_grows : grows_geometrically pow2 2.
Proof.
  unfold grows_geometrically. split; [ | split ].
  - rewrite Qlt_alt; reflexivity.
  - simpl. rewrite Qlt_alt; reflexivity.
  - intro n. simpl. apply Qle_refl.
Qed.

Lemma pow2_singular : SingularLimit pow2.
Proof. apply (growth_singular pow2 2 pow2_grows). Qed.

(** Shared helper: inversion is antitone on the positives. *)
Lemma Qinv_antitone : forall a b, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  assert (Hb : 0 < b) by (apply Qlt_le_trans with a; assumption).
  assert (Hz : 0 < a * b) by (apply Qmult_lt_0_compat; assumption).
  apply (proj1 (Qmult_le_r (/ b) (/ a) (a * b) Hz)).
  assert (E1 : / b * (a * b) == a) by (field; lra).
  assert (E2 : / a * (a * b) == b) by (field; lra).
  rewrite E1, E2. exact Hab.
Qed.

(* ---- Canonical convergent Species-I witness: basel n = sum_{j=1}^n 1/j^2 ---- *)
Fixpoint basel (n : nat) : Q :=
  match n with
  | O => 0
  | S k => basel k + / (inject_Z (Z.of_nat (S k)) * inject_Z (Z.of_nat (S k)))
  end.

Lemma basel_S : forall k,
  basel (S k) == basel k + / (inject_Z (Z.of_nat (S k)) * inject_Z (Z.of_nat (S k))).
Proof. intro k. reflexivity. Qed.

(** Telescoping: 1/k^2 <= 1/(k-1) - 1/k for k>=2 gives basel n <= 2 - 1/n. *)
Lemma basel_bound : forall n, basel (S n) <= 2 - / inject_Z (Z.of_nat (S n)).
Proof.
  induction n.
  - assert (Hb1 : basel (S 0) == 1) by (vm_compute; reflexivity).
    assert (Hr : 2 - / inject_Z (Z.of_nat (S 0)) == 1) by (vm_compute; reflexivity).
    rewrite Hb1, Hr. apply Qle_refl.
  - rewrite (basel_S (S n)).
    set (p := inject_Z (Z.of_nat (S n))) in *.
    set (q := inject_Z (Z.of_nat (S (S n)))) in *.
    assert (Hp : 0 < p) by (unfold p; apply injZ_S_pos).
    assert (Hq : 0 < q) by (unfold q; apply injZ_S_pos).
    assert (Hpq : q == p + 1) by (unfold p, q; apply injZ_S_succ).
    assert (Hdiff : / p - / q == / (p * q)) by (rewrite Hpq; field; lra).
    assert (Hkey : / (q * q) <= / p - / q).
    { rewrite Hdiff. apply Qinv_antitone.
      - apply Qmult_lt_0_compat; assumption.
      - apply Qmult_le_compat_r; [ rewrite Hpq; lra | apply Qlt_le_weak; exact Hq ]. }
    lra.
Qed.

Lemma basel_regular : RegularLimit basel.
Proof.
  exists 2. intro n. destruct n as [|m].
  - simpl. rewrite Qle_alt. discriminate.
  - apply Qle_trans with (2 - / inject_Z (Z.of_nat (S m))); [ apply basel_bound | ].
    assert (Hpos : 0 < / inject_Z (Z.of_nat (S m)))
      by (apply Qinv_lt_0_compat; apply injZ_S_pos).
    lra.
Qed.

(* ---- Canonical divergent Species-II witness: harmonic n = sum_{j=1}^n 1/j ---- *)
Fixpoint harmonic (n : nat) : Q :=
  match n with O => 0 | S k => harmonic k + / inject_Z (Z.of_nat (S k)) end.

Lemma harmonic_S : forall k,
  harmonic (S k) == harmonic k + / inject_Z (Z.of_nat (S k)).
Proof. intro k. reflexivity. Qed.

(** Each of the k terms in (p, p+k] is >= 1/(p+k), so the block adds >= k/(p+k). *)
Lemma harmonic_block : forall p k, (1 <= p)%nat ->
  harmonic p + inject_Z (Z.of_nat k) * / inject_Z (Z.of_nat (p + k)) <= harmonic (p + k).
Proof.
  intros p k Hp. induction k.
  - replace (p + 0)%nat with p by lia.
    replace (inject_Z (Z.of_nat 0)) with 0 by reflexivity.
    rewrite Qmult_0_l, Qplus_0_r. apply Qle_refl.
  - replace (p + S k)%nat with (S (p + k)) by lia.
    rewrite (harmonic_S (p + k)).
    set (A := inject_Z (Z.of_nat (p + k))) in *.
    set (B := inject_Z (Z.of_nat (S (p + k)))).
    assert (HA : 0 < A)
      by (unfold A; change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
    assert (HBA : B == A + 1) by (unfold A, B; apply injZ_S_succ).
    assert (Hinv : / B <= / A) by (apply Qinv_antitone; [ exact HA | rewrite HBA; lra ]).
    assert (Hkk : 0 <= inject_Z (Z.of_nat k))
      by (change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia).
    assert (Hmul : inject_Z (Z.of_nat k) * / B <= inject_Z (Z.of_nat k) * / A).
    { rewrite (Qmult_comm (inject_Z (Z.of_nat k)) (/ B)),
              (Qmult_comm (inject_Z (Z.of_nat k)) (/ A)).
      apply Qmult_le_compat_r; [ exact Hinv | exact Hkk ]. }
    assert (HSkk : inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1) by apply injZ_S_succ.
    assert (Hexp : inject_Z (Z.of_nat (S k)) * / B ==
                   inject_Z (Z.of_nat k) * / B + / B) by (rewrite HSkk; ring).
    rewrite Hexp. lra.
Qed.

Fixpoint twopow (m : nat) : nat :=
  match m with O => 1%nat | S k => (twopow k + twopow k)%nat end.

Lemma twopow_pos : forall m, (1 <= twopow m)%nat.
Proof. induction m; simpl; lia. Qed.

(** Doubling: harmonic(2^m) >= 1 + m/2 (each doubling adds a >=1/2 block). *)
Lemma harmonic_double : forall m,
  1 + inject_Z (Z.of_nat m) * (1#2) <= harmonic (twopow m).
Proof.
  induction m.
  - assert (Hh : harmonic (twopow 0) == 1) by (vm_compute; reflexivity).
    assert (Hl : 1 + inject_Z (Z.of_nat 0) * (1#2) == 1) by (vm_compute; reflexivity).
    rewrite Hh, Hl. apply Qle_refl.
  - simpl (twopow (S m)).
    assert (Hblk := harmonic_block (twopow m) (twopow m) (twopow_pos m)).
    assert (Hhalf : inject_Z (Z.of_nat (twopow m)) *
                    / inject_Z (Z.of_nat (twopow m + twopow m)) == (1#2)).
    { assert (Ha : 0 < inject_Z (Z.of_nat (twopow m))).
      { change 0 with (inject_Z 0). rewrite <- Zlt_Qlt.
        assert (1 <= twopow m)%nat by apply twopow_pos. lia. }
      assert (Hsum : inject_Z (Z.of_nat (twopow m + twopow m)) ==
                     inject_Z (Z.of_nat (twopow m)) + inject_Z (Z.of_nat (twopow m)))
        by (rewrite Nat2Z.inj_add, inject_Z_plus; reflexivity).
      rewrite Hsum. field. lra. }
    rewrite Hhalf in Hblk.
    assert (Hexp : inject_Z (Z.of_nat (S m)) * (1#2) ==
                   inject_Z (Z.of_nat m) * (1#2) + (1#2))
      by (assert (HSm : inject_Z (Z.of_nat (S m)) == inject_Z (Z.of_nat m) + 1)
            by apply injZ_S_succ; rewrite HSm; ring).
    rewrite Hexp. lra.
Qed.

Lemma harmonic_singular : SingularLimit harmonic.
Proof.
  intro M. destruct (Q_unbounded_nat (2 * (M - 1))) as [m Hm].
  exists (twopow m).
  apply Qlt_le_trans with (1 + inject_Z (Z.of_nat m) * (1#2));
    [ | apply harmonic_double ].
  lra.
Qed.

(** ★ The classic boundary pair: Sigma 1/n^2 (Species I) vs Sigma 1/n (Species II). ★ *)
Theorem canonical_witnesses : RegularLimit basel /\ SingularLimit harmonic.
Proof. split; [ exact basel_regular | exact harmonic_singular ]. Qed.

(* ================================================================== *)
(*  Part V: NS placement (honest — classified by L3, which-side open)   *)
(* ================================================================== *)

(** Let Omega K be the enstrophy of the K-truncation (each finite — the
    Galerkin energy bound). "No blow-up / global regularity" IS RegularLimit Omega.
    By species_dichotomy (L3) NS is DEFINITELY one species; criticality (r=1) means
    neither dial certificate fires — that undecided disjunct is the Millennium gap. *)
Definition ns_regular (Omega : nat -> Q) : Prop := RegularLimit Omega.

Theorem ns_is_classified : forall Omega, ns_regular Omega \/ SingularLimit Omega.
Proof. intro Omega. unfold ns_regular. apply species_dichotomy. Qed.

(* ================================================================== *)
(*  Part VI: capstone                                                  *)
(* ================================================================== *)

Theorem role_limit_species_capstone :
  (forall N, RegularLimit N \/ SingularLimit N) /\                  (* exhaustive = L3 *)
  (forall N, RegularLimit N -> ~ SingularLimit N) /\                (* exclusive *)
  (forall N c, decays_geometrically N c -> RegularLimit N) /\       (* subcritical -> I *)
  (forall N r, grows_geometrically N r -> SingularLimit N) /\       (* supercritical -> II *)
  (forall a, is_cauchy a -> RegularLimit (fun n => Qabs (a n))) /\  (* convergent -> bounded *)
  RegularLimit cap /\ SingularLimit lin.                            (* r=1: BOTH species *)
Proof.
  repeat split.
  - exact species_dichotomy.
  - exact regular_not_singular.
  - exact decay_regular.
  - exact growth_singular.
  - exact cauchy_regular.
  - exact cap_regular.
  - exact lin_singular.
Qed.

Print Assumptions species_dichotomy.
Print Assumptions role_limit_species_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  39 Qed, 0 Admitted, 0 axioms beyond classic (L3).                         *)
(*  H1 stratified: Species I (bounded, dissolved-by-process) vs Species II    *)
(*  (unbounded, the open analytic stratum). NS enstrophy = r=1 critical       *)
(*  member, classified by L3, decided by finer structure (cancellation).      *)
(* ========================================================================= *)
