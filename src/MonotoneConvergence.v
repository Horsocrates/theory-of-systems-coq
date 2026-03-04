(* ========================================================================= *)
(*            MONOTONE CONVERGENCE THEOREM                                  *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove the Monotone Convergence Theorem:                        *)
(*    - Q-level: increasing bounded rational sequences are Cauchy            *)
(*    - CauchySeq construction from such sequences                          *)
(*    - Squeeze theorem for Cauchy equivalence                              *)
(*    - cauchy_le transitivity and sequence ordering                         *)
(*                                                                          *)
(*  AXIOMS: classic (Law of Excluded Middle) — required for MCT over Q      *)
(*          MCT is equivalent to LPO in constructive settings               *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

From ToS Require Import CauchyReal.
From ToS Require Import Completeness.

Open Scope Q_scope.
Local Open Scope cauchy_scope.

(* ========================================================================= *)
(* SECTION 1: Q-LEVEL HELPERS                                                *)
(* ========================================================================= *)

(** Monotone increasing implies d(n) <= d(m) for n <= m *)
Lemma inc_le : forall (d : nat -> Q),
  (forall n, d n <= d (S n)) ->
  forall m n, (n <= m)%nat -> d n <= d m.
Proof.
  intros d Hinc m. induction m; intros n Hnm.
  - replace n with 0%nat by lia. lra.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne].
    + lra.
    + assert (Hle : (n <= m)%nat) by lia.
      specialize (IHm n Hle).
      specialize (Hinc m). lra.
Qed.

(** Monotone decreasing implies d(m) <= d(n) for n <= m *)
Lemma dec_le : forall (d : nat -> Q),
  (forall n, d (S n) <= d n) ->
  forall m n, (n <= m)%nat -> d m <= d n.
Proof.
  intros d Hdec m. induction m; intros n Hnm.
  - replace n with 0%nat by lia. lra.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne].
    + lra.
    + assert (Hle : (n <= m)%nat) by lia.
      specialize (IHm n Hle).
      specialize (Hdec m). lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: Q-LEVEL MCT (uses classical logic)                             *)
(*                                                                           *)
(*  Key theorem: an increasing bounded Q-sequence is Cauchy.                 *)
(*  Proof by contradiction: if not Cauchy, can extract arbitrarily many      *)
(*  jumps of size >= eps, which exceeds the bound.                           *)
(* ========================================================================= *)

(** Archimedean helper: for any gap and eps > 0, exists K with K*eps > gap *)
Lemma nat_archimedean : forall (gap eps : Q),
  0 < eps -> exists K : nat, gap < inject_Z (Z.of_nat K) * eps.
Proof.
  intros [gn gd] [en ed] Heps.
  unfold Qlt in Heps. simpl in Heps.
  assert (Hen : (en > 0)%Z) by lia.
  (* Take K = max(0, gn * Z.pos ed / (en * Z.pos gd)) + 1 *)
  set (denom := (en * Z.pos gd)%Z).
  assert (Hdenom : (denom > 0)%Z) by (unfold denom; lia).
  set (numer := (gn * Z.pos ed)%Z).
  set (K := (Z.max 0 (numer / denom) + 1)%Z).
  assert (HK_pos : (K > 0)%Z) by (unfold K; lia).
  exists (Z.to_nat K).
  unfold Qlt, Qmult, inject_Z. simpl.
  rewrite Z2Nat.id by lia.
  (* Goal: gn * (Z.pos ed * 1) < K * en * (1 * Z.pos gd) *)
  assert (Hle : (denom * (numer / denom) <= numer)%Z)
    by (apply Z.mul_div_le; lia).
  assert (HK_ge : (K >= numer / denom + 1)%Z) by (unfold K; lia).
  assert (HK_denom : (K * denom > numer)%Z).
  { assert (Hmod := Z.div_mod numer denom ltac:(lia)).
    assert (Hmod_bound := Z.mod_pos_bound numer denom ltac:(lia)).
    nia. }
  unfold numer, denom in HK_denom. nia.
Qed.

(** Increasing unbounded: if after every index there's a jump >= eps,
    then d exceeds d(0) + K*eps for any K. *)
Lemma jumps_unbounded : forall (d : nat -> Q) (eps : Q) (K : nat),
  (forall n, d n <= d (S n)) ->
  0 < eps ->
  (forall N, exists m, (N <= m)%nat /\ d m >= d N + eps) ->
  exists m, d m >= d 0%nat + inject_Z (Z.of_nat (S K)) * eps.
Proof.
  intros d eps K Hinc Heps Hbig.
  induction K.
  - (* K = 0: need d m >= d 0 + 1 * eps *)
    destruct (Hbig 0%nat) as [m [Hm Hdm]].
    exists m.
    assert (H1 : inject_Z (Z.of_nat 1) * eps == eps).
    { simpl Z.of_nat. unfold inject_Z. ring. }
    rewrite H1. exact Hdm.
  - (* K -> S K *)
    destruct IHK as [m0 Hm0].
    destruct (Hbig m0) as [m1 [Hm1 Hdm1]].
    exists m1.
    assert (Hdm0_le : d m0 <= d m1) by (apply inc_le; assumption).
    (* d m1 >= d m0 + eps >= d 0 + (S K)*eps + eps = d 0 + (S(S K))*eps *)
    assert (Hstep : inject_Z (Z.of_nat (S (S K))) * eps ==
                    inject_Z (Z.of_nat (S K)) * eps + eps).
    { rewrite Nat2Z.inj_succ.
      setoid_replace (inject_Z (Z.succ (Z.of_nat (S K))))
        with (inject_Z (Z.of_nat (S K)) + 1)
        by (unfold inject_Z, Qeq, Qplus; simpl; lia).
      ring. }
    rewrite Hstep. lra.
Qed.

(** MAIN THEOREM: Increasing bounded Q-sequence is Cauchy.
    Uses classical logic (NNPP, not_all_ex_not). *)
Theorem q_inc_bounded_cauchy : forall (d : nat -> Q) (B : Q),
  (forall n, d n <= d (S n)) ->
  (forall n, d n <= B) ->
  is_cauchy d.
Proof.
  intros d B Hinc Hbnd eps Heps.
  (* By contradiction *)
  apply NNPP. intro Hncauchy.
  (* Derive: after every index, there's a jump >= eps *)
  assert (Hbig : forall N, exists m, (N <= m)%nat /\ d m >= d N + eps).
  { intro N. apply NNPP. intro Hnot.
    apply Hncauchy. exists N.
    intros m n Hm Hn.
    (* From ¬(∃m ≥ N, d m ≥ d N + eps): ∀m ≥ N: d m < d N + eps *)
    assert (Hall : forall m0, (N <= m0)%nat -> d m0 < d N + eps).
    { intros m0 Hm0. apply NNPP. intro Hnot2.
      apply Hnot. exists m0. split; [exact Hm0 | lra]. }
    assert (H1 : d m < d N + eps) by (apply Hall; exact Hm).
    assert (H2 : d n < d N + eps) by (apply Hall; exact Hn).
    assert (HdN_m : d N <= d m) by (apply inc_le; assumption).
    assert (HdN_n : d N <= d n) by (apply inc_le; assumption).
    apply Qabs_lt_bound; lra. }
  (* Get K such that (S K)*eps > B - d 0 *)
  destruct (nat_archimedean (B - d 0%nat) eps Heps) as [K HK].
  (* From jumps_unbounded: exists m, d m >= d 0 + (S K)*eps *)
  destruct (jumps_unbounded d eps K Hinc Heps Hbig) as [m Hm].
  (* But d m <= B, so d 0 + (S K)*eps <= B, i.e., (S K)*eps <= B - d 0 *)
  assert (HdB : d m <= B) by (apply Hbnd).
  (* Contradiction: B - d 0 < (S K)*eps but (S K)*eps <= B - d 0 *)
  assert (HSK_bound : inject_Z (Z.of_nat (S K)) * eps > B - d 0%nat).
  { (* (S K)*eps >= K*eps + eps > (B - d 0) *)
    assert (Hstep : inject_Z (Z.of_nat (S K)) * eps ==
                    inject_Z (Z.of_nat K) * eps + eps).
    { rewrite Nat2Z.inj_succ.
      setoid_replace (inject_Z (Z.succ (Z.of_nat K)))
        with (inject_Z (Z.of_nat K) + 1)
        by (unfold inject_Z, Qeq, Qplus; simpl; lia).
      ring. }
    lra. }
  lra.
Qed.

(** Decreasing bounded Q-sequence is Cauchy (dual) *)
Theorem q_dec_bounded_cauchy : forall (d : nat -> Q) (B : Q),
  (forall n, d (S n) <= d n) ->
  (forall n, B <= d n) ->
  is_cauchy d.
Proof.
  intros d B Hdec Hbnd.
  (* Apply increasing MCT to the negated sequence *)
  assert (Hcauchy_neg : is_cauchy (fun n => - d n)).
  { apply q_inc_bounded_cauchy with (- B).
    - intros n. specialize (Hdec n). lra.
    - intros n. specialize (Hbnd n). lra. }
  (* is_cauchy (fun n => -d n) implies is_cauchy d *)
  intros eps Heps.
  destruct (Hcauchy_neg eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  assert (Heq : Qabs (- d m - - d n) == Qabs (d m - d n)).
  { setoid_replace (- d m - - d n) with (-(d m - d n)) by ring.
    apply Qabs_opp. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: CAUCHY SEQUENCE CONSTRUCTIONS                                  *)
(* ========================================================================= *)

(** Construct a CauchySeq from an increasing bounded Q-sequence *)
Definition mct_limit_inc (d : nat -> Q) (B : Q)
  (Hinc : forall n, d n <= d (S n))
  (Hbnd : forall n, d n <= B) : CauchySeq :=
  mkCauchy d (q_inc_bounded_cauchy d B Hinc Hbnd).

(** Construct a CauchySeq from a decreasing bounded Q-sequence *)
Definition mct_limit_dec (d : nat -> Q) (B : Q)
  (Hdec : forall n, d (S n) <= d n)
  (Hbnd : forall n, B <= d n) : CauchySeq :=
  mkCauchy d (q_dec_bounded_cauchy d B Hdec Hbnd).

(** The increasing limit is an upper bound: d(n) <= L for all n *)
Lemma mct_inc_upper_bound : forall d B Hinc Hbnd n,
  cauchy_le (cauchy_const (d n)) (mct_limit_inc d B Hinc Hbnd).
Proof.
  intros d B Hinc Hbnd n.
  intros eps Heps.
  (* Need: exists N, forall k >= N, d(n) < d(k) + eps *)
  exists n. intros k Hk.
  simpl.
  assert (Hdn_dk : d n <= d k) by (apply inc_le; assumption).
  lra.
Qed.

(** The increasing limit is the least upper bound:
    if cauchy_le (cauchy_const (d n)) C for all n, then cauchy_le L C *)
Lemma mct_inc_least : forall d B Hinc Hbnd (C : CauchySeq),
  (forall n, cauchy_le (cauchy_const (d n)) C) ->
  cauchy_le (mct_limit_inc d B Hinc Hbnd) C.
Proof.
  intros d B Hinc Hbnd C HC.
  intros eps Heps.
  (* C is above all d(n), and L(k) = d(k), so L(k) < C(k) + eps *)
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  (* Get N1 from HC for d(k) with eps/2 — but we need uniform k *)
  (* Use the fact that L(k) = d(k), and cauchy_le (cauchy_const (d k)) C *)
  (* gives: exists M_k, forall j >= M_k: d(k) < C(j) + eps/2 *)
  (* Take j = k (if k >= M_k): d(k) < C(k) + eps/2 *)
  (* Need k >= M_k, but M_k depends on k... *)
  (* Alternative: use HC(k) with eps/2 to get M_k, then take k >= M_k *)
  (* Since we output an existential, we can pick K large enough *)
  destruct (HC 0%nat (eps * (1#2)) Heps2) as [M0 HM0].
  (* HM0: forall j >= M0, d(0) < C(j) + eps/2 *)
  (* This only bounds d(0). We need d(k) < C(k) + eps *)
  (* Better approach: for each k, use HC(k) to get M_k *)
  (* Then pick k >= M_k *)
  (* Actually, this requires a uniform bound *)
  (* Let's use a different approach: use cs_cauchy of C *)
  destruct (cs_cauchy C (eps * (1#2)) Heps2) as [NC HNC].
  (* HC(k): exists M, forall j >= M, d(k) < C(j) + eps/2 *)
  (* Take k = NC, so we get M_NC *)
  destruct (HC NC (eps * (1#2)) Heps2) as [MNC HMNC].
  (* HMNC: forall j >= MNC, d(NC) < C(j) + eps/2 *)
  (* For k >= max(NC, MNC): *)
  exists (Nat.max NC MNC).
  intros k Hk.
  simpl.
  assert (Hk_NC : (NC <= k)%nat) by lia.
  assert (Hk_MNC : (MNC <= k)%nat) by lia.
  (* d(k) <= B (bounded) *)
  (* d(NC) < C(k) + eps/2 from HMNC since k >= MNC *)
  assert (H1 : d NC < cs_seq C k + eps * (1#2)) by (simpl in HMNC; apply HMNC; lia).
  (* |C(k) - C(NC)| < eps/2 from C's Cauchy property since k, NC >= NC *)
  assert (H2 : Qabs (cs_seq C k - cs_seq C NC) < eps * (1#2))
    by (apply HNC; lia).
  apply Qabs_Qlt_condition in H2.
  (* d(k) >= d(NC) since k >= NC and d increasing *)
  assert (H3 : d NC <= d k) by (apply inc_le; assumption).
  (* d(k) < C(NC) + eps from triangle *)
  (* C(k) > C(NC) - eps/2, and d(NC) < C(k) + eps/2 *)
  (* So d(k) <= ... *)
  (* Actually: d(NC) < C(k) + eps/2 and d(k) >= d(NC) doesn't help directly *)
  (* We need d(k) < C(k) + eps *)
  (* Use HC(k) directly *)
  destruct (HC k (eps * (1#2)) Heps2) as [Mk HMk].
  (* HMk: forall j >= Mk, d(k) < C(j) + eps/2 *)
  (* Need j = k >= Mk. But Mk depends on k... *)
  (* Take j = max(k, Mk) — but then it's not k anymore *)
  (* Alternative: use C's Cauchy property to bridge *)
  assert (HMk_bound : (Mk <= Nat.max k Mk)%nat) by lia.
  assert (Hk_bound : (k <= Nat.max k Mk)%nat) by lia.
  assert (H4 : d k < cs_seq C (Nat.max k Mk) + eps * (1#2))
    by (simpl in HMk; apply HMk; lia).
  destruct (cs_cauchy C (eps * (1#2)) Heps2) as [NC2 HNC2].
  (* This is getting too complex. Let me use a cleaner approach. *)
  (* For any k: cauchy_le (cauchy_const (d k)) C means
     forall eps' > 0, exists M, forall j >= M: d(k) < C(j) + eps'.
     In particular with eps' = eps/2: exists M_k, forall j >= M_k: d(k) < C(j) + eps/2.
     Also C is Cauchy: exists NC, forall j1 j2 >= NC: |C(j1) - C(j2)| < eps/2.
     So for j = max(M_k, NC) (call it J):
       d(k) < C(J) + eps/2
       |C(J) - C(k)| < eps/2 if k >= NC
     So d(k) < C(J) + eps/2 < C(k) + eps/2 + eps/2 = C(k) + eps, IF k >= NC.
     But J = max(M_k, NC) depends on k...
     The key: we output exists K, forall k >= K. So we can pick K >= NC.
     For k >= NC: use HC(k) with eps/2 to get M_k.
     Set J = max(k, M_k). Then:
       d(k) < C(J) + eps/2  (from HC(k))
       |C(J) - C(k)| < eps/2 (from C Cauchy, since J >= k >= NC and J >= NC)
     So d(k) < C(k) + eps/2 + eps/2 = C(k) + eps. ✓
  *)
  (* OK restart the proof with cleaner structure *)
  Restart.
  intros d B Hinc Hbnd C HC.
  intros eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (cs_cauchy C (eps * (1#2)) Heps2) as [NC HNC].
  exists NC.
  intros k Hk. simpl.
  (* For this k >= NC, get M_k from HC(k) *)
  destruct (HC k (eps * (1#2)) Heps2) as [Mk HMk].
  (* Pick J = max(k, Mk) *)
  set (J := Nat.max k Mk).
  assert (HJ_k : (k <= J)%nat) by lia.
  assert (HJ_Mk : (Mk <= J)%nat) by lia.
  assert (HJ_NC : (NC <= J)%nat) by lia.
  (* d(k) < C(J) + eps/2 *)
  assert (H1 : d k < cs_seq C J + eps * (1#2))
    by (simpl in HMk; apply HMk; exact HJ_Mk).
  (* |C(J) - C(k)| < eps/2 since J, k >= NC *)
  assert (H2 : Qabs (cs_seq C J - cs_seq C k) < eps * (1#2))
    by (apply HNC; [exact HJ_NC | exact Hk]).
  apply Qabs_Qlt_condition in H2.
  (* C(J) < C(k) + eps/2, so d(k) < C(k) + eps *)
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: CAUCHY ORDERING                                                *)
(* ========================================================================= *)

(** Transitivity of cauchy_le *)
Lemma cauchy_le_trans : forall a b c : CauchySeq,
  cauchy_le a b -> cauchy_le b c -> cauchy_le a c.
Proof.
  intros a b c Hab Hbc eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hab (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (Hbc (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 n Hn1).
  specialize (HN2 n Hn2).
  lra.
Qed.

(** cauchy_le is antisymmetric up to equivalence *)
Lemma cauchy_le_antisym : forall a b : CauchySeq,
  cauchy_le a b -> cauchy_le b a -> a ~~ b.
Proof.
  intros a b Hab Hba eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hab (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (Hba (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 n Hn1).
  specialize (HN2 n Hn2).
  apply Qabs_lt_bound; lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: SQUEEZE THEOREM                                                *)
(* ========================================================================= *)

(** Squeeze theorem: if a(n) <= c(n) <= b(n) pointwise for large n,
    and a ~~ b, then c ~~ a. *)
Lemma squeeze_equiv : forall a b c : CauchySeq,
  (exists N0 : nat, forall n, (N0 <= n)%nat ->
    cs_seq a n <= cs_seq c n /\ cs_seq c n <= cs_seq b n) ->
  a ~~ b -> c ~~ a.
Proof.
  intros a b c [N0 Hsqueeze] Hab eps Heps.
  destruct (Hab eps Heps) as [N1 HN1].
  exists (Nat.max N0 N1).
  intros n Hn.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  destruct (Hsqueeze n Hn0) as [Hlo Hhi].
  specialize (HN1 n Hn1).
  apply Qabs_Qlt_condition in HN1.
  apply Qabs_lt_bound; lra.
Qed.

(** Squeeze with cauchy_le (weaker but more typical) *)
Lemma squeeze_cauchy_le : forall a b c : CauchySeq,
  cauchy_le a c -> cauchy_le c b -> a ~~ b -> c ~~ a.
Proof.
  intros a b c Hac Hcb Hab eps Heps.
  assert (Heps3 : 0 < eps * (1#3)) by lra.
  destruct (Hac (eps * (1#3)) Heps3) as [N1 HN1].
  destruct (Hcb (eps * (1#3)) Heps3) as [N2 HN2].
  destruct (Hab (eps * (1#3)) Heps3) as [N3 HN3].
  exists (Nat.max N1 (Nat.max N2 N3)).
  intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  assert (Hn3 : (N3 <= n)%nat) by lia.
  specialize (HN1 n Hn1).
  specialize (HN2 n Hn2).
  specialize (HN3 n Hn3).
  apply Qabs_Qlt_condition in HN3.
  apply Qabs_lt_bound; lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: CONVERGENCE TO A CONSTANT                                      *)
(* ========================================================================= *)

(** If d(n) -> q (i.e., d is eventually close to q), then
    mct_limit_inc d ~~ cauchy_const q *)
Lemma mct_inc_limit_const : forall d B Hinc Hbnd (q : Q),
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (d n - q) < eps) ->
  mct_limit_inc d B Hinc Hbnd ~~ cauchy_const q.
Proof.
  intros d B Hinc Hbnd q Hlim eps Heps.
  destruct (Hlim eps Heps) as [N HN].
  exists N. intros n Hn.
  simpl. exact (HN n Hn).
Qed.

(** Constant sequence limit: cauchy_const q as mct_limit *)
Lemma mct_const_seq : forall (q : Q),
  is_cauchy (fun _ => q).
Proof.
  intros q eps Heps.
  exists 0%nat. intros m n _ _.
  setoid_replace (q - q) with 0 by ring.
  rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: SEQUENCE-OF-CAUCHYSEQS DEFINITIONS                            *)
(* ========================================================================= *)

(** Monotone increasing sequence of CauchySeqs *)
Definition seq_increasing (s : nat -> CauchySeq) : Prop :=
  forall n : nat, cauchy_le (s n) (s (S n)).

(** Monotone decreasing sequence of CauchySeqs *)
Definition seq_decreasing (s : nat -> CauchySeq) : Prop :=
  forall n : nat, cauchy_le (s (S n)) (s n).

(** Bounded above by a CauchySeq *)
Definition seq_bounded_above (s : nat -> CauchySeq) (B : CauchySeq) : Prop :=
  forall n : nat, cauchy_le (s n) B.

(** Bounded below by a CauchySeq *)
Definition seq_bounded_below (s : nat -> CauchySeq) (B : CauchySeq) : Prop :=
  forall n : nat, cauchy_le B (s n).

(** Convergence of a sequence of CauchySeqs *)
Definition seq_converges_to (s : nat -> CauchySeq) (L : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists K : nat, forall k : nat,
      (K <= k)%nat -> cauchy_close (s k) L eps.

(** Increasing + cauchy_le gives transitive ordering *)
Lemma seq_increasing_le : forall (s : nat -> CauchySeq),
  seq_increasing s ->
  forall m n, (n <= m)%nat -> cauchy_le (s n) (s m).
Proof.
  intros s Hinc m. induction m; intros n Hnm.
  - replace n with 0%nat by lia. apply cauchy_le_refl.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne].
    + apply cauchy_le_refl.
    + assert (Hle : (n <= m)%nat) by lia.
      apply cauchy_le_trans with (s m).
      * exact (IHm n Hle).
      * exact (Hinc m).
Qed.

(* ========================================================================= *)
(* SECTION 8: VERIFICATION                                                    *)
(* ========================================================================= *)

Check inc_le.
Check dec_le.
Check nat_archimedean.
Check jumps_unbounded.
Check q_inc_bounded_cauchy.
Check q_dec_bounded_cauchy.
Check mct_limit_inc.
Check mct_limit_dec.
Check mct_inc_upper_bound.
Check mct_inc_least.
Check cauchy_le_trans.
Check cauchy_le_antisym.
Check squeeze_equiv.
Check squeeze_cauchy_le.
Check mct_inc_limit_const.
Check mct_const_seq.
Check seq_increasing_le.

Print Assumptions q_inc_bounded_cauchy.
Print Assumptions q_dec_bounded_cauchy.
Print Assumptions mct_inc_upper_bound.
Print Assumptions mct_inc_least.
Print Assumptions cauchy_le_trans.
Print Assumptions squeeze_equiv.
Print Assumptions squeeze_cauchy_le.
Print Assumptions seq_increasing_le.
