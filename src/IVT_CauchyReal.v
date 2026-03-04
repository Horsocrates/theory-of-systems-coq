(* ========================================================================= *)
(*              INTERMEDIATE VALUE THEOREM ON CAUCHY REALS                  *)
(*                                                                         *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)       *)
(*                                                                         *)
(*  PURPOSE: Lift the epsilon-IVT (IVT_ERR.v) to Cauchy real numbers       *)
(*  (CauchyReal.v), proving the existential statement:                     *)
(*    exists c : CauchySeq, f(c_n) -> 0                                   *)
(*                                                                         *)
(*  CONTENTS:                                                              *)
(*    1. Bridge lemmas: is_Cauchy <-> is_cauchy, equiv <-> cauchy_equiv    *)
(*    2. Bisection as CauchySeq                                            *)
(*    3. Uniform continuity preserves Cauchy property                      *)
(*    4. IVT on Cauchy reals: existential root                             *)
(*    5. IVT: f(root) is Cauchy-equivalent to 0                            *)
(*                                                                         *)
(*  STATUS: 8 Qed, 0 Admitted (100%)                                       *)
(*                                                                         *)
(*  AXIOMS: classic (from IVT_ERR, via Archimedean_ERR)                    *)
(*                                                                         *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import Archimedean_ERR.
From ToS Require Import IVT_ERR.
From ToS Require Import CauchyReal.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: BRIDGE LEMMAS                                                  *)
(*                                                                           *)
(*  IVT_ERR uses: is_Cauchy (n > N), equiv (n > N)                          *)
(*  CauchyReal uses: is_cauchy (N <= n), cauchy_equiv (N <= n)               *)
(*  These are equivalent — bridge with N' = S N or N' = N-1.                 *)
(* ========================================================================= *)

(** Bridge: is_Cauchy (strict >) implies is_cauchy (non-strict <=) *)
Lemma is_Cauchy_to_is_cauchy : forall R : nat -> Q,
  is_Cauchy R -> is_cauchy R.
Proof.
  intros R HC eps Heps.
  destruct (HC eps Heps) as [N HN].
  exists (S N).
  intros m n Hm Hn.
  apply HN; lia.
Qed.

(** Bridge: is_cauchy implies is_Cauchy *)
Lemma is_cauchy_to_is_Cauchy : forall R : nat -> Q,
  is_cauchy R -> is_Cauchy R.
Proof.
  intros R HC eps Heps.
  destruct (HC eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  apply HN; lia.
Qed.

(** Bridge: IVT equiv (n > N) to a form compatible with cauchy_equiv *)
Lemma equiv_to_converges : forall (R : RealProcess) (q : Q),
  equiv R (fun _ => q) ->
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (R n - q) < eps.
Proof.
  intros R q Hequiv eps Heps.
  destruct (Hequiv eps Heps) as [N HN].
  exists (S N).
  intros n Hn.
  assert (HnN : (n > N)%nat) by lia.
  assert (H := HN n HnN).
  (* R n - (fun _ => q) n = R n - q *)
  simpl in H.
  exact H.
Qed.

(* ========================================================================= *)
(* SECTION 2: BISECTION AS CAUCHYSEQ                                        *)
(* ========================================================================= *)

(** The bisection process wrapped as a CauchySeq *)
Definition bisection_cauchy_seq (f : ContinuousFunction) (a b : Q)
  (Hab : a < b) : CauchySeq :=
  mkCauchy (bisection_process f a b)
           (is_Cauchy_to_is_cauchy _ (bisection_is_Cauchy f a b Hab)).

(** Bisection CauchySeq stays in [a, b] *)
Lemma bisection_cauchy_in_interval :
  forall (f : ContinuousFunction) (a b : Q) (Hab : a < b) (n : nat),
    a <= cs_seq (bisection_cauchy_seq f a b Hab) n /\
    cs_seq (bisection_cauchy_seq f a b Hab) n <= b.
Proof.
  intros f a b Hab n.
  simpl.
  exact (bisection_in_interval f a b (Qlt_le_weak _ _ Hab) n).
Qed.

(* ========================================================================= *)
(* SECTION 3: UNIFORM CONTINUITY PRESERVES CAUCHY PROPERTY                   *)
(* ========================================================================= *)

(** If f is uniformly continuous on [a,b] and c is a CauchySeq in [a,b],
    then f ∘ c is also Cauchy. *)
Lemma continuous_compose_cauchy :
  forall (f : ContinuousFunction) (c : CauchySeq) (a b : Q),
    uniformly_continuous_on f a b ->
    (forall n : nat, a <= cs_seq c n /\ cs_seq c n <= b) ->
    is_cauchy (fun n => f (cs_seq c n)).
Proof.
  intros f c a b Huc Hbounds eps Heps.
  (* Get delta from uniform continuity *)
  destruct (Huc eps Heps) as [delta [Hdelta_pos Hdelta_uc]].
  (* Get N from Cauchy property of c *)
  destruct (cs_cauchy c delta Hdelta_pos) as [N HN].
  exists N.
  intros m n Hm Hn.
  (* |c(m) - c(n)| < delta *)
  assert (Hclose := HN m n Hm Hn).
  (* c(m), c(n) in [a,b] *)
  destruct (Hbounds m) as [Ham Hmb].
  destruct (Hbounds n) as [Han Hnb].
  (* By uniform continuity: |f(c(m)) - f(c(n))| < eps *)
  apply Hdelta_uc.
  - split; assumption.
  - split; assumption.
  - exact Hclose.
Qed.

(** Wrap f ∘ c as a CauchySeq *)
Definition compose_cauchy_seq
  (f : ContinuousFunction) (c : CauchySeq) (a b : Q)
  (Huc : uniformly_continuous_on f a b)
  (Hbounds : forall n : nat, a <= cs_seq c n /\ cs_seq c n <= b)
  : CauchySeq :=
  mkCauchy (fun n => f (cs_seq c n))
           (continuous_compose_cauchy f c a b Huc Hbounds).

(* ========================================================================= *)
(* SECTION 4: IVT ON CAUCHY REALS — CONVERGENCE TO ZERO                     *)
(* ========================================================================= *)

(** The bisection CauchySeq composed with f converges to 0.
    Direct proof using the bisection building blocks from IVT_ERR. *)
Lemma bisection_f_converges_to_zero :
  forall (f : ContinuousFunction) (a b : Q)
    (Hab : a < b) (Huc : uniformly_continuous_on f a b)
    (Hfa : f a < 0) (Hfb : f b > 0),
    forall eps : Q, 0 < eps ->
      exists N : nat, forall n : nat,
        (N <= n)%nat ->
        Qabs (f (bisection_process f a b n)) < eps.
Proof.
  intros f a b Hab Huc Hfa Hfb eps Heps.
  (* The IVT_process proof shows equiv (apply_to_process f (bisection_process f a b)) (fun _ => 0) *)
  (* Let's reprove this directly using the same structure *)

  (* Get delta from uniform continuity *)
  destruct (Huc eps Heps) as [delta [Hdelta_pos Hdelta_uc]].

  (* Get N such that bisection width < delta *)
  assert (Hpos_width : b - a > 0).
  { unfold Qlt, Qminus, Qplus, Qopp in *.
    destruct a as [ap aq]. destruct b as [bp bq].
    simpl in *. nia. }
  destruct (Archimedean_width (b - a) delta Hpos_width Hdelta_pos) as [N HN].

  exists (S N).
  intros n Hn.

  set (s := bisection_iter f (mkBisection a b) n).
  set (mid := (bis_left s + bis_right s) / 2).

  (* Sign preservation *)
  pose proof (bisection_preserves_signs_weak f a b n
                (Qlt_le_weak _ _ Hfa) (Qlt_le_weak _ _ Hfb)) as [Hleft Hright].
  fold s in Hleft, Hright.

  (* Bounds *)
  pose proof (iter_bounds f a b n (Qlt_le_weak _ _ Hab)) as [Ha_le [Hb_ge Hlr]].
  fold s in Ha_le, Hb_ge, Hlr.

  (* Width *)
  pose proof (bisection_width f a b n) as Hwidth.
  fold s in Hwidth.

  (* Width < delta *)
  assert (Hsmall : bis_right s - bis_left s < delta).
  { rewrite Hwidth.
    apply Qle_lt_trans with ((b - a) / Qpow2 N).
    - apply width_shrinks.
      + exact Hpos_width.
      + lia.
    - exact HN. }

  (* mid is bisection_process f a b n *)
  assert (Hmid_eq : bisection_process f a b n = mid).
  { unfold bisection_process, mid. fold s. reflexivity. }
  rewrite Hmid_eq.

  (* mid in [a,b] *)
  assert (Hmid_bounds : a <= mid <= b).
  { unfold mid. split.
    - apply Qle_trans with (bis_left s).
      + exact Ha_le.
      + apply Qle_half_sum_l. exact Hlr.
    - apply Qle_trans with (bis_right s).
      + apply Qle_half_sum_r. exact Hlr.
      + exact Hb_ge. }

  (* left in [a,b] *)
  assert (Hleft_bounds : a <= bis_left s <= b).
  { split. exact Ha_le.
    apply Qle_trans with (bis_right s); [exact Hlr | exact Hb_ge]. }

  (* Half width < delta *)
  assert (Hhalf_width : (bis_right s - bis_left s) / 2 < delta).
  { apply Qle_lt_trans with (bis_right s - bis_left s).
    - apply half_le_full.
      setoid_replace 0 with (bis_left s - bis_left s) by ring.
      apply Qle_sub_r. exact Hlr.
    - exact Hsmall. }

  (* |mid - left| < delta *)
  assert (Hmid_left : Qabs (mid - bis_left s) < delta).
  { unfold mid.
    setoid_replace ((bis_left s + bis_right s) / 2 - bis_left s)
      with ((bis_right s - bis_left s) / 2) by field.
    rewrite Qabs_pos.
    - exact Hhalf_width.
    - apply Qle_shift_div_l.
      + reflexivity.
      + rewrite Qmult_0_l.
        setoid_replace 0 with (bis_left s - bis_left s) by ring.
        apply Qle_sub_r. exact Hlr. }

  (* |f(mid) - f(left)| < eps *)
  assert (Hf_diff : Qabs (f mid - f (bis_left s)) < eps).
  { apply Hdelta_uc.
    - exact Hmid_bounds.
    - exact Hleft_bounds.
    - exact Hmid_left. }

  (* Right endpoint: |mid - right| < delta *)
  assert (Hright_bounds : a <= bis_right s <= b).
  { split. apply Qle_trans with (bis_left s); [exact Ha_le | exact Hlr].
    exact Hb_ge. }

  assert (Hmid_right : Qabs (mid - bis_right s) < delta).
  { unfold mid.
    setoid_replace ((bis_left s + bis_right s) / 2 - bis_right s)
      with (-((bis_right s - bis_left s) / 2)) by field.
    rewrite Qabs_opp. rewrite Qabs_pos.
    - exact Hhalf_width.
    - apply Qle_shift_div_l.
      + reflexivity.
      + rewrite Qmult_0_l.
        setoid_replace 0 with (bis_left s - bis_left s) by ring.
        apply Qle_sub_r. exact Hlr. }

  assert (Hf_diff_r : Qabs (f mid - f (bis_right s)) < eps).
  { apply Hdelta_uc.
    - exact Hmid_bounds.
    - exact Hright_bounds.
    - exact Hmid_right. }

  (* |f(mid)| < eps from f(left) <= 0 <= f(right) and continuity *)
  apply Qabs_case.
  + intro Hfmid_pos.
    apply Qle_lt_trans with (Qabs (f mid - f (bis_left s))).
    * apply Qle_trans with (f mid - f (bis_left s)).
      -- rewrite Qle_minus_iff.
         setoid_replace ((f mid - f (bis_left s)) + - f mid)
           with (- f (bis_left s)) by ring.
         pose proof (Qopp_le_compat _ _ Hleft) as H.
         setoid_replace (- (0)) with 0 in H by ring. exact H.
      -- apply Qle_Qabs.
    * exact Hf_diff.
  + intro Hfmid_neg.
    apply Qabs_Qlt_condition in Hf_diff_r.
    destruct Hf_diff_r as [Hlo Hhi].
    unfold Qlt, Qle, Qopp, Qminus, Qplus in *.
    destruct (f mid) as [fmn fmd].
    destruct (f (bis_right s)) as [frn frd].
    destruct eps as [en ed].
    simpl in *. nia.
Qed.

(* ========================================================================= *)
(* SECTION 5: MAIN THEOREM — IVT ON CAUCHY REALS                            *)
(* ========================================================================= *)

(**
  INTERMEDIATE VALUE THEOREM (Cauchy Real version):

  If f : Q -> Q is uniformly continuous on [a,b], f(a) < 0, and f(b) > 0,
  then there exists a CauchySeq c in [a,b] such that f(c) converges to 0.

  This is the TYPE-LEVEL upgrade of IVT_process from IVT_ERR.v:
  - IVT_ERR gives: ∃ c : nat -> Q, is_Cauchy c ∧ f(c_n) → 0
  - This gives: ∃ c : CauchySeq, f(c_n) → 0  (Cauchy proof baked into type)
*)
Theorem ivt_cauchy_real :
  forall (f : ContinuousFunction) (a b : Q),
    a < b ->
    uniformly_continuous_on f a b ->
    f a < 0 -> f b > 0 ->
    exists c : CauchySeq,
      (forall n : nat, a <= cs_seq c n /\ cs_seq c n <= b) /\
      (forall eps : Q, 0 < eps ->
        exists N : nat, forall n : nat,
          (N <= n)%nat ->
          Qabs (f (cs_seq c n)) < eps).
Proof.
  intros f a b Hab Huc Hfa Hfb.
  exists (bisection_cauchy_seq f a b Hab).
  split.
  - (* c stays in [a, b] *)
    intro n. apply bisection_cauchy_in_interval.
  - (* f(c_n) → 0 *)
    intros eps Heps.
    apply (bisection_f_converges_to_zero f a b Hab Huc Hfa Hfb eps Heps).
Qed.

(** Corollary: the composition f ∘ root is a CauchySeq equivalent to 0 *)
Corollary ivt_cauchy_real_equiv :
  forall (f : ContinuousFunction) (a b : Q),
    a < b ->
    uniformly_continuous_on f a b ->
    f a < 0 -> f b > 0 ->
    exists c : CauchySeq,
      (forall n : nat, a <= cs_seq c n /\ cs_seq c n <= b) /\
      exists fc : CauchySeq,
        (forall n : nat, cs_seq fc n = f (cs_seq c n)) /\
        cauchy_equiv fc (cauchy_const 0).
Proof.
  intros f a b Hab Huc Hfa Hfb.
  exists (bisection_cauchy_seq f a b Hab).
  split.
  - intro n. apply bisection_cauchy_in_interval.
  - (* Build f ∘ c as CauchySeq *)
    set (c := bisection_cauchy_seq f a b Hab).
    assert (Hbounds : forall n, a <= cs_seq c n /\ cs_seq c n <= b).
    { intro n. apply bisection_cauchy_in_interval. }
    exists (compose_cauchy_seq f c a b Huc Hbounds).
    split.
    + (* Values match *)
      intro n. simpl. reflexivity.
    + (* f(c_n) ~~ 0 *)
      intros eps Heps.
      destruct (bisection_f_converges_to_zero f a b Hab Huc Hfa Hfb eps Heps) as [N HN].
      exists N.
      intros n Hn.
      simpl.
      assert (Hsub : f (bisection_process f a b n) - 0 ==
                     f (bisection_process f a b n)) by ring.
      qabs_rw Hsub.
      apply HN. exact Hn.
Qed.

(* ========================================================================= *)
(* SECTION 6: VERIFICATION                                                    *)
(* ========================================================================= *)

Check is_Cauchy_to_is_cauchy.
Check is_cauchy_to_is_Cauchy.
Check bisection_cauchy_seq.
Check bisection_cauchy_in_interval.
Check continuous_compose_cauchy.
Check compose_cauchy_seq.
Check bisection_f_converges_to_zero.
Check ivt_cauchy_real.
Check ivt_cauchy_real_equiv.

Print Assumptions ivt_cauchy_real.
Print Assumptions ivt_cauchy_real_equiv.
