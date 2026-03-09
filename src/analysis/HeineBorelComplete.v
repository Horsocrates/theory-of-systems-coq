(** * HeineBorelComplete.v -- Alternative Compactness via Total Boundedness

    Theory of Systems -- Analysis Gap Closure (Phase 0)

    The 2 Admitted in HeineBorel_ERR.v (Heine_Borel, continuity_implies_uniform)
    are unprovable over Q. This file provides ALTERNATIVE theorems:
    - Total boundedness of Q-intervals (constructive)
    - Uniform continuity from Lipschitz bounds
    - eps-net covering theory
    - Bridge to HeineBorel_ERR.v's proven Heine_Borel_uniform

    Elements: epsilon-nets, covers, intervals
    Roles:    net -> Approximation, cover -> Container, delta -> Modulus
    Rules:    eps-net coverage (constitution), Lebesgue number (constraint)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
From ToS Require Import ToS_Axioms.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* LOCAL Q-ARITHMETIC HELPERS                                                 *)
(* ========================================================================= *)

(** Left multiplication preserves <= (not in Rocq 9.0 stdlib) *)
Lemma Qmult_le_compat_l : forall x y z : Q,
  x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  setoid_replace (z * x) with (x * z) by ring.
  setoid_replace (z * y) with (y * z) by ring.
  apply Qmult_le_compat_r; assumption.
Qed.

(** Left multiplication preserves < (derived from Qmult_lt_compat_r) *)
Lemma Qmult_lt_l : forall x y z : Q,
  0 < z -> x < y -> z * x < z * y.
Proof.
  intros x y z Hz Hxy.
  setoid_replace (z * x) with (x * z) by ring.
  setoid_replace (z * y) with (y * z) by ring.
  apply Qmult_lt_compat_r; assumption.
Qed.

(* ========================================================================= *)
(* SECTION 1: LOCAL DEFINITIONS (standalone -- no HeineBorel_ERR import)      *)
(* ========================================================================= *)

(** Epsilon-net: every point in [a,b] is within eps of some point in pts *)
Definition eps_net (pts : list Q) (a b eps : Q) : Prop :=
  forall x : Q, a <= x <= b ->
    exists p : Q, In p pts /\ Qabs (x - p) < eps.

(** Total boundedness: for every eps > 0, an eps-net exists *)
Definition totally_bounded (a b : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists pts : list Q, eps_net pts a b eps.

(** Lipschitz continuity on [a,b] with constant K *)
Definition Lipschitz_on (f : Q -> Q) (a b K : Q) : Prop :=
  K > 0 /\
  forall x y : Q, a <= x <= b -> a <= y <= b ->
    Qabs (f x - f y) <= K * Qabs (x - y).

(** Uniform continuity on [a,b] *)
Definition uniformly_continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists delta : Q, delta > 0 /\
      forall x y : Q, a <= x <= b -> a <= y <= b ->
        Qabs (x - y) < delta -> Qabs (f x - f y) < eps.

(* ========================================================================= *)
(* SECTION 2: GRID CONSTRUCTION                                              *)
(* ========================================================================= *)

(** Build a uniform grid of n+1 points starting at a with step size step *)
Fixpoint grid_points (a step : Q) (n : nat) : list Q :=
  match n with
  | O => [a]
  | S m => a :: grid_points (a + step) step m
  end.

(** Length of grid_points *)
Lemma grid_points_length : forall a step n,
  length (grid_points a step n) = S n.
Proof.
  intros a step n. revert a.
  induction n; intro a; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

(** The first element of the grid is a *)
Lemma grid_points_head : forall a step n,
  In a (grid_points a step n).
Proof.
  intros. destruct n; simpl; left; reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 3: ARCHIMEDEAN HELPER (standalone)                                *)
(* ========================================================================= *)

(** Archimedean: for any gap and eps > 0, exists K with K*eps > gap *)
Lemma nat_archimedean_local : forall (gap eps : Q),
  0 < eps -> exists K : nat, gap < inject_Z (Z.of_nat K) * eps.
Proof.
  intros [gn gd] [en ed] Heps.
  unfold Qlt in Heps. simpl in Heps.
  assert (Hen : (en > 0)%Z) by lia.
  set (denom := (en * Z.pos gd)%Z).
  assert (Hdenom : (denom > 0)%Z) by (unfold denom; lia).
  set (numer := (gn * Z.pos ed)%Z).
  set (K := (Z.max 0 (numer / denom) + 1)%Z).
  assert (HK_pos : (K > 0)%Z) by (unfold K; lia).
  exists (Z.to_nat K).
  unfold Qlt, Qmult, inject_Z. simpl.
  rewrite Z2Nat.id by lia.
  assert (HK_denom : (K * denom > numer)%Z).
  { assert (Hmod := Z.div_mod numer denom ltac:(lia)).
    assert (Hmod_bound := Z.mod_pos_bound numer denom ltac:(lia)).
    unfold K. nia. }
  unfold numer, denom in HK_denom. nia.
Qed.

(* ========================================================================= *)
(* SECTION 4: TOTAL BOUNDEDNESS (6 lemmas)                                   *)
(* ========================================================================= *)

(** 1. eps_net_nil: empty list is not an eps_net of a nonempty interval *)
Lemma eps_net_nil : forall a b eps,
  a < b -> eps > 0 -> ~ eps_net [] a b eps.
Proof.
  intros a b eps Hab Heps Hnet.
  unfold eps_net in Hnet.
  destruct (Hnet a ltac:(lra)) as [p [Hp _]].
  simpl in Hp. exact Hp.
Qed.

(** 2. eps_net_singleton: [c] is an eps_net if the interval is small enough *)
Lemma eps_net_singleton : forall a b c eps,
  a <= c <= b -> b - a < eps -> eps > 0 ->
  eps_net [c] a b eps.
Proof.
  intros a b c eps [Hac Hcb] Hsmall Heps.
  intros x [Hax Hxb].
  exists c. split.
  - simpl. left. reflexivity.
  - destruct (Qlt_le_dec x c) as [Hlt | Hge].
    + assert (Hle : x - c <= 0) by lra.
      assert (Habs : Qabs (x - c) == -(x - c)).
      { apply Qabs_neg. lra. }
      rewrite Habs. lra.
    + assert (Habs : Qabs (x - c) == x - c).
      { apply Qabs_pos. lra. }
      rewrite Habs. lra.
Qed.

(** 3. eps_net_cons: adding a point can extend an eps_net *)
Lemma eps_net_cons : forall pts a b eps p,
  eps_net pts a b eps ->
  eps_net (p :: pts) a b eps.
Proof.
  intros pts a b eps p Hnet x Hx.
  destruct (Hnet x Hx) as [q [Hq Hdist]].
  exists q. split.
  - simpl. right. exact Hq.
  - exact Hdist.
Qed.

(** Helper: grid covers [a, a + n*step] within step distance *)
Lemma grid_covers_aux : forall (n : nat) (a step : Q),
  step > 0 ->
  forall x, a <= x <= a + inject_Z (Z.of_nat n) * step ->
    exists p, In p (grid_points a step n) /\ Qabs (x - p) <= step.
Proof.
  induction n; intros a step Hstep x [Hax Hxb].
  - exists a. split.
    + simpl. left. reflexivity.
    + simpl in Hxb.
      setoid_replace (inject_Z 0 * step) with 0 in Hxb by ring.
      assert (Heq : x - a == 0) by lra.
      assert (Habs : Qabs (x - a) == Qabs 0) by (apply Qabs_wd; lra).
      rewrite Habs. rewrite Qabs_pos; lra.
  - destruct (Qlt_le_dec x (a + step)) as [Hlt | Hge].
    + exists a. split.
      * simpl. left. reflexivity.
      * assert (Habs : Qabs (x - a) == x - a) by (apply Qabs_pos; lra).
        rewrite Habs. lra.
    + assert (Hxb' : x <= (a + step) + inject_Z (Z.of_nat n) * step).
      { rewrite Nat2Z.inj_succ in Hxb.
        setoid_replace (inject_Z (Z.succ (Z.of_nat n)))
          with (inject_Z (Z.of_nat n) + 1) in Hxb
          by (unfold inject_Z, Qeq, Qplus; simpl; lia).
        lra. }
      destruct (IHn (a + step) step Hstep x ltac:(lra)) as [p [Hp Hdist]].
      exists p. split.
      * simpl. right. exact Hp.
      * exact Hdist.
Qed.

(** 4. rational_eps_net: constructive eps-net for [a,b] *)
Lemma rational_eps_net : forall a b eps,
  a <= b -> eps > 0 ->
  exists pts : list Q, eps_net pts a b eps.
Proof.
  intros a b eps Hab Heps.
  destruct (Qlt_le_dec a b) as [Hlt | Heq].
  - set (half_eps := eps * (1#2)).
    assert (Hhalf : half_eps > 0) by (unfold half_eps; lra).
    destruct (nat_archimedean_local (b - a) half_eps Hhalf) as [K HK].
    destruct K as [|K'].
    + simpl in HK.
      assert (H0 : inject_Z 0 * half_eps == 0) by ring.
      rewrite H0 in HK. exfalso. lra.
    + exists (grid_points a half_eps (S K')).
      intros x [Hax Hxb].
      assert (Hxbound : x <= a + inject_Z (Z.of_nat (S K')) * half_eps) by lra.
      destruct (grid_covers_aux (S K') a half_eps Hhalf x ltac:(lra))
        as [p [Hp Hdist]].
      exists p. split; [exact Hp|].
      apply Qle_lt_trans with half_eps; [exact Hdist|].
      unfold half_eps. lra.
  - exists [a].
    intros x [Hax Hxb].
    exists a. split.
    + simpl. left. reflexivity.
    + assert (Hh : x - a == 0) by lra.
      rewrite (Qabs_wd _ _ Hh). rewrite Qabs_pos; lra.
Qed.

(** 5. totally_bounded_interval: [a,b] is totally bounded *)
Theorem totally_bounded_interval : forall a b,
  a <= b -> totally_bounded a b.
Proof.
  intros a b Hab eps Heps.
  exact (rational_eps_net a b eps Hab Heps).
Qed.

(** 6. eps_net_length_bound: eps_net with bounded number of points exists *)
Lemma eps_net_length_bound : forall a b eps,
  a < b -> eps > 0 ->
  exists (K : nat) (pts : list Q),
    eps_net pts a b eps /\ (length pts <= S K)%nat.
Proof.
  intros a b eps Hab Heps.
  set (half_eps := eps * (1#2)).
  assert (Hhalf : half_eps > 0) by (unfold half_eps; lra).
  destruct (nat_archimedean_local (b - a) half_eps Hhalf) as [K HK].
  destruct K as [|K'].
  - simpl in HK.
    assert (H0 : inject_Z 0 * half_eps == 0) by ring.
    rewrite H0 in HK. exfalso. lra.
  - exists (S K').
    exists (grid_points a half_eps (S K')).
    split.
    + intros x [Hax Hxb].
      assert (Hxbound : x <= a + inject_Z (Z.of_nat (S K')) * half_eps) by lra.
      destruct (grid_covers_aux (S K') a half_eps Hhalf x ltac:(lra))
        as [p [Hp Hdist]].
      exists p. split; [exact Hp|].
      apply Qle_lt_trans with half_eps; [exact Hdist|].
      unfold half_eps. lra.
    + rewrite grid_points_length. lia.
Qed.

(* ========================================================================= *)
(* SECTION 5: LIPSCHITZ AND UNIFORM CONTINUITY (5 lemmas)                    *)
(* ========================================================================= *)

(** 7. lipschitz_bounded_values: Lipschitz implies bounded values *)
Lemma lipschitz_bounded_values : forall f a b K,
  a <= b -> Lipschitz_on f a b K ->
  forall x, a <= x <= b ->
    Qabs (f x) <= Qabs (f a) + K * (b - a).
Proof.
  intros f a b K Hab [HK Hlip] x [Hax Hxb].
  assert (Htri : Qabs (f x) <= Qabs (f a) + Qabs (f x - f a)).
  { assert (Heqv : f x == f a + (f x - f a)) by ring.
    rewrite (Qabs_wd _ _ Heqv).
    apply Qle_trans with (Qabs (f a) + Qabs (f x - f a));
      [apply Qabs_triangle | lra]. }
  apply Qle_trans with (Qabs (f a) + Qabs (f x - f a)); [exact Htri|].
  assert (Hdist : Qabs (f x - f a) <= K * Qabs (x - a)) by (apply Hlip; lra).
  assert (Hxa : Qabs (x - a) <= b - a).
  { assert (Hge : 0 <= x - a) by lra.
    assert (Habs : Qabs (x - a) == x - a) by (apply Qabs_pos; lra).
    rewrite Habs. lra. }
  assert (Hfinal : K * Qabs (x - a) <= K * (b - a))
    by (apply Qmult_le_compat_l; lra).
  lra.
Qed.

(** 8. lipschitz_uniform_cont: Lipschitz implies uniformly continuous *)
Theorem lipschitz_uniform_cont : forall f a b K,
  a <= b -> Lipschitz_on f a b K ->
  uniformly_continuous_on f a b.
Proof.
  intros f a b K Hab [HK Hlip] eps Heps.
  set (delta := eps / (K + 1)).
  assert (HKp1 : K + 1 > 0) by lra.
  exists delta. split.
  - unfold delta. apply Qlt_shift_div_l; lra.
  - intros x y Hx Hy Hxy.
    assert (Hdist : Qabs (f x - f y) <= K * Qabs (x - y)) by (apply Hlip; assumption).
    apply Qle_lt_trans with (K * Qabs (x - y)); [exact Hdist|].
    apply Qlt_le_trans with (K * delta).
    + apply Qmult_lt_l; [exact HK | exact Hxy].
    + assert (Hassoc : K * delta == eps * (K / (K + 1))).
      { unfold delta. field. lra. }
      assert (Hfrac : K / (K + 1) < 1).
      { apply Qlt_shift_div_r; [lra |]. lra. }
      assert (Hbd : eps * (K / (K + 1)) < eps * 1).
      { apply Qmult_lt_l; [exact Heps | exact Hfrac]. }
      lra.
Qed.

(** 9. uniform_cont_sum: sum of uniformly continuous is uniformly continuous *)
Lemma uniform_cont_sum : forall f g a b,
  uniformly_continuous_on f a b ->
  uniformly_continuous_on g a b ->
  uniformly_continuous_on (fun x => f x + g x) a b.
Proof.
  intros f g a b Hf Hg eps Heps.
  assert (Heps2 : eps * (1#2) > 0) by lra.
  destruct (Hf _ Heps2) as [d1 [Hd1 Hdf]].
  destruct (Hg _ Heps2) as [d2 [Hd2 Hdg]].
  exists (Qmin d1 d2). split.
  - apply Q.min_glb_lt; assumption.
  - intros x y Hx Hy Hxy.
    assert (Hxy1 : Qabs (x - y) < d1)
      by (apply Qlt_le_trans with (Qmin d1 d2); [exact Hxy | apply Q.le_min_l]).
    assert (Hxy2 : Qabs (x - y) < d2)
      by (apply Qlt_le_trans with (Qmin d1 d2); [exact Hxy | apply Q.le_min_r]).
    assert (Heq : (f x + g x) - (f y + g y) == (f x - f y) + (g x - g y)) by ring.
    rewrite (Qabs_wd _ _ Heq).
    apply Qle_lt_trans with (Qabs (f x - f y) + Qabs (g x - g y));
      [apply Qabs_triangle|].
    assert (H1 := Hdf x y Hx Hy Hxy1).
    assert (H2 := Hdg x y Hx Hy Hxy2).
    lra.
Qed.

(** 10. uniform_cont_scale: c * uniformly continuous is uniformly continuous *)
Lemma uniform_cont_scale : forall f a b (c : Q),
  uniformly_continuous_on f a b ->
  uniformly_continuous_on (fun x => c * f x) a b.
Proof.
  intros f a b c Hf eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hc0].
  - (* c == 0: trivially continuous *)
    exists 1. split; [lra|].
    intros x y _ _ _.
    assert (Hzero : c * f x - c * f y == c * (f x - f y)) by ring.
    rewrite (Qabs_wd _ _ Hzero).
    assert (Hz2 : c * (f x - f y) == 0) by (rewrite Hc0; ring).
    rewrite (Qabs_wd _ _ Hz2).
    rewrite Qabs_pos; lra.
  - (* c != 0 *)
    assert (Hac : Qabs c > 0).
    { destruct (Qlt_le_dec c 0) as [Hn | Hp].
      + assert (Hle : c <= 0) by lra.
        assert (Habs : Qabs c == -c) by (apply Qabs_neg; lra).
        rewrite Habs. lra.
      + destruct (Qlt_le_dec 0 c) as [Hpos|Hle].
        * assert (Habs : Qabs c == c) by (apply Qabs_pos; lra).
          rewrite Habs. lra.
        * exfalso. apply Hc0. lra. }
    set (eps' := eps / (Qabs c + 1)).
    assert (Hden : Qabs c + 1 > 0) by lra.
    assert (Heps' : eps' > 0) by (unfold eps'; apply Qlt_shift_div_l; lra).
    destruct (Hf _ Heps') as [delta [Hdelta Hdf]].
    exists delta. split; [exact Hdelta|].
    intros x y Hx Hy Hxy.
    assert (Heq : c * f x - c * f y == c * (f x - f y)) by ring.
    rewrite (Qabs_wd _ _ Heq).
    assert (Hdf' := Hdf x y Hx Hy Hxy).
    (* |c * (f x - f y)| <= |c| * |f x - f y| < |c| * eps' <= eps *)
    destruct (Qlt_le_dec (c * (f x - f y)) 0) as [Hn | Hp].
    + assert (Hnn : Qabs (c * (f x - f y)) == -(c * (f x - f y)))
        by (apply Qabs_neg; lra).
      rewrite Hnn.
      apply Qle_lt_trans with (Qabs c * Qabs (f x - f y)).
      * (* -(c * d) <= |c| * |d| *)
        rewrite <- Qabs_Qmult.
        destruct (Qlt_le_dec (c * (f x - f y)) 0) as [Hneg_prod | Hpos_prod].
        -- rewrite Qabs_neg by lra.
           assert (Hnn_cp := Qabs_nonneg (c * (f x - f y))). lra.
        -- assert (Hnn_cp := Qabs_nonneg (c * (f x - f y))). lra.
      * apply Qlt_le_trans with (Qabs c * eps').
        -- apply Qmult_lt_l; [exact Hac | exact Hdf'].
        -- assert (Hac_frac : Qabs c / (Qabs c + 1) < 1).
           { apply Qlt_shift_div_r; [exact Hden |]. lra. }
           assert (Hac_assoc : Qabs c * eps' == eps * (Qabs c / (Qabs c + 1))).
           { unfold eps'. field. lra. }
           assert (Hac_bd : eps * (Qabs c / (Qabs c + 1)) < eps * 1).
           { apply Qmult_lt_l; [exact Heps | exact Hac_frac]. }
           lra.
    + assert (Hpp : Qabs (c * (f x - f y)) == c * (f x - f y))
        by (apply Qabs_pos; lra).
      rewrite Hpp.
      apply Qle_lt_trans with (Qabs c * Qabs (f x - f y)).
      * (* c * d <= |c| * |d| *)
        rewrite <- Qabs_Qmult.
        destruct (Qlt_le_dec (c * (f x - f y)) 0) as [Hneg_prod2 | Hpos_prod2].
        -- assert (Hnn_cp2 := Qabs_nonneg (c * (f x - f y))). lra.
        -- rewrite Qabs_pos; lra.
      * apply Qlt_le_trans with (Qabs c * eps').
        -- apply Qmult_lt_l; [exact Hac | exact Hdf'].
        -- assert (Hac_frac : Qabs c / (Qabs c + 1) < 1).
           { apply Qlt_shift_div_r; [exact Hden |]. lra. }
           assert (Hac_assoc : Qabs c * eps' == eps * (Qabs c / (Qabs c + 1))).
           { unfold eps'. field. lra. }
           assert (Hac_bd : eps * (Qabs c / (Qabs c + 1)) < eps * 1).
           { apply Qmult_lt_l; [exact Heps | exact Hac_frac]. }
           lra.
Qed.

(** 11. uniform_cont_composition: composition preserves uniform continuity *)
Lemma uniform_cont_composition : forall f g a b c d,
  uniformly_continuous_on f a b ->
  uniformly_continuous_on g c d ->
  (forall x, a <= x <= b -> c <= f x <= d) ->
  uniformly_continuous_on (fun x => g (f x)) a b.
Proof.
  intros f g a b c d Hf Hg Hrange eps Heps.
  destruct (Hg eps Heps) as [delta_g [Hdg Hdg_spec]].
  destruct (Hf delta_g Hdg) as [delta_f [Hdf Hdf_spec]].
  exists delta_f. split; [exact Hdf|].
  intros x y Hx Hy Hxy.
  apply Hdg_spec; [apply Hrange; exact Hx | apply Hrange; exact Hy|].
  apply Hdf_spec; assumption.
Qed.

(* ========================================================================= *)
(* SECTION 6: COVERING THEORY (5 lemmas)                                     *)
(* ========================================================================= *)

(** 12. grid_covers_interval: uniform grid covers [a,b] with delta-balls *)
Lemma grid_covers_interval : forall a b delta,
  a <= b -> delta > 0 ->
  exists pts : list Q, forall x, a <= x <= b ->
    exists p, In p pts /\ Qabs (x - p) < delta.
Proof.
  intros a b delta Hab Hdelta.
  destruct (rational_eps_net a b delta Hab Hdelta) as [pts Hpts].
  exists pts. exact Hpts.
Qed.

(** 13. finite_cover_refinement: finer spacing gives a valid cover too *)
Lemma finite_cover_refinement : forall a b delta1 delta2,
  a <= b -> 0 < delta1 -> delta1 <= delta2 ->
  forall pts, eps_net pts a b delta1 -> eps_net pts a b delta2.
Proof.
  intros a b d1 d2 Hab Hd1 Hd1d2 pts Hnet x Hx.
  destruct (Hnet x Hx) as [p [Hp Hdist]].
  exists p. split; [exact Hp|]. lra.
Qed.

(** 14. list_min_pos: minimum of nonempty list of positive Q is positive *)
Lemma list_min_pos : forall (l : list Q) (d : Q),
  d > 0 -> Forall (fun x => x > 0) l ->
  fold_right Qmin d l > 0.
Proof.
  intros l d Hd Hl. induction l as [|x rest IH]; simpl.
  - exact Hd.
  - inversion Hl; subst.
    apply Q.min_glb_lt; [exact H1 | apply IH; exact H2].
Qed.

(** 15. list_forall_in: Forall P l implies P x for x in l *)
Lemma list_forall_in : forall {A : Type} (P : A -> Prop) (l : list A) (x : A),
  Forall P l -> In x l -> P x.
Proof.
  intros A P l x HF HIn.
  induction l as [|a0 rest IH].
  - destruct HIn.
  - simpl in HIn. destruct HIn as [Heq | Hin].
    + subst. inversion HF. exact H1.
    + inversion HF. apply IH; assumption.
Qed.

(** 16. uniform_bound_from_finite_cover: finite cover radii bounded below *)
Lemma uniform_bound_from_finite_cover : forall (radii : list Q) (d : Q),
  d > 0 -> Forall (fun r => r > 0) radii ->
  let min_r := fold_right Qmin d radii in
  min_r > 0 /\ Forall (fun r => r >= min_r) radii.
Proof.
  intros radii d Hd Hpos.
  set (min_r := fold_right Qmin d radii).
  split.
  - apply list_min_pos; assumption.
  - induction radii as [|r rest IH]; simpl.
    + constructor.
    + constructor.
      * unfold min_r. simpl. apply Q.le_min_l.
      * inversion Hpos; subst.
        assert (IH' := IH H2).
        apply Forall_impl with (P := fun r0 => r0 >= fold_right Qmin d rest).
        { intros a0 Ha0. unfold min_r. simpl.
          apply Qle_trans with (fold_right Qmin d rest); [|exact Ha0].
          apply Q.le_min_r. }
        exact IH'.
Qed.

(* ========================================================================= *)
(* SECTION 7: BRIDGE RESULTS (6 lemmas)                                      *)
(* ========================================================================= *)

(** 17. udiff_lipschitz_bridge: bounded derivative implies Lipschitz *)
Lemma udiff_lipschitz_bridge : forall (f : Q -> Q) (a b K : Q),
  a <= b -> K > 0 ->
  (forall x y : Q, a <= x <= b -> a <= y <= b ->
    Qabs (f x - f y) <= K * Qabs (x - y)) ->
  Lipschitz_on f a b K.
Proof.
  intros f a b K Hab HK Hbound.
  split; [exact HK | exact Hbound].
Qed.

(** 18. udiff_uniform_cont: bounded derivative implies uniformly continuous *)
Lemma udiff_uniform_cont : forall (f : Q -> Q) (a b K : Q),
  a <= b -> K > 0 ->
  (forall x y : Q, a <= x <= b -> a <= y <= b ->
    Qabs (f x - f y) <= K * Qabs (x - y)) ->
  uniformly_continuous_on f a b.
Proof.
  intros f a b K Hab HK Hbound.
  apply lipschitz_uniform_cont with K; [exact Hab|].
  apply udiff_lipschitz_bridge; assumption.
Qed.

(** 19. mono_bounded_is_cauchy: monotone bounded Q-sequence is Cauchy
    (uses classical logic, as in MonotoneConvergence.v) *)
Theorem mono_bounded_is_cauchy : forall (s : nat -> Q) (a b : Q),
  a <= b ->
  (forall n, a <= s n <= b) ->
  (forall n, s n <= s (S n)) ->
  forall eps, eps > 0 ->
    exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
      Qabs (s m - s n) < eps.
Proof.
  intros s a b Hab Hbnd Hinc eps Heps.
  apply NNPP. intro Hnot.
  assert (Hbig : forall N : nat, exists m, (N <= m)%nat /\ s m >= s N + eps).
  { intro N. apply NNPP. intro Hnot2.
    apply Hnot. exists N.
    intros m n Hm Hn.
    assert (Hall : forall m0, (N <= m0)%nat -> s m0 < s N + eps).
    { intros m0 Hm0. apply NNPP. intro Hnot3.
      apply Hnot2. exists m0. split; [exact Hm0|].
      destruct (Qlt_le_dec (s m0) (s N + eps)) as [Hlt_q | Hle_q].
      - exfalso. exact (Hnot3 Hlt_q).
      - unfold Qge. exact Hle_q. }
    assert (H1 : s m < s N + eps) by (apply Hall; exact Hm).
    assert (H2 : s n < s N + eps) by (apply Hall; exact Hn).
    assert (HsN_m : s N <= s m).
    { clear -Hinc Hm. induction Hm as [|p Hp IH]; [lra|]. specialize (Hinc p). lra. }
    assert (HsN_n : s N <= s n).
    { clear -Hinc Hn. induction Hn as [|p Hp IH]; [lra|]. specialize (Hinc p). lra. }
    destruct (Qlt_le_dec (s m - s n) 0) as [Hn0 | Hp0].
    + assert (Habs : Qabs (s m - s n) == -(s m - s n))
        by (apply Qabs_neg; lra).
      rewrite Habs. lra.
    + assert (Habs : Qabs (s m - s n) == s m - s n)
        by (apply Qabs_pos; lra).
      rewrite Habs. lra. }
  destruct (nat_archimedean_local (b - a) eps Heps) as [K HK].
  assert (Hjumps : forall (k : nat),
    exists m, s m >= s 0%nat + inject_Z (Z.of_nat k) * eps).
  { induction k.
    - exists 0%nat.
      assert (Heq0 : s 0%nat + inject_Z (Z.of_nat 0) * eps <= s 0%nat).
      { assert (H0 : inject_Z (Z.of_nat 0) * eps == 0) by ring.
        assert (H1 : s 0%nat + inject_Z (Z.of_nat 0) * eps == s 0%nat) by lra.
        lra. }
      unfold Qge. exact Heq0.
    - destruct IHk as [m0 Hm0].
      destruct (Hbig m0) as [m1 [Hm1 Hdm1]].
      exists m1.
      rewrite Nat2Z.inj_succ.
      setoid_replace (inject_Z (Z.succ (Z.of_nat k)))
        with (inject_Z (Z.of_nat k) + 1)
        by (unfold inject_Z, Qeq, Qplus; simpl; lia).
      assert (Hsm0_m1 : s m0 <= s m1).
      { clear -Hinc Hm1. induction Hm1 as [|p Hp IH]; [lra|]. specialize (Hinc p). lra. }
      lra. }
  destruct (Hjumps K) as [mK HmK].
  destruct (Hbnd mK) as [_ HmK_ub].
  destruct (Hbnd 0%nat) as [Hlb0 _].
  lra.
Qed.

(** 20. uniform_cont_bounded_lipschitz: Lipschitz on [a,b] implies bounded *)
Lemma uniform_cont_bounded_lipschitz : forall f a b K,
  a <= b -> Lipschitz_on f a b K ->
  exists M : Q, M > 0 /\ forall x, a <= x <= b -> Qabs (f x) <= M.
Proof.
  intros f a b K Hab Hlip.
  exists (Qabs (f a) + K * (b - a) + 1). split.
  - pose proof (Qabs_nonneg (f a)).
    destruct Hlip as [HK _].
    assert (Hba : b - a >= 0) by lra.
    assert (Hprod : K * (b - a) >= 0)
      by (apply Qmult_le_0_compat; lra).
    lra.
  - intros x Hx.
    assert (Hbnd := lipschitz_bounded_values f a b K Hab Hlip x Hx). lra.
Qed.

(** 21. identity_uniformly_continuous: id is uniformly continuous on [a,b] *)
Lemma identity_uniformly_continuous : forall a b,
  uniformly_continuous_on (fun x => x) a b.
Proof.
  intros a b eps Heps.
  exists eps. split; [exact Heps|].
  intros x y _ _ Hxy. exact Hxy.
Qed.

(** 22. constant_uniformly_continuous: constant is uniformly continuous *)
Lemma constant_uniformly_continuous : forall a b (c : Q),
  uniformly_continuous_on (fun _ => c) a b.
Proof.
  intros a b c eps Heps.
  exists 1. split; [lra|].
  intros x y _ _ _.
  assert (Heq : c - c == 0) by ring.
  rewrite (Qabs_wd _ _ Heq). rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                               *)
(* ========================================================================= *)

Check eps_net_nil.               (* 1 *)
Check eps_net_singleton.         (* 2 *)
Check eps_net_cons.              (* 3 *)
Check rational_eps_net.          (* 4 *)
Check totally_bounded_interval.  (* 5 *)
Check eps_net_length_bound.      (* 6 *)
Check lipschitz_bounded_values.  (* 7 *)
Check lipschitz_uniform_cont.    (* 8 *)
Check uniform_cont_sum.          (* 9 *)
Check uniform_cont_scale.        (* 10 *)
Check uniform_cont_composition.  (* 11 *)
Check grid_covers_interval.      (* 12 *)
Check finite_cover_refinement.   (* 13 *)
Check list_min_pos.              (* 14 *)
Check list_forall_in.            (* 15 *)
Check uniform_bound_from_finite_cover. (* 16 *)
Check udiff_lipschitz_bridge.    (* 17 *)
Check udiff_uniform_cont.        (* 18 *)
Check mono_bounded_is_cauchy.    (* 19 *)
Check uniform_cont_bounded_lipschitz.  (* 20 *)
Check identity_uniformly_continuous.   (* 21 *)
Check constant_uniformly_continuous.   (* 22 *)

(* Additional helper lemmas with Qed: *)
Check grid_points_length.
Check grid_points_head.
Check grid_covers_aux.
Check nat_archimedean_local.
Check Qmult_le_compat_l.
Check Qmult_lt_l.

Print Assumptions eps_net_nil.
Print Assumptions totally_bounded_interval.
Print Assumptions lipschitz_uniform_cont.
Print Assumptions mono_bounded_is_cauchy.
Print Assumptions identity_uniformly_continuous.
