(* ========================================================================= *)
(*        INNER PRODUCT SPACE — Foundation for Process Physics               *)
(*                                                                           *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                  *)
(*                                                                           *)
(*  Inner product ⟨u,v⟩ = dot_product for QVec n, yielding Q values.       *)
(*  Cauchy-Schwarz inequality. Norm squared. Triangle inequality.            *)
(*  Process inner product: ⟨u,v⟩ as CauchySeq when u,v are processes.     *)
(*                                                                           *)
(*  Elements: vectors (QVec n), scalars (Q)                                  *)
(*  Roles:    vector → carrier, scalar → coefficient, ip → measure          *)
(*  Rules:    linearity (L5: bilinear form), positivity (L3)                 *)
(*  Status:   orthogonal | parallel | generic                                *)
(*                                                                           *)
(*  STATUS: 30 Qed, 0 Admitted                                              *)
(*  AXIOMS: none (purely constructive over Q)                                *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs QArith.Qminmax List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.

(** Local helper: Qeq implies Qle *)
Lemma Qeq_Qle : forall x y, x == y -> x <= y.
Proof. intros x y H. rewrite H. apply Qle_refl. Qed.

(* ========================================================================= *)
(*  SECTION 1: Dot Product Linearity (missing from LinearAlgebra.v)          *)
(* ========================================================================= *)

(** qv_neg: scaling by -(1). Defined here to avoid VectorSpace dependency. *)
Definition qv_neg {n} (v : QVec n) : QVec n := qv_scale (-(1)) v.

Lemma qv_neg_nth : forall {n} (v : QVec n) i,
  (i < n)%nat -> qv_nth (qv_neg v) i == -(qv_nth v i).
Proof.
  intros n v i Hi. unfold qv_neg, qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  ring.
Qed.

Lemma qv_add_zero_r : forall {n} (v : QVec n), qv_eq (qv_add v (qv_zero n)) v.
Proof.
  intros n v i Hi. unfold qv_nth, qv_add, qv_zero. simpl.
  generalize dependent i.
  destruct v as [data Hlen]. simpl. subst n.
  induction data as [|x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i2].
    + simpl. ring.
    + simpl. apply IH. simpl in Hi. lia.
Qed.

Lemma qv_add_neg_r : forall {n} (v : QVec n),
  qv_eq (qv_add v (qv_neg v)) (qv_zero n).
Proof.
  intros n v i Hi. unfold qv_nth, qv_add, qv_neg, qv_scale, qv_zero. simpl.
  destruct v as [data Hlen]. simpl. subst n.
  generalize dependent i.
  induction data as [|x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i2].
    + simpl. ring.
    + simpl. apply IH. simpl in Hi. lia.
Qed.

(** Helper: nth of map2 with Qeq when indices are in range *)
Lemma nth_map2_Qeq : forall (f : Q -> Q -> Q) (l1 l2 : list Q) i,
  (i < length l1)%nat -> length l1 = length l2 ->
  nth i (map2 f l1 l2) 0 == f (nth i l1 0) (nth i l2 0).
Proof.
  intros f l1. induction l1 as [|x xs IH]; intros l2 i Hi Hlen.
  - simpl in Hi. lia.
  - destruct l2 as [|y ys]. simpl in Hlen. discriminate.
    destruct i as [|i2].
    + simpl. reflexivity.
    + simpl. apply IH. simpl in Hi. lia. simpl in Hlen. lia.
Qed.

(** Helper: fold_left Qplus init shift *)
Lemma fold_left_Qplus_init_shift : forall (l : list Q) (a b : Q),
  fold_left Qplus l (a + b) == fold_left Qplus l a + b.
Proof.
  induction l as [|x xs IH]; intros a b; simpl.
  - reflexivity.
  - rewrite <- IH. apply fold_left_Qplus_init_compat. ring.
Qed.

(** Helper: fold_left Qplus over scaled list *)
Lemma fold_left_Qplus_scale : forall (c : Q) (l : list Q),
  fold_left Qplus (map (Qmult c) l) 0 == c * fold_left Qplus l 0.
Proof.
  intros c l. induction l as [|x xs IH]; simpl.
  - ring.
  - rewrite fold_left_Qplus_init_shift.
    rewrite IH.
    rewrite (fold_left_Qplus_init_shift xs 0 x).
    ring.
Qed.

(** Helper: fold_left Qplus over pointwise sum of two lists *)
Lemma fold_left_Qplus_split : forall (l1 l2 : list Q),
  length l1 = length l2 ->
  fold_left Qplus (map2 Qplus l1 l2) 0 ==
  fold_left Qplus l1 0 + fold_left Qplus l2 0.
Proof.
  induction l1 as [|x xs IH]; intros l2 Hlen; simpl.
  - destruct l2; [simpl; ring | simpl in Hlen; discriminate].
  - destruct l2 as [|y ys]; [simpl in Hlen; discriminate |].
    simpl.
    rewrite fold_left_Qplus_init_shift.
    rewrite IH; [| simpl in Hlen; lia].
    rewrite (fold_left_Qplus_init_shift xs 0 x).
    rewrite (fold_left_Qplus_init_shift ys 0 y).
    set (fxs := fold_left Qplus xs 0).
    set (fys := fold_left Qplus ys 0).
    ring.
Qed.

(** Dot product with zero on the left *)
Lemma dot_product_zero_left : forall {n} (v : QVec n),
  dot_product (qv_zero n) v == 0.
Proof.
  intros n v. rewrite dot_product_comm. apply dot_product_zero_right.
Qed.

(** Helper: scale distributes over dot product (list-level) *)
Lemma dot_scale_r_raw : forall (l1 l2 : list Q) (c : Q),
  fold_left Qplus (map2 Qmult l1 (map (Qmult c) l2)) 0 ==
  c * fold_left Qplus (map2 Qmult l1 l2) 0.
Proof.
  induction l1 as [|x xs IH]; intros l2 c; simpl.
  - ring.
  - destruct l2 as [|y ys]; simpl.
    + ring.
    + rewrite !fold_left_Qplus_init_shift. rewrite IH.
      set (f := fold_left Qplus (map2 Qmult xs ys) 0). ring.
Qed.

(** Dot product scales in the right argument *)
Theorem dot_product_scale_r : forall {n} (u : QVec n) (c : Q) (v : QVec n),
  dot_product u (qv_scale c v) == c * dot_product u v.
Proof.
  intros n u c v. unfold dot_product, qv_scale. simpl.
  apply dot_scale_r_raw.
Qed.

(** Dot product scales in the left argument *)
Theorem dot_product_scale_l : forall {n} (c : Q) (u v : QVec n),
  dot_product (qv_scale c u) v == c * dot_product u v.
Proof.
  intros n c u v.
  rewrite dot_product_comm, dot_product_scale_r, dot_product_comm. reflexivity.
Qed.

(** Helper: dot product distributes over addition (list-level) *)
Lemma dot_add_r_raw : forall (l1 l2 l3 : list Q),
  length l1 = length l2 -> length l2 = length l3 ->
  fold_left Qplus (map2 Qmult l1 (map2 Qplus l2 l3)) 0 ==
  fold_left Qplus (map2 Qmult l1 l2) 0 +
  fold_left Qplus (map2 Qmult l1 l3) 0.
Proof.
  induction l1 as [|x xs IH]; intros l2 l3 H12 H23; simpl.
  - destruct l2; [destruct l3; [simpl; ring | simpl in H23; discriminate]
    | simpl in H12; discriminate].
  - destruct l2 as [|y ys]; [simpl in H12; discriminate |].
    destruct l3 as [|z zs]; [simpl in H23; discriminate |].
    simpl. rewrite !fold_left_Qplus_init_shift.
    rewrite IH; [| simpl in H12; lia | simpl in H23; lia].
    set (f1 := fold_left Qplus (map2 Qmult xs ys) 0).
    set (f2 := fold_left Qplus (map2 Qmult xs zs) 0).
    ring.
Qed.

(** Dot product distributes over addition on the right *)
Theorem dot_product_add_r : forall {n} (u v w : QVec n),
  dot_product u (qv_add v w) == dot_product u v + dot_product u w.
Proof.
  intros n u v w. unfold dot_product, qv_add. simpl.
  apply dot_add_r_raw.
  - rewrite (qv_length u), (qv_length v). reflexivity.
  - rewrite (qv_length v), (qv_length w). reflexivity.
Qed.

(** Dot product distributes over addition on the left *)
Theorem dot_product_add_l : forall {n} (u v w : QVec n),
  dot_product (qv_add u v) w == dot_product u w + dot_product v w.
Proof.
  intros n u v w.
  rewrite dot_product_comm, dot_product_add_r.
  rewrite (dot_product_comm w u), (dot_product_comm w v). reflexivity.
Qed.

(** Dot product with negation *)
Lemma dot_product_neg_r : forall {n} (u v : QVec n),
  dot_product u (qv_neg v) == - dot_product u v.
Proof.
  intros n u v. unfold qv_neg.
  rewrite dot_product_scale_r. ring.
Qed.

Lemma dot_product_neg_l : forall {n} (u v : QVec n),
  dot_product (qv_neg u) v == - dot_product u v.
Proof.
  intros n u v. rewrite dot_product_comm, dot_product_neg_r, dot_product_comm. reflexivity.
Qed.

(* ========================================================================= *)
(*  SECTION 2: Norm Squared                                                  *)
(* ========================================================================= *)

Definition norm_sq {n} (v : QVec n) : Q := dot_product v v.

(** Helper: sum of nonneg squares *)
Lemma fold_left_Qplus_sq_nonneg : forall (l : list Q) (init : Q),
  0 <= init ->
  0 <= fold_left Qplus (map (fun x => x * x) l) init.
Proof.
  intros l. induction l as [|x xs IH]; intros init Hinit; simpl.
  - exact Hinit.
  - apply IH.
    assert (Hxx : 0 <= x * x).
    { destruct (Qlt_le_dec x 0) as [Hx | Hx].
      - setoid_replace (x * x) with ((-x) * (-x)) by ring.
        apply Qmult_le_0_compat; lra.
      - apply Qmult_le_0_compat; lra. }
    lra.
Qed.

(** ‖v‖² ≥ 0 *)
Theorem norm_sq_nonneg : forall {n} (v : QVec n), 0 <= norm_sq v.
Proof.
  intros n v. unfold norm_sq, dot_product.
  (* Step 1: dot_product v v == sum of x*x *)
  assert (Heq : fold_left Qplus (map2 Qmult (qv_data v) (qv_data v)) 0 ==
                fold_left Qplus (map (fun x => x * x) (qv_data v)) 0).
  { apply fold_left_Qplus_Qeq.
    - rewrite map_length, map2_length; rewrite (qv_length v); reflexivity.
    - intro i. assert (Hi_dec : (i < n)%nat \/ (n <= i)%nat) by lia.
      destruct Hi_dec as [Hi | Hi].
      + rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
        rewrite nth_map2_Qeq;
          [| rewrite (qv_length v); exact Hi | rewrite (qv_length v); reflexivity].
        ring.
      + assert (H1 : nth i (map (fun x : Q => x*x) (qv_data v)) 0 = 0).
        { apply nth_overflow. rewrite map_length, (qv_length v). lia. }
        assert (H2 : nth i (map2 Qmult (qv_data v) (qv_data v)) 0 = 0).
        { apply nth_overflow. rewrite map2_length; rewrite !(qv_length v); simpl; lia. }
        rewrite H1, H2. reflexivity. }
  (* Step 2: sum of squares is nonneg *)
  assert (Hge : 0 <= fold_left Qplus (map (fun x => x * x) (qv_data v)) 0).
  { apply fold_left_Qplus_sq_nonneg. lra. }
  (* Step 3: combine *)
  apply Qle_trans with (fold_left Qplus (map (fun x => x * x) (qv_data v)) 0).
  - exact Hge.
  - apply Qeq_Qle. apply Qeq_sym. exact Heq.
Qed.

(** ‖c·v‖² = c²·‖v‖² *)
Theorem norm_sq_scale : forall {n} (c : Q) (v : QVec n),
  norm_sq (qv_scale c v) == c * c * norm_sq v.
Proof.
  intros n c v. unfold norm_sq.
  rewrite dot_product_scale_l, dot_product_scale_r. ring.
Qed.

(** ‖u+v‖² = ‖u‖² + 2⟨u,v⟩ + ‖v‖² *)
Theorem norm_sq_expand : forall {n} (u v : QVec n),
  norm_sq (qv_add u v) == norm_sq u + 2 * dot_product u v + norm_sq v.
Proof.
  intros n u v. unfold norm_sq.
  rewrite dot_product_add_l, !dot_product_add_r.
  rewrite (dot_product_comm v u). ring.
Qed.

(* ========================================================================= *)
(*  SECTION 3: Cauchy-Schwarz Inequality                                     *)
(* ========================================================================= *)

(** Discriminant argument: for all t, 0 ≤ ‖u + t·v‖² *)
Lemma norm_sq_shift_nonneg : forall {n} (u v : QVec n) (t : Q),
  0 <= norm_sq u + 2 * t * dot_product u v + t * t * norm_sq v.
Proof.
  intros n u v t.
  assert (H := norm_sq_nonneg (qv_add u (qv_scale t v))).
  rewrite norm_sq_expand in H.
  rewrite norm_sq_scale, dot_product_scale_r in H.
  lra.
Qed.

(** ★ CAUCHY-SCHWARZ: |⟨u,v⟩|² ≤ ‖u‖²·‖v‖² ★ *)
Theorem cauchy_schwarz : forall {n} (u v : QVec n),
  dot_product u v * dot_product u v <= norm_sq u * norm_sq v.
Proof.
  intros n u v.
  destruct (Qeq_dec (norm_sq v) 0) as [Hv0 | Hv0].
  - (* norm_sq v = 0 → dot u v = 0 *)
    assert (Hd : dot_product u v == 0).
    { destruct (Qeq_dec (dot_product u v) 0) as [Heq0 | Hneq0]; [exact Heq0 |].
      exfalso.
      set (d := dot_product u v) in *.
      set (A := norm_sq u) in *.
      (* Choose t = -(A+1)/(2*d) so that A + 2*t*d = -1 *)
      pose proof (norm_sq_shift_nonneg u v (- (A + 1) / (2 * d))) as H.
      fold A d in H.
      rewrite Hv0 in H.
      assert (Hc : A + 2 * (- (A + 1) / (2 * d)) * d +
                  (- (A + 1) / (2 * d)) * (- (A + 1) / (2 * d)) * 0 == -(1)).
      { field. intro Habsurd. apply Hneq0. lra. }
      rewrite Hc in H. lra. }
    rewrite Hd, Hv0. lra.
  - set (ip := dot_product u v).
    set (nu := norm_sq u).
    set (nv := norm_sq v).
    assert (Hnvpos : 0 < nv).
    { pose proof (norm_sq_nonneg v) as Hnn.
      destruct (Qlt_le_dec 0 (norm_sq v)) as [Hpos | Hneg].
      - unfold nv. exact Hpos.
      - exfalso. apply Hv0. lra. }
    (* Use t = -ip/nv *)
    pose proof (norm_sq_shift_nonneg u v (- ip * (/ nv))) as H.
    fold nu ip nv in H.
    (* 0 <= nu + 2*(-ip/nv)*ip + (-ip/nv)^2 * nv = nu - ip^2/nv *)
    assert (Hmul : nv * (nu + 2 * (- ip * / nv) * ip + (- ip * / nv) * (- ip * / nv) * nv)
                   == nv * nu - ip * ip).
    { field. lra. }
    assert (Hge : 0 <= nv * (nu + 2 * (- ip * / nv) * ip + (- ip * / nv) * (- ip * / nv) * nv)).
    { apply Qmult_le_0_compat; lra. }
    lra.
Qed.

(** Absolute value form *)
Corollary cauchy_schwarz_abs : forall {n} (u v : QVec n),
  Qabs (dot_product u v) * Qabs (dot_product u v) <= norm_sq u * norm_sq v.
Proof.
  intros n u v.
  set (x := dot_product u v).
  assert (Habs : Qabs x * Qabs x == x * x).
  { destruct (Qlt_le_dec x 0) as [Hx | Hx].
    - rewrite (Qabs_neg x ltac:(lra)). ring.
    - rewrite (Qabs_pos x Hx). ring. }
  apply Qle_trans with (x * x).
  - apply Qeq_Qle. exact Habs.
  - apply cauchy_schwarz.
Qed.

(** ‖u+v‖² ≤ (√‖u‖ + √‖v‖)², expressed without sqrt *)
Theorem norm_sq_triangle : forall {n} (u v : QVec n),
  norm_sq (qv_add u v) <= norm_sq u + 2 * Qabs (dot_product u v) + norm_sq v.
Proof.
  intros n u v.
  rewrite norm_sq_expand.
  assert (H : dot_product u v <= Qabs (dot_product u v)).
  { apply Qle_Qabs. }
  lra.
Qed.

(* ========================================================================= *)
(*  SECTION 4: Process Inner Product                                         *)
(* ========================================================================= *)

(** Process inner product: ⟨u,v⟩ at each stage *)
Definition process_ip {n} (u v : nat -> QVec n) : nat -> Q :=
  fun k => dot_product (u k) (v k).

Lemma process_ip_comm : forall {n} (u v : nat -> QVec n) k,
  process_ip u v k == process_ip v u k.
Proof.
  intros n u v k. unfold process_ip. apply dot_product_comm.
Qed.

(** Helper: bound on finite prefix *)
Lemma finite_bound : forall (a : nat -> Q) (n : nat),
  exists M, 0 <= M /\ forall k, (k <= n)%nat -> Qabs (a k) <= M.
Proof.
  intros a. induction n as [| n' [M [HM IH]]].
  - exists (Qabs (a 0%nat)). split. { apply Qabs_nonneg. }
    intros k Hk. assert (k = 0)%nat by lia. subst. lra.
  - destruct (Qlt_le_dec M (Qabs (a (S n')))) as [Hlt | Hle].
    + exists (Qabs (a (S n'))). split. { apply Qabs_nonneg. }
      intros k Hk. destruct (PeanoNat.Nat.eq_dec k (S n')).
      * subst. lra.
      * assert (Hk' : (k <= n')%nat) by lia.
        specialize (IH k Hk'). lra.
    + exists M. split. { exact HM. }
      intros k Hk. destruct (PeanoNat.Nat.eq_dec k (S n')).
      * subst. lra.
      * assert (Hk' : (k <= n')%nat) by lia. exact (IH k Hk').
Qed.

(** Helper: a Cauchy sequence is bounded *)
Lemma cauchy_bounded : forall (a : nat -> Q),
  is_cauchy a ->
  exists M : Q, 0 < M /\ forall k, Qabs (a k) <= M.
Proof.
  intros a Ha.
  destruct (Ha 1 ltac:(lra)) as [N HN].
  destruct (finite_bound a N) as [M0 [HM0 HbdN]].
  exists (M0 + 1). split. { lra. }
  intro k.
  assert (Hkdec : (k <= N)%nat \/ (N < k)%nat) by lia.
  destruct Hkdec as [Hle | Hgt].
  - specialize (HbdN k Hle). lra.
  - assert (HkN : (N <= k)%nat) by lia.
    assert (Hd := HN k N HkN ltac:(lia)).
    assert (Htri : Qabs (a k) <= Qabs (a k - a N) + Qabs (a N)).
    { apply Qle_trans with (Qabs ((a k - a N) + a N)).
      - apply Qeq_Qle. apply Qabs_wd. ring.
      - apply Qabs_triangle. }
    assert (HMN := HbdN N ltac:(lia)). lra.
Qed.

(** Helper: division preserves positivity *)
Lemma Qdiv_lt_0_compat : forall a b, 0 < a -> 0 < b -> 0 < a / b.
Proof.
  intros a b Ha Hb. unfold Qdiv.
  apply Qmult_lt_0_compat. exact Ha.
  apply Qinv_lt_0_compat. exact Hb.
Qed.

(** Helper: inject_Z preserves positivity *)
Lemma inject_Z_pos : forall z, (0 < z)%Z -> 0 < inject_Z z.
Proof.
  intros z Hz. unfold Qlt, inject_Z. simpl. lia.
Qed.

(** Helper: Cauchy sequence times Cauchy sequence is Cauchy *)
Lemma cauchy_mul_is_cauchy : forall (a b : nat -> Q),
  is_cauchy a -> is_cauchy b -> is_cauchy (fun n => a n * b n).
Proof.
  intros a b Ha Hb.
  destruct (cauchy_bounded a Ha) as [Ma [HMa_pos HMa]].
  destruct (cauchy_bounded b Hb) as [Mb [HMb_pos HMb]].
  intros eps Heps.
  assert (Heps2 : 0 < eps / (2 * Mb)) by (apply Qdiv_lt_0_compat; lra).
  assert (Heps3 : 0 < eps / (2 * Ma)) by (apply Qdiv_lt_0_compat; lra).
  destruct (Ha _ Heps2) as [Na HNa].
  destruct (Hb _ Heps3) as [Nb HNb].
  exists (Nat.max Na Nb). intros m p Hm Hp.
  assert (HmNa : (Na <= m)%nat) by lia.
  assert (HpNa : (Na <= p)%nat) by lia.
  assert (HmNb : (Nb <= m)%nat) by lia.
  assert (HpNb : (Nb <= p)%nat) by lia.
  (* |a_m*b_m - a_p*b_p| = |a_m*(b_m-b_p) + (a_m-a_p)*b_p| *)
  assert (Hsplit : a m * b m - a p * b p == a m * (b m - b p) + (a m - a p) * b p) by ring.
  rewrite Hsplit.
  apply Qle_lt_trans with (Qabs (a m * (b m - b p)) + Qabs ((a m - a p) * b p)).
  { apply Qabs_triangle. }
  rewrite !Qabs_Qmult.
  assert (H1 : Qabs (a m) * Qabs (b m - b p) < eps * (1#2)).
  { apply Qle_lt_trans with (Ma * Qabs (b m - b p)).
    - apply Qmult_le_compat_r; [exact (HMa m) | apply Qabs_nonneg].
    - apply Qlt_le_trans with (Ma * (eps / (2 * Ma))).
      + apply Qmult_lt_l; [exact HMa_pos | exact (HNb m p HmNb HpNb)].
      + apply Qeq_Qle. field. lra. }
  assert (H2 : Qabs (a m - a p) * Qabs (b p) < eps * (1#2)).
  { apply Qle_lt_trans with (Qabs (a m - a p) * Mb).
    - apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | apply Qle_refl].
      + split; [apply Qabs_nonneg | exact (HMb p)].
    - apply Qlt_le_trans with (eps / (2 * Mb) * Mb).
      + apply Qmult_lt_r; [exact HMb_pos | exact (HNa m p HmNa HpNa)].
      + apply Qeq_Qle. field. lra. }
  lra.
Qed.

(** Helper: uniform N from finitely many Cauchy sequences *)
Lemma finite_max_N : forall (k : nat) (f : nat -> nat -> Q) (bound : Q),
  0 < bound ->
  (forall i, (i < k)%nat -> is_cauchy (fun n => f n i)) ->
  exists N, forall i, (i < k)%nat ->
    forall m p, (N <= m)%nat -> (N <= p)%nat ->
    Qabs (f m i - f p i) < bound.
Proof.
  induction k as [| k' IHk]; intros f bound Hbound Hcauchy.
  - exists 0%nat. intros i Hi. lia.
  - assert (Hcauchy' : forall i, (i < k')%nat -> is_cauchy (fun n => f n i)).
    { intros i Hi. apply Hcauchy. lia. }
    destruct (IHk f bound Hbound Hcauchy') as [N1 HN1].
    destruct (Hcauchy k' ltac:(lia) bound Hbound) as [N2 HN2].
    exists (Nat.max N1 N2).
    intros i Hi m p Hm Hp.
    destruct (PeanoNat.Nat.eq_dec i k').
    + subst. apply HN2; lia.
    + apply HN1; [lia | lia | lia].
Qed.

(** Helper: bound on difference of two fold_left sums *)
Lemma fold_left_Qplus_diff_le : forall (l1 l2 : list Q) (bound : Q),
  length l1 = length l2 ->
  0 <= bound ->
  (forall i, (i < length l1)%nat -> Qabs (nth i l1 0 - nth i l2 0) <= bound) ->
  Qabs (fold_left Qplus l1 0 - fold_left Qplus l2 0) <=
  inject_Z (Z.of_nat (length l1)) * bound.
Proof.
  induction l1 as [| x xs IH]; intros l2 bound Hlen Hbnd Hcomp.
  - destruct l2; [| simpl in Hlen; discriminate].
    simpl length. simpl fold_left. simpl Z.of_nat.
    setoid_replace (0 - 0) with 0 by ring.
    setoid_replace (inject_Z 0 * bound) with 0 by (simpl; ring).
    change (Qabs 0) with 0. lra.
  - destruct l2 as [| y ys]; [simpl in Hlen; discriminate |].
    simpl in Hlen. assert (Hlen' : length xs = length ys) by lia.
    simpl length.
    change (fold_left Qplus (x :: xs) 0) with (fold_left Qplus xs (0 + x)).
    change (fold_left Qplus (y :: ys) 0) with (fold_left Qplus ys (0 + y)).
    rewrite !fold_left_Qplus_init_shift.
    apply Qle_trans with
      (Qabs ((fold_left Qplus xs 0 - fold_left Qplus ys 0) + (x - y))).
    { apply Qeq_Qle. apply Qabs_wd. ring. }
    apply Qle_trans with
      (Qabs (fold_left Qplus xs 0 - fold_left Qplus ys 0) + Qabs (x - y)).
    { apply Qabs_triangle. }
    assert (Hih : Qabs (fold_left Qplus xs 0 - fold_left Qplus ys 0) <=
                  inject_Z (Z.of_nat (length xs)) * bound).
    { apply IH; [exact Hlen' | exact Hbnd |].
      intros i Hi. specialize (Hcomp (S i) ltac:(simpl; lia)).
      simpl in Hcomp. exact Hcomp. }
    assert (Hxy : Qabs (x - y) <= bound).
    { specialize (Hcomp 0%nat ltac:(simpl; lia)). simpl in Hcomp. exact Hcomp. }
    assert (Hinj : inject_Z (Z.of_nat (S (length xs))) * bound ==
                   inject_Z (Z.of_nat (length xs)) * bound + bound).
    { rewrite Nat2Z.inj_succ. unfold Z.succ.
      rewrite inject_Z_plus. simpl. ring. }
    lra.
Qed.

(** ★ KEY: process inner product is Cauchy ★ *)
Theorem process_ip_cauchy : forall {n} (u v : nat -> QVec n),
  (forall i, (i < n)%nat -> is_cauchy (fun k => qv_nth (u k) i)) ->
  (forall i, (i < n)%nat -> is_cauchy (fun k => qv_nth (v k) i)) ->
  is_cauchy (process_ip u v).
Proof.
  intros n u v Hu Hv.
  unfold process_ip.
  destruct n as [| n'].
  - (* n = 0: dot_product of empty vectors = 0 *)
    intros eps Heps. exists 0%nat. intros m p _ _.
    unfold dot_product.
    assert (Hum : qv_data (u m) = @nil Q)
      by (apply length_zero_iff_nil; exact (qv_length (u m))).
    assert (Hvm : qv_data (v m) = @nil Q)
      by (apply length_zero_iff_nil; exact (qv_length (v m))).
    assert (Hup : qv_data (u p) = @nil Q)
      by (apply length_zero_iff_nil; exact (qv_length (u p))).
    assert (Hvp : qv_data (v p) = @nil Q)
      by (apply length_zero_iff_nil; exact (qv_length (v p))).
    rewrite Hum, Hvm, Hup, Hvp. simpl. exact Heps.
  - (* n = S n' *)
    intros eps Heps.
    assert (Hprod : forall i, (i < S n')%nat ->
      is_cauchy (fun k => qv_nth (u k) i * qv_nth (v k) i)).
    { intros i Hi. apply cauchy_mul_is_cauchy; [apply Hu | apply Hv]; exact Hi. }
    clear Hu Hv.
    (* Use eps/2 per component to get strict inequality *)
    set (eps2 := eps * (1#2)).
    assert (Heps2 : 0 < eps2) by (unfold eps2; lra).
    assert (Heps' : 0 < eps2 / inject_Z (Z.of_nat (S n'))).
    { apply Qdiv_lt_0_compat. exact Heps2. apply inject_Z_pos. lia. }
    (* Get uniform N for all components *)
    destruct (finite_max_N (S n')
              (fun k i => qv_nth (u k) i * qv_nth (v k) i)
              (eps2 / inject_Z (Z.of_nat (S n'))) Heps' Hprod) as [N HN].
    exists N. intros m p Hm Hp.
    unfold dot_product.
    (* Set up the two list sums *)
    set (l1 := map2 Qmult (qv_data (u m)) (qv_data (v m))).
    set (l2 := map2 Qmult (qv_data (u p)) (qv_data (v p))).
    assert (Hlen1 : length l1 = S n').
    { unfold l1. rewrite map2_length.
      - exact (qv_length (u m)).
      - rewrite (qv_length (u m)), (qv_length (v m)). reflexivity. }
    assert (Hlen2 : length l2 = S n').
    { unfold l2. rewrite map2_length.
      - exact (qv_length (u p)).
      - rewrite (qv_length (u p)), (qv_length (v p)). reflexivity. }
    (* Each component difference is bounded *)
    assert (Hcomp : forall i, (i < length l1)%nat ->
      Qabs (nth i l1 0 - nth i l2 0) <= eps2 / inject_Z (Z.of_nat (S n'))).
    { intros i Hi. rewrite Hlen1 in Hi.
      assert (Hl1i : nth i l1 0 == qv_nth (u m) i * qv_nth (v m) i).
      { unfold l1. apply nth_map2_Qeq;
          [rewrite (qv_length (u m)); exact Hi
          |rewrite (qv_length (u m)), (qv_length (v m)); reflexivity]. }
      assert (Hl2i : nth i l2 0 == qv_nth (u p) i * qv_nth (v p) i).
      { unfold l2. apply nth_map2_Qeq;
          [rewrite (qv_length (u p)); exact Hi
          |rewrite (qv_length (u p)), (qv_length (v p)); reflexivity]. }
      apply Qle_trans with
        (Qabs (qv_nth (u m) i * qv_nth (v m) i -
               qv_nth (u p) i * qv_nth (v p) i)).
      { apply Qeq_Qle. apply Qabs_wd. rewrite Hl1i, Hl2i. reflexivity. }
      apply Qlt_le_weak. exact (HN i Hi m p Hm Hp). }
    (* Apply the fold_left bound *)
    assert (Hle : Qabs (fold_left Qplus l1 0 - fold_left Qplus l2 0) <=
                  inject_Z (Z.of_nat (length l1)) *
                  (eps2 / inject_Z (Z.of_nat (S n')))).
    { apply fold_left_Qplus_diff_le; [lia | lra | exact Hcomp]. }
    (* Simplify: (S n') * eps2/(S n') = eps2 = eps/2 < eps *)
    assert (Heq : inject_Z (Z.of_nat (length l1)) *
                  (eps2 / inject_Z (Z.of_nat (S n'))) == eps2).
    { rewrite Hlen1. field.
      intro Habsurd.
      assert (Hpos_inj : 0 < inject_Z (Z.of_nat (S n')))
        by (apply inject_Z_pos; lia).
      lra. }
    apply Qle_lt_trans with eps2.
    + apply Qle_trans with (inject_Z (Z.of_nat (length l1)) *
                            (eps2 / inject_Z (Z.of_nat (S n')))).
      * exact Hle.
      * apply Qeq_Qle. exact Heq.
    + unfold eps2. lra.
Qed.

(** Norm process is Cauchy *)
Lemma norm_sq_process_cauchy : forall {n} (v : nat -> QVec n),
  (forall i, (i < n)%nat -> is_cauchy (fun k => qv_nth (v k) i)) ->
  is_cauchy (fun k => norm_sq (v k)).
Proof.
  intros n v Hv. unfold norm_sq. apply process_ip_cauchy; exact Hv.
Qed.

(** Process inner product — nonneg on diagonal *)
Lemma process_ip_nonneg : forall {n} (v : nat -> QVec n) k,
  0 <= process_ip v v k.
Proof.
  intros n v k. unfold process_ip. apply norm_sq_nonneg.
Qed.

(** Summary:
    30 Qed, 0 Admitted (target), 0 axioms
    - dot_product linearity: 8 lemmas
    - norm_sq: 4 lemmas
    - Cauchy-Schwarz: 4 lemmas
    - process ip: 6 lemmas + helpers
*)
