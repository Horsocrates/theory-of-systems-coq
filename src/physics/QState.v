(* ========================================================================= *)
(*        QSTATE — Quantum States as Convergent Processes                   *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                 *)
(*                                                                          *)
(*  A quantum state is a process (nat → QVec dim) whose components are     *)
(*  Cauchy sequences: the state converges. This models the ToS principle    *)
(*  P4 (Infinity as Process): no completed infinity, only convergent        *)
(*  processes.                                                              *)
(*                                                                          *)
(*  Elements: QState records, basis states, state inner product             *)
(*  Roles:    state → carrier of quantum information                       *)
(*  Rules:    component-wise Cauchy (convergence), norm ≈ 1 (L5)           *)
(*  Status:   convergent state | basis state | superposition               *)
(*                                                                          *)
(*  STATUS: ~25 Qed, 0 Admitted                                            *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import ProcessGeneral.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.

(* ========================================================================= *)
(*  SECTION 1: Quantum State Definition                                     *)
(* ========================================================================= *)

(** A quantum state in dimension dim: a process of vectors whose
    components each form a Cauchy sequence *)
Record QState (dim : nat) := mkQState {
  qs_seq : nat -> QVec dim;
  qs_cauchy : forall i, (i < dim)%nat ->
    is_cauchy (fun k => qv_nth (qs_seq k) i)
}.

(** Access state at a given step *)
Definition state_at {dim} (s : QState dim) (k : nat) : QVec dim :=
  qs_seq dim s k.

(* ========================================================================= *)
(*  SECTION 2: State Equivalence                                            *)
(* ========================================================================= *)

(** Two states are equivalent if their components converge to the same
    limits (co-Cauchy condition, component-wise) *)
Definition state_equiv {dim} (s1 s2 : QState dim) : Prop :=
  forall i, (i < dim)%nat ->
    forall eps, 0 < eps ->
      exists N, forall k, (N <= k)%nat ->
        Qabs (qv_nth (state_at s1 k) i - qv_nth (state_at s2 k) i) < eps.

Notation "s1 ≈ s2" := (state_equiv s1 s2) (at level 70).

Lemma state_equiv_refl : forall {dim} (s : QState dim),
  s ≈ s.
Proof.
  intros dim s i Hi eps Heps.
  exists 0%nat. intros k _.
  setoid_replace (qv_nth (state_at s k) i - qv_nth (state_at s k) i) with 0 by ring.
  rewrite Qabs_pos; lra.
Qed.

Lemma state_equiv_sym : forall {dim} (s1 s2 : QState dim),
  s1 ≈ s2 -> s2 ≈ s1.
Proof.
  intros dim s1 s2 H12 i Hi eps Heps.
  destruct (H12 i Hi eps Heps) as [N HN].
  exists N. intros k Hk.
  specialize (HN k Hk).
  set (a := qv_nth (state_at s1 k) i) in *.
  set (b := qv_nth (state_at s2 k) i) in *.
  assert (Hopp : b - a == -(a - b)) by ring.
  assert (Habs := Qabs_wd _ _ Hopp). rewrite Habs.
  rewrite Qabs_opp. exact HN.
Qed.

Lemma state_equiv_trans : forall {dim} (s1 s2 s3 : QState dim),
  s1 ≈ s2 -> s2 ≈ s3 -> s1 ≈ s3.
Proof.
  intros dim s1 s2 s3 H12 H23 i Hi eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (H12 i Hi _ Heps2) as [N1 HN1].
  destruct (H23 i Hi _ Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros k Hk.
  assert (Hk1 : (N1 <= k)%nat) by lia.
  assert (Hk2 : (N2 <= k)%nat) by lia.
  apply Qle_lt_trans with
    (Qabs (qv_nth (state_at s1 k) i - qv_nth (state_at s2 k) i) +
     Qabs (qv_nth (state_at s2 k) i - qv_nth (state_at s3 k) i)).
  - apply Qle_trans with
      (Qabs ((qv_nth (state_at s1 k) i - qv_nth (state_at s2 k) i) +
             (qv_nth (state_at s2 k) i - qv_nth (state_at s3 k) i))).
    + apply Qeq_Qle. apply Qabs_wd.
      set (a := qv_nth (state_at s1 k) i).
      set (b := qv_nth (state_at s2 k) i).
      set (c := qv_nth (state_at s3 k) i).
      ring.
    + apply Qabs_triangle.
  - specialize (HN1 k Hk1). specialize (HN2 k Hk2). lra.
Qed.

(* ========================================================================= *)
(*  SECTION 3: Basis States                                                 *)
(* ========================================================================= *)

(** Standard basis vector: e_j has 1 at position j, 0 elsewhere *)
Definition basis_vec (dim j : nat) : QVec dim.
Proof.
  refine (mkQVec (map (fun i => if Nat.eq_dec i j then 1 else 0)
                      (seq 0 dim)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

(** Helper: nth of map over nat list *)
Lemma nth_map_nat_Q : forall (f : nat -> Q) (l : list nat) (i : nat),
  (i < length l)%nat ->
  nth i (map f l) 0 == f (nth i l 0%nat).
Proof.
  intros f l. induction l as [| x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i; [reflexivity | apply IH; lia].
Qed.

(** Basis vector component access *)
Lemma basis_vec_same : forall dim j,
  (j < dim)%nat -> qv_nth (basis_vec dim j) j == 1.
Proof.
  intros dim j Hj. unfold qv_nth, basis_vec. simpl.
  rewrite nth_map_nat_Q; [| rewrite seq_length; exact Hj].
  rewrite seq_nth; [| exact Hj]. simpl.
  destruct (Nat.eq_dec j j); [reflexivity | contradiction].
Qed.

Lemma basis_vec_diff : forall dim i j,
  (i < dim)%nat -> i <> j -> qv_nth (basis_vec dim j) i == 0.
Proof.
  intros dim i j Hi Hij. unfold qv_nth, basis_vec. simpl.
  rewrite nth_map_nat_Q; [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  destruct (Nat.eq_dec i j); [contradiction | reflexivity].
Qed.

(** Constant process: same vector at every step *)
Definition const_state {dim} (v : QVec dim) : QState dim.
Proof.
  refine (mkQState dim (fun _ => v) _).
  intros i Hi. intros eps Heps.
  exists 0%nat. intros m p _ _.
  setoid_replace (qv_nth v i - qv_nth v i) with 0 by ring.
  rewrite Qabs_pos; lra.
Defined.

(** Basis state: constant process of basis vector *)
Definition basis_state (dim j : nat) : QState dim :=
  const_state (basis_vec dim j).

(** Basis state at any step is the basis vector *)
Lemma basis_state_at : forall dim j k,
  state_at (basis_state dim j) k = basis_vec dim j.
Proof.
  intros dim j k. unfold state_at, basis_state, const_state. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*  SECTION 4: State Inner Product                                          *)
(* ========================================================================= *)

(** Inner product of two states at step k *)
Definition state_ip_at {dim} (s1 s2 : QState dim) (k : nat) : Q :=
  dot_product (state_at s1 k) (state_at s2 k).

(** State inner product is Cauchy *)
Theorem state_ip_cauchy : forall {dim} (s1 s2 : QState dim),
  is_cauchy (state_ip_at s1 s2).
Proof.
  intros dim s1 s2.
  unfold state_ip_at.
  apply process_ip_cauchy.
  - intros i Hi. exact (qs_cauchy dim s1 i Hi).
  - intros i Hi. exact (qs_cauchy dim s2 i Hi).
Qed.

(** State inner product as a CauchySeq *)
Definition state_ip {dim} (s1 s2 : QState dim) : CauchySeq :=
  mkCauchy (state_ip_at s1 s2) (state_ip_cauchy s1 s2).

(** State inner product is commutative *)
Lemma state_ip_comm : forall {dim} (s1 s2 : QState dim) k,
  state_ip_at s1 s2 k == state_ip_at s2 s1 k.
Proof.
  intros dim s1 s2 k. unfold state_ip_at.
  apply dot_product_comm.
Qed.

(** State inner product is linear in second argument *)
Lemma state_ip_linear_scale : forall {dim} (s : QState dim) (c : Q) (v : QVec dim) k,
  dot_product (state_at s k) (qv_scale c v) == c * dot_product (state_at s k) v.
Proof.
  intros dim s c v k.
  apply dot_product_scale_r.
Qed.

(** State self-inner-product is nonneg *)
Lemma state_ip_nonneg : forall {dim} (s : QState dim) k,
  0 <= state_ip_at s s k.
Proof.
  intros dim s k. unfold state_ip_at.
  apply norm_sq_nonneg.
Qed.

(* ========================================================================= *)
(*  SECTION 5: State Operations                                             *)
(* ========================================================================= *)

(** Scale a state by a rational constant *)
Definition state_scale {dim} (c : Q) (s : QState dim) : QState dim.
Proof.
  refine (mkQState dim (fun k => qv_scale c (state_at s k)) _).
  intros i Hi eps Heps.
  assert (Hsc_m : forall k, qv_nth (qv_scale c (state_at s k)) i == c * qv_nth (state_at s k) i).
  { intros k. apply qv_scale_nth. exact Hi. }
  destruct (Qeq_dec c 0) as [Hc0 | Hcnz].
  - exists 0%nat. intros m p _ _.
    assert (Heq : qv_nth (qv_scale c (state_at s m)) i -
                  qv_nth (qv_scale c (state_at s p)) i == 0).
    { rewrite !Hsc_m. rewrite Hc0. ring. }
    assert (Habs := Qabs_wd _ _ Heq). rewrite Habs.
    rewrite Qabs_pos; lra.
  - assert (Hcpos : 0 < Qabs c).
    { destruct (Qlt_le_dec 0 c).
      - rewrite Qabs_pos; lra.
      - rewrite Qabs_neg; [lra |].
        destruct (Qeq_dec c 0); [contradiction | lra]. }
    assert (Heps' : 0 < eps / Qabs c).
    { apply Qdiv_lt_0_compat; assumption. }
    destruct (qs_cauchy dim s i Hi _ Heps') as [N HN].
    exists N. intros m p Hm Hp.
    assert (Heq : qv_nth (qv_scale c (state_at s m)) i -
                  qv_nth (qv_scale c (state_at s p)) i ==
                  c * (qv_nth (state_at s m) i - qv_nth (state_at s p) i)).
    { rewrite !Hsc_m. ring. }
    assert (Habs := Qabs_wd _ _ Heq). rewrite Habs.
    rewrite Qabs_Qmult.
    apply Qlt_le_trans with (Qabs c * (eps / Qabs c)).
    + apply Qmult_lt_l; [exact Hcpos | exact (HN m p Hm Hp)].
    + apply Qeq_Qle. field. lra.
Defined.

(** Add two states component-wise *)
Definition state_add {dim} (s1 s2 : QState dim) : QState dim.
Proof.
  refine (mkQState dim (fun k => qv_add (state_at s1 k) (state_at s2 k)) _).
  intros i Hi eps Heps.
  set (eps2 := eps * (1#2)).
  assert (Heps2 : 0 < eps2) by (unfold eps2; lra).
  destruct (qs_cauchy dim s1 i Hi _ Heps2) as [N1 HN1].
  destruct (qs_cauchy dim s2 i Hi _ Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros m p Hm Hp.
  assert (Hadd_m : qv_nth (qv_add (state_at s1 m) (state_at s2 m)) i ==
                   qv_nth (state_at s1 m) i + qv_nth (state_at s2 m) i)
    by (apply qv_add_nth; exact Hi).
  assert (Hadd_p : qv_nth (qv_add (state_at s1 p) (state_at s2 p)) i ==
                   qv_nth (state_at s1 p) i + qv_nth (state_at s2 p) i)
    by (apply qv_add_nth; exact Hi).
  assert (Heq : qv_nth (qv_add (state_at s1 m) (state_at s2 m)) i -
                qv_nth (qv_add (state_at s1 p) (state_at s2 p)) i ==
                (qv_nth (state_at s1 m) i - qv_nth (state_at s1 p) i) +
                (qv_nth (state_at s2 m) i - qv_nth (state_at s2 p) i))
    by (rewrite Hadd_m, Hadd_p; ring).
  assert (Habs := Qabs_wd _ _ Heq). rewrite Habs.
  set (x := Qabs (qv_nth (state_at s1 m) i - qv_nth (state_at s1 p) i)).
  set (y := Qabs (qv_nth (state_at s2 m) i - qv_nth (state_at s2 p) i)).
  apply Qle_lt_trans with (x + y).
  { apply Qabs_triangle. }
  assert (H1 : x < eps2) by (apply HN1; lia).
  assert (H2 : y < eps2) by (apply HN2; lia).
  unfold eps2 in *. lra.
Defined.

(** Scale preserves state equivalence *)
Lemma state_scale_compat : forall {dim} (c : Q) (s1 s2 : QState dim),
  s1 ≈ s2 -> state_scale c s1 ≈ state_scale c s2.
Proof.
  intros dim c s1 s2 Heq i Hi eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hcnz].
  - exists 0%nat. intros k _.
    change (state_at (state_scale c s1) k) with (qv_scale c (state_at s1 k)).
    change (state_at (state_scale c s2) k) with (qv_scale c (state_at s2 k)).
    assert (Hsc1 := qv_scale_nth c (state_at s1 k) i Hi).
    assert (Hsc2 := qv_scale_nth c (state_at s2 k) i Hi).
    assert (Hdiff : qv_nth (qv_scale c (state_at s1 k)) i -
                    qv_nth (qv_scale c (state_at s2 k)) i == 0).
    { rewrite Hsc1, Hsc2, Hc0. ring. }
    assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
    rewrite Qabs_pos; lra.
  - assert (Hcpos : 0 < Qabs c).
    { destruct (Qlt_le_dec 0 c).
      - rewrite Qabs_pos; lra.
      - rewrite Qabs_neg; [lra |].
        destruct (Qeq_dec c 0); [contradiction | lra]. }
    assert (Heps' : 0 < eps / Qabs c).
    { apply Qdiv_lt_0_compat; assumption. }
    destruct (Heq i Hi _ Heps') as [N HN].
    exists N. intros k Hk.
    change (state_at (state_scale c s1) k) with (qv_scale c (state_at s1 k)).
    change (state_at (state_scale c s2) k) with (qv_scale c (state_at s2 k)).
    assert (Hsc1 := qv_scale_nth c (state_at s1 k) i Hi).
    assert (Hsc2 := qv_scale_nth c (state_at s2 k) i Hi).
    assert (Hdiff : qv_nth (qv_scale c (state_at s1 k)) i -
                    qv_nth (qv_scale c (state_at s2 k)) i ==
                    c * (qv_nth (state_at s1 k) i - qv_nth (state_at s2 k) i)).
    { rewrite Hsc1, Hsc2. ring. }
    assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
    rewrite Qabs_Qmult.
    apply Qlt_le_trans with (Qabs c * (eps / Qabs c)).
    + apply Qmult_lt_l; [exact Hcpos |].
      exact (HN k Hk).
    + apply Qeq_Qle. field. lra.
Qed.

(* ========================================================================= *)
(*  SECTION 6: Basis State Properties                                       *)
(* ========================================================================= *)

(** Helper: fold_left Qplus of all-zero terms is 0 *)
Lemma fold_left_Qplus_zero_terms : forall (l : list Q),
  (forall idx, (idx < length l)%nat -> nth idx l 0 == 0) ->
  fold_left Qplus l 0 == 0.
Proof.
  induction l as [| x xs IH]; intros Hterms.
  - simpl. reflexivity.
  - simpl. rewrite fold_left_Qplus_init_shift.
    assert (Hx0 : x == 0).
    { specialize (Hterms 0%nat ltac:(simpl; lia)). simpl in Hterms. exact Hterms. }
    rewrite Hx0.
    assert (IHxs : fold_left Qplus xs 0 == 0).
    { apply IH. intros idx Hidx.
      specialize (Hterms (S idx) ltac:(simpl; lia)).
      simpl in Hterms. exact Hterms. }
    rewrite IHxs. ring.
Qed.

(** Basis states are orthogonal *)
Lemma basis_orthogonal_direct : forall dim i j k,
  (i < dim)%nat -> (j < dim)%nat -> i <> j ->
  state_ip_at (basis_state dim i) (basis_state dim j) k == 0.
Proof.
  intros dim i j k Hi Hj Hij.
  unfold state_ip_at. rewrite !basis_state_at.
  unfold dot_product.
  set (li := qv_data (basis_vec dim i)).
  set (lj := qv_data (basis_vec dim j)).
  assert (Hlen : length li = length lj).
  { unfold li, lj. rewrite !(qv_length _). reflexivity. }
  assert (Hlen_i : length li = dim).
  { unfold li. exact (qv_length (basis_vec dim i)). }
  set (prods := map2 Qmult li lj).
  assert (Hlen2 : length prods = dim).
  { unfold prods. rewrite map2_length; [exact Hlen_i | exact Hlen]. }
  apply fold_left_Qplus_zero_terms.
  intros idx Hidx. rewrite Hlen2 in Hidx.
  unfold prods.
  assert (Hidx_li : (idx < length li)%nat) by (rewrite Hlen_i; exact Hidx).
  rewrite nth_map2_Qeq; [| exact Hidx_li | exact Hlen].
  unfold li, lj.
  (* Now: nth idx (qv_data (basis_vec dim i)) 0 * nth idx (qv_data (basis_vec dim j)) 0 == 0 *)
  (* Use basis_vec_same/diff *)
  change (nth idx (qv_data (basis_vec dim i)) 0) with (qv_nth (basis_vec dim i) idx).
  change (nth idx (qv_data (basis_vec dim j)) 0) with (qv_nth (basis_vec dim j) idx).
  destruct (Nat.eq_dec idx i) as [Heqi | Hneqi].
  - subst idx. rewrite basis_vec_same; [| exact Hi].
    rewrite basis_vec_diff; [| exact Hi | exact Hij].
    ring.
  - rewrite basis_vec_diff; [| exact Hidx | exact Hneqi].
    ring.
Qed.

(** Helper: sum with exactly one nonzero term at position j *)
Lemma fold_left_Qplus_single_one : forall (l : list Q) (j : nat),
  (j < length l)%nat ->
  (forall idx, (idx < length l)%nat ->
    nth idx l 0 == (if Nat.eq_dec idx j then 1 else 0)) ->
  fold_left Qplus l 0 == 1.
Proof.
  intros l. induction l as [| x xs IH]; intros j Hj Hterms.
  - simpl in Hj. lia.
  - simpl. rewrite fold_left_Qplus_init_shift.
    assert (Hx : x == if Nat.eq_dec 0 j then 1 else 0).
    { specialize (Hterms 0%nat ltac:(simpl; lia)). simpl in Hterms. exact Hterms. }
    destruct (Nat.eq_dec 0 j) as [H0j | H0j].
    + subst j. rewrite Hx.
      assert (Hrest : fold_left Qplus xs 0 == 0).
      { apply fold_left_Qplus_zero_terms. intros idx Hidx.
        assert (Hs := Hterms (S idx) ltac:(simpl; lia)).
        simpl in Hs. destruct (Nat.eq_dec (S idx) 0); [lia |]. exact Hs. }
      rewrite Hrest. ring.
    + rewrite Hx. ring_simplify.
      assert (Hpred_j : (j - 1 < length xs)%nat) by (simpl in Hj; lia).
      assert (Hpred_terms : forall idx, (idx < length xs)%nat ->
        nth idx xs 0 == (if Nat.eq_dec idx (j - 1) then 1 else 0)).
      { intros idx Hidx.
        assert (Hs := Hterms (S idx) ltac:(simpl; lia)).
        change (nth (S idx) (x :: xs) 0) with (nth idx xs 0) in Hs.
        (* Hs : nth idx xs 0 == (if Nat.eq_dec (S idx) j then 1 else 0) *)
        destruct (Nat.eq_dec (S idx) j) as [HSj | HnSj];
          simpl in Hs;
          destruct (Nat.eq_dec idx (j - 1)) as [Hjm | Hnjm].
        - exact Hs.
        - exfalso. apply Hnjm. lia.
        - exfalso. apply HnSj. lia.
        - exact Hs. }
      exact (IH (j - 1)%nat Hpred_j Hpred_terms).
Qed.

(** Basis self-inner-product *)
Lemma basis_self_ip : forall dim j k,
  (j < dim)%nat ->
  state_ip_at (basis_state dim j) (basis_state dim j) k == 1.
Proof.
  intros dim j k Hj.
  unfold state_ip_at. rewrite !basis_state_at.
  unfold dot_product.
  set (l := qv_data (basis_vec dim j)).
  assert (Hlen : length l = dim).
  { unfold l. exact (qv_length (basis_vec dim j)). }
  set (prods := map2 Qmult l l).
  assert (Hlen2 : length prods = dim).
  { unfold prods. rewrite map2_length; [exact Hlen | reflexivity]. }
  apply fold_left_Qplus_single_one with (j := j).
  - rewrite Hlen2. exact Hj.
  - intros idx Hidx. rewrite Hlen2 in Hidx.
    unfold prods.
    assert (Hidx_l : (idx < length l)%nat) by (rewrite Hlen; exact Hidx).
    rewrite nth_map2_Qeq; [| exact Hidx_l | reflexivity].
    change (nth idx l 0) with (qv_nth (basis_vec dim j) idx).
    destruct (Nat.eq_dec idx j) as [Heq | Hneq].
    + subst idx. rewrite basis_vec_same; [ring | exact Hj].
    + rewrite basis_vec_diff; [ring | exact Hidx | exact Hneq].
Qed.

(** Basis states of different indices are inequivalent *)
Lemma basis_state_distinct : forall dim i j,
  (i < dim)%nat -> (j < dim)%nat -> i <> j ->
  ~ (basis_state dim i ≈ basis_state dim j).
Proof.
  intros dim i j Hi Hj Hij Heq.
  specialize (Heq i Hi (1#2) ltac:(lra)).
  destruct Heq as [N HN].
  specialize (HN N ltac:(lia)).
  rewrite !basis_state_at in HN.
  (* HN : Qabs (qv_nth (basis_vec dim i) i - qv_nth (basis_vec dim j) i) < 1#2 *)
  assert (Hval : qv_nth (basis_vec dim i) i - qv_nth (basis_vec dim j) i == 1).
  { rewrite (basis_vec_same dim i Hi). rewrite (basis_vec_diff dim i j Hi Hij). ring. }
  assert (Habs := Qabs_wd _ _ Hval).
  (* Habs : Qabs (...) == Qabs 1 *)
  assert (Habs1 : Qabs 1 == 1) by (rewrite Qabs_pos; lra).
  assert (Hfull : Qabs (qv_nth (basis_vec dim i) i - qv_nth (basis_vec dim j) i) == 1).
  { transitivity (Qabs 1); assumption. }
  lra.
Qed.

(** Norm of basis state is 1 *)
Lemma basis_state_normalized : forall dim j k,
  (j < dim)%nat ->
  norm_sq (state_at (basis_state dim j) k) == 1.
Proof.
  intros dim j k Hj.
  unfold norm_sq. rewrite basis_state_at.
  (* This is just basis_self_ip specialized *)
  change (dot_product (basis_vec dim j) (basis_vec dim j)) with
    (state_ip_at (basis_state dim j) (basis_state dim j) k).
  apply basis_self_ip. exact Hj.
Qed.

(* ========================================================================= *)
(*  SECTION 7: Cauchy-Schwarz for States                                    *)
(* ========================================================================= *)

(** Cauchy-Schwarz at each step *)
Lemma state_cauchy_schwarz : forall {dim} (s1 s2 : QState dim) k,
  state_ip_at s1 s2 k * state_ip_at s1 s2 k <=
  state_ip_at s1 s1 k * state_ip_at s2 s2 k.
Proof.
  intros dim s1 s2 k. unfold state_ip_at.
  apply cauchy_schwarz.
Qed.

(** Summary:
    ~25 Qed, 0 Admitted, 0 axioms
    - State definition: QState record, state_at accessor
    - Equivalence: refl, sym, trans
    - Basis: basis_vec (with same/diff lemmas), const_state, basis_state
    - Inner product: state_ip_at, state_ip_cauchy, state_ip (CauchySeq),
      comm, linear_scale, nonneg
    - Operations: state_scale, state_add + compat
    - Basis properties: orthogonal, self_ip = 1, distinct, normalized
    - Cauchy-Schwarz for states
*)
