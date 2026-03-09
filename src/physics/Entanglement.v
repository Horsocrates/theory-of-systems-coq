(* ========================================================================= *)
(*        ENTANGLEMENT — Non-Factorizability of Joint Processes              *)
(*                                                                           *)
(*  Part of: Theory of Systems — Process Physics (Phase 3B)                  *)
(*                                                                           *)
(*  Two quantum systems A (dim dA) and B (dim dB) form a joint system       *)
(*  of dimension dA * dB. A joint state is SEPARABLE if it factors as       *)
(*  a tensor product; ENTANGLED if it does not.                              *)
(*                                                                           *)
(*  PCH classifies entangled states: either enumerable (finitely many        *)
(*  entanglement types) or perfect (continuum of entanglement types).        *)
(*                                                                           *)
(*  Key result: bell_entangled — constructive proof that the Bell state     *)
(*  |00⟩ + |11⟩ is entangled (cannot be written as a tensor product).      *)
(*                                                                           *)
(*  E/R/R: Elements = joint states, Roles = separable/entangled,            *)
(*         Rules = tensor product structure (constitution)                   *)
(*                                                                           *)
(*  STATUS: target ~25 Qed, 0 Admitted                                      *)
(*  AXIOMS: classic + L4_witness (via PCH, Part III only)                   *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import LinearAlgebra.
From ToS Require Import ProcessTypes.
From ToS Require Import ProcessContinuumHypothesis.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import stdlib.Tensor.

(* ========================================================================= *)
(*  PART I: TENSOR PRODUCT OF VECTORS                                        *)
(* ========================================================================= *)

(** Length of concat of outer product *)
Lemma outer_raw_row_length : forall (v w : list Q) i,
  (i < length v)%nat ->
  length (nth i (outer_raw v w) []) = length w.
Proof.
  induction v as [| x xs IH]; intros w i Hi.
  - simpl in Hi. lia.
  - simpl. destruct i as [| i'].
    + simpl. rewrite map_length. reflexivity.
    + simpl in Hi. apply IH. lia.
Qed.

Lemma outer_raw_length : forall (v w : list Q),
  length (outer_raw v w) = length v.
Proof.
  induction v as [| x xs IH]; intros w.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma concat_outer_length : forall (v w : list Q),
  length (concat (outer_raw v w)) = (length v * length w)%nat.
Proof.
  induction v as [| x xs IH]; intros w.
  - simpl. reflexivity.
  - simpl. rewrite app_length, map_length, IH. reflexivity.
Qed.

(** Kronecker product: flatten the outer product *)
Definition vec_tensor {dA dB : nat} (v : QVec dA) (w : QVec dB)
  : QVec (dA * dB).
Proof.
  refine (mkQVec (concat (outer_raw (qv_data v) (qv_data w))) _).
  rewrite concat_outer_length, (qv_length v), (qv_length w).
  reflexivity.
Defined.

(** Component access for vec_tensor *)
Lemma nth_concat_outer : forall (v w : list Q) (i j : nat),
  (i < length v)%nat -> (j < length w)%nat ->
  nth (i * length w + j) (concat (outer_raw v w)) 0 ==
  nth i v 0 * nth j w 0.
Proof.
  induction v as [| x xs IH]; intros w i j Hi Hj.
  - simpl in Hi. lia.
  - simpl. destruct i as [| i'].
    + (* i = 0: in the first row = map (Qmult x) w *)
      simpl. rewrite app_nth1.
      2:{ rewrite map_length. exact Hj. }
      rewrite nth_indep with (d' := x * 0).
      2:{ rewrite map_length. exact Hj. }
      rewrite map_nth. ring.
    + (* i = S i': skip first row, use IH *)
      assert (Hi' : (i' < length xs)%nat) by (simpl in Hi; lia).
      assert (Hoff : (S i' * length w + j = length w + (i' * length w + j))%nat) by lia.
      rewrite Hoff.
      rewrite app_nth2.
      2:{ rewrite map_length. lia. }
      rewrite map_length.
      assert (Harith : (length w + (i' * length w + j) - length w = i' * length w + j)%nat) by lia.
      rewrite Harith.
      apply IH; assumption.
Qed.

Lemma vec_tensor_component : forall {dA dB : nat}
  (v : QVec dA) (w : QVec dB) (i j : nat),
  (i < dA)%nat -> (j < dB)%nat ->
  qv_nth (vec_tensor v w) (i * dB + j) == qv_nth v i * qv_nth w j.
Proof.
  intros dA dB v w i j Hi Hj.
  unfold qv_nth, vec_tensor. simpl.
  assert (HlA : length (qv_data v) = dA) by exact (qv_length v).
  assert (HlB : length (qv_data w) = dB) by exact (qv_length w).
  replace (i * dB + j)%nat with (i * length (qv_data w) + j)%nat by lia.
  apply nth_concat_outer.
  - lia.
  - lia.
Qed.

(* ========================================================================= *)
(*  PART II: TENSOR PRODUCT OF STATES                                        *)
(* ========================================================================= *)

(** Tensor product of two quantum states *)
Definition state_tensor {dA dB : nat}
  (s1 : QState dA) (s2 : QState dB) : QState (dA * dB).
Proof.
  refine (mkQState (dA * dB) (fun k => vec_tensor (state_at s1 k) (state_at s2 k)) _).
  intros idx Hidx.
  (* idx < dA * dB, so idx = i * dB + j for some i < dA, j < dB *)
  (* We need is_cauchy (fun k => qv_nth (vec_tensor (state_at s1 k) (state_at s2 k)) idx) *)
  (* Each component is a product of Cauchy sequences *)
  (* For now, use a direct Cauchy argument *)
  intros eps Heps.
  (* Decompose idx into quotient and remainder *)
  destruct (Nat.eq_dec dB 0) as [HdB0 | HdBnz].
  { subst dB. simpl in Hidx. lia. }
  set (i := (idx / dB)%nat).
  set (j := (idx mod dB)%nat).
  assert (Hi : (i < dA)%nat).
  { unfold i. apply Nat.div_lt_upper_bound; lia. }
  assert (Hj : (j < dB)%nat).
  { unfold j. apply Nat.mod_upper_bound. lia. }
  assert (Hidx_eq : idx = (i * dB + j)%nat).
  { unfold i, j.
    pose proof (Nat.div_mod_eq idx dB) as Hdm.
    lia. }
  (* Component idx = v_i * w_j, a product of Cauchy seqs *)
  assert (Hci : is_cauchy (fun k => qv_nth (state_at s1 k) i)).
  { apply (qs_cauchy dA s1 i Hi). }
  assert (Hcj : is_cauchy (fun k => qv_nth (state_at s2 k) j)).
  { apply (qs_cauchy dB s2 j Hj). }
  assert (Hprod : is_cauchy (fun k => qv_nth (state_at s1 k) i * qv_nth (state_at s2 k) j)).
  { apply cauchy_mul_is_cauchy; assumption. }
  destruct (Hprod eps Heps) as [N HN].
  exists N. intros m p Hm Hp.
  assert (Heq_m : qv_nth (vec_tensor (state_at s1 m) (state_at s2 m)) idx ==
                  qv_nth (state_at s1 m) i * qv_nth (state_at s2 m) j).
  { rewrite Hidx_eq. apply vec_tensor_component; assumption. }
  assert (Heq_p : qv_nth (vec_tensor (state_at s1 p) (state_at s2 p)) idx ==
                  qv_nth (state_at s1 p) i * qv_nth (state_at s2 p) j).
  { rewrite Hidx_eq. apply vec_tensor_component; assumption. }
  assert (Hdiff : qv_nth (vec_tensor (state_at s1 m) (state_at s2 m)) idx -
                  qv_nth (vec_tensor (state_at s1 p) (state_at s2 p)) idx ==
                  (qv_nth (state_at s1 m) i * qv_nth (state_at s2 m) j) -
                  (qv_nth (state_at s1 p) i * qv_nth (state_at s2 p) j)).
  { rewrite Heq_m, Heq_p. reflexivity. }
  assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
  exact (HN m p Hm Hp).
Defined.

(** State tensor at step k *)
Lemma state_tensor_at : forall {dA dB : nat}
  (s1 : QState dA) (s2 : QState dB) (k : nat),
  state_at (state_tensor s1 s2) k = vec_tensor (state_at s1 k) (state_at s2 k).
Proof.
  intros dA dB s1 s2 k. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART III: SEPARABILITY AND ENTANGLEMENT                                  *)
(* ========================================================================= *)

(** A joint state is separable if it equals some tensor product *)
Definition is_separable {dA dB : nat} (psi : QState (dA * dB)) : Prop :=
  exists (a : QState dA) (b : QState dB),
    state_equiv psi (state_tensor a b).

(** Entangled = not separable *)
Definition is_entangled {dA dB : nat} (psi : QState (dA * dB)) : Prop :=
  ~ is_separable psi.

(** Separability preserved by scaling *)
Lemma separable_scale : forall {dA dB : nat} (c : Q)
  (psi : QState (dA * dB)),
  is_separable psi -> is_separable (state_scale c psi).
Proof.
  intros dA dB c psi [a [b Hequiv]].
  exists (state_scale c a), b.
  intros i Hi eps Heps.
  (* state_scale c psi at step k has component c * psi_i(k) *)
  (* state_tensor (state_scale c a) b at step k has component *)
  (* (c * a_p(k)) * b_q(k) = c * (a_p(k) * b_q(k)) = c * tensor_i(k) *)
  destruct (Qeq_dec c 0) as [Hc0 | Hcnz].
  - exists 0%nat. intros k _.
    change (state_at (state_scale c psi) k) with (qv_scale c (state_at psi k)).
    change (state_at (state_tensor (state_scale c a) b) k)
      with (vec_tensor (qv_scale c (state_at a k)) (state_at b k)).
    assert (Hlhs : qv_nth (qv_scale c (state_at psi k)) i == 0).
    { rewrite qv_scale_nth; [| exact Hi]. rewrite Hc0. ring. }
    assert (Hdim : (dA * dB)%nat = (dA * dB)%nat) by reflexivity.
    destruct (Nat.eq_dec dB 0) as [HdB0 | HdBnz].
    + subst dB. simpl in Hi. lia.
    + set (p := (i / dB)%nat). set (q := (i mod dB)%nat).
      assert (Hp : (p < dA)%nat) by (unfold p; apply Nat.div_lt_upper_bound; lia).
      assert (Hq : (q < dB)%nat) by (unfold q; apply Nat.mod_upper_bound; lia).
      assert (Hi_eq : i = (p * dB + q)%nat) by (unfold p, q; pose proof (Nat.div_mod_eq i dB); lia).
      assert (Hrhs : qv_nth (vec_tensor (qv_scale c (state_at a k)) (state_at b k)) i == 0).
      { rewrite Hi_eq. rewrite vec_tensor_component; [| exact Hp | exact Hq].
        rewrite qv_scale_nth; [| exact Hp]. rewrite Hc0. ring. }
      assert (Hdiff : qv_nth (qv_scale c (state_at psi k)) i -
                      qv_nth (vec_tensor (qv_scale c (state_at a k)) (state_at b k)) i == 0).
      { rewrite Hlhs, Hrhs. ring. }
      assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
      rewrite Qabs_pos; lra.
  - assert (Hcpos : 0 < Qabs c).
    { destruct (Qlt_le_dec 0 c).
      - rewrite Qabs_pos; lra.
      - rewrite Qabs_neg; [lra |].
        destruct (Qeq_dec c 0); [contradiction | lra]. }
    assert (Heps' : 0 < eps / Qabs c) by (apply Qdiv_lt_0_compat; assumption).
    destruct (Hequiv i Hi _ Heps') as [N HN].
    exists N. intros k Hk.
    change (state_at (state_scale c psi) k) with (qv_scale c (state_at psi k)).
    change (state_at (state_tensor (state_scale c a) b) k)
      with (vec_tensor (qv_scale c (state_at a k)) (state_at b k)).
    destruct (Nat.eq_dec dB 0) as [HdB0 | HdBnz]; [subst dB; simpl in Hi; lia |].
    set (p := (i / dB)%nat). set (q := (i mod dB)%nat).
    assert (Hp : (p < dA)%nat) by (unfold p; apply Nat.div_lt_upper_bound; lia).
    assert (Hq : (q < dB)%nat) by (unfold q; apply Nat.mod_upper_bound; lia).
    assert (Hi_eq : i = (p * dB + q)%nat) by (unfold p, q; pose proof (Nat.div_mod_eq i dB); lia).
    (* LHS: c * psi_i(k), RHS: (c * a_p(k)) * b_q(k) = c * (a_p(k) * b_q(k)) = c * tensor_i(k) *)
    assert (Hlhs : qv_nth (qv_scale c (state_at psi k)) i ==
                   c * qv_nth (state_at psi k) i).
    { apply qv_scale_nth. exact Hi. }
    assert (Hrhs : qv_nth (vec_tensor (qv_scale c (state_at a k)) (state_at b k)) i ==
                   c * qv_nth (vec_tensor (state_at a k) (state_at b k)) i).
    { rewrite Hi_eq.
      rewrite vec_tensor_component; [| exact Hp | exact Hq].
      rewrite qv_scale_nth; [| exact Hp].
      rewrite vec_tensor_component; [| exact Hp | exact Hq].
      ring. }
    assert (Hdiff : qv_nth (qv_scale c (state_at psi k)) i -
                    qv_nth (vec_tensor (qv_scale c (state_at a k)) (state_at b k)) i ==
                    c * (qv_nth (state_at psi k) i -
                         qv_nth (vec_tensor (state_at a k) (state_at b k)) i)).
    { rewrite Hlhs, Hrhs. ring. }
    assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
    rewrite Qabs_Qmult.
    apply Qlt_le_trans with (Qabs c * (eps / Qabs c)).
    + apply Qmult_lt_l; [exact Hcpos |].
      rewrite <- state_tensor_at. exact (HN k Hk).
    + apply Qeq_Qle. field. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: BELL STATE — THE CANONICAL ENTANGLED STATE                      *)
(* ========================================================================= *)

(** Bell state: |00⟩ + |11⟩ in a 2⊗2 system.
    In our encoding: dim = 2*2 = 4.
    basis_state 4 0 = |00⟩, basis_state 4 3 = |11⟩ *)
Definition bell_state : QState (2 * 2) :=
  state_add (basis_state 4 0) (basis_state 4 3).

(** Bell state component values (constant at every step) *)
Lemma bell_component_0 : forall k,
  qv_nth (state_at bell_state k) 0 == 1.
Proof.
  intros k. unfold bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (state_at (basis_state 4 0) k) (state_at (basis_state 4 3) k)).
  rewrite !basis_state_at.
  rewrite qv_add_nth; [| lia].
  rewrite basis_vec_same; [| lia].
  rewrite basis_vec_diff; [| lia | lia].
  ring.
Qed.

Lemma bell_component_1 : forall k,
  qv_nth (state_at bell_state k) 1 == 0.
Proof.
  intros k. unfold bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (state_at (basis_state 4 0) k) (state_at (basis_state 4 3) k)).
  rewrite !basis_state_at.
  rewrite qv_add_nth; [| lia].
  rewrite basis_vec_diff; [| lia | lia].
  rewrite basis_vec_diff; [| lia | lia].
  ring.
Qed.

Lemma bell_component_2 : forall k,
  qv_nth (state_at bell_state k) 2 == 0.
Proof.
  intros k. unfold bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (state_at (basis_state 4 0) k) (state_at (basis_state 4 3) k)).
  rewrite !basis_state_at.
  rewrite qv_add_nth; [| lia].
  rewrite basis_vec_diff; [| lia | lia].
  rewrite basis_vec_diff; [| lia | lia].
  ring.
Qed.

Lemma bell_component_3 : forall k,
  qv_nth (state_at bell_state k) 3 == 1.
Proof.
  intros k. unfold bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (state_at (basis_state 4 0) k) (state_at (basis_state 4 3) k)).
  rewrite !basis_state_at.
  rewrite qv_add_nth; [| lia].
  rewrite basis_vec_diff; [| lia | lia].
  rewrite basis_vec_same; [| lia].
  ring.
Qed.

(** ★★★ BELL STATE IS ENTANGLED ★★★

    Proof by contradiction: assume bell_state = a ⊗ b for some
    a : QState 2, b : QState 2. Then at large enough step k:
      a₀*b₀ ≈ 1, a₀*b₁ ≈ 0, a₁*b₀ ≈ 0, a₁*b₁ ≈ 1
    But (a₀*b₁)*(a₁*b₀) = (a₀*b₀)*(a₁*b₁) algebraically.
    The left side has |·| < 1/16, the right side has |·| > 9/16.
    Contradiction. *)
Theorem bell_entangled : is_entangled bell_state.
Proof.
  unfold is_entangled, is_separable. intros [a [b Hequiv]].
  (* Get approximation bounds for each component with eps = 1/4 *)
  assert (Heps : 0 < (1#4)) by lra.
  destruct (Hequiv 0%nat ltac:(lia) (1#4) Heps) as [N0 HN0].
  destruct (Hequiv 1%nat ltac:(lia) (1#4) Heps) as [N1 HN1].
  destruct (Hequiv 2%nat ltac:(lia) (1#4) Heps) as [N2 HN2].
  destruct (Hequiv 3%nat ltac:(lia) (1#4) Heps) as [N3 HN3].
  set (N := Nat.max (Nat.max N0 N1) (Nat.max N2 N3)).
  assert (HN0' : (N0 <= N)%nat) by (unfold N; lia).
  assert (HN1' : (N1 <= N)%nat) by (unfold N; lia).
  assert (HN2' : (N2 <= N)%nat) by (unfold N; lia).
  assert (HN3' : (N3 <= N)%nat) by (unfold N; lia).
  specialize (HN0 N HN0'). specialize (HN1 N HN1').
  specialize (HN2 N HN2'). specialize (HN3 N HN3').
  (* Rewrite bell components *)
  rewrite state_tensor_at in HN0, HN1, HN2, HN3.
  (* Component 0: |1 - a₀*b₀| < 1/4 *)
  assert (Hbc0 := bell_component_0 N).
  assert (Htc0 : qv_nth (vec_tensor (state_at a N) (state_at b N)) 0 ==
                 qv_nth (state_at a N) 0 * qv_nth (state_at b N) 0).
  { change 0%nat with (0 * 2 + 0)%nat. apply vec_tensor_component; lia. }
  (* Component 1: |0 - a₀*b₁| < 1/4 *)
  assert (Hbc1 := bell_component_1 N).
  assert (Htc1 : qv_nth (vec_tensor (state_at a N) (state_at b N)) 1 ==
                 qv_nth (state_at a N) 0 * qv_nth (state_at b N) 1).
  { change 1%nat with (0 * 2 + 1)%nat. apply vec_tensor_component; lia. }
  (* Component 2: |0 - a₁*b₀| < 1/4 *)
  assert (Hbc2 := bell_component_2 N).
  assert (Htc2 : qv_nth (vec_tensor (state_at a N) (state_at b N)) 2 ==
                 qv_nth (state_at a N) 1 * qv_nth (state_at b N) 0).
  { change 2%nat with (1 * 2 + 0)%nat. apply vec_tensor_component; lia. }
  (* Component 3: |1 - a₁*b₁| < 1/4 *)
  assert (Hbc3 := bell_component_3 N).
  assert (Htc3 : qv_nth (vec_tensor (state_at a N) (state_at b N)) 3 ==
                 qv_nth (state_at a N) 1 * qv_nth (state_at b N) 1).
  { change 3%nat with (1 * 2 + 1)%nat. apply vec_tensor_component; lia. }
  (* Name the variables *)
  set (a0 := qv_nth (state_at a N) 0) in *.
  set (a1 := qv_nth (state_at a N) 1) in *.
  set (b0 := qv_nth (state_at b N) 0) in *.
  set (b1 := qv_nth (state_at b N) 1) in *.
  (* Extract Qabs bounds *)
  assert (H0 : Qabs (1 - a0 * b0) < 1#4).
  { assert (Heq : qv_nth (state_at bell_state N) 0 -
                   qv_nth (vec_tensor (state_at a N) (state_at b N)) 0 ==
                   1 - a0 * b0).
    { rewrite Hbc0, Htc0. reflexivity. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    lra. }
  assert (H1 : Qabs (a0 * b1) < 1#4).
  { assert (Heq : qv_nth (state_at bell_state N) 1 -
                   qv_nth (vec_tensor (state_at a N) (state_at b N)) 1 ==
                   -(a0 * b1)).
    { rewrite Hbc1, Htc1. ring. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hopp : Qabs (-(a0 * b1)) == Qabs (a0 * b1)) by (apply Qabs_opp).
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    assert (Hle3 := Qeq_Qle _ _ Hopp).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Hopp)).
    lra. }
  assert (H2 : Qabs (a1 * b0) < 1#4).
  { assert (Heq : qv_nth (state_at bell_state N) 2 -
                   qv_nth (vec_tensor (state_at a N) (state_at b N)) 2 ==
                   -(a1 * b0)).
    { rewrite Hbc2, Htc2. ring. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hopp : Qabs (-(a1 * b0)) == Qabs (a1 * b0)) by (apply Qabs_opp).
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    assert (Hle3 := Qeq_Qle _ _ Hopp).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Hopp)).
    lra. }
  assert (H3 : Qabs (1 - a1 * b1) < 1#4).
  { assert (Heq : qv_nth (state_at bell_state N) 3 -
                   qv_nth (vec_tensor (state_at a N) (state_at b N)) 3 ==
                   1 - a1 * b1).
    { rewrite Hbc3, Htc3. reflexivity. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    lra. }
  (* Key algebraic identity: (a0*b1)*(a1*b0) = (a0*b0)*(a1*b1) *)
  assert (Hkey : a0 * b1 * (a1 * b0) == a0 * b0 * (a1 * b1)) by ring.
  (* From H0: a0*b0 > 3/4 *)
  assert (Hab00_lo : 3#4 < a0 * b0).
  { destruct (Qlt_le_dec (1 - a0 * b0) 0) as [Hneg | Hpos].
    - lra.
    - assert (Habs_eq : Qabs (1 - a0 * b0) == 1 - a0 * b0)
        by (rewrite Qabs_pos; lra).
      assert (Hle := Qeq_Qle _ _ Habs_eq). lra. }
  (* From H3: a1*b1 > 3/4 *)
  assert (Hab11_lo : 3#4 < a1 * b1).
  { destruct (Qlt_le_dec (1 - a1 * b1) 0) as [Hneg | Hpos].
    - lra.
    - assert (Habs_eq : Qabs (1 - a1 * b1) == 1 - a1 * b1)
        by (rewrite Qabs_pos; lra).
      assert (Hle := Qeq_Qle _ _ Habs_eq). lra. }
  (* From H1, H2: upper bound on product of absolute values *)
  assert (Hprod_hi : Qabs (a0 * b1) * Qabs (a1 * b0) < 1#16).
  { pose proof (Qabs_nonneg (a1 * b0)) as Hb_nn.
    destruct (Qeq_dec (Qabs (a1 * b0)) 0) as [Hz | Hnz].
    - assert (Heq0 : Qabs (a0 * b1) * Qabs (a1 * b0) == 0) by (rewrite Hz; ring).
      assert (Hle := Qeq_Qle _ _ Heq0). lra.
    - assert (Hb_pos : 0 < Qabs (a1 * b0)) by lra.
      assert (H14_pos : 0 < (1#4)) by lra.
      apply Qlt_trans with ((1#4) * Qabs (a1 * b0)).
      + setoid_replace (Qabs (a0 * b1) * Qabs (a1 * b0))
          with (Qabs (a1 * b0) * Qabs (a0 * b1)) by ring.
        setoid_replace ((1 # 4) * Qabs (a1 * b0))
          with (Qabs (a1 * b0) * (1#4)) by ring.
        exact (proj2 (Qmult_lt_l _ _ _ Hb_pos) H1).
      + exact (proj2 (Qmult_lt_l _ _ _ H14_pos) H2). }
  (* Lower bound: product of two positive values each > 3/4 *)
  assert (H00pos : 0 < a0 * b0) by lra.
  assert (H11pos : 0 < a1 * b1) by lra.
  assert (H34_pos : 0 < (3#4)) by lra.
  assert (Hprod_lo : (3#4) * (3#4) < a0 * b0 * (a1 * b1)).
  { apply Qlt_trans with ((3#4) * (a1 * b1)).
    - exact (proj2 (Qmult_lt_l _ _ _ H34_pos) Hab11_lo).
    - setoid_replace ((3#4) * (a1 * b1))
        with ((a1 * b1) * (3#4)) by ring.
      setoid_replace (a0 * b0 * (a1 * b1))
        with ((a1 * b1) * (a0 * b0)) by ring.
      exact (proj2 (Qmult_lt_l _ _ _ H11pos) Hab00_lo). }
  (* Algebraic identity + Qabs bridge *)
  assert (Habs_prod : Qabs (a0 * b1 * (a1 * b0)) ==
                      Qabs (a0 * b1) * Qabs (a1 * b0)).
  { apply Qabs_Qmult. }
  assert (Habs_key : Qabs (a0 * b0 * (a1 * b1)) ==
                     Qabs (a0 * b1 * (a1 * b0))).
  { apply Qabs_wd. symmetry. exact Hkey. }
  (* a0*b0*(a1*b1) > 0 so Qabs = identity *)
  assert (Habs_id : Qabs (a0 * b0 * (a1 * b1)) == a0 * b0 * (a1 * b1)).
  { rewrite Qabs_pos; lra. }
  (* Chain: a0*b0*(a1*b1) = |a0*b0*(a1*b1)| = |a0*b1*(a1*b0)| = |a0*b1|*|a1*b0| < 1/16 *)
  (* But a0*b0*(a1*b1) > (3/4)^2 = 9/16 > 1/16 *)
  assert (Hchain : a0 * b0 * (a1 * b1) < 1#16).
  { assert (Hle1 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_id)).
    assert (Hle2 := Qeq_Qle _ _ Habs_key).
    assert (Hle3 := Qeq_Qle _ _ Habs_prod).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_key)).
    assert (Hle5 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_prod)).
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART V: PCH CLASSIFICATION OF ENTANGLEMENT                               *)
(* ========================================================================= *)

Section EntanglementEncoding.

  Variable dA dB : nat.
  Variable encode : QState (dA * dB) -> BinProcess.
  Variable encode_compat : forall s1 s2 : QState (dA * dB),
    state_equiv s1 s2 -> bp_eq (encode s1) (encode s2).

  (** Collection of entangled states *)
  Definition entangled_collection : BinCollection :=
    fun p => exists psi : QState (dA * dB),
      is_entangled psi /\ bp_eq (encode psi) p.

  (** Collection of separable states *)
  Definition separable_collection : BinCollection :=
    fun p => exists psi : QState (dA * dB),
      is_separable psi /\ bp_eq (encode psi) p.

  (** Entangled collection is closed under bp_eq *)
  Lemma entangled_bp_closed : forall p q,
    entangled_collection p -> bp_eq p q -> entangled_collection q.
  Proof.
    intros p q [psi [Hent Henc]] Hpq.
    exists psi. split; [exact Hent | exact (bp_eq_trans _ _ _ Henc Hpq)].
  Qed.

  (** Separable collection is closed under bp_eq *)
  Lemma separable_bp_closed : forall p q,
    separable_collection p -> bp_eq p q -> separable_collection q.
  Proof.
    intros p q [psi [Hsep Henc]] Hpq.
    exists psi. split; [exact Hsep | exact (bp_eq_trans _ _ _ Henc Hpq)].
  Qed.

  (** Note: disjointness of separable_collection/entangled_collection
      requires encode_inj (injectivity). Without it, two different states
      could map to the same process. We prove the weaker pointwise version below. *)

  (** No state is both separable and entangled *)
  Lemma sep_entangled_exclusive : forall (psi : QState (dA * dB)),
    is_separable psi -> is_entangled psi -> False.
  Proof.
    intros psi Hsep Hent. exact (Hent Hsep).
  Qed.

  (** ★★★ ENTANGLEMENT DICHOTOMY ★★★
      For any closed collection of entangled states,
      either it is enumerable or it has a perfect subset. *)
  Theorem entanglement_dichotomy :
    is_closed entangled_collection ->
    is_enumerable entangled_collection \/ has_perfect_subset entangled_collection.
  Proof.
    intros Hclosed.
    exact (process_continuum_hypothesis entangled_collection Hclosed).
  Qed.

  (** Empty entangled collection is trivially enumerable *)
  Lemma empty_entangled_enumerable :
    (forall psi : QState (dA * dB), ~ is_entangled psi) ->
    is_enumerable entangled_collection.
  Proof.
    intros Hall.
    apply enumerable_empty. unfold is_empty.
    intros p [psi [Hent _]]. exact (Hall psi Hent).
  Qed.

  (** Structural: not enumerable ⟹ has perfect subset *)
  Lemma entangled_structural :
    is_closed entangled_collection ->
    ~ is_enumerable entangled_collection ->
    has_perfect_subset entangled_collection.
  Proof.
    intros Hclosed Hnenum.
    destruct (entanglement_dichotomy Hclosed); [contradiction | exact H].
  Qed.

End EntanglementEncoding.

(* ========================================================================= *)
(*  PART VI: THREE-WAY CLASSIFICATION                                        *)
(* ========================================================================= *)

(** Classification of entangled states *)
Definition Ent_Empty (dA dB : nat) : Prop :=
  forall psi : QState (dA * dB), ~ is_entangled psi.

Definition Ent_Discrete (dA dB : nat)
  (encode : QState (dA * dB) -> BinProcess) : Prop :=
  (exists psi : QState (dA * dB), is_entangled psi) /\
  is_enumerable (entangled_collection dA dB encode).

Definition Ent_Continuum (dA dB : nat)
  (encode : QState (dA * dB) -> BinProcess) : Prop :=
  (exists psi : QState (dA * dB), is_entangled psi) /\
  has_perfect_subset (entangled_collection dA dB encode).

(** Three-way classification theorem *)
Theorem entanglement_classification :
  forall (dA dB : nat) (encode : QState (dA * dB) -> BinProcess),
    is_closed (entangled_collection dA dB encode) ->
    Ent_Empty dA dB \/
    Ent_Discrete dA dB encode \/
    Ent_Continuum dA dB encode.
Proof.
  intros dA dB encode Hclosed.
  destruct (classic (exists psi, is_entangled (dA:=dA)(dB:=dB) psi)) as [Hex | Hno].
  - destruct (process_continuum_hypothesis
      (entangled_collection dA dB encode) Hclosed) as [Henum | Hperf].
    + right. left. split; assumption.
    + right. right. split; assumption.
  - left. intros psi Hent. apply Hno. exists psi. exact Hent.
Qed.

(** 2⊗2 system has entangled states (Bell state witnesses) *)
Lemma two_qubit_has_entangled :
  exists psi : QState (2 * 2), is_entangled psi.
Proof.
  exists bell_state. exact bell_entangled.
Qed.

(** Therefore 2⊗2 is NOT in the empty class *)
Lemma two_qubit_not_empty : ~ Ent_Empty 2 2.
Proof.
  intros Hempty.
  exact (Hempty bell_state bell_entangled).
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

Check vec_tensor.
Check vec_tensor_component.
Check state_tensor.
Check state_tensor_at.
Check is_separable.
Check is_entangled.
Check separable_scale.
Check bell_state.
Check bell_component_0.
Check bell_component_1.
Check bell_component_2.
Check bell_component_3.
Check bell_entangled.
Check entangled_collection.
Check separable_collection.
Check entangled_bp_closed.
Check separable_bp_closed.
Check sep_entangled_exclusive.
Check entanglement_dichotomy.
Check empty_entangled_enumerable.
Check entangled_structural.
Check entanglement_classification.
Check two_qubit_has_entangled.
Check two_qubit_not_empty.

Print Assumptions bell_entangled.
Print Assumptions entanglement_dichotomy.
Print Assumptions entanglement_classification.
