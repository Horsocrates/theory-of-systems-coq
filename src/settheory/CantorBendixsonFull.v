(** * CantorBendixsonFull.v -- Cantor-Bendixson for omega-iterations (separable Q)
    Elements: PointSet, CB_deriv, CB_iter, CB_omega, is_isolated, is_accumulation
    Roles:    Derivative removes isolated points, iteration forms decreasing chain
    Rules:    the omega-limit CONTAINS every perfect subset; if the process
              stabilises at a finite step, that step is the perfect kernel;
              every finite set is scattered
    STATUS:   35 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    P4 perspective: CB derivative is a PROCESS operating on point sets.
    Each iteration step keeps the accumulation points of the previous one.

    HONEST SCOPE (Nov 2026).  "The omega-limit is the perfect kernel" is NOT
    proved here and is false in general: a set of Cantor-Bendixson rank
    omega + 1 has a one-point omega-limit.  What is proved (last section):
    every perfect subset survives all finite steps (perfect_kernel_in_omega);
    if step n is stable it is perfect, equals the omega-limit and contains
    every perfect subset (stable_stage_is_perfect_kernel); every finite set
    of rationals is scattered and its derivative is empty
    (finite_set_scattered, finite_set_deriv_empty).  The lemma
    CB_omega_stable returns its own premise.  In general the kernel is
    reached only by continuing the iteration along the notations (CB_ord).
*)

From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import foundation.Ordinal.

(* ================================================================= *)
(* POINT SET DEFINITIONS                                              *)
(* ================================================================= *)

Definition PointSet := Q -> Prop.

(* Point is isolated in S: has neighborhood with no other S-points *)
Definition is_isolated (S : PointSet) (x : Q) : Prop :=
  S x /\ exists eps : Q, eps > 0 /\
    forall y, S y -> Qabs (x - y) < eps -> x == y.

(* Point is accumulation: other S-points arbitrarily close *)
Definition is_accumulation (S : PointSet) (x : Q) : Prop :=
  S x /\ forall eps : Q, eps > 0 ->
    exists y, S y /\ ~(x == y) /\ Qabs (x - y) < eps.

(* CB derivative: keep only accumulation points *)
Definition CB_deriv (S : PointSet) : PointSet :=
  fun x => is_accumulation S x.

(* Iterated CB derivative (nat-indexed for omega iteration) *)
Fixpoint CB_iter (S : PointSet) (n : nat) : PointSet :=
  match n with
  | O => S
  | Datatypes.S n' => CB_deriv (CB_iter S n')
  end.

(* omega-limit: intersection of all finite iterates *)
Definition CB_omega (S : PointSet) : PointSet :=
  fun x => forall n, CB_iter S n x.

(* Perfect set: every point is an accumulation point *)
Definition is_perfect (S : PointSet) : Prop :=
  forall x, S x -> is_accumulation S x.

(* Countable set *)
Definition is_countable (S : PointSet) : Prop :=
  exists enum : nat -> Q, forall x, S x -> exists n, x == enum n.

(* Scattered: no perfect non-empty subset *)
Definition is_scattered (S : PointSet) : Prop :=
  forall P : PointSet, (forall x, P x -> S x) -> is_perfect P ->
    ~(exists x, P x).

(* Subset relation *)
Definition subset (A B : PointSet) : Prop :=
  forall x, A x -> B x.

(* Empty set *)
Definition empty_set : PointSet := fun _ => False.

(* ================================================================= *)
(* CB DERIVATIVE PROPERTIES                                           *)
(* ================================================================= *)

(* 1. Derivative is a subset *)
Lemma CB_deriv_subset : forall S x, CB_deriv S x -> S x.
Proof.
  intros S x H. unfold CB_deriv, is_accumulation in H. destruct H as [Hsx _]. exact Hsx.
Qed.

(* 2. Iterated derivatives form decreasing chain *)
Lemma CB_iter_subset : forall S n x, CB_iter S (Datatypes.S n) x -> CB_iter S n x.
Proof.
  intros S n x H. simpl in H. apply CB_deriv_subset in H. exact H.
Qed.

(* 3. Monotonicity of iterated derivatives *)
Lemma CB_iter_monotone : forall S m n x, (m <= n)%nat -> CB_iter S n x -> CB_iter S m x.
Proof.
  intros S m n x Hmn. revert x. induction n as [| n' IH].
  - intros x H. assert (m = 0)%nat by lia. subst. exact H.
  - intros x H.
    destruct (Nat.eq_dec m (Datatypes.S n')) as [Heq | Hneq].
    + subst. exact H.
    + assert (Hle : (m <= n')%nat) by lia.
      apply IH; [exact Hle | apply CB_iter_subset; exact H].
Qed.

(* 4. omega-limit is subset of original *)
Lemma CB_omega_subset : forall S x, CB_omega S x -> S x.
Proof.
  intros S x H. unfold CB_omega in H. specialize (H 0%nat). simpl in H. exact H.
Qed.

(* 5. omega-limit is in every iterate *)
Lemma CB_omega_in_all : forall S n x, CB_omega S x -> CB_iter S n x.
Proof.
  intros S n x H. unfold CB_omega in H. exact (H n).
Qed.

(* 6. omega-limit is stable under CB_deriv *)
Lemma CB_omega_stable : forall S x, CB_omega S x -> CB_deriv (CB_omega S) x -> CB_omega S x.
Proof.
  intros S x Hom _. exact Hom.
Qed.

(* ================================================================= *)
(* ISOLATED vs ACCUMULATION                                           *)
(* ================================================================= *)

(* 7. Isolated and accumulation are mutually exclusive *)
Lemma isolated_not_accumulation : forall S x,
  is_isolated S x -> ~is_accumulation S x.
Proof.
  intros S x [Hsx [eps [Heps Hiso]]] [_ Hacc].
  specialize (Hacc eps Heps).
  destruct Hacc as [y [Hsy [Hneq Hclose]]].
  apply Hneq. apply Hiso; assumption.
Qed.

(* 8. Accumulation implies not isolated *)
Lemma accumulation_not_isolated : forall S x,
  is_accumulation S x -> ~is_isolated S x.
Proof.
  intros S x Hacc Hiso. exact (isolated_not_accumulation S x Hiso Hacc).
Qed.

(* ================================================================= *)
(* EMPTY SET PROPERTIES                                               *)
(* ================================================================= *)

(* 9. Empty set is vacuously perfect *)
Lemma empty_is_perfect : is_perfect empty_set.
Proof.
  unfold is_perfect, empty_set. intros x Hf. contradiction.
Qed.

(* 10. Derivative of empty is empty *)
Lemma CB_deriv_empty : forall x, ~CB_deriv empty_set x.
Proof.
  intros x H. apply CB_deriv_subset in H. exact H.
Qed.

(* 11. omega-limit of empty is empty *)
Lemma CB_omega_empty : forall x, ~CB_omega empty_set x.
Proof.
  intros x H. apply CB_omega_subset in H. exact H.
Qed.

(* ================================================================= *)
(* FINITE SET EXAMPLE: {0, 1, 2}                                     *)
(* ================================================================= *)

Definition S_finite (x : Q) : Prop := x == 0 \/ x == 1 \/ x == 2.

(* Helper: if y is in S_finite and |y - 0| < 1/2, then y == 0 *)
Lemma S_finite_near_0 : forall y, S_finite y -> Qabs (0 - y) < (1#2) -> 0 == y.
Proof.
  intros y [Hy | [Hy | Hy]].
  - intros _. symmetry. exact Hy.
  - intros Habs. exfalso.
    assert (H0y : 0 - y == -(1)) by (rewrite Hy; ring).
    rewrite H0y in Habs.
    assert (Habs1 : Qabs (-(1)) == 1).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs1 in Habs. lra.
  - intros Habs. exfalso.
    assert (H0y : 0 - y == -(2)) by (rewrite Hy; ring).
    rewrite H0y in Habs.
    assert (Habs2 : Qabs (-(2)) == 2).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs2 in Habs. lra.
Qed.

(* 12. 0 is isolated in S_finite *)
Lemma S_finite_0_isolated : is_isolated S_finite 0.
Proof.
  split.
  - left. reflexivity.
  - exists (1#2). split; [lra |].
    intros y Hy Habs.
    assert (Heq : 0 - y == -(y - 0)) by ring.
    rewrite Heq in *.
    rewrite Qabs_opp in *.
    assert (H0y : Qabs (0 - y) < (1#2)).
    { rewrite Heq. rewrite Qabs_opp. exact Habs. }
    apply S_finite_near_0; assumption.
Qed.

(* Helper: if y is in S_finite and |y - 1| < 1/2, then y == 1 *)
Lemma S_finite_near_1 : forall y, S_finite y -> Qabs (1 - y) < (1#2) -> 1 == y.
Proof.
  intros y [Hy | [Hy | Hy]].
  - intros Habs. exfalso.
    assert (H1y : 1 - y == 1) by (rewrite Hy; ring).
    rewrite H1y in Habs.
    assert (Habs1 : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs1 in Habs. lra.
  - intros _. symmetry. exact Hy.
  - intros Habs. exfalso.
    assert (H1y : 1 - y == -(1)) by (rewrite Hy; ring).
    rewrite H1y in Habs.
    assert (Habs1 : Qabs (-(1)) == 1).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs1 in Habs. lra.
Qed.

(* 13. 1 is isolated in S_finite *)
Lemma S_finite_1_isolated : is_isolated S_finite 1.
Proof.
  split.
  - right. left. reflexivity.
  - exists (1#2). split; [lra |].
    intros y Hy Habs. apply S_finite_near_1; assumption.
Qed.

(* Helper: if y is in S_finite and |y - 2| < 1/2, then y == 2 *)
Lemma S_finite_near_2 : forall y, S_finite y -> Qabs (2 - y) < (1#2) -> 2 == y.
Proof.
  intros y [Hy | [Hy | Hy]].
  - intros Habs. exfalso.
    assert (H2y : 2 - y == 2) by (rewrite Hy; ring).
    rewrite H2y in Habs.
    assert (Habs2 : Qabs 2 == 2).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs2 in Habs. lra.
  - intros Habs. exfalso.
    assert (H2y : 2 - y == 1) by (rewrite Hy; ring).
    rewrite H2y in Habs.
    assert (Habs1 : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    rewrite Habs1 in Habs. lra.
  - intros _. symmetry. exact Hy.
Qed.

(* 14. 2 is isolated in S_finite *)
Lemma S_finite_2_isolated : is_isolated S_finite 2.
Proof.
  split.
  - right. right. exact (Qeq_refl 2).
  - exists (1#2). split; [lra |].
    intros y Hy Habs. apply S_finite_near_2; assumption.
Qed.

(* 15. CB_deriv of S_finite is empty *)
Lemma CB_deriv_finite_empty : forall x, ~CB_deriv S_finite x.
Proof.
  intros x [Hsx Hacc].
  destruct Hsx as [Hx0 | [Hx1 | Hx2]].
  - (* x == 0 *)
    assert (Hiso : is_isolated S_finite x).
    { split.
      - left. exact Hx0.
      - exists (1#2). split; [lra |].
        intros y Hy Habs.
        assert (Habs' : Qabs (0 - y) < (1#2)).
        { assert (Heq : x - y == (x - 0) + (0 - y)) by ring.
          assert (Heq2 : x - 0 == 0) by (rewrite Hx0; ring).
          assert (Heq3 : x - y == 0 - y) by lra.
          rewrite Heq3 in Habs. exact Habs. }
        assert (H0y := S_finite_near_0 y Hy Habs').
        rewrite Hx0. exact H0y. }
    exfalso. exact (isolated_not_accumulation S_finite x Hiso (conj (proj1 Hiso) Hacc)).
  - (* x == 1 *)
    assert (Hiso : is_isolated S_finite x).
    { split.
      - right. left. exact Hx1.
      - exists (1#2). split; [lra |].
        intros y Hy Habs.
        assert (Habs' : Qabs (1 - y) < (1#2)).
        { assert (Heq3 : x - y == (x - 1) + (1 - y)) by ring.
          assert (Heq4 : x - 1 == 0) by lra.
          assert (Heq5 : x - y == 1 - y) by lra.
          rewrite Heq5 in Habs. exact Habs. }
        assert (H1y := S_finite_near_1 y Hy Habs').
        rewrite Hx1. exact H1y. }
    exfalso. exact (isolated_not_accumulation S_finite x Hiso (conj (proj1 Hiso) Hacc)).
  - (* x == 2 *)
    assert (Hiso : is_isolated S_finite x).
    { split.
      - right. right. exact Hx2.
      - exists (1#2). split; [lra |].
        intros y Hy Habs.
        assert (Habs' : Qabs (2 - y) < (1#2)).
        { assert (Heq5 : x - y == (x - 2) + (2 - y)) by ring.
          assert (Heq6 : x - 2 == 0) by lra.
          assert (Heq7 : x - y == 2 - y) by lra.
          rewrite Heq7 in Habs. exact Habs. }
        assert (H2y := S_finite_near_2 y Hy Habs').
        rewrite Hx2. exact H2y. }
    exfalso. exact (isolated_not_accumulation S_finite x Hiso (conj (proj1 Hiso) Hacc)).
Qed.

(* ================================================================= *)
(* FINITE SETS ARE SCATTERED                                          *)
(* ================================================================= *)

(* 16. CB_iter of S_finite becomes empty after 1 step *)
Lemma CB_iter_finite_empty : forall n x, (n >= 1)%nat -> ~CB_iter S_finite n x.
Proof.
  intros n x Hn. destruct n as [| n'].
  - lia.
  - intro H. simpl in H.
    assert (Hsub : CB_iter S_finite n' x -> S_finite x).
    { intro Hiter. apply (CB_iter_monotone S_finite 0 n' x). lia. exact Hiter. }
    (* H : CB_deriv (CB_iter S_finite n') x *)
    unfold CB_deriv, is_accumulation in H.
    destruct H as [Hiter Hacc].
    (* All points in CB_iter S_finite n' are in S_finite *)
    assert (Hfin : S_finite x) by (apply Hsub; exact Hiter).
    (* But S_finite has no accumulation points *)
    assert (Hnoderiv := CB_deriv_finite_empty x).
    apply Hnoderiv.
    unfold CB_deriv, is_accumulation.
    split.
    + exact Hfin.
    + intros eps Heps.
      specialize (Hacc eps Heps).
      destruct Hacc as [y [Hsy [Hneq Hclose]]].
      exists y. split; [| split; [exact Hneq | exact Hclose]].
      apply (CB_iter_monotone S_finite 0 n' y). lia. exact Hsy.
Qed.

(* 17. omega-limit of S_finite is empty *)
Lemma CB_omega_finite_empty : forall x, ~CB_omega S_finite x.
Proof.
  intros x H.
  unfold CB_omega in H. specialize (H 1%nat).
  exact (CB_iter_finite_empty 1 x ltac:(lia) H).
Qed.

(* 18. S_finite is scattered *)
Lemma S_finite_scattered : is_scattered S_finite.
Proof.
  unfold is_scattered. intros P Hsub Hperf [x Hpx].
  (* P is perfect and subset of S_finite *)
  (* So P x implies is_accumulation P x *)
  assert (Hacc := Hperf x Hpx).
  unfold is_accumulation in Hacc. destruct Hacc as [_ Hacc].
  (* x is in S_finite *)
  assert (Hfin : S_finite x) by (apply Hsub; exact Hpx).
  (* But x is isolated in S_finite *)
  destruct Hfin as [Hx0 | [Hx1 | Hx2]].
  - (* x == 0: find eps = 1/2 *)
    specialize (Hacc (1#2) ltac:(lra)).
    destruct Hacc as [y [Hpy [Hneq Hclose]]].
    assert (Hfy : S_finite y) by (apply Hsub; exact Hpy).
    assert (Habs' : Qabs (0 - y) < (1#2)).
    { assert (Heq : x - y == (x - 0) + (0 - y)) by ring.
      assert (Heq2 : x - 0 == 0) by lra.
      assert (Heq3 : x - y == 0 - y) by lra.
      rewrite Heq3 in Hclose. exact Hclose. }
    assert (H0y := S_finite_near_0 y Hfy Habs').
    apply Hneq. rewrite Hx0. exact H0y.
  - specialize (Hacc (1#2) ltac:(lra)).
    destruct Hacc as [y [Hpy [Hneq Hclose]]].
    assert (Hfy : S_finite y) by (apply Hsub; exact Hpy).
    assert (Habs' : Qabs (1 - y) < (1#2)).
    { assert (Heq3 : x - y == (x - 1) + (1 - y)) by ring.
      assert (Heq4 : x - 1 == 0) by lra.
      assert (Heq5 : x - y == 1 - y) by lra.
      rewrite Heq5 in Hclose. exact Hclose. }
    assert (H1y := S_finite_near_1 y Hfy Habs').
    apply Hneq. rewrite Hx1. exact H1y.
  - specialize (Hacc (1#2) ltac:(lra)).
    destruct Hacc as [y [Hpy [Hneq Hclose]]].
    assert (Hfy : S_finite y) by (apply Hsub; exact Hpy).
    assert (Habs' : Qabs (2 - y) < (1#2)).
    { assert (Heq5 : x - y == (x - 2) + (2 - y)) by ring.
      assert (Heq6 : x - 2 == 0) by lra.
      assert (Heq7 : x - y == 2 - y) by lra.
      rewrite Heq7 in Hclose. exact Hclose. }
    assert (H2y := S_finite_near_2 y Hfy Habs').
    apply Hneq. rewrite Hx2. exact H2y.
Qed.

(* ================================================================= *)
(* ORDINAL CONNECTION                                                  *)
(* ================================================================= *)

(* Connect nat iteration to ordinal indexing via Ordinal.v *)
Definition CB_ord_step (S : PointSet) (alpha : Ord) : PointSet :=
  match alpha with
  | OZero => S
  | OSucc _ => CB_deriv S    (* one derivative step *)
  | OLim f => fun x => forall n, CB_iter S n x  (* omega = intersection *)
  end.

(* 19. omega ordinal gives same result as CB_omega for base case *)
Lemma CB_ord_omega_eq : forall S x,
  CB_ord_step S omega x <-> CB_omega S x.
Proof.
  intros S x. unfold CB_ord_step, omega, CB_omega. split; auto.
Qed.

(* ================================================================= *)
(* PERFECT KERNEL THEOREM (omega version)                              *)
(* ================================================================= *)

(* 20. If omega-limit is nonempty, every point is accumulation within it
       relative to the ORIGINAL set -- key ingredient for perfect kernel *)
Lemma CB_omega_accumulation_in_parent : forall S x,
  CB_omega S x ->
  forall eps, eps > 0 ->
    exists y, S y /\ ~(x == y) /\ Qabs (x - y) < eps.
Proof.
  intros S x Hom eps Heps.
  unfold CB_omega in Hom.
  specialize (Hom 1%nat). simpl in Hom.
  unfold CB_deriv, is_accumulation in Hom.
  destruct Hom as [_ Hacc].
  specialize (Hacc eps Heps).
  destruct Hacc as [y [Hsy [Hneq Hclose]]].
  exists y. split; [exact Hsy | split; [exact Hneq | exact Hclose]].
Qed.

(* ================================================================= *)
(* END OF FILE                                                         *)
(* ================================================================= *)

(* ================================================================= *)
(* Nov 2026: THE DERIVATIVE ITERATED ALONG THE NOTATIONS               *)
(* ================================================================= *)

(* CB_ord_step above is not a recursion: at OSucc _ it takes ONE derivative
   whatever the predecessor is.  Here the derivative is iterated along Ord by
   structural recursion: zero, successor (derivative of the previous stage),
   limit (intersection of the stages). *)
Fixpoint CB_ord (X : PointSet) (a : Ord) : PointSet :=
  match a with
  | OZero => X
  | OSucc b => CB_deriv (CB_ord X b)
  | OLim f => fun x => forall k, CB_ord X (f k) x
  end.

(* every stage is a subset of the original set *)
Lemma CB_ord_subset : forall X a x, CB_ord X a x -> X x.
Proof.
  intros X a. induction a as [| b IH | f IH]; intros x H; simpl in H.
  - exact H.
  - apply IH. apply CB_deriv_subset. exact H.
  - apply (IH 0%nat). apply H.
Qed.

(* on finite notations the iteration is CB_iter *)
Lemma CB_ord_nat : forall X n, CB_ord X (nat_to_ord n) = CB_iter X n.
Proof.
  intros X n. induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* at the stage omega it is the intersection of the finite stages, CB_omega;
   the stage omega + 1 is, by the same Fixpoint, the derivative of that *)
Theorem CB_ord_omega : forall X x, CB_ord X omega x <-> CB_omega X x.
Proof.
  intros X x. unfold omega, CB_omega. simpl. split; intros H n.
  - rewrite <- CB_ord_nat. apply H.
  - rewrite CB_ord_nat. apply H.
Qed.

(* ================================================================= *)
(* Nov 2026: THE PERFECT KERNEL AND THE OMEGA-LIMIT; FINITE SETS       *)
(* ================================================================= *)

(* 1. Every perfect subset of A survives every derivative step, hence lies in
      the omega-limit: the omega-limit CONTAINS the perfect kernel. *)
Lemma perfect_subset_in_iter : forall (A P : PointSet),
  subset P A -> is_perfect P -> forall n x, P x -> CB_iter A n x.
Proof.
  intros A P Hsub Hperf. induction n as [| n IH]; intros x Hx.
  - simpl. apply Hsub. exact Hx.
  - simpl. unfold CB_deriv, is_accumulation. split.
    + apply IH. exact Hx.
    + intros eps Heps. destruct (Hperf x Hx) as [_ Hacc].
      destruct (Hacc eps Heps) as [y [Hy [Hne Hd]]].
      exists y. split; [apply IH; exact Hy | split; assumption].
Qed.

Theorem perfect_kernel_in_omega : forall (A P : PointSet),
  subset P A -> is_perfect P -> subset P (CB_omega A).
Proof.
  intros A P Hsub Hperf x Hx n.
  exact (perfect_subset_in_iter A P Hsub Hperf n x Hx).
Qed.

(* 2. If the omega-limit is empty, the set is scattered. *)
Theorem omega_empty_scattered : forall A : PointSet,
  (forall x, ~ CB_omega A x) -> is_scattered A.
Proof.
  intros A Hempty P Hsub Hperf [x Hx].
  exact (Hempty x (perfect_kernel_in_omega A P Hsub Hperf x Hx)).
Qed.

(* 3. Every finite set of rationals (given by a list) is scattered. *)
Definition in_list (l : list Q) : PointSet :=
  fun x => exists q, In q l /\ x == q.

Lemma Qabs_pos_of_neq : forall x q : Q, ~ x == q -> 0 < Qabs (x - q).
Proof.
  intros x q Hne.
  destruct (Qlt_le_dec 0 (Qabs (x - q))) as [H | H]; [exact H |].
  exfalso. apply Hne.
  apply Qabs_Qle_condition in H. destruct H as [H1 H2]. lra.
Qed.

Lemma finite_gap : forall (l : list Q) (x : Q),
  exists eps : Q, 0 < eps /\
    forall q, In q l -> ~ x == q -> eps <= Qabs (x - q).
Proof.
  induction l as [| q0 l IH]; intro x.
  - exists 1. split; [lra |]. intros q [].
  - destruct (IH x) as [eps0 [Heps0 Hgap]].
    destruct (Qeq_dec x q0) as [Heq | Hne].
    + exists eps0. split; [exact Heps0 |].
      intros q [Hq | Hq] Hxq.
      * exfalso. apply Hxq. rewrite <- Hq. exact Heq.
      * apply Hgap; assumption.
    + pose proof (Qabs_pos_of_neq x q0 Hne) as Hd.
      destruct (Qlt_le_dec eps0 (Qabs (x - q0))) as [Hlt | Hle].
      * exists eps0. split; [exact Heps0 |].
        intros q [Hq | Hq] Hxq.
        -- rewrite <- Hq. apply Qlt_le_weak. exact Hlt.
        -- apply Hgap; assumption.
      * exists (Qabs (x - q0)). split; [exact Hd |].
        intros q [Hq | Hq] Hxq.
        -- rewrite <- Hq. apply Qle_refl.
        -- apply Qle_trans with eps0; [exact Hle | apply Hgap; assumption].
Qed.

Theorem finite_set_scattered : forall l : list Q, is_scattered (in_list l).
Proof.
  intros l P Hsub Hperf [x Hx].
  destruct (finite_gap l x) as [eps [Heps Hgap]].
  destruct (Hperf x Hx) as [_ Hacc].
  destruct (Hacc eps Heps) as [y [Hy [Hne Hd]]].
  destruct (Hsub y Hy) as [q [Hq Hyq]].
  assert (Hxq : ~ x == q).
  { intro H. apply Hne. rewrite H. symmetry. exact Hyq. }
  pose proof (Hgap q Hq Hxq) as Hge.
  assert (Hsame : Qabs (x - y) == Qabs (x - q)) by (rewrite Hyq; reflexivity).
  rewrite Hsame in Hd.
  apply (Qlt_irrefl eps). apply Qle_lt_trans with (Qabs (x - q)); assumption.
Qed.

(* the omega-limit of a finite set is empty, and already the first derivative *)
Theorem finite_set_deriv_empty : forall (l : list Q) (x : Q),
  ~ CB_deriv (in_list l) x.
Proof.
  intros l x [Hx Hacc].
  destruct (finite_gap l x) as [eps [Heps Hgap]].
  destruct (Hacc eps Heps) as [y [[q [Hq Hyq]] [Hne Hd]]].
  assert (Hxq : ~ x == q).
  { intro H. apply Hne. rewrite H. symmetry. exact Hyq. }
  pose proof (Hgap q Hq Hxq) as Hge.
  assert (Hsame : Qabs (x - y) == Qabs (x - q)) by (rewrite Hyq; reflexivity).
  rewrite Hsame in Hd.
  apply (Qlt_irrefl eps). apply Qle_lt_trans with (Qabs (x - q)); assumption.
Qed.

(* 4. If the derivative process stabilizes at a finite stage n, that stage is
      perfect and coincides with the omega-limit: the perfect kernel. *)
Lemma stable_from : forall (A : PointSet) (n : nat),
  (forall x, CB_iter A n x -> CB_iter A (S n) x) ->
  forall (k : nat) x, CB_iter A n x -> CB_iter A (k + n)%nat x.
Proof.
  intros A n Hst. induction k as [| k IH]; intros x Hx.
  - exact Hx.
  - change (CB_deriv (CB_iter A (k + n)%nat) x). split.
    + apply IH. exact Hx.
    + intros eps Heps.
      destruct (Hst x Hx) as [_ Hacc].
      destruct (Hacc eps Heps) as [y [Hy [Hne Hd]]].
      exists y. split; [apply IH; exact Hy | split; assumption].
Qed.

Theorem stable_stage_is_perfect_kernel : forall (A : PointSet) (n : nat),
  (forall x, CB_iter A n x -> CB_iter A (S n) x) ->
  is_perfect (CB_iter A n) /\
  (forall x, CB_omega A x <-> CB_iter A n x) /\
  (forall P : PointSet, subset P A -> is_perfect P -> subset P (CB_iter A n)).
Proof.
  intros A n Hst. split; [| split].
  - intros x Hx. exact (Hst x Hx).
  - intro x. split.
    + intro H. exact (H n).
    + intros Hx m. destruct (Nat.le_gt_cases m n) as [Hle | Hgt].
      * exact (CB_iter_monotone A m n x Hle Hx).
      * replace m with ((m - n) + n)%nat by lia.
        exact (stable_from A n Hst (m - n)%nat x Hx).
  - intros P Hsub Hperf x Hx.
    exact (perfect_subset_in_iter A P Hsub Hperf n x Hx).
Qed.
