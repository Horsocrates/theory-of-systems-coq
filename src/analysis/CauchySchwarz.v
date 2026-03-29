(** * CauchySchwarz.v — Cauchy-Schwarz Inequality (Wiedijk #78)

    Theory of Systems — Analysis

    The Cauchy-Schwarz inequality: |⟨u,v⟩|² ≤ ‖u‖²·‖v‖²
    for finite-dimensional vectors over Q.

    Elements: vectors (list Q), dot product, norm squared
    Roles:    dot -> bilinear form, norm_sq -> quadratic form, scalar_mult -> scaling
    Rules:    non-negativity of norm_sq (L5: sum of squares ≥ 0)
    Status:   verified | concrete_checked

    Strategy: Prove for general lists via the identity
      ‖u - tv‖² = ‖u‖² - 2t⟨u,v⟩ + t²‖v‖² ≥ 0.
    For ‖v‖² > 0 set t = ⟨u,v⟩/‖v‖² and simplify.
    For ‖v‖² = 0, dot u v = 0 so both sides are 0.

    STATUS: 17 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: VECTOR OPERATIONS                                              *)
(* ========================================================================= *)

Fixpoint dot (u v : list Q) : Q :=
  match u, v with
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0
  end.

Definition norm_sq (u : list Q) : Q := dot u u.

Fixpoint scalar_mult (c : Q) (u : list Q) : list Q :=
  match u with
  | [] => []
  | x :: xs => (c * x) :: scalar_mult c xs
  end.

Fixpoint vec_sub (u v : list Q) : list Q :=
  match u, v with
  | x :: xs, y :: ys => (x - y) :: vec_sub xs ys
  | _, _ => []
  end.

Fixpoint vec_add (u v : list Q) : list Q :=
  match u, v with
  | x :: xs, y :: ys => (x + y) :: vec_add xs ys
  | _, _ => []
  end.

(* ========================================================================= *)
(* SECTION 2: BASIC PROPERTIES                                               *)
(* ========================================================================= *)

Lemma sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q.
  destruct (Qlt_le_dec q 0).
  - (* q < 0 *)
    assert (Hnq : 0 <= -q) by lra.
    assert (H : (-q) * (-q) == q * q) by ring.
    rewrite <- H.
    assert (H2 : 0 == 0 * (-q)) by ring. rewrite H2.
    apply Qmult_le_compat_r; lra.
  - (* 0 <= q *)
    assert (H2 : 0 == 0 * q) by ring. rewrite H2.
    apply Qmult_le_compat_r; lra.
Qed.

Lemma dot_nil_l : forall v, dot [] v == 0.
Proof. destruct v; reflexivity. Qed.

Lemma dot_nil_r : forall u, dot u [] == 0.
Proof. induction u as [| x xs IH]; simpl; lra. Qed.

Lemma norm_sq_nonneg : forall u, 0 <= norm_sq u.
Proof.
  induction u as [| x xs IH].
  - unfold norm_sq. simpl. lra.
  - unfold norm_sq. simpl.
    assert (Hx : 0 <= x * x) by apply sq_nonneg.
    unfold norm_sq in IH.
    lra.
Qed.

Lemma dot_comm : forall u v, dot u v == dot v u.
Proof.
  induction u as [| x xs IH]; intro v.
  - simpl. assert (H := dot_nil_r v). lra.
  - destruct v as [| y ys].
    + simpl. assert (H := dot_nil_r (x :: xs)). simpl in H. lra.
    + simpl. specialize (IH ys). rewrite IH. ring.
Qed.

Lemma length_scalar_mult : forall c u, length (scalar_mult c u) = length u.
Proof.
  intros c u. induction u as [| x xs IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma length_vec_sub : forall u v,
  length u = length v -> length (vec_sub u v) = length u.
Proof.
  intros u. induction u as [| x xs IH]; intros v Hlen.
  - destruct v; simpl in *; [reflexivity | discriminate].
  - destruct v as [| y ys].
    + simpl in Hlen. discriminate.
    + simpl in *. f_equal. apply IH. lia.
Qed.

(* ========================================================================= *)
(* SECTION 3: LINEARITY OF DOT PRODUCT                                      *)
(* ========================================================================= *)

Lemma dot_scale : forall c u v, dot (scalar_mult c u) v == c * dot u v.
Proof.
  intros c u. induction u as [| x xs IH]; intro v.
  - simpl. destruct v; simpl; ring.
  - destruct v as [| y ys].
    + simpl. ring.
    + simpl. rewrite IH. ring.
Qed.

Lemma dot_sub_l : forall u v w,
  length u = length v -> length v = length w ->
  dot (vec_sub u v) w == dot u w - dot v w.
Proof.
  intros u. induction u as [| x xs IH]; intros v w Huv Hvw.
  - destruct v; [| simpl in Huv; discriminate].
    destruct w; simpl; [lra | lra].
  - destruct v as [| y ys]; [simpl in Huv; discriminate |].
    destruct w as [| z ws]; [simpl; lra |].
    simpl in *.
    assert (Hlen1 : length xs = length ys) by lia.
    assert (Hlen2 : length ys = length ws) by lia.
    specialize (IH ys ws Hlen1 Hlen2).
    rewrite IH. ring.
Qed.

(* ========================================================================= *)
(* SECTION 4: NORM OF SUBTRACTION EXPANSION                                 *)
(* ========================================================================= *)

Lemma norm_sq_sub_expand : forall t u v,
  length u = length v ->
  norm_sq (vec_sub u (scalar_mult t v)) ==
  norm_sq u - (2 # 1) * t * dot u v + t * t * norm_sq v.
Proof.
  intros t u. induction u as [| x xs IH]; intros v Hlen.
  - destruct v; [| simpl in Hlen; discriminate].
    unfold norm_sq. simpl. ring.
  - destruct v as [| y ys]; [simpl in Hlen; discriminate |].
    simpl in Hlen.
    assert (Hlen' : length xs = length ys) by lia.
    unfold norm_sq. simpl.
    unfold norm_sq in IH.
    specialize (IH ys Hlen').
    assert (Heq : dot (vec_sub xs (scalar_mult t ys)) (vec_sub xs (scalar_mult t ys)) ==
                  dot xs xs - (2 # 1) * t * dot xs ys + t * t * dot ys ys) by exact IH.
    rewrite Heq. ring.
Qed.

(* ========================================================================= *)
(* SECTION 5: ZERO NORM IMPLIES ZERO DOT                                    *)
(* ========================================================================= *)

Lemma norm_sq_zero_dot_zero : forall u v,
  length u = length v ->
  norm_sq v == 0 ->
  dot u v == 0.
Proof.
  intros u. induction u as [| x xs IH]; intros v Hlen Hnorm.
  - destruct v; simpl; reflexivity.
  - destruct v as [| y ys]; [simpl in Hlen; discriminate |].
    simpl in Hlen.
    unfold norm_sq in Hnorm. simpl in Hnorm.
    assert (Hlen' : length xs = length ys) by lia.
    (* y*y + dot ys ys == 0 with both nonneg means both zero *)
    assert (Hyy : 0 <= y * y) by apply sq_nonneg.
    assert (Hdd : 0 <= dot ys ys) by apply (norm_sq_nonneg ys).
    assert (Hy0 : y * y == 0) by lra.
    assert (Hd0 : dot ys ys == 0) by lra.
    assert (Hy : y == 0).
    { (* y*y == 0 and y*y >= 0. If y <> 0 then y*y > 0, contradiction. *)
      destruct (Qeq_dec y 0) as [Hdec|Hdec]; [exact Hdec|].
      exfalso.
      assert (Hpos : 0 < y * y).
      { destruct (Qlt_le_dec y 0).
        - assert ((-y)*(-y) == y * y) by ring.
          assert (0 < -y) by lra.
          assert (0 < (-y) * (-y)).
          { apply Qle_lt_trans with ((-y) * 0). lra.
            apply Qmult_lt_l; lra. }
          lra.
        - assert (0 < y) by lra.
          apply Qle_lt_trans with (y * 0). lra.
          apply Qmult_lt_l; lra. }
      lra. }
    simpl. rewrite Hy.
    assert (Hih : dot xs ys == 0) by (apply (IH ys Hlen'); unfold norm_sq; exact Hd0).
    rewrite Hih. ring.
Qed.

(* ========================================================================= *)
(* SECTION 6: CAUCHY-SCHWARZ INEQUALITY                                     *)
(* ========================================================================= *)

Lemma Qmult_Qdiv_nonneg_helper : forall a b : Q,
  0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros a b Ha Hb.
  unfold Qdiv.
  assert (H0 : 0 == 0 * / b) by ring. rewrite H0.
  apply Qmult_le_compat_r; [exact Ha | apply Qinv_le_0_compat; lra].
Qed.

Theorem cauchy_schwarz : forall u v,
  length u = length v ->
  dot u v * dot u v <= norm_sq u * norm_sq v.
Proof.
  intros u v Hlen.
  destruct (Qlt_le_dec 0 (norm_sq v)) as [Hpos | Hzero].
  - (* Case: norm_sq v > 0 *)
    set (t := dot u v / norm_sq v).
    assert (Hge0 : 0 <= norm_sq (vec_sub u (scalar_mult t v))) by apply norm_sq_nonneg.
    assert (Hexpand : norm_sq (vec_sub u (scalar_mult t v)) ==
      norm_sq u - (2 # 1) * t * dot u v + t * t * norm_sq v).
    { apply norm_sq_sub_expand. exact Hlen. }
    assert (Hge0' : 0 <= norm_sq u - (2 # 1) * t * dot u v + t * t * norm_sq v) by lra.
    (* Multiply by norm_sq v > 0 *)
    assert (Hinv : norm_sq v * / norm_sq v == 1) by (apply Qmult_inv_r; lra).
    (* Substitute t = dot u v / norm_sq v and simplify *)
    assert (Hkey : (norm_sq u - (2 # 1) * t * dot u v + t * t * norm_sq v) * norm_sq v ==
                   norm_sq u * norm_sq v - dot u v * dot u v).
    { unfold t. field. lra. }
    assert (Hfinal : 0 <= (norm_sq u - (2 # 1) * t * dot u v + t * t * norm_sq v) * norm_sq v).
    { apply Qle_trans with (0 * norm_sq v). lra.
      apply Qmult_le_compat_r; lra. }
    lra.
  - (* Case: norm_sq v <= 0 *)
    assert (Hnn : 0 <= norm_sq v) by apply norm_sq_nonneg.
    assert (Heq : norm_sq v == 0) by lra.
    assert (Hdot0 : dot u v == 0) by (apply norm_sq_zero_dot_zero; assumption).
    assert (H1 : dot u v * dot u v == 0) by (rewrite Hdot0; ring).
    assert (H2 : norm_sq u * norm_sq v == 0) by (rewrite Heq; ring).
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: CONCRETE EXAMPLES                                             *)
(* ========================================================================= *)

Lemma cs_concrete_34_10 :
  dot [3#1; 4#1] [1#1; 0#1] * dot [3#1; 4#1] [1#1; 0#1] <=
  norm_sq [3#1; 4#1] * norm_sq [1#1; 0#1].
Proof.
  unfold norm_sq. simpl. lra.
Qed.

Lemma cs_concrete_11_11 :
  dot [1#1; 1#1] [1#1; 1#1] * dot [1#1; 1#1] [1#1; 1#1] <=
  norm_sq [1#1; 1#1] * norm_sq [1#1; 1#1].
Proof.
  unfold norm_sq. simpl. lra.
Qed.

Lemma cs_concrete_12_34 :
  dot [1#1; 2#1] [3#1; 4#1] * dot [1#1; 2#1] [3#1; 4#1] <=
  norm_sq [1#1; 2#1] * norm_sq [3#1; 4#1].
Proof.
  (* dot = 1*3 + 2*4 = 11, norm_sq [1;2] = 5, norm_sq [3;4] = 25 *)
  (* 121 <= 125 *)
  unfold norm_sq. simpl. lra.
Qed.

Lemma cs_concrete_3d :
  dot [1#1; 2#1; 3#1] [4#1; 5#1; 6#1] * dot [1#1; 2#1; 3#1] [4#1; 5#1; 6#1] <=
  norm_sq [1#1; 2#1; 3#1] * norm_sq [4#1; 5#1; 6#1].
Proof.
  (* dot = 4+10+18 = 32, norm_sq [1;2;3] = 14, norm_sq [4;5;6] = 77 *)
  (* 1024 <= 1078 *)
  unfold norm_sq. simpl. lra.
Qed.

(* ========================================================================= *)
(* SECTION 8: SUMMARY                                                       *)
(* ========================================================================= *)

(** Summary of results:
    - dot: dot product of Q-valued lists
    - norm_sq: squared norm (dot u u)
    - scalar_mult: scalar-vector multiplication
    - vec_sub: pointwise vector subtraction
    - norm_sq_nonneg: sum of squares is non-negative
    - dot_comm: commutativity of dot product
    - dot_scale: linearity in first argument
    - norm_sq_sub_expand: quadratic expansion identity
    - cauchy_schwarz: THE main theorem ⟨u,v⟩² ≤ ‖u‖²·‖v‖²
    - 4 concrete examples verified by computation
*)
