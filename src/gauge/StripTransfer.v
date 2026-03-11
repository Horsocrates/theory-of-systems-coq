(* ========================================================================= *)
(*        STRIP TRANSFER — N x 1 Transfer Matrix                              *)
(*                                                                            *)
(*  T(s,s') = w(s) * alpha^{dH(s,s')} * w(s')                              *)
(*                                                                            *)
(*  At beta=8 (alpha=0): T(s,s') = delta_{s,s'} * gamma^{2d(s)}.            *)
(*  The matrix is DIAGONAL for any N.                                         *)
(*                                                                            *)
(*  STATUS: ~38 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List Bool.
Import ListNotations.
From ToS Require Import gauge.DomainWalls gauge.Coupled2D.
Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: Spatial Weight                                                    *)
(* ========================================================================= *)

(** Weight w(s) = gamma^{d(s)} *)
Fixpoint gamma_pow (beta : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => gamma_2d beta * gamma_pow beta k
  end.

Definition strip_weight (beta : Q) (s : bstring) : Q :=
  gamma_pow beta (domain_walls s).

Lemma gamma_pow_0 : forall beta, gamma_pow beta 0 == 1.
Proof. intros. reflexivity. Qed.

Lemma gamma_pow_1 : forall beta, gamma_pow beta 1 == gamma_2d beta.
Proof. intros. simpl. lra. Qed.

Lemma gamma_pow_at_8_0 : gamma_pow 8 0 == 1.
Proof. reflexivity. Qed.

Lemma gamma_pow_at_8_1 : gamma_pow 8 1 == 1#2.
Proof. simpl. rewrite gamma_at_8. lra. Qed.

Lemma gamma_pow_at_8_2 : gamma_pow 8 2 == 1#4.
Proof.
  simpl. assert (Hg := gamma_at_8).
  unfold Qeq in *. simpl in *. lia.
Qed.

Lemma strip_weight_ground : forall beta n,
  strip_weight beta (all_same false n) == 1.
Proof.
  intros. unfold strip_weight. rewrite domain_walls_all_false. reflexivity.
Qed.

Lemma strip_weight_ground_true : forall beta n,
  strip_weight beta (all_same true n) == 1.
Proof.
  intros. unfold strip_weight. rewrite domain_walls_all_true. reflexivity.
Qed.

Lemma strip_weight_d1 : forall beta s,
  domain_walls s = 1%nat ->
  strip_weight beta s == gamma_2d beta.
Proof.
  intros beta s Hd. unfold strip_weight. rewrite Hd. simpl. lra.
Qed.

(** At beta=8: weight of d=0 state *)
Lemma strip_weight_at_8_d0 : forall s,
  domain_walls s = 0%nat -> strip_weight 8 s == 1.
Proof.
  intros s Hd. unfold strip_weight. rewrite Hd. reflexivity.
Qed.

(** At beta=8: weight of d=1 state *)
Lemma strip_weight_at_8_d1 : forall s,
  domain_walls s = 1%nat -> strip_weight 8 s == 1#2.
Proof.
  intros s Hd. unfold strip_weight. rewrite Hd. exact gamma_pow_at_8_1.
Qed.

(** At beta=8: weight of d=2 state *)
Lemma strip_weight_at_8_d2 : forall s,
  domain_walls s = 2%nat -> strip_weight 8 s == 1#4.
Proof.
  intros s Hd. unfold strip_weight. rewrite Hd. exact gamma_pow_at_8_2.
Qed.

(* ========================================================================= *)
(*  PART II: Alpha Power (temporal coupling)                                  *)
(* ========================================================================= *)

Fixpoint alpha_pow (beta : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => alpha_2d beta * alpha_pow beta k
  end.

Lemma alpha_pow_0 : forall beta, alpha_pow beta 0 == 1.
Proof. intros. reflexivity. Qed.

Lemma alpha_pow_at_8_0 : alpha_pow 8 0 == 1.
Proof. reflexivity. Qed.

(** At beta=8: alpha=0, so alpha^n = 0 for n >= 1 *)
Lemma alpha_at_8_zero : alpha_2d 8 == 0.
Proof. exact alpha_at_8. Qed.

Lemma alpha_pow_at_8_pos : forall n,
  (1 <= n)%nat -> alpha_pow 8 n == 0.
Proof.
  intros n Hn. destruct n as [|n']; [lia |].
  simpl. rewrite alpha_at_8. lra.
Qed.

(* ========================================================================= *)
(*  PART III: Transfer Matrix Entry                                           *)
(* ========================================================================= *)

(** General N x 1 strip transfer matrix entry *)
Definition strip_transfer (beta : Q) (s s' : bstring) : Q :=
  strip_weight beta s * alpha_pow beta (hamming_dist s s') * strip_weight beta s'.

(** At beta=8: off-diagonal vanishes *)
Lemma hamming_pos_neq : forall s s',
  s <> s' ->
  length s = length s' ->
  (1 <= hamming_dist s s')%nat.
Proof.
  induction s as [|x xs IH]; intros [|y ys] Hneq Hlen; simpl in *.
  - exfalso. apply Hneq. reflexivity.
  - lia.
  - lia.
  - destruct (Bool.eqb x y) eqn:Heqb.
    + apply Bool.eqb_prop in Heqb. subst y.
      assert (Hneq' : xs <> ys) by (intro Heq; apply Hneq; f_equal; exact Heq).
      assert (Hlen' : length xs = length ys) by lia.
      specialize (IH ys Hneq' Hlen').
      unfold bdiff. destruct x; simpl; lia.
    + unfold bdiff. destruct x, y; simpl; try lia.
      all: exfalso; rewrite Bool.eqb_reflx in Heqb; discriminate.
Qed.

Theorem strip_diagonal_at_8 : forall s s',
  s <> s' ->
  length s = length s' ->
  strip_transfer 8 s s' == 0.
Proof.
  intros s s' Hneq Hlen.
  unfold strip_transfer.
  assert (H : (1 <= hamming_dist s s')%nat) by (apply hamming_pos_neq; assumption).
  rewrite (alpha_pow_at_8_pos (hamming_dist s s') H).
  lra.
Qed.

(** Diagonal entries at beta=8: T(s,s) = gamma^{2*d(s)} *)
Theorem strip_diag_at_8 : forall s,
  strip_transfer 8 s s == strip_weight 8 s * strip_weight 8 s.
Proof.
  intros s. unfold strip_transfer.
  rewrite hamming_dist_zero.
  simpl. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Consistency with Previous Results                                *)
(* ========================================================================= *)

(** N=1: single site, no plaquettes *)
Theorem strip_n1_same : forall beta b,
  strip_transfer beta [b] [b] == 1.
Proof.
  intros beta b. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, alpha_pow, gamma_pow, bdiff.
  destruct b; simpl; lra.
Qed.

Theorem strip_n1_diff : forall beta b,
  strip_transfer beta [b] [negb b] == alpha_2d beta.
Proof.
  intros beta b. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, alpha_pow, gamma_pow, bdiff.
  destruct b; simpl; lra.
Qed.

(** N=2: four concrete entries from ground state [false;false] *)
Lemma strip_n2_00_00 : forall beta,
  strip_transfer beta [false;false] [false;false] == 1.
Proof.
  intros. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, bdiff, alpha_pow, gamma_pow.
  simpl. lra.
Qed.

Lemma strip_n2_00_01 : forall beta,
  strip_transfer beta [false;false] [false;true] == alpha_2d beta * gamma_2d beta.
Proof.
  intros. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, bdiff, alpha_pow, gamma_pow.
  simpl. lra.
Qed.

Lemma strip_n2_00_10 : forall beta,
  strip_transfer beta [false;false] [true;false] == alpha_2d beta * gamma_2d beta.
Proof.
  intros. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, bdiff, alpha_pow, gamma_pow.
  simpl. lra.
Qed.

Lemma strip_n2_00_11 : forall beta,
  strip_transfer beta [false;false] [true;true] == alpha_2d beta * alpha_2d beta.
Proof.
  intros. unfold strip_transfer, strip_weight, hamming_dist, domain_walls, bdiff, alpha_pow, gamma_pow.
  simpl. lra.
Qed.

(** At beta=8: N=2 is diagonal *)
Theorem strip_n2_at_8 :
  strip_transfer 8 [false;false] [false;false] == 1 /\
  strip_transfer 8 [false;false] [false;true] == 0 /\
  strip_transfer 8 [false;false] [true;false] == 0 /\
  strip_transfer 8 [false;false] [true;true] == 0.
Proof.
  split; [| split; [| split]].
  - rewrite strip_n2_00_00. lra.
  - rewrite strip_n2_00_01. rewrite alpha_at_8. lra.
  - rewrite strip_n2_00_10. rewrite alpha_at_8. lra.
  - rewrite strip_n2_00_11. rewrite alpha_at_8. lra.
Qed.

(* ========================================================================= *)
(*  PART V: Symmetries                                                        *)
(* ========================================================================= *)

(** Complement symmetry: T(compl(s), compl(s')) = T(s, s') *)
Lemma hamming_complement : forall s s',
  hamming_dist (complement s) (complement s') = hamming_dist s s'.
Proof.
  induction s as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  rewrite bdiff_negb_negb. f_equal. exact (IH ys).
Qed.

Theorem strip_complement_sym : forall beta s s',
  strip_transfer beta (complement s) (complement s') ==
  strip_transfer beta s s'.
Proof.
  intros. unfold strip_transfer.
  unfold strip_weight. rewrite complement_preserves_walls.
  rewrite complement_preserves_walls.
  rewrite hamming_complement.
  lra.
Qed.

(** Reversal preserves domain walls: concrete cases *)
Lemma rev_walls_2 : forall a b,
  domain_walls (rev [a; b]) = domain_walls [a; b].
Proof. intros [] []; reflexivity. Qed.

Lemma rev_walls_3 : forall a b c,
  domain_walls (rev [a; b; c]) = domain_walls [a; b; c].
Proof. intros [] [] []; reflexivity. Qed.

(** Strip transfer is nonneg at beta=8 *)
Lemma gamma_pow_nonneg : forall beta n,
  0 < beta -> beta < 16 ->
  0 <= gamma_pow beta n.
Proof.
  intros beta n Hb1 Hb2. induction n as [|n IH]; simpl; [lra |].
  apply Qmult_le_0_compat; [| exact IH].
  assert (Hg := gamma_positive beta Hb1 Hb2). lra.
Qed.

Lemma strip_weight_nonneg : forall beta s,
  0 < beta -> beta < 16 ->
  0 <= strip_weight beta s.
Proof.
  intros. unfold strip_weight. apply gamma_pow_nonneg; assumption.
Qed.

Lemma strip_transfer_at_8_nonneg : forall s,
  0 <= strip_transfer 8 s s.
Proof.
  intros s. rewrite strip_diag_at_8.
  apply Qmult_le_0_compat; apply strip_weight_nonneg; lra.
Qed.

(* ========================================================================= *)
(*  PART VI: Summary                                                          *)
(* ========================================================================= *)

Theorem strip_transfer_main :
  (* N=2 at beta=8: diagonal with {1, 0, 0, 0} in row 0 *)
  strip_transfer 8 [false;false] [false;false] == 1 /\
  strip_transfer 8 [false;false] [false;true] == 0 /\
  (* Alpha vanishes at beta=8 *)
  alpha_2d 8 == 0 /\
  (* Ground state weight is 1 *)
  strip_weight 8 (all_same false 100) == 1.
Proof.
  split; [| split; [| split]].
  - rewrite strip_n2_00_00. lra.
  - rewrite strip_n2_00_01. rewrite alpha_at_8. lra.
  - exact alpha_at_8.
  - exact (strip_weight_ground 8 100).
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~38 Qed, 0 Admitted (1 Admitted pending reversal symmetry)                *)
(*                                                                            *)
(*  Part I: gamma_pow_0, gamma_pow_1, gamma_pow_at_8_0/1/2,                  *)
(*          strip_weight_ground/ground_true/d1/at_8_d0/d1/d2 (11)            *)
(*  Part II: alpha_pow_0, alpha_pow_at_8_0, alpha_at_8_zero,                 *)
(*           alpha_pow_at_8_pos (4)                                           *)
(*  Part III: hamming_pos_neq, strip_diagonal_at_8, strip_diag_at_8 (3)     *)
(*  Part IV: strip_n1_same/diff, strip_n2_00_00/01/10/11,                    *)
(*           strip_n2_at_8 (7)                                               *)
(*  Part V: hamming_complement, strip_complement_sym,                        *)
(*          strip_transfer_at_8_nonneg (3)                                   *)
(*  Part VI: strip_transfer_main (1)                                          *)
(* ========================================================================= *)
