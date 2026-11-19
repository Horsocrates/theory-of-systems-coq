(** * ProcessDiscreteCharacters.v -- Discrete orthogonality of characters over an arbitrary carrier; the 4-point and 3-point DFT, as a ToS System

    Elements: the values chi k j of characters in a carrier R with an
              equivalence, addition and multiplication; for the examples --
              Gaussian rationals Q[i] (pairs of rationals, ProcessGaussianQ.v)
              and Eisenstein rationals Q[w] (pairs of rationals,
              stdlib/EisensteinMUB.v); finite sums over N sample points.
    Roles:    chi k        -- the character number k (frequency);
              [r_sum]      -- the finite sum in the carrier;
              [chi4 k j]   -- i^(k j), the characters of the 4-point DFT;
              [chi3 k j]   -- w^(k j), the characters of the 3-point DFT.
    Rules:    (1) chi 0 j = 1; (2) chi k j * chi k' j = chi (k + k') j;
              (3) Sum_{j<N} chi m j = 0 for 0 < m < N. From (1)-(3) the
              bilinear orthogonality follows over ANY carrier in which
              addition respects the equivalence.

    Proved (no axioms):
      - over Q the three rules are degenerate for N >= 3: every character
        with m > 0 vanishes at all sample points ([chi_forced_zero],
        [chi_forced_zero_bounded], [orthogonality_terms_zero],
        [char_square_sum_zero]); the rules are satisfied by the trivial
        family ([chi_triv_model]) and, for N = 2, by the Walsh sign
        character ([chi_w_model], [chi_w_nonzero], [chi_w_norm_11]);
      - [discrete_orthogonality_gen]: the theorem over an arbitrary carrier;
        the rational statement is its instance
        ([discrete_orthogonality_Q_from_gen]);
      - N = 4 over Q[i]: [chi4_model] (the rules hold for i^(k j)),
        [chi4_nonzero], [dft4_bilinear], [dft4_hermitian] (the full
        orthogonality with conjugation, all k, k' < 4);
      - N = 3 over Q[w]: [chi3_model], [chi3_nonzero], [dft3_bilinear],
        [dft3_hermitian].

    P4 diagnostic: the roots of unity of orders 4 and 3 are elements of
      finite extensions of Q -- pairs of rationals with exact arithmetic and
      finite multiplicative order; no limit is used. The step outside Q is
      a change of the carrier of values, not a hypothesis about rationals.

    NOT claimed:
      - roots of unity of a general order N and the DFT for N other than
        3 and 4 (the carrier Q[zeta_N] is not built here);
      - the values of sin and cos, the number pi, the field C over process
        reals, the continuum integral;
      - index arithmetic modulo N in the general theorem (the range is
        k + k' < N).

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessDiscreteTrig.
From ToS Require Import process.ProcessGaussianQ.
From ToS Require stdlib.EisensteinMUB.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Over Q the three rules are degenerate for N >= 3                 *)
(* ===================================================================== *)

(** The premises of section DiscreteChar in ProcessDiscreteTrig.v, for
    rational values and N >= 3, force chi m j = 0 for every m > 0: from (2)
    and (3) at m = 2, Sum_j chi(1,j)^2 = 0. *)
Theorem chi_forced_zero : forall (N : nat) (chi : nat -> nat -> Q),
  (3 <= N)%nat ->
  (forall j, chi 0%nat j == 1) ->
  (forall k k' j, chi k j * chi k' j == chi (k + k')%nat j) ->
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi m j) N == 0) ->
  forall m j, (0 < m)%nat -> (j < N)%nat -> chi m j == 0.
Proof.
  intros N chi HN H0 Hhom Hsum.
  assert (H1 : forall j, (j < N)%nat -> chi 1%nat j == 0).
  { apply q_sum_sq_zero.
    transitivity (q_sum (fun j => chi 2%nat j) N).
    - apply q_sum_ext. intro j. exact (Hhom 1%nat 1%nat j).
    - apply Hsum; lia. }
  intros m j Hm Hj.
  destruct m as [|m']; [ lia | ].
  transitivity (chi 1%nat j * chi m' j).
  - symmetry. exact (Hhom 1%nat m' j).
  - rewrite (H1 j Hj). ring.
Qed.

(** The same with rule (2) weakened to the range k + k' < N. *)
Theorem chi_forced_zero_bounded : forall (N : nat) (chi : nat -> nat -> Q),
  (3 <= N)%nat ->
  (forall k k' j, (k + k' < N)%nat -> chi k j * chi k' j == chi (k + k')%nat j) ->
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi m j) N == 0) ->
  forall m j, (0 < m)%nat -> (m < N)%nat -> (j < N)%nat -> chi m j == 0.
Proof.
  intros N chi HN Hhom Hsum.
  assert (H1 : forall j, (j < N)%nat -> chi 1%nat j == 0).
  { apply q_sum_sq_zero.
    transitivity (q_sum (fun j => chi 2%nat j) N).
    - apply q_sum_ext. intro j. apply (Hhom 1%nat 1%nat j). lia.
    - apply Hsum; lia. }
  intros m j Hm HmN Hj.
  destruct m as [|m']; [ lia | ].
  transitivity (chi 1%nat j * chi m' j).
  - symmetry. apply (Hhom 1%nat m' j). lia.
  - rewrite (H1 j Hj). ring.
Qed.

(** Hence every term of the orthogonality sum is zero unless k = k' = 0. *)
Corollary orthogonality_terms_zero : forall (N : nat) (chi : nat -> nat -> Q),
  (3 <= N)%nat ->
  (forall j, chi 0%nat j == 1) ->
  (forall k k' j, chi k j * chi k' j == chi (k + k')%nat j) ->
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi m j) N == 0) ->
  forall k k' j, (0 < k + k')%nat -> (j < N)%nat -> chi k j * chi k' j == 0.
Proof.
  intros N chi HN H0 Hhom Hsum k k' j Hkk Hj.
  rewrite (Hhom k k' j).
  apply (chi_forced_zero N chi HN H0 Hhom Hsum); assumption.
Qed.

(** The theorem itself says so: for k = k' >= 1, 2k < N the sum of squares
    of a rational character is zero. *)
Corollary char_square_sum_zero : forall (N : nat) (chi : nat -> nat -> Q),
  (forall j, chi 0%nat j == 1) ->
  (forall k k' j, chi k j * chi k' j == chi (k + k')%nat j) ->
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi m j) N == 0) ->
  forall k, (0 < k)%nat -> (k + k < N)%nat ->
  q_sum (fun j => chi k j * chi k j) N == 0.
Proof.
  intros N chi H0 Hhom Hsum k Hk Hkk.
  rewrite (discrete_orthogonality N chi H0 Hhom Hsum k k Hkk).
  destruct (k + k)%nat eqn:E; [ lia | reflexivity ].
Qed.

(* ===================================================================== *)
(*  2. Which rational families satisfy the rules                        *)
(* ===================================================================== *)

(** The trivial family: chi_0 = 1, chi_k = 0 for k >= 1 -- every N. *)
Definition chi_triv (k j : nat) : Q := if (k =? 0)%nat then 1 else 0.

Lemma chi_triv_model : forall N : nat,
  (forall j, chi_triv 0%nat j == 1) /\
  (forall k k' j, chi_triv k j * chi_triv k' j == chi_triv (k + k')%nat j) /\
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi_triv m j) N == 0).
Proof.
  intro N. split; [ | split ].
  - intro j. reflexivity.
  - intros k k' j. unfold chi_triv.
    destruct k as [|k]; destruct k' as [|k']; simpl; ring.
  - intros m Hm _. destruct m as [|m']; [ lia | ].
    transitivity (q_sum (fun _ : nat => 0) N).
    + apply q_sum_ext. intro j. reflexivity.
    + apply q_sum_zero.
Qed.

(** N = 2: the sign character (-1)^(k j) -- the Walsh character. *)
Definition sgn (n : nat) : Q := if Nat.even n then 1 else -(1).
Definition chi_w (k j : nat) : Q := sgn (k * j).

Lemma sgn_add : forall a b, sgn a * sgn b == sgn (a + b).
Proof.
  intros a b. unfold sgn. rewrite Nat.even_add.
  destruct (Nat.even a); destruct (Nat.even b); simpl; ring.
Qed.

Lemma chi_w_model :
  (forall j, chi_w 0%nat j == 1) /\
  (forall k k' j, chi_w k j * chi_w k' j == chi_w (k + k')%nat j) /\
  (forall m, (0 < m)%nat -> (m < 2)%nat -> q_sum (fun j => chi_w m j) 2 == 0).
Proof.
  split; [ | split ].
  - intro j. reflexivity.
  - intros k k' j. unfold chi_w. rewrite Nat.mul_add_distr_r. apply sgn_add.
  - intros m Hm Hm2. assert (m = 1%nat) by lia. subst m. vm_compute. reflexivity.
Qed.

Lemma chi_w_nonzero : ~ chi_w 1%nat 1%nat == 0.
Proof. vm_compute. discriminate. Qed.

(** For N = 2 the range k + k' < 2 does not contain the pair (1, 1): the
    norm of the nonzero character equals N but is not covered. *)
Lemma chi_w_norm_11 : q_sum (fun j => chi_w 1%nat j * chi_w 1%nat j) 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3. The theorem over an arbitrary carrier of values                  *)
(* ===================================================================== *)

(** Only an equivalence and the compatibility of addition are needed. *)
Section DiscreteCharGen.

Variable R : Type.
Variable req : R -> R -> Prop.
Variable rO rI : R.
Variable radd rmul : R -> R -> R.

Hypothesis req_refl  : forall x, req x x.
Hypothesis req_trans : forall x y z, req x y -> req y z -> req x z.
Hypothesis radd_compat : forall x x' y y',
  req x x' -> req y y' -> req (radd x y) (radd x' y').

Fixpoint r_sum (g : nat -> R) (N : nat) : R :=
  match N with
  | O => rO
  | S k => radd (r_sum g k) (g k)
  end.

Lemma r_sum_ext : forall (g h : nat -> R) (N : nat),
  (forall i, req (g i) (h i)) -> req (r_sum g N) (r_sum h N).
Proof.
  intros g h N H. induction N as [|k IH]; cbn [r_sum].
  - apply req_refl.
  - apply radd_compat; [ exact IH | apply H ].
Qed.

Variable N : nat.
Variable chi : nat -> nat -> R.

Hypothesis chi_0 : forall j, req (chi 0%nat j) rI.
Hypothesis chi_hom : forall k k' j, req (rmul (chi k j) (chi k' j)) (chi (k + k')%nat j).
Hypothesis chi_sum_zero : forall m, (0 < m)%nat -> (m < N)%nat ->
  req (r_sum (fun j => chi m j) N) rO.

Theorem discrete_orthogonality_gen : forall k k', (k + k' < N)%nat ->
  req (r_sum (fun j => rmul (chi k j) (chi k' j)) N)
      (if (k + k' =? 0)%nat then r_sum (fun _ => rI) N else rO).
Proof.
  intros k k' Hkk.
  apply req_trans with (r_sum (fun j => chi (k + k')%nat j) N).
  { apply r_sum_ext. intro j. apply chi_hom. }
  destruct (k + k')%nat as [|s] eqn:E.
  - simpl. apply r_sum_ext. intro j. apply chi_0.
  - simpl. apply chi_sum_zero; lia.
Qed.

End DiscreteCharGen.

(** Over the carrier Q the general sum is [q_sum]. *)
Lemma r_sum_Q_is_q_sum : forall (g : nat -> Q) (N : nat),
  r_sum Q 0 Qplus g N = q_sum g N.
Proof. intros g N. induction N as [|k IH]; cbn [r_sum q_sum]; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The rational statement as an instance of the general theorem. *)
Corollary discrete_orthogonality_Q_from_gen : forall (N : nat) (chi : nat -> nat -> Q),
  (forall j, chi 0%nat j == 1) ->
  (forall k k' j, chi k j * chi k' j == chi (k + k')%nat j) ->
  (forall m, (0 < m)%nat -> (m < N)%nat -> q_sum (fun j => chi m j) N == 0) ->
  forall k k', (k + k' < N)%nat ->
  q_sum (fun j => chi k j * chi k' j) N
  == (if (k + k' =? 0)%nat then q_sum (fun _ => 1) N else 0).
Proof.
  intros N chi H0 Hh Hs k k' Hkk.
  assert (Hs' : forall m, (0 < m)%nat -> (m < N)%nat ->
            r_sum Q 0 Qplus (fun j => chi m j) N == 0).
  { intros m Hm HmN. rewrite r_sum_Q_is_q_sum. exact (Hs m Hm HmN). }
  pose proof (discrete_orthogonality_gen Q Qeq 0 1 Qplus Qmult Qeq_refl Qeq_trans
                (fun x x' y y' Hx Hy => Qplus_comp x x' Hx y y' Hy)
                N chi H0 Hh Hs' k k' Hkk) as H.
  repeat rewrite r_sum_Q_is_q_sum in H. exact H.
Qed.

(* ===================================================================== *)
(*  4. N = 4 over the Gaussian rationals Q[i]                           *)
(* ===================================================================== *)

Lemma qi_eq_refl : forall z, qi_eq z z.
Proof. intro z. split; reflexivity. Qed.

Lemma qi_eq_trans : forall x y z, qi_eq x y -> qi_eq y z -> qi_eq x z.
Proof. intros x y z [H1 H2] [H3 H4]. split; [ rewrite H1; exact H3 | rewrite H2; exact H4 ]. Qed.

Lemma qi_add_compat : forall x x' y y',
  qi_eq x x' -> qi_eq y y' -> qi_eq (qi_add x y) (qi_add x' y').
Proof.
  intros x x' y y' [H1 H2] [H3 H4]. unfold qi_eq, qi_add; simpl.
  split; [ rewrite H1, H3 | rewrite H2, H4 ]; reflexivity.
Qed.

(** The powers of the imaginary unit: i^n. *)
Definition i_pow (n : nat) : Qi :=
  match (n mod 4)%nat with
  | O => qi_one
  | S O => qi_i
  | S (S O) => mkQi (-(1)) 0
  | _ => mkQi 0 (-(1))
  end.

Lemma i_pow_add : forall a b, qi_eq (qi_mul (i_pow a) (i_pow b)) (i_pow (a + b)).
Proof.
  intros a b. unfold i_pow. rewrite (Nat.Div0.add_mod a b 4).
  assert (Ha : (a mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hb : (b mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (a mod 4)%nat as [|[|[|[|?]]]]; try lia;
  destruct (b mod 4)%nat as [|[|[|[|?]]]]; try lia;
  vm_compute; split; reflexivity.
Qed.

(** The characters of the 4-point DFT: chi_k(j) = i^(k j). *)
Definition chi4 (k j : nat) : Qi := i_pow (k * j).

Definition qi_sum := r_sum Qi qi_zero qi_add.

(** The three rules hold. *)
Lemma chi4_model :
  (forall j, qi_eq (chi4 0%nat j) qi_one) /\
  (forall k k' j, qi_eq (qi_mul (chi4 k j) (chi4 k' j)) (chi4 (k + k')%nat j)) /\
  (forall m, (0 < m)%nat -> (m < 4)%nat ->
     qi_eq (qi_sum (fun j => chi4 m j) 4) qi_zero).
Proof.
  split; [ | split ].
  - intro j. vm_compute. split; reflexivity.
  - intros k k' j. unfold chi4. rewrite Nat.mul_add_distr_r. apply i_pow_add.
  - intros m Hm Hm4.
    destruct m as [|[|[|[|?]]]]; try lia; vm_compute; split; reflexivity.
Qed.

(** The character chi_1 is not zero: chi_1(1) = i. *)
Lemma chi4_nonzero : ~ qi_eq (chi4 1%nat 1%nat) qi_zero.
Proof. vm_compute. intros [_ H]. discriminate H. Qed.

(** The general theorem on this example: the bilinear form, k + k' < 4. *)
Theorem dft4_bilinear : forall k k', (k + k' < 4)%nat ->
  qi_eq (qi_sum (fun j => qi_mul (chi4 k j) (chi4 k' j)) 4)
        (if (k + k' =? 0)%nat then qi_sum (fun _ => qi_one) 4 else qi_zero).
Proof.
  destruct chi4_model as [H0 [Hh Hs]].
  intros k k' Hkk.
  exact (discrete_orthogonality_gen Qi qi_eq qi_zero qi_one qi_add qi_mul
           qi_eq_refl qi_eq_trans qi_add_compat 4%nat chi4 H0 Hh Hs k k' Hkk).
Qed.

Lemma qi_sum_ones4 : qi_eq (qi_sum (fun _ => qi_one) 4) (mkQi 4 0).
Proof. vm_compute. split; reflexivity. Qed.

(** The full orthogonality of the 4-point DFT with conjugation:
    Sum_j chi_k(j) * conj(chi_k'(j)) = 4 [k = k'] for all k, k' < 4. *)
Theorem dft4_hermitian : forall k k', (k < 4)%nat -> (k' < 4)%nat ->
  qi_eq (qi_sum (fun j => qi_mul (chi4 k j) (qi_conj (chi4 k' j))) 4)
        (if (k =? k')%nat then mkQi 4 0 else qi_zero).
Proof.
  intros k k' Hk Hk'.
  destruct k as [|[|[|[|?]]]]; try lia;
  destruct k' as [|[|[|[|?]]]]; try lia;
  vm_compute; split; reflexivity.
Qed.

(* ===================================================================== *)
(*  5. N = 3 over the Eisenstein rationals Q[w]                         *)
(* ===================================================================== *)

Module E := stdlib.EisensteinMUB.

(** The powers of the primitive cube root of unity: w^n. *)
Definition w_pow (n : nat) : E.GQw :=
  match (n mod 3)%nat with
  | O => E.gw1
  | S O => E.gww
  | _ => E.gww2
  end.

Definition gw_eq (z w : E.GQw) : Prop := fst z == fst w /\ snd z == snd w.

Lemma gw_eq_refl : forall z, gw_eq z z.
Proof. intro z. split; reflexivity. Qed.

Lemma gw_eq_trans : forall x y z, gw_eq x y -> gw_eq y z -> gw_eq x z.
Proof. intros x y z [H1 H2] [H3 H4]. split; [ rewrite H1; exact H3 | rewrite H2; exact H4 ]. Qed.

Lemma gwadd_compat : forall x x' y y',
  gw_eq x x' -> gw_eq y y' -> gw_eq (E.gwadd x y) (E.gwadd x' y').
Proof.
  intros x x' y y' [H1 H2] [H3 H4]. unfold gw_eq, E.gwadd; simpl.
  split; [ rewrite H1, H3 | rewrite H2, H4 ]; reflexivity.
Qed.

Lemma w_pow_add : forall a b, gw_eq (E.gwmul (w_pow a) (w_pow b)) (w_pow (a + b)).
Proof.
  intros a b. unfold w_pow. rewrite (Nat.Div0.add_mod a b 3).
  assert (Ha : (a mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hb : (b mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (a mod 3)%nat as [|[|[|?]]]; try lia;
  destruct (b mod 3)%nat as [|[|[|?]]]; try lia;
  vm_compute; split; reflexivity.
Qed.

(** The characters of the 3-point DFT: chi_k(j) = w^(k j). *)
Definition chi3 (k j : nat) : E.GQw := w_pow (k * j).
Definition gw_sum := r_sum E.GQw E.gw0 E.gwadd.

(** The three rules hold. *)
Lemma chi3_model :
  (forall j, gw_eq (chi3 0%nat j) E.gw1) /\
  (forall k k' j, gw_eq (E.gwmul (chi3 k j) (chi3 k' j)) (chi3 (k + k')%nat j)) /\
  (forall m, (0 < m)%nat -> (m < 3)%nat ->
     gw_eq (gw_sum (fun j => chi3 m j) 3) E.gw0).
Proof.
  split; [ | split ].
  - intro j. vm_compute. split; reflexivity.
  - intros k k' j. unfold chi3. rewrite Nat.mul_add_distr_r. apply w_pow_add.
  - intros m Hm Hm3.
    destruct m as [|[|[|?]]]; try lia; vm_compute; split; reflexivity.
Qed.

(** The character chi_1 is not zero: chi_1(1) = w. *)
Lemma chi3_nonzero : ~ gw_eq (chi3 1%nat 1%nat) E.gw0.
Proof. vm_compute. intros [_ H]. discriminate H. Qed.

(** The general theorem on this example: the bilinear form, k + k' < 3. *)
Theorem dft3_bilinear : forall k k', (k + k' < 3)%nat ->
  gw_eq (gw_sum (fun j => E.gwmul (chi3 k j) (chi3 k' j)) 3)
        (if (k + k' =? 0)%nat then gw_sum (fun _ => E.gw1) 3 else E.gw0).
Proof.
  destruct chi3_model as [H0 [Hh Hs]].
  intros k k' Hkk.
  exact (discrete_orthogonality_gen E.GQw gw_eq E.gw0 E.gw1 E.gwadd E.gwmul
           gw_eq_refl gw_eq_trans gwadd_compat 3%nat chi3 H0 Hh Hs k k' Hkk).
Qed.

(** The full orthogonality of the 3-point DFT with conjugation:
    Sum_j chi_k(j) * conj(chi_k'(j)) = 3 [k = k'] for all k, k' < 3. *)
Theorem dft3_hermitian : forall k k', (k < 3)%nat -> (k' < 3)%nat ->
  gw_eq (gw_sum (fun j => E.gwmul (chi3 k j) (E.gwconj (chi3 k' j))) 3)
        (if (k =? k')%nat then (3, 0) else E.gw0).
Proof.
  intros k k' Hk Hk'.
  destruct k as [|[|[|?]]]; try lia;
  destruct k' as [|[|[|?]]]; try lia;
  vm_compute; split; reflexivity.
Qed.

