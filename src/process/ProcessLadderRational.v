(** * ProcessLadderRational.v -- The oscillator ladder with rational weights; truncations, as a ToS System

    Elements: rational amplitudes psi(n) on the number states |n> (the Fock
              process of ProcessHarmonicLadder.v); two sequences of rational
              weights al, be; truncations to the first K levels.
    Roles:    [gann al]   -- lowering:  (a psi)(n)  = al(n+1) * psi(n+1);
              [gcre be]   -- raising:   (a+ psi)(n) = be(n) * psi(n-1), 0 at n = 0;
              [num], [ham] -- number operator and Hamiltonian N + 1/2;
              [trunc K]   -- the truncation to the first K levels;
              [tann], [tcre] -- the ladder operators of the truncation;
              weight w    -- the pairing in which a and a+ are mutually
                             adjoint (w(n+1) be(n+1) = w(n) al(n+1)).
    Rules:    al(n) * be(n) = n gives a+ a = N and [a, a+] = 1 on all
              sequences; (a+ a + 1/2) psi = H psi, so the level formula
              E_n = n + 1/2 is a consequence of the ladder; on a truncation
              the commutator is 1 below the top level and -(K-1) on it.

    Proved (no axioms):
      - [ladder_premise_unsatisfiable]: no rational s has s(n)^2 = n for
        all n (s(2) would be a square root of 2) -- the premise of the
        section Ladder of ProcessHarmonicLadder.v has no instance;
      - under al(n) * be(n) = n: [gcre_gann_eq_num], [gann_gcre_eq],
        [gcommutator_canonical], [gham_from_ladder], [gham_ladder_eigen],
        [gann_ket_S], [gann_ket_O], [gcre_ket], [ladder_adjoint_weighted];
      - truncations: [tcre_tann_eq], [truncated_commutator_below_top],
        [truncated_commutator_top];
      - the rational realization al(n) = n, be(n) = 1 (no premises):
        [commutator_canonical_rational], [number_operator_rational],
        [ham_rational_eigen], [ladder_adjoint_factorial] (a and a+ are
        mutually adjoint in the pairing with the weights n!),
        [truncated_rational_below_top], [truncated_rational_top];
      - [ladder_weights_unbounded]: in every such ladder one of the weights
        is unbounded.

    P4 diagnostic: the square root of n is not an element; it is replaced by
      two rational weights whose product is n (the unnormalised number
      states, <n|n> = n!). The Fock space is the process of truncations:
      every truncation is a finite rational object, and its defect sits on
      the top level only, which moves away as K grows.

    NOT claimed:
      - the normalised ladder with the coefficient sqrt(n) itself (it needs
        the square root as a process);
      - a completed Fock space or a spectral theorem for the completed
        operator;
      - boundedness or unboundedness of operators in a norm (there is no
        operator norm in this layer).

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require process.ProcessHarmonicLadder.
From ToS Require analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The premise s(n)^2 = n has no rational instance                  *)
(* ===================================================================== *)

(** The section Ladder of ProcessHarmonicLadder.v assumes a rational
    s : nat -> Q with s n * s n == n for every n. There is none. *)
Lemma ladder_premise_unsatisfiable :
  forall s : nat -> Q, (forall n, s n * s n == inject_Z (Z.of_nat n)) -> False.
Proof.
  intros s Hs. apply (Sqrt2Irrational.no_rational_sqrt2 (s 2%nat)).
  rewrite (Hs 2%nat). reflexivity.
Qed.

(* ===================================================================== *)
(*  2. The ladder with two rational weights                             *)
(* ===================================================================== *)

Section GenLadder.

Variables al be : nat -> Q.
Hypothesis Hab : forall n, al n * be n == inject_Z (Z.of_nat n).

(** Lowering: (a psi)(n) = al(n+1) * psi(n+1). *)
Definition gann (psi : nat -> Q) : nat -> Q := fun n => al (S n) * psi (S n).

(** Raising: (a+ psi)(n) = be(n) * psi(n-1), zero at n = 0. *)
Definition gcre (psi : nat -> Q) : nat -> Q :=
  fun n => match n with O => 0 | S m => be (S m) * psi m end.

(** a+ a = N. *)
Lemma gcre_gann_eq_num : forall psi n,
  gcre (gann psi) n == ProcessHarmonicLadder.num psi n.
Proof.
  intros psi n. unfold gcre, gann, ProcessHarmonicLadder.num. destruct n as [|m].
  - simpl. ring.
  - setoid_replace (inject_Z (Z.of_nat (S m))) with (al (S m) * be (S m))
      by (symmetry; apply Hab).
    ring.
Qed.

(** a a+ = N + 1. *)
Lemma gann_gcre_eq : forall psi n,
  gann (gcre psi) n == inject_Z (Z.of_nat (S n)) * psi n.
Proof.
  intros psi n. unfold gann, gcre.
  setoid_replace (inject_Z (Z.of_nat (S n))) with (al (S n) * be (S n))
    by (symmetry; apply Hab).
  ring.
Qed.

(** [a, a+] = 1 on all sequences nat -> Q, coordinate by coordinate. *)
Theorem gcommutator_canonical : forall psi n,
  gann (gcre psi) n - gcre (gann psi) n == psi n.
Proof.
  intros psi n. rewrite (gann_gcre_eq psi n), (gcre_gann_eq_num psi n).
  unfold ProcessHarmonicLadder.num.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite inject_Z_plus. change (inject_Z 1) with (1 # 1). ring.
Qed.

(** The level formula as a consequence of the ladder: (a+ a + 1/2) psi = H psi. *)
Theorem gham_from_ladder : forall psi n,
  gcre (gann psi) n + (1 # 2) * psi n == ProcessHarmonicLadder.ham psi n.
Proof.
  intros psi n. rewrite (gcre_gann_eq_num psi n).
  unfold ProcessHarmonicLadder.num, ProcessHarmonicLadder.ham, ProcessHarmonicLadder.energy.
  ring.
Qed.

(** (a+ a + 1/2) |n> = (n + 1/2) |n>. *)
Corollary gham_ladder_eigen : forall n m,
  gcre (gann (ProcessHarmonicLadder.ket n)) m + (1 # 2) * ProcessHarmonicLadder.ket n m
  == ProcessHarmonicLadder.energy n * ProcessHarmonicLadder.ket n m.
Proof.
  intros n m. rewrite (gham_from_ladder (ProcessHarmonicLadder.ket n) m).
  apply ProcessHarmonicLadder.ham_eigenvalue.
Qed.

(** The ladder on the number states: a |n+1> = al(n+1) |n>, a |0> = 0,
    a+ |n> = be(n+1) |n+1>. *)
Lemma gann_ket_S : forall n m,
  gann (ProcessHarmonicLadder.ket (S n)) m == al (S n) * ProcessHarmonicLadder.ket n m.
Proof.
  intros n m. unfold gann, ProcessHarmonicLadder.ket. cbn [Nat.eqb].
  destruct (Nat.eqb m n) eqn:E.
  - apply Nat.eqb_eq in E. subst m. reflexivity.
  - ring.
Qed.

Lemma gann_ket_O : forall m, gann (ProcessHarmonicLadder.ket 0%nat) m == 0.
Proof.
  intro m. unfold gann, ProcessHarmonicLadder.ket. cbn [Nat.eqb]. ring.
Qed.

Lemma gcre_ket : forall n m,
  gcre (ProcessHarmonicLadder.ket n) m == be (S n) * ProcessHarmonicLadder.ket (S n) m.
Proof.
  intros n m. unfold gcre, ProcessHarmonicLadder.ket. destruct m as [|k]; cbn [Nat.eqb].
  - ring.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k. reflexivity.
    + ring.
Qed.

(** a and a+ are mutually adjoint in the pairing with a weight w such that
    w(n+1) * be(n+1) = w(n) * al(n+1):
    Sum_{n<K} w n (a psi) n phi n = Sum_{n<K+1} w n psi n (a+ phi) n. *)
Theorem ladder_adjoint_weighted : forall (w : nat -> Q),
  (forall n, w (S n) * be (S n) == w n * al (S n)) ->
  forall psi phi K,
  q_sum (fun n => w n * gann psi n * phi n) K
  == q_sum (fun n => w n * psi n * gcre phi n) (S K).
Proof.
  intros w Hw psi phi K. induction K as [|k IH].
  - cbn [q_sum]. unfold gcre. ring.
  - change (q_sum (fun n => w n * gann psi n * phi n) (S k))
      with (q_sum (fun n => w n * gann psi n * phi n) k + w k * gann psi k * phi k).
    change (q_sum (fun n => w n * psi n * gcre phi n) (S (S k)))
      with (q_sum (fun n => w n * psi n * gcre phi n) (S k)
            + w (S k) * psi (S k) * gcre phi (S k)).
    rewrite IH. apply Qplus_comp; [ reflexivity | ].
    unfold gann, gcre.
    assert (H := Hw k).
    transitivity ((w k * al (S k)) * (psi (S k) * phi k)); [ ring | ].
    rewrite <- H. ring.
Qed.

(** Truncation to the first K levels. *)
Definition trunc (K : nat) (psi : nat -> Q) : nat -> Q :=
  fun n => if (n <? K)%nat then psi n else 0.
Definition tann (K : nat) (psi : nat -> Q) : nat -> Q := trunc K (gann (trunc K psi)).
Definition tcre (K : nat) (psi : nat -> Q) : nat -> Q := trunc K (gcre (trunc K psi)).

Lemma trunc_in : forall K psi n, (n < K)%nat -> trunc K psi n = psi n.
Proof. intros K psi n H. unfold trunc. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma trunc_out : forall K psi n, (K <= n)%nat -> trunc K psi n = 0.
Proof. intros K psi n H. unfold trunc. apply Nat.ltb_ge in H. rewrite H. reflexivity. Qed.

(** On a truncation a+ a is still the number operator. *)
Lemma tcre_tann_eq : forall K psi n, (n < K)%nat ->
  tcre K (tann K psi) n == inject_Z (Z.of_nat n) * psi n.
Proof.
  intros K psi n Hn. unfold tcre. rewrite trunc_in by lia. destruct n as [|m].
  - unfold gcre. simpl. ring.
  - unfold gcre. rewrite trunc_in by lia. unfold tann. rewrite trunc_in by lia.
    unfold gann. rewrite trunc_in by lia.
    setoid_replace (inject_Z (Z.of_nat (S m))) with (al (S m) * be (S m))
      by (symmetry; apply Hab).
    ring.
Qed.

(** Below the top level the commutator of the truncation is 1. *)
Theorem truncated_commutator_below_top : forall K psi n, (S n < K)%nat ->
  tann K (tcre K psi) n - tcre K (tann K psi) n == psi n.
Proof.
  intros K psi n Hn.
  assert (E1 : tann K (tcre K psi) n == inject_Z (Z.of_nat (S n)) * psi n).
  { unfold tann. rewrite trunc_in by lia. unfold gann.
    rewrite trunc_in by lia. unfold tcre. rewrite trunc_in by lia.
    unfold gcre. rewrite trunc_in by lia.
    setoid_replace (inject_Z (Z.of_nat (S n))) with (al (S n) * be (S n))
      by (symmetry; apply Hab).
    ring. }
  rewrite E1, (tcre_tann_eq K psi n) by lia.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite inject_Z_plus. change (inject_Z 1) with (1 # 1). ring.
Qed.

(** On the top level it is -(K - 1): the defect of the truncation. *)
Theorem truncated_commutator_top : forall k psi,
  tann (S k) (tcre (S k) psi) k - tcre (S k) (tann (S k) psi) k
  == - inject_Z (Z.of_nat k) * psi k.
Proof.
  intros k psi.
  assert (E1 : tann (S k) (tcre (S k) psi) k == 0).
  { unfold tann. rewrite trunc_in by lia. unfold gann.
    rewrite trunc_out by lia. ring. }
  rewrite E1, (tcre_tann_eq (S k) psi k) by lia. ring.
Qed.

End GenLadder.

(* ===================================================================== *)
(*  3. The rational realization: al(n) = n, be(n) = 1                   *)
(* ===================================================================== *)

Definition al1 : nat -> Q := fun n => inject_Z (Z.of_nat n).
Definition be1 : nat -> Q := fun _ => 1.

Lemma al1_be1 : forall n, al1 n * be1 n == inject_Z (Z.of_nat n).
Proof. intro n. unfold al1, be1. ring. Qed.

Theorem commutator_canonical_rational : forall psi n,
  gann al1 (gcre be1 psi) n - gcre be1 (gann al1 psi) n == psi n.
Proof. intros psi n. apply (gcommutator_canonical al1 be1 al1_be1). Qed.

Theorem number_operator_rational : forall psi n,
  gcre be1 (gann al1 psi) n == ProcessHarmonicLadder.num psi n.
Proof. intros psi n. apply (gcre_gann_eq_num al1 be1 al1_be1). Qed.

Theorem ham_rational_eigen : forall n m,
  gcre be1 (gann al1 (ProcessHarmonicLadder.ket n)) m + (1 # 2) * ProcessHarmonicLadder.ket n m
  == ProcessHarmonicLadder.energy n * ProcessHarmonicLadder.ket n m.
Proof. intros n m. apply (gham_ladder_eigen al1 be1 al1_be1). Qed.

(** The weights n! make a and a+ mutually adjoint in this realization
    (the number states are not normalised: <n|n> = n!). *)
Definition fq (n : nat) : Q := inject_Z (Z.of_nat (fact n)).

Lemma fq_succ : forall n, fq (S n) * be1 (S n) == fq n * al1 (S n).
Proof.
  intro n. unfold fq, be1, al1. rewrite Qmult_1_r. rewrite <- inject_Z_mult.
  replace (Z.of_nat (fact (S n))) with (Z.of_nat (fact n) * Z.of_nat (S n))%Z.
  - reflexivity.
  - rewrite <- Nat2Z.inj_mul. f_equal.
    change (fact (S n)) with (S n * fact n)%nat. apply Nat.mul_comm.
Qed.

Theorem ladder_adjoint_factorial : forall psi phi K,
  q_sum (fun n => fq n * gann al1 psi n * phi n) K
  == q_sum (fun n => fq n * psi n * gcre be1 phi n) (S K).
Proof. intros psi phi K. apply (ladder_adjoint_weighted al1 be1 fq fq_succ). Qed.

(** The truncated rational ladder: 1 below the top level, the defect on it. *)
Theorem truncated_rational_below_top : forall K psi n, (S n < K)%nat ->
  tann al1 K (tcre be1 K psi) n - tcre be1 K (tann al1 K psi) n == psi n.
Proof. intros K psi n Hn. apply (truncated_commutator_below_top al1 be1 al1_be1); exact Hn. Qed.

Theorem truncated_rational_top : forall k psi,
  tann al1 (S k) (tcre be1 (S k) psi) k - tcre be1 (S k) (tann al1 (S k) psi) k
  == - inject_Z (Z.of_nat k) * psi k.
Proof. intros k psi. apply (truncated_commutator_top al1 be1 al1_be1). Qed.

(* ===================================================================== *)
(*  4. One of the weights is unbounded                                  *)
(* ===================================================================== *)

(** In every ladder with al(n) * be(n) = n one of the two weights is
    unbounded. *)
Theorem ladder_weights_unbounded : forall al be : nat -> Q,
  (forall n, al n * be n == inject_Z (Z.of_nat n)) ->
  forall K : Q, exists n, K < al n * al n \/ K < be n * be n.
Proof.
  intros al be Hab K.
  assert (H01 : (0:Q) < 1) by lra.
  destruct (q_archimedean K 1 H01) as [n Hn]. rewrite Qmult_1_r in Hn.
  exists n.
  destruct (Qlt_le_dec K (al n * al n)) as [Ha | Ha]; [ left; exact Ha | ].
  destruct (Qlt_le_dec K (be n * be n)) as [Hb | Hb]; [ right; exact Hb | ].
  exfalso.
  assert (Ha0 : 0 <= al n * al n) by apply q_sq_nonneg.
  assert (Hb0 : 0 <= be n * be n) by apply q_sq_nonneg.
  assert (HK0 : 0 <= K) by lra.
  set (z := inject_Z (Z.of_nat n)) in *.
  assert (Hzz : z * z == (al n * al n) * (be n * be n)).
  { unfold z. rewrite <- (Hab n). ring. }
  assert (Hle : (al n * al n) * (be n * be n) <= K * K).
  { apply Qle_trans with (K * (be n * be n)).
    - apply Qmult_le_compat_r; assumption.
    - setoid_replace (K * (be n * be n)) with ((be n * be n) * K) by ring.
      apply Qmult_le_compat_r; assumption. }
  assert (Hlt : K * K < z * z).
  { apply Qle_lt_trans with (K * z).
    - setoid_replace (K * z) with (z * K) by ring.
      apply Qmult_le_compat_r; lra.
    - apply Qmult_lt_compat_r; lra. }
  rewrite Hzz in Hlt. lra.
Qed.

