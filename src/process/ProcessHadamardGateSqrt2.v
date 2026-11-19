(** * ProcessHadamardGateSqrt2.v -- The Hadamard gate over Q[sqrt 2], as a ToS System

    Elements: rational amplitudes; amplitudes in Q[sqrt 2] -- pairs (a, b) of
              rationals read as a + b sqrt 2 ([CliffordField.RQ]); the +-1
              entries of the Hadamard matrix of size 2.
    Roles:    [hgate s]  -- the gate with a RATIONAL factor s
                            (ProcessHadamardGate.v);
              [hgateR]   -- the gate with the factor 1 / sqrt 2 = (0, 1/2),
                            an element of Q[sqrt 2];
              [e0R]      -- the basis state |0>.
    Rules:    over Q the square of the gate with a factor s is the
              multiplication by 2 s^2, and 2 s^2 = 1 has no rational
              solution; over Q[sqrt 2] the relation s^2 * 2 = 1 holds and the
              gate is an involution and an isometry. The observable
              quantity -- the squared amplitude 1/2 -- is rational.

    Proved (no axioms):
      - [hgate_premise_unsat]: no rational s satisfies s * s * 2 == 1 (the
        premise of section Gate in ProcessHadamardGate.v);
      - [hgate_sq_scale], [hgate_involution_iff],
        [hgate_never_involution_over_Q]: with a rational factor the gate is
        never an involution;
      - the rational form of invertibility: [walsh_inverse] (every N = 2^k),
        [half_HH_is_identity];
      - over Q[sqrt 2]: [s2_relation_holds], [s2_sq_half], [hgateR_rows]
        (the gate is the matrix [CliffordField.mH]), [hgateR_involution],
        [hgateR_superposition], [hgateR_isometry], [hgateR_on_rationals].

    P4 diagnostic: sqrt 2 enters as an element of the extended carrier
      Q[sqrt 2]: a pair of rationals with exact arithmetic. No limit and no
      approximation process is used; over Q itself the normalising factor
      does not exist, and this is a theorem.

    NOT claimed:
      - a rational normalised gate;
      - gates on more than one qubit, or the normalisation 1 / sqrt N for
        other odd k;
      - complex amplitudes (the carrier is Q[sqrt 2], not Q[sqrt 2, i]).

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool Arith.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessSelfAdjointSpectral.
From ToS Require Import process.ProcessWalshHadamard.
From ToS Require Import process.ProcessFourierON.
From ToS Require Import process.ProcessHadamardGate.
From ToS Require Import process.ProcessOrthogonalWalsh.
From ToS Require analysis.Sqrt2Irrational.
From ToS Require stdlib.CliffordField.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Over Q the normalised gate does not exist                        *)
(* ===================================================================== *)

(** The premise of section Gate in ProcessHadamardGate.v -- a rational s
    with s * s * 2 == 1 -- has no instance: (2 s)^2 = 2. *)
Lemma hgate_premise_unsat : forall s : Q, ~ (s * s * 2 == 1).
Proof.
  intros s H. apply (Sqrt2Irrational.no_rational_sqrt2 (2 * s)).
  assert (E : 2 * s * (2 * s) == 2 * (s * s * 2)) by ring.
  rewrite E, H. reflexivity.
Qed.

(** For EVERY rational s the gate applied twice is the multiplication by
    2 s^2. *)
Lemma hgate_sq_scale : forall (s : Q) (f : nat -> Q) (m : nat), (m < pow2 1)%nat ->
  hgate s (hgate s f) m == (s * s * 2) * f m.
Proof.
  intros s f m Hm. unfold hgate. cbn beta.
  rewrite op_apply_scale. rewrite (walsh_HH 1 f m Hm).
  assert (Hp : inject_Z (Z.of_nat (pow2 1)) == 2) by (vm_compute; reflexivity).
  rewrite Hp. ring.
Qed.

(** The gate with a rational factor is an involution exactly when
    s * s * 2 == 1 ... *)
Lemma hgate_involution_iff : forall s : Q,
  (forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat -> hgate s (hgate s f) m == f m)
  <-> s * s * 2 == 1.
Proof.
  intro s. split.
  - intro H.
    assert (H0lt : (0 < pow2 1)%nat) by (cbn; lia).
    pose proof (H e0 0%nat H0lt) as H0.
    rewrite (hgate_sq_scale s e0 0%nat H0lt) in H0.
    assert (He : e0 0%nat == 1) by reflexivity.
    rewrite He in H0. rewrite Qmult_1_r in H0. exact H0.
  - intros Hs f m Hm. exact (hgate_involution s Hs f m Hm).
Qed.

(** ... that is, for no rational factor. *)
Theorem hgate_never_involution_over_Q : forall s : Q,
  ~ (forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat -> hgate s (hgate s f) m == f m).
Proof.
  intros s H. apply (hgate_premise_unsat s). apply (proj1 (hgate_involution_iff s)). exact H.
Qed.

(* ===================================================================== *)
(*  2. The rational form of invertibility                               *)
(* ===================================================================== *)

(** H^{-1} = (1/N) H for every N = 2^k. *)
Theorem walsh_inverse : forall k (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  op_apply (had k)
           (fun j => / inject_Z (Z.of_nat (pow2 k)) * op_apply (had k) f (pow2 k) j)
           (pow2 k) m
  == f m.
Proof.
  intros k f m Hm. rewrite op_apply_scale. rewrite (walsh_HH k f m Hm).
  field. apply pow2_Q_neq0.
Qed.

(** N = 2: the squared normalisation 1/2 is rational. *)
Corollary half_HH_is_identity : forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat ->
  (1 # 2) * op_apply (had 1) (op_apply (had 1) f (pow2 1)) (pow2 1) m == f m.
Proof.
  intros f m Hm. rewrite (walsh_HH 1 f m Hm).
  assert (Hp : inject_Z (Z.of_nat (pow2 1)) == 2) by (vm_compute; reflexivity).
  rewrite Hp. field.
Qed.

(* ===================================================================== *)
(*  3. The gate over Q[sqrt 2]                                          *)
(* ===================================================================== *)

(** Amplitudes are pairs (a, b) = a + b sqrt 2 (stdlib/CliffordField.v). *)
Definition rscale (q : Q) (z : CliffordField.RQ) : CliffordField.RQ :=
  (q * fst z, q * snd z).

Definition rsum (g : nat -> CliffordField.RQ) (n : nat) : CliffordField.RQ :=
  (q_sum (fun j => fst (g j)) n, q_sum (fun j => snd (g j)) n).

(** (hgateR f)_m = (1 / sqrt 2) * Sum_{j<2} H_{mj} f_j. *)
Definition hgateR (f : nat -> CliffordField.RQ) : nat -> CliffordField.RQ :=
  fun m => CliffordField.rmul CliffordField.s2
             (rsum (fun j => rscale (had 1 m j) (f j)) (pow2 1)).

(** In Q[sqrt 2] the relation s^2 * 2 = 1 HOLDS for s = (0, 1/2). *)
Lemma s2_relation_holds :
  CliffordField.req
    (CliffordField.rmul (CliffordField.rmul CliffordField.s2 CliffordField.s2) (2, 0))
    CliffordField.r1.
Proof. unfold CliffordField.req. split; vm_compute; reflexivity. Qed.

(** The squared amplitude is the rational number 1/2. *)
Lemma s2_sq_half :
  CliffordField.req (CliffordField.rmul CliffordField.s2 CliffordField.s2) (1 # 2, 0).
Proof. unfold CliffordField.req. split; vm_compute; reflexivity. Qed.

Lemma had1_entries :
  had 1 0 0 == 1 /\ had 1 0 1 == 1 /\ had 1 1 0 == 1 /\ had 1 1 1 == - (1).
Proof. exact hadamard_2x2. Qed.

(** The gate is the matrix mH of stdlib/CliffordField.v: rows (s, s) and
    (s, -s). *)
Lemma hgateR_rows : forall f : nat -> CliffordField.RQ,
  CliffordField.req (hgateR f 0%nat)
    (CliffordField.radd (CliffordField.rmul CliffordField.s2 (f 0%nat))
                        (CliffordField.rmul CliffordField.s2 (f 1%nat)))
  /\ CliffordField.req (hgateR f 1%nat)
    (CliffordField.radd (CliffordField.rmul CliffordField.s2 (f 0%nat))
                        (CliffordField.rmul CliffordField.ns2 (f 1%nat))).
Proof.
  intro f. destruct hadamard_2x2 as [H00 [H01 [H10 H11]]].
  unfold hgateR, rsum, rscale, CliffordField.req, CliffordField.radd, CliffordField.rmul,
         CliffordField.s2, CliffordField.ns2.
  change (pow2 1) with 2%nat. cbn [q_sum fst snd].
  repeat split; rewrite ?H00, ?H01, ?H10, ?H11; ring.
Qed.

(** The gate is an involution: no premise. *)
Theorem hgateR_involution : forall (f : nat -> CliffordField.RQ) (m : nat),
  (m < pow2 1)%nat -> CliffordField.req (hgateR (hgateR f) m) (f m).
Proof.
  intros f m Hm.
  destruct hadamard_2x2 as [H00 [H01 [H10 H11]]].
  assert (Hm2 : (m < 2)%nat) by exact Hm.
  destruct m as [|[|m]]; [ | | lia ];
    unfold hgateR, rsum, rscale, CliffordField.req, CliffordField.rmul, CliffordField.s2;
    change (pow2 1) with 2%nat; cbn [q_sum fst snd];
    (split; rewrite ?H00, ?H01, ?H10, ?H11; ring).
Qed.

(** The basis state |0>. *)
Definition e0R (j : nat) : CliffordField.RQ :=
  if Nat.eqb j 0%nat then CliffordField.r1 else CliffordField.r0.

(** |0> goes to (1 / sqrt 2, 1 / sqrt 2). *)
Theorem hgateR_superposition :
  CliffordField.req (hgateR e0R 0%nat) CliffordField.s2
  /\ CliffordField.req (hgateR e0R 1%nat) CliffordField.s2.
Proof.
  destruct had1_entries as [H00 [H01 [H10 H11]]].
  unfold hgateR, rsum, rscale, e0R, CliffordField.req, CliffordField.rmul,
         CliffordField.s2, CliffordField.r1, CliffordField.r0.
  change (pow2 1) with 2%nat. cbn [q_sum fst snd Nat.eqb].
  repeat split; rewrite ?H00, ?H01, ?H10, ?H11; ring.
Qed.

(** The gate preserves the sum of the squared amplitudes. *)
Theorem hgateR_isometry : forall f : nat -> CliffordField.RQ,
  CliffordField.req
    (CliffordField.radd (CliffordField.rmul (hgateR f 0%nat) (hgateR f 0%nat))
                        (CliffordField.rmul (hgateR f 1%nat) (hgateR f 1%nat)))
    (CliffordField.radd (CliffordField.rmul (f 0%nat) (f 0%nat))
                        (CliffordField.rmul (f 1%nat) (f 1%nat))).
Proof.
  intro f. destruct hadamard_2x2 as [H00 [H01 [H10 H11]]].
  unfold hgateR, rsum, rscale, CliffordField.req, CliffordField.radd, CliffordField.rmul,
         CliffordField.s2.
  change (pow2 1) with 2%nat. cbn [q_sum fst snd].
  split; rewrite ?H00, ?H01, ?H10, ?H11; ring.
Qed.

(** On rational amplitudes the gate is (1 / sqrt 2) * (H f): the pair
    (0, (H f)_m / 2). *)
Lemma hgateR_on_rationals : forall (f : nat -> Q) (m : nat),
  CliffordField.req (hgateR (fun j => (f j, 0)) m)
                    (0, (1 # 2) * op_apply (had 1) f (pow2 1) m).
Proof.
  intros f m.
  unfold hgateR, rsum, rscale, CliffordField.req, CliffordField.rmul, CliffordField.s2, op_apply.
  change (pow2 1) with 2%nat. cbn [q_sum fst snd].
  split; ring.
Qed.

