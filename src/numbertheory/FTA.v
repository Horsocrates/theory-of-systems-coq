(* ========================================================================= *)
(*       FUNDAMENTAL THEOREM OF ARITHMETIC (EXISTENCE) VIA L5              *)
(*                                                                          *)
(*  THESIS: Every n ≥ 2 admits a prime factorization, constructed via       *)
(*  the L5/μ-operator applied to the divisor predicate.                    *)
(*                                                                          *)
(*  The smallest divisor of n (in [2, n]) is always prime — this is the    *)
(*  central observation. The L5 operator [smallest_divisor] (from           *)
(*  MuRecursion.v) provides this divisor constructively, without LEM       *)
(*  or AC. Recursive division by the smallest prime divisor yields the     *)
(*  complete factorization.                                                *)
(*                                                                          *)
(*  WHAT THIS FILE PROVES:                                                  *)
(*                                                                          *)
(*    [smallest_divisor_is_prime] — the L5-chosen divisor is prime.        *)
(*    [factorize_correct] — recursive factorization yields a list of      *)
(*                          primes whose product is n.                     *)
(*    [factorize_all_prime] — every factor in the list is prime.          *)
(*                                                                          *)
(*  WHAT IS DEFERRED:                                                       *)
(*                                                                          *)
(*    Uniqueness (Euclid's lemma): if p prime divides a*b, then p|a or    *)
(*    p|b. This needs gcd / Bezout / extended Euclidean — a separate file. *)
(*    The EXISTENCE part — which is what this file proves — already        *)
(*    demonstrates that prime factorization is L5-constructible.          *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  natural numbers ≥ 2.                                 *)
(*    Roles (L1):     divisor (decidable: n mod d = 0).                   *)
(*    Rules (L2):     divisibility predicate is decidable on bounded range.*)
(*    Order (L5):     smallest divisor in [2, n].                         *)
(*    Process (P4):   recursive division, bounded by Nat.log2 n.          *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From ToS Require Import cs.MuRecursion.
Import ListNotations.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: DIVISIBILITY UTILITIES                              *)
(* ========================================================================= *)

(** Divisibility: d divides n iff n mod d = 0 (assuming d > 0). *)
Definition divides (d n : nat) : Prop := exists k, n = d * k.

Lemma divides_mod_iff : forall d n, d > 0 -> (divides d n <-> n mod d = 0).
Proof.
  intros d n Hd. split.
  - intros [k Hk]. subst n. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
  - intros Hmod. exists (n / d). rewrite (Nat.div_mod n d) at 1 by lia.
    rewrite Hmod, Nat.add_0_r. lia.
Qed.

(** Boolean divisibility check. *)
Definition divides_b (d n : nat) : bool :=
  if Nat.eqb d 0 then Nat.eqb n 0 else Nat.eqb (n mod d) 0.

Lemma divides_b_iff : forall d n, d > 0 -> (divides_b d n = true <-> divides d n).
Proof.
  intros d n Hd. unfold divides_b.
  destruct (Nat.eqb_spec d 0); [lia|].
  rewrite Nat.eqb_eq.
  rewrite <- divides_mod_iff by lia. reflexivity.
Qed.

(** Self-divisibility: every n divides itself. *)
Lemma divides_refl : forall n, divides n n.
Proof. intros n. exists 1. lia. Qed.

(** 1 divides everything. *)
Lemma divides_1 : forall n, divides 1 n.
Proof. intros n. exists n. lia. Qed.

(* ========================================================================= *)
(*               PART II: PRIME DEFINITION                                  *)
(* ========================================================================= *)

(** A prime number is ≥ 2 with no proper divisor in [2, n). *)
Definition is_prime (n : nat) : Prop :=
  2 <= n /\ forall d, 2 <= d < n -> ~ divides d n.

(** Bool-valued primality: no divisor in [2, n-1]. *)
Definition is_prime_b (n : nat) : bool :=
  if 2 <=? n
  then match mu_le (fun d => andb (2 <=? d) (andb (Nat.ltb d n) (divides_b d n))) (n - 1) with
       | Some _ => false
       | None => true
       end
  else false.

(** Examples. *)
Example prime_2 : is_prime_b 2 = true. Proof. reflexivity. Qed.
Example prime_3 : is_prime_b 3 = true. Proof. reflexivity. Qed.
Example prime_5 : is_prime_b 5 = true. Proof. reflexivity. Qed.
Example prime_7 : is_prime_b 7 = true. Proof. reflexivity. Qed.
Example prime_11 : is_prime_b 11 = true. Proof. reflexivity. Qed.
Example not_prime_4 : is_prime_b 4 = false. Proof. reflexivity. Qed.
Example not_prime_9 : is_prime_b 9 = false. Proof. reflexivity. Qed.
Example not_prime_15 : is_prime_b 15 = false. Proof. reflexivity. Qed.

(* ========================================================================= *)
(*               PART III: SMALLEST DIVISOR IS PRIME                        *)
(* ========================================================================= *)

(** [smallest_divisor] (from MuRecursion.v) returns the smallest k ∈ [2, n]
    with k | n. We claim this k is prime: any proper divisor would be even
    smaller and would divide n too. *)

(** Divisibility is transitive: a | b ∧ b | c ⟹ a | c. *)
Lemma divides_trans : forall a b c,
  divides a b -> divides b c -> divides a c.
Proof.
  intros a b c [k1 Hk1] [k2 Hk2]. exists (k1 * k2). subst. lia.
Qed.

(** Helper: any divisor of a divisor is also a divisor. *)
Lemma divides_div_chain : forall d e n, 2 <= d -> divides e d -> divides d n -> divides e n.
Proof.
  intros d e n Hd He Hdn. apply (divides_trans e d n He Hdn).
Qed.

(** The L5/μ-smallest divisor of n ≥ 2 is prime. *)
Theorem smallest_divisor_is_prime : forall n d,
  2 <= n -> smallest_divisor n = Some d -> is_prime d.
Proof.
  intros n d Hn Hsd.
  unfold smallest_divisor in Hsd.
  apply mu_le_some_iff in Hsd. destruct Hsd as [Hd_le [Hd_div Hno_smaller]].
  unfold is_divisor in Hd_div.
  apply Bool.andb_true_iff in Hd_div. destruct Hd_div as [Hd2 Hdmod].
  apply Nat.leb_le in Hd2. apply Nat.eqb_eq in Hdmod.
  (* d >= 2, d <= n, d | n. We must show d is prime. *)
  (* Suppose 2 <= e < d. We show ¬(e | d). If e | d and d | n, then e | n.
     But e < d ≤ n and e ≥ 2. So e would be a smaller divisor in [2, n-1] —
     contradicting Hno_smaller. *)
  split; [exact Hd2|].
  intros e [He2 He_lt] He_div.
  pose proof (divides_div_chain d e n Hd2 He_div) as He_div_n.
  - assert (Hd_div_n : divides d n).
    { apply divides_mod_iff; [lia|exact Hdmod]. }
    specialize (He_div_n Hd_div_n).
    assert (He_le : e <= n).
    { destruct He_div_n as [k Hk]. subst n. lia. }
    pose proof (Hno_smaller e He_lt) as Hno_e.
    unfold is_divisor in Hno_e.
    assert (He2b : 2 <=? e = true) by (apply Nat.leb_le; lia).
    rewrite He2b in Hno_e. cbn in Hno_e.
    apply divides_mod_iff in He_div_n; [|lia].
    apply Nat.eqb_neq in Hno_e. congruence.
Qed.

(** Corollary: every n ≥ 2 has a prime divisor (namely, the smallest divisor). *)
Theorem prime_divisor_exists : forall n,
  2 <= n -> exists p, is_prime p /\ divides p n.
Proof.
  intros n Hn.
  pose proof (smallest_divisor_exists n Hn) as [d [Hsd [Hd_range Hd_div]]].
  exists d. split.
  - apply (smallest_divisor_is_prime n d Hn Hsd).
  - apply divides_mod_iff; [lia|exact Hd_div].
Qed.

(* ========================================================================= *)
(*               PART IV: RECURSIVE FACTORIZATION                           *)
(* ========================================================================= *)

(** Recursive factorization with explicit fuel parameter.
    For n ≥ 2, this returns the list of prime factors (with multiplicity).
    For n = 0 or 1, returns []. *)
Fixpoint factorize_fuel (n : nat) (fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S k =>
      if n <=? 1 then []
      else match smallest_divisor n with
           | Some d => d :: factorize_fuel (n / d) k
           | None => []
           end
  end.

(** factorize n: enough fuel for any factorization (n fuel suffices). *)
Definition factorize (n : nat) : list nat := factorize_fuel n n.

(** Examples. *)
Example factorize_2 : factorize 2 = [2]. Proof. reflexivity. Qed.
Example factorize_4 : factorize 4 = [2; 2]. Proof. reflexivity. Qed.
Example factorize_6 : factorize 6 = [2; 3]. Proof. reflexivity. Qed.
Example factorize_12 : factorize 12 = [2; 2; 3]. Proof. reflexivity. Qed.
Example factorize_15 : factorize 15 = [3; 5]. Proof. reflexivity. Qed.
Example factorize_30 : factorize 30 = [2; 3; 5]. Proof. reflexivity. Qed.

(** Product of a list of factors. *)
Definition list_prod (l : list nat) : nat := fold_right Nat.mul 1 l.

Example list_prod_empty : list_prod [] = 1. Proof. reflexivity. Qed.
Example list_prod_236 : list_prod [2; 3] = 6. Proof. reflexivity. Qed.

(* ========================================================================= *)
(*               PART V: FACTORIZATION CORRECTNESS                          *)
(* ========================================================================= *)

(** Helper: if d > 0 divides n, then n / d > 0 iff n > 0. *)
Lemma div_pos_iff : forall d n, d > 0 -> n mod d = 0 -> (n / d > 0 <-> n > 0).
Proof.
  intros d n Hd Hmod. split.
  - intros Hdiv. rewrite (Nat.div_mod n d) by lia. rewrite Hmod. lia.
  - intros Hn.
    rewrite (Nat.div_mod n d) in Hn at 1 by lia. rewrite Hmod, Nat.add_0_r in Hn.
    destruct (n / d); lia.
Qed.

(** Key: dividing n by d ≥ 2 strictly decreases n (when n ≥ 2 and d | n). *)
Lemma div_decreases : forall n d, 2 <= n -> 2 <= d -> n mod d = 0 -> n / d < n.
Proof.
  intros n d Hn Hd Hmod.
  assert (Hn_eq : n = d * (n / d)).
  { rewrite (Nat.div_mod n d) at 1 by lia. rewrite Hmod. lia. }
  destruct (n / d) as [|q] eqn:Hq.
  - cbn in Hn_eq. lia.
  - nia.
Qed.

(** factorize_fuel correctness: given enough fuel, returns prime factors
    whose product is n. *)
Lemma factorize_fuel_correct : forall fuel n,
  2 <= n -> n <= fuel ->
  list_prod (factorize_fuel n fuel) = n /\
  (forall p, In p (factorize_fuel n fuel) -> is_prime p).
Proof.
  induction fuel as [|k IH]; intros n Hn Hfuel.
  - lia.
  - cbn [factorize_fuel].
    destruct (Nat.leb_spec n 1); [lia|].
    destruct (smallest_divisor n) as [d|] eqn:Hsd.
    + (* d is the smallest divisor. *)
      pose proof (smallest_divisor_exists n Hn) as [d' [Hsd' [Hd_range Hd_div]]].
      rewrite Hsd in Hsd'. inversion Hsd'. subst d'.
      pose proof (smallest_divisor_is_prime n d Hn Hsd) as Hd_prime.
      destruct Hd_prime as [Hd2 _].
      assert (Hd_div' : divides d n) by (apply divides_mod_iff; [lia|exact Hd_div]).
      destruct Hd_div' as [k' Hk'].
      assert (Hk_eq : n / d = k').
      { rewrite Hk'. rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
      assert (Hk_pos : k' > 0).
      { rewrite Hk' in Hn. destruct k'; lia. }
      (* Apply IH to n/d *)
      destruct (Nat.le_gt_cases 2 k') as [Hk2|Hk1].
      * (* k' >= 2: recursive case *)
        assert (Hk_le : k' <= k).
        { rewrite <- Hk_eq. pose proof (div_decreases n d Hn Hd2 Hd_div). lia. }
        rewrite Hk_eq in *.
        specialize (IH k' Hk2 Hk_le) as [Hprod Hall].
        split.
        -- change (list_prod (d :: factorize_fuel k' k))
              with (d * list_prod (factorize_fuel k' k)).
           rewrite Hprod, Hk'. lia.
        -- intros p [Hp|Hp].
           ++ subst p. apply (smallest_divisor_is_prime n d Hn Hsd).
           ++ apply Hall. exact Hp.
      * (* k' = 1: base case (n = d, prime). *)
        assert (Hk1' : k' = 1) by lia.
        assert (Hnd_eq : n / d = 1) by (rewrite Hk_eq; exact Hk1').
        rewrite Hnd_eq.
        assert (Hfuel_done : factorize_fuel 1 k = []).
        { destruct k; cbn; try reflexivity. }
        rewrite Hfuel_done.
        split.
        -- change (list_prod (d :: [])) with (d * 1).
           rewrite Hk', Hk1'. lia.
        -- intros p [Hp|[]]. subst p. apply (smallest_divisor_is_prime n d Hn Hsd).
    + (* smallest_divisor returns None — impossible for n >= 2 *)
      exfalso.
      pose proof (smallest_divisor_exists n Hn) as [d' [Hsd' _]].
      congruence.
Qed.

(** Main FTA-existence theorem: for n ≥ 2, factorize gives a list of primes
    whose product is n. *)
Theorem factorize_correct : forall n,
  2 <= n -> list_prod (factorize n) = n.
Proof.
  intros n Hn. unfold factorize.
  apply (factorize_fuel_correct n n Hn (Nat.le_refl n)).
Qed.

Theorem factorize_all_prime : forall n p,
  2 <= n -> In p (factorize n) -> is_prime p.
Proof.
  intros n p Hn Hin. unfold factorize in Hin.
  apply (factorize_fuel_correct n n Hn (Nat.le_refl n)). exact Hin.
Qed.

(** Combined: existence of prime factorization (the substantial half of FTA). *)
Theorem fta_existence : forall n,
  2 <= n ->
  exists primes : list nat,
    (forall p, In p primes -> is_prime p) /\
    list_prod primes = n.
Proof.
  intros n Hn. exists (factorize n). split.
  - intros p Hp. apply (factorize_all_prime n p Hn Hp).
  - apply factorize_correct. exact Hn.
Qed.

(* ========================================================================= *)
(*               PART VI: NUMERICAL VERIFICATION                            *)
(* ========================================================================= *)

Example fta_60 : exists primes,
  (forall p, In p primes -> is_prime p) /\
  list_prod primes = 60.
Proof. apply fta_existence. lia. Qed.

Example fta_100 : exists primes,
  (forall p, In p primes -> is_prime p) /\
  list_prod primes = 100.
Proof. apply fta_existence. lia. Qed.

Example factorize_60 : factorize 60 = [2; 2; 3; 5].
Proof. reflexivity. Qed.

Example factorize_100 : factorize 100 = [2; 2; 5; 5].
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*               PART VII: ERR + COMMENTARY                                 *)
(* ========================================================================= *)

(**
  THE L5/μ STRUCTURE OF FTA-EXISTENCE:

  The classical statement of FTA: every integer n ≥ 2 has a unique prime
  factorization n = p₁ * p₂ * ... * p_k.

  Classical proofs split into EXISTENCE and UNIQUENESS. The existence proof
  is by strong induction on n: find any non-trivial divisor, recurse.

  OUR L5/μ-CANONICAL VERSION:

  Existence proof:
    1. By [smallest_divisor] (L5/μ over divisor predicate): for n ≥ 2,
       there is a SMALLEST divisor d in [2, n]. This is canonical, not
       just an arbitrary choice. (Classical proof needs LEM or choice
       for "pick a divisor".)

    2. The smallest divisor IS PRIME ([smallest_divisor_is_prime]):
       any smaller divisor of d would also divide n (transitivity),
       contradicting the smallness of d.

    3. Recurse on n / d. By [div_decreases], n / d < n, so the recursion
       terminates with fuel ≤ n.

    4. Concatenate: factorize n = d :: factorize (n / d).

  The whole proof is CONSTRUCTIVE — no LEM, no AC. The smallest divisor
  L5/μ is the canonical "choice" of the next prime factor.

  UNIQUENESS (DEFERRED):

  Uniqueness needs Euclid's lemma: if p prime divides a * b, then p | a
  or p | b. The classical proof uses Bezout's identity and gcd. In our
  framework, gcd is computable via L5 (smallest positive linear combination
  of a and b), and Bezout follows constructively.

  Once Euclid's lemma is in hand, uniqueness is a straightforward induction
  on factorization length: the smallest prime factor of n is uniquely
  determined; recurse on n / (that smallest prime).

  Both gcd-via-L5 and Euclid's lemma are tractable in a separate file
  ("Bezout.v" or "EuclidsLemma.v" in the numbertheory branch). The
  EXISTENCE we've proven here is the substantive half; uniqueness is
  the routine algebraic finish.

  WHY EXISTENCE IS THE INTERESTING HALF:

  Existence demonstrates the L5/μ structure: a "choice" of prime factor
  at each step is made canonically by smallest_divisor. The factorization
  is THUS UNIQUELY DETERMINED as a process — even before proving classical
  uniqueness, the algorithm gives the SAME answer every time.

  In a sense, our framework proves a STRONGER existence: not just
  "some factorization exists", but "the L5-canonical factorization is
  given by factorize". Classical uniqueness is then the observation that
  ANY factorization equals the L5-canonical one.

  CONNECTION TO THE PROJECT THESIS:

  This file is a direct illustration of P4 + L5 = arithmetic without ZFC:

    - P4: factorize uses fuel — a P4-process-bounded recursion. No actual
      infinity. The number of steps to factor n is bounded by Nat.log₂ n.

    - L5: smallest_divisor at each step makes a CANONICAL choice — no
      Axiom of Choice needed because the choice is uniquely determined
      by smallness.

  The entire foundational arithmetic theory (FTA-existence, gcd, Bezout,
  Euler's theorem, Fermat's little, CRT) is similarly L5-buildable. This
  pillar — number theory without ZFC — is now opened.

  WHAT THIS OPENS NEXT:

  - [Bezout.v] / [EuclidsLemma.v]: gcd via L5, Bezout, Euclid's lemma,
    FTA-uniqueness.
  - [Fermat.v]: Fermat's little theorem (smallest order of a mod p).
  - [Euler.v]: Euler's totient and theorem.
  - [CRT.v]: Chinese remainder theorem (smallest common residue).
  - [Quadratic.v]: quadratic reciprocity via L5 over Legendre symbols.

  Each is a natural extension of L5/μ-recursion to the corresponding
  number-theoretic predicate.
*)
