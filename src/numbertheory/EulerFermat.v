(** * EulerFermat.v — Fermat's Little Theorem (general prime) as ToS System

    Theory of Systems — Number Theory layer (Part XIII, round 2+)

    Elements: natural numbers; the reduced residue list [1, .., p-1]
    Roles:    multiplication by a -> a PERMUTATION of the residues mod p
    Rules:    a^(p-1) ≡ 1 (mod p) for prime p and p ∤ a
    Status:   the multiplicative group of residues mod p has order p-1

    Fermat's little theorem for a GENERAL prime p (the repo previously had only
    the concrete cases F5, F7 in algebra/FiniteFieldFp.v).  Classical proof by
    the product of residues: x |-> (a*x) mod p permutes [1,..,p-1], so
    a^(p-1) * (p-1)! ≡ (p-1)! (mod p); cancelling the unit (p-1)! gives the
    result.  Built on PrimeFactorization.euclid_lemma and the stdlib tool
    Permutation_map_same_l (a self-injective list map is a permutation).

    RELATED: algebra/FiniteFieldFp.v (concrete F5/F7 Fermat),
    numbertheory/PrimeFactorization.v (euclid_lemma), stdlib/Primes.v.

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import ArithRing.
From Stdlib Require Import Permutation.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import numbertheory.PrimeFactorization.

(* ================================================================= *)
(*  List helper: NoDup of a map under injectivity on the list         *)
(* ================================================================= *)

Lemma NoDup_map_local : forall (f : nat -> nat) (l : list nat),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  induction l as [|a l IH]; simpl; intros Hinj Hnd.
  - constructor.
  - inversion Hnd as [|aa ll Hnotin Hndl]; subst.
    constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [b [Hfb Hinb]].
      assert (Hab : a = b)
        by (apply (Hinj a b); [left; reflexivity | right; exact Hinb | symmetry; exact Hfb]).
      subst b. apply Hnotin. exact Hinb.
    + apply IH; [intros x y Hx Hy; apply Hinj; right; assumption | exact Hndl].
Qed.

(* ================================================================= *)
(*  Natural-number product of a list and its permutation invariance   *)
(* ================================================================= *)

Definition Nprod (l : list nat) : nat := fold_right Nat.mul 1 l.

Lemma Nprod_perm : forall l l', Permutation l l' -> Nprod l = Nprod l'.
Proof.
  intros l l' H.
  induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - ring.
  - rewrite IH1. exact IH2.
Qed.

Lemma Nprod_map_mult : forall a l, Nprod (map (Nat.mul a) l) = a ^ (length l) * Nprod l.
Proof.
  induction l as [|x l IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** product of element-wise congruent (mod n) lists are congruent mod n *)
Lemma Nprod_map_cong : forall (g h : nat -> nat) l n, n <> 0 ->
  (forall x, In x l -> g x mod n = h x mod n) ->
  (Nprod (map g l)) mod n = (Nprod (map h l)) mod n.
Proof.
  intros g h l n Hn. induction l as [|x l IH]; simpl; intros Hcong.
  - reflexivity.
  - rewrite (Nat.Div0.mul_mod (g x)). rewrite (Nat.Div0.mul_mod (h x)).
    rewrite (Hcong x (or_introl eq_refl)).
    rewrite IH; [reflexivity | intros y Hy; apply Hcong; right; exact Hy].
Qed.

(* ================================================================= *)
(*  Modular congruence and divisibility of differences                *)
(* ================================================================= *)

Lemma mod_eq_divides_sub : forall x y n, x <= y -> x mod n = y mod n -> divides n (y - x).
Proof.
  intros x y n Hxy Hmod.
  exists (y / n - x / n).
  pose proof (Nat.div_mod_eq x n) as Hx.
  pose proof (Nat.div_mod_eq y n) as Hy.
  pose proof (Nat.Div0.div_le_mono x y n Hxy) as Hmono.
  nia.
Qed.

Lemma divides_sub_mod_eq : forall x y n, x <= y -> divides n (y - x) -> x mod n = y mod n.
Proof.
  intros x y n Hxy [k Hk].
  assert (Hy : y = x + n * k) by lia.
  subst y. rewrite (Nat.mul_comm n k). rewrite Nat.Div0.mod_add. reflexivity.
Qed.

(** cancellation: if p is prime and p ∤ a, multiplication by a is injective mod p *)
Lemma mod_mul_cancel_l : forall p a x y, is_prime p -> ~ divides p a ->
  (a * x) mod p = (a * y) mod p -> x mod p = y mod p.
Proof.
  intros p a x y Hp Hpa Heq.
  destruct (Nat.le_ge_cases x y) as [Hxy | Hyx].
  - apply (divides_sub_mod_eq x y p Hxy).
    assert (Hd : divides p (a * y - a * x)).
    { apply (mod_eq_divides_sub (a * x) (a * y) p);
        [apply Nat.mul_le_mono_l; exact Hxy | exact Heq]. }
    assert (Hrw : a * y - a * x = a * (y - x)) by (rewrite Nat.mul_sub_distr_l; reflexivity).
    rewrite Hrw in Hd.
    destruct (euclid_lemma p a (y - x) Hp Hd) as [Hbad | Hok].
    + exfalso. apply Hpa. exact Hbad.
    + exact Hok.
  - symmetry. apply (divides_sub_mod_eq y x p Hyx).
    assert (Hd : divides p (a * x - a * y)).
    { apply (mod_eq_divides_sub (a * y) (a * x) p);
        [apply Nat.mul_le_mono_l; exact Hyx | symmetry; exact Heq]. }
    assert (Hrw : a * x - a * y = a * (x - y)) by (rewrite Nat.mul_sub_distr_l; reflexivity).
    rewrite Hrw in Hd.
    destruct (euclid_lemma p a (x - y) Hp Hd) as [Hbad | Hok].
    + exfalso. apply Hpa. exact Hbad.
    + exact Hok.
Qed.

(* ================================================================= *)
(*  (p-1)! is a unit mod p                                            *)
(* ================================================================= *)

(** a prime dividing a product divides one of the factors *)
Lemma prime_divides_Nprod : forall p l, is_prime p ->
  divides p (Nprod l) -> Exists (divides p) l.
Proof.
  intros p l Hp. induction l as [|x l IH]; simpl; intros Hdiv.
  - exfalso.
    assert (Hle : p <= 1) by (apply (divides_le p 1); [lia | exact Hdiv]).
    destruct Hp as [Hp2 _]. lia.
  - destruct (euclid_lemma p x (Nprod l) Hp Hdiv) as [Hx | Hr].
    + apply Exists_cons_hd. exact Hx.
    + apply Exists_cons_tl. apply IH. exact Hr.
Qed.

(** p does not divide (p-1)! : every factor lies in [1, p-1] < p *)
Lemma not_p_divides_fact : forall p, is_prime p ->
  ~ divides p (Nprod (seq 1 (p - 1))).
Proof.
  intros p Hp Hdiv.
  apply prime_divides_Nprod in Hdiv; [| exact Hp].
  apply Exists_exists in Hdiv. destruct Hdiv as [x [Hin Hpx]].
  apply in_seq in Hin.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (p <= x) by (apply (divides_le p x); [lia | exact Hpx]).
  lia.
Qed.

(* ================================================================= *)
(*  Residue map and the main theorem                                  *)
(* ================================================================= *)

Definition res (a p x : nat) : nat := (a * x) mod p.

(** FERMAT'S LITTLE THEOREM (general prime p):  a^(p-1) mod p = 1  when p ∤ a *)
Theorem fermat_little : forall p a, is_prime p -> ~ divides p a ->
  (a ^ (p - 1)) mod p = 1.
Proof.
  intros p a Hp Hpa.
  assert (Hp0 : p <> 0) by (destruct Hp; lia).
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Ha1 : 1 <= a).
  { destruct a as [|a']; [exfalso; apply Hpa; exists 0; lia | lia]. }
  (* x |-> (a*x) mod p permutes the residues [1, p-1] *)
  assert (Hperm : Permutation (map (res a p) (seq 1 (p - 1))) (seq 1 (p - 1))).
  { apply Permutation_map_same_l.
    - apply NoDup_map_local.
      + intros x y Hx Hy Hxy.
        assert (Hxy' : (a * x) mod p = (a * y) mod p) by exact Hxy.
        apply (mod_mul_cancel_l p a x y Hp Hpa) in Hxy'.
        apply in_seq in Hx. apply in_seq in Hy.
        rewrite (Nat.mod_small x p) in Hxy'; [| lia].
        rewrite (Nat.mod_small y p) in Hxy'; [| lia].
        exact Hxy'.
      + apply seq_NoDup.
    - intros z Hz. apply in_map_iff in Hz. destruct Hz as [x [Hfx Hx]].
      apply in_seq in Hx. apply in_seq. unfold res in Hfx. subst z.
      split.
      + assert (Hne : (a * x) mod p <> 0).
        { intro Hz0.
          assert (Hdax : divides p (a * x)).
          { apply (proj1 (divides_bool_correct p (a * x) Hp0)).
            unfold divides_bool. rewrite Hz0. reflexivity. }
          destruct (euclid_lemma p a x Hp Hdax) as [Hbad | Hpx].
          - apply Hpa; exact Hbad.
          - assert (p <= x) by (apply (divides_le p x); [lia | exact Hpx]). lia. }
        lia.
      + assert ((a * x) mod p < p) by (apply Nat.mod_upper_bound; exact Hp0). lia. }
  (* products: (p-1)! = prod of permuted residues *)
  pose proof (Nprod_perm _ _ Hperm) as Hprodeq.
  (* prod of (a*x) mod p ≡ prod of (a*x) (mod p) *)
  assert (Hcong : (Nprod (map (res a p) (seq 1 (p - 1)))) mod p
                = (Nprod (map (Nat.mul a) (seq 1 (p - 1)))) mod p).
  { apply Nprod_map_cong; [exact Hp0 |].
    intros x _. unfold res. rewrite Nat.Div0.mod_mod. reflexivity. }
  pose proof (Nprod_map_mult a (seq 1 (p - 1))) as Hmult.
  assert (HlenR : length (seq 1 (p - 1)) = p - 1) by apply length_seq.
  rewrite HlenR in Hmult.
  (* key congruence: (p-1)! ≡ a^(p-1) * (p-1)! (mod p) *)
  assert (Hkey : (Nprod (seq 1 (p - 1))) mod p
               = (a ^ (p - 1) * Nprod (seq 1 (p - 1))) mod p).
  { rewrite <- Hmult. rewrite <- Hcong. rewrite Hprodeq. reflexivity. }
  (* (p-1)! is a unit *)
  assert (Hcop : ~ divides p (Nprod (seq 1 (p - 1)))) by (apply not_p_divides_fact; exact Hp).
  (* X := a^(p-1) >= 1 *)
  assert (HX1 : 1 <= a ^ (p - 1)).
  { pose proof (Nat.pow_le_mono_l 1 a (p - 1) Ha1) as Hpow.
    rewrite Nat.pow_1_l in Hpow. exact Hpow. }
  (* p | (p-1)! * (X - 1) *)
  assert (Hdsub : divides p (a ^ (p - 1) * Nprod (seq 1 (p - 1)) - Nprod (seq 1 (p - 1)))).
  { apply (mod_eq_divides_sub (Nprod (seq 1 (p - 1))) (a ^ (p - 1) * Nprod (seq 1 (p - 1))) p).
    - rewrite <- (Nat.mul_1_l (Nprod (seq 1 (p - 1)))) at 1.
      apply Nat.mul_le_mono_r. exact HX1.
    - exact Hkey. }
  assert (Hrw : a ^ (p - 1) * Nprod (seq 1 (p - 1)) - Nprod (seq 1 (p - 1))
              = Nprod (seq 1 (p - 1)) * (a ^ (p - 1) - 1)) by nia.
  rewrite Hrw in Hdsub.
  destruct (euclid_lemma p (Nprod (seq 1 (p - 1))) (a ^ (p - 1) - 1) Hp Hdsub) as [Hbad | Hgood].
  - exfalso. apply Hcop. exact Hbad.
  - destruct Hgood as [k Hk].
    assert (HXval : a ^ (p - 1) = 1 + k * p) by nia.
    rewrite HXval. rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia.
Qed.

(* ================================================================= *)
(*  Corollaries and concrete checks                                   *)
(* ================================================================= *)

(** the a^p ≡ a form: a^p mod p = a mod p (Fermat, multiplicative restatement) *)
Corollary fermat_pow_p : forall p a, is_prime p -> ~ divides p a ->
  (a ^ (p - 1) * a) mod p = a mod p.
Proof.
  intros p a Hp Hpa.
  assert (Hp0 : p <> 0) by (destruct Hp; lia).
  rewrite (Nat.Div0.mul_mod (a ^ (p - 1)) a).
  rewrite (fermat_little p a Hp Hpa).
  rewrite Nat.mul_1_l. rewrite Nat.Div0.mod_mod. reflexivity.
Qed.

(** 12. concrete: 3^6 mod 7 = 1 *)
Example fermat_3_7 : (3 ^ (7 - 1)) mod 7 = 1.
Proof. vm_compute. reflexivity. Qed.

(** 13. concrete: 2^10 mod 11 = 1 *)
Example fermat_2_11 : (2 ^ (11 - 1)) mod 11 = 1.
Proof. vm_compute. reflexivity. Qed.

(** 14. concrete: 5^12 mod 13 = 1 *)
Example fermat_5_13 : (5 ^ (13 - 1)) mod 13 = 1.
Proof. vm_compute. reflexivity. Qed.
