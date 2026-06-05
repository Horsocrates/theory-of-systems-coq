(** * MobiusDirichlet.v — Dirichlet Convolution and Mobius Inversion as ToS System

    Theory of Systems — Number Theory layer (Part XIII, round 2)

    Elements: arithmetic functions nat -> Z; finite divisor lists
    Roles:    Dirichlet convolution -> the operational composition of
              arithmetic functions; mu -> the inverse of the constant 1
    Rules:    (f * g)(n) = sum_{d|n} f(d) g(n/d); divisors pair via d <-> n/d
    Status:   convolution is commutative (structural pairing); the classical
              Mobius identities hold

    The "operational" algebra of arithmetic functions (Chapter 13.6, motive M2):
    Dirichlet convolution, the divisor-pairing involution d <-> n/d (a GENERAL
    theorem, the structural heart), and the resulting commutativity of
    convolution.  The Mobius function mu (squarefree definition via the explicit
    factorization) and the three classical identities -- sum_{d|n} mu(d)=[n=1],
    Gauss sum_{d|n} phi(d)=n, and Mobius inversion phi(n)=sum_{d|n} mu(d)(n/d)
    -- are machine-checked over a range (Element-side), in the style of N3/N5.

    RELATED: numbertheory/ArithmeticFunctions.v (divisors, phi, divisors_spec),
    numbertheory/PrimeFactorization.v (factorization), zeta/MobiusSpin.v
    (mobius VALUES; the convolution algebra and pairing are not there).

    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import ArithRing.
From Stdlib Require Import ZArith.
From Stdlib Require Import Permutation.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import numbertheory.ArithmeticFunctions.

(* nat is the default scope; Z operations are written explicitly (Z.add/Z.mul) *)
Open Scope nat_scope.

(* ================================================================= *)
(*  Helper: a Z-sum is invariant under permutation of its list        *)
(* ================================================================= *)

(** 1. permutation-invariance of fold_right Z.add *)
Lemma Zsum_perm : forall l l', Permutation l l' ->
  fold_right Z.add 0%Z l = fold_right Z.add 0%Z l'.
Proof.
  intros l l' H. induction H; simpl in *; lia.
Qed.

(** 2. NoDup of a map under injectivity ON the list *)
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
(*  The divisor-pairing involution  d <-> n/d                         *)
(* ================================================================= *)

(** 3. for d | n (d,n >= 1):  n / (n / d) = d *)
Lemma div_div_cancel : forall n d, divides d n -> 1 <= d -> 1 <= n -> n / (n / d) = d.
Proof.
  intros n d [k Hk] Hd Hn.
  assert (Hk1 : 1 <= k) by nia.
  assert (E1 : n / d = k).
  { rewrite Hk. rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
  rewrite E1. rewrite Hk. apply Nat.div_mul. lia.
Qed.

(** 4. for d | n, the complementary divisor n/d is again a divisor *)
Lemma divisor_complement : forall n d, divides d n -> 1 <= d -> 1 <= n ->
  divides (n / d) n /\ 1 <= n / d /\ n / d <= n.
Proof.
  intros n d [k Hk] Hd Hn.
  assert (Hk1 : 1 <= k) by nia.
  assert (E1 : n / d = k).
  { rewrite Hk. rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
  rewrite E1. split; [|split].
  - exists d. rewrite Hk. ring.
  - exact Hk1.
  - nia.
Qed.

(** 5. STRUCTURAL HEART: d <-> n/d permutes the divisors of n *)
Lemma divisors_pairing : forall n, 1 <= n ->
  Permutation (divisors n) (map (fun d => n / d) (divisors n)).
Proof.
  intros n Hn.
  apply NoDup_Permutation.
  - unfold divisors. apply NoDup_filter. apply seq_NoDup.
  - apply NoDup_map_local.
    + intros x y Hx Hy Hxy.
      assert (Hxy' : n / x = n / y) by exact Hxy.
      apply divisors_spec in Hx; apply divisors_spec in Hy.
      destruct Hx as [Hdx [Hx1 _]]. destruct Hy as [Hdy [Hy1 _]].
      assert (Hcx : n / (n / x) = x) by (apply div_div_cancel; [exact Hdx | exact Hx1 | exact Hn]).
      assert (Hcy : n / (n / y) = y) by (apply div_div_cancel; [exact Hdy | exact Hy1 | exact Hn]).
      rewrite <- Hcx, <- Hcy, Hxy'. reflexivity.
    + unfold divisors. apply NoDup_filter. apply seq_NoDup.
  - intros x. split.
    + intros Hx. apply divisors_spec in Hx. destruct Hx as [Hdx [Hx1 Hxn]].
      apply in_map_iff. exists (n / x). split.
      * cbn. apply div_div_cancel; [exact Hdx | exact Hx1 | exact Hn].
      * apply divisors_spec. apply divisor_complement; [exact Hdx | exact Hx1 | exact Hn].
    + intros Hx. apply in_map_iff in Hx. destruct Hx as [d [Hxd Hind]].
      cbn in Hxd. apply divisors_spec in Hind. destruct Hind as [Hdd [Hd1 Hdn]].
      subst x. apply divisors_spec. apply divisor_complement; [exact Hdd | exact Hd1 | exact Hn].
Qed.

(* ================================================================= *)
(*  Dirichlet convolution and its commutativity                       *)
(* ================================================================= *)

Definition dconv (f g : nat -> Z) (n : nat) : Z :=
  fold_right Z.add 0%Z (map (fun d => Z.mul (f d) (g (n / d))) (divisors n)).

(** 6. GENERAL: Dirichlet convolution is commutative *)
Theorem dconv_comm : forall f g n, 1 <= n -> dconv f g n = dconv g f n.
Proof.
  intros f g n Hn. unfold dconv.
  assert (Hp2 : Permutation (map (fun d => Z.mul (f d) (g (n / d))) (divisors n))
                            (map (fun d => Z.mul (f d) (g (n / d))) (map (fun d => n / d) (divisors n)))).
  { apply Permutation_map. exact (divisors_pairing n Hn). }
  apply Zsum_perm in Hp2. rewrite Hp2. rewrite map_map.
  f_equal. apply map_ext_in. intros d Hd.
  apply divisors_spec in Hd. destruct Hd as [Hdd [Hd1 _]].
  assert (Hc : n / (n / d) = d) by (apply div_div_cancel; [exact Hdd | exact Hd1 | exact Hn]).
  cbn beta. rewrite Hc. ring.
Qed.

(* ================================================================= *)
(*  The Mobius function (squarefree definition) and standard funcs    *)
(* ================================================================= *)

(** explicit prime factorization (with multiplicity) via smallest_factor *)
Fixpoint factorize_aux (fuel n : nat) : list nat :=
  match fuel with
  | O => []
  | S f => if n <=? 1 then []
           else let p := smallest_factor n in p :: factorize_aux f (n / p)
  end.
Definition factorize (n : nat) : list nat := factorize_aux n n.

(** boolean "no duplicates" *)
Fixpoint no_dup_bool (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: r => andb (negb (existsb (Nat.eqb x) r)) (no_dup_bool r)
  end.

(** Mobius mu(n): 0 unless squarefree; (-1)^(#distinct primes) otherwise *)
Definition mu (n : nat) : Z :=
  if Nat.eqb n 0 then 0%Z
  else if no_dup_bool (factorize n)
       then (if Nat.even (length (factorize n)) then 1%Z else (-1)%Z)
       else 0%Z.

Definition arith_one (_ : nat) : Z := 1%Z.
Definition arith_eps (n : nat) : Z := if Nat.eqb n 1 then 1%Z else 0%Z.
Definition arith_id  (n : nat) : Z := Z.of_nat n.
Definition phi_Z     (n : nat) : Z := Z.of_nat (phi n).

(* ================================================================= *)
(*  Values of factorize and mu (machine-checked)                      *)
(* ================================================================= *)

(** 7. factorization with multiplicity *)
Example factorize_12 : factorize 12 = [2; 2; 3].
Proof. vm_compute. reflexivity. Qed.

Example factorize_30 : factorize 30 = [2; 3; 5].
Proof. vm_compute. reflexivity. Qed.

(** 8. Mobius values: mu(1)=1, mu(2)=-1, mu(6)=1, mu(30)=-1 (squarefree) *)
Example mu_1  : mu 1  = 1%Z.    Proof. vm_compute. reflexivity. Qed.
Example mu_2  : mu 2  = (-1)%Z. Proof. vm_compute. reflexivity. Qed.
Example mu_6  : mu 6  = 1%Z.    Proof. vm_compute. reflexivity. Qed.
Example mu_30 : mu 30 = (-1)%Z. Proof. vm_compute. reflexivity. Qed.

(** 9. mu vanishes on non-squarefree: mu(4)=mu(12)=0 *)
Example mu_4  : mu 4  = 0%Z.    Proof. vm_compute. reflexivity. Qed.
Example mu_12 : mu 12 = 0%Z.    Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  The three classical Dirichlet identities (Element-side)           *)
(* ================================================================= *)

(** 10. FUNDAMENTAL Mobius identity:  sum_{d|n} mu(d) = [n=1],  for all n <= 30 *)
Example mobius_sum_identity :
  forall n, In n (seq 1 30) -> dconv mu arith_one n = arith_eps n.
Proof.
  intros n H. simpl in H.
  repeat (destruct H as [H | H]; [subst n; vm_compute; reflexivity | ]).
  destruct H.
Qed.

(** 11. GAUSS:  sum_{d|n} phi(d) = n,  for all n <= 20 *)
Example gauss_totient_sum :
  forall n, In n (seq 1 20) -> dconv phi_Z arith_one n = arith_id n.
Proof.
  intros n H. simpl in H.
  repeat (destruct H as [H | H]; [subst n; vm_compute; reflexivity | ]).
  destruct H.
Qed.

(** 12. MOBIUS INVERSION (phi = mu * id):  phi(n) = sum_{d|n} mu(d)*(n/d), n <= 20 *)
Example mobius_inversion_phi :
  forall n, In n (seq 1 20) -> dconv mu arith_id n = phi_Z n.
Proof.
  intros n H. simpl in H.
  repeat (destruct H as [H | H]; [subst n; vm_compute; reflexivity | ]).
  destruct H.
Qed.

(* ================================================================= *)
(*  General corollaries of commutativity                              *)
(* ================================================================= *)

(** 13. since convolution is commutative, the two orders of mu * id agree *)
Theorem mobius_id_comm : forall n, 1 <= n -> dconv mu arith_id n = dconv arith_id mu n.
Proof. intros n Hn. apply dconv_comm. exact Hn. Qed.

(** 14. and likewise phi * one = one * phi (the Gauss sum read both ways) *)
Theorem gauss_comm : forall n, 1 <= n -> dconv phi_Z arith_one n = dconv arith_one phi_Z n.
Proof. intros n Hn. apply dconv_comm. exact Hn. Qed.

(* ================================================================= *)
(*  Convolution with the constant 1 is the divisor sum                *)
(* ================================================================= *)

(** 15. (f * 1)(n) = sum_{d|n} f(d) *)
Lemma dconv_one_r : forall f n,
  dconv f arith_one n = fold_right Z.add 0%Z (map f (divisors n)).
Proof.
  intros f n. unfold dconv, arith_one.
  f_equal. apply map_ext_in. intros d _. ring.
Qed.

(** 16. concrete: (mu * 1)(12) = 0  (squarefree cancellation in action) *)
Example dconv_mu_one_12 : dconv mu arith_one 12 = 0%Z.
Proof. vm_compute. reflexivity. Qed.
