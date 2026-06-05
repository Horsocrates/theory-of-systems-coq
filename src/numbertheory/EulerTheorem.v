(** * EulerTheorem.v — Euler's Theorem (general modulus) as ToS System

    Theory of Systems — Number Theory layer (Part XIII, remainder)

    Elements: natural numbers; the reduced residue system (units mod n)
    Roles:    multiplication by a (coprime to n) -> a PERMUTATION of the units
    Rules:    a^phi(n) ≡ 1 (mod n) whenever gcd(n,a) = 1
    Status:   the group of units mod n has order phi(n)

    Euler's theorem, the generalization of Fermat's little theorem (N6) to a
    composite modulus.  Same product-of-residues argument, now over the reduced
    residue system units(n) = { k in [1,n] : gcd(n,k)=1 }, whose length is
    phi(n).  Needs two number-theoretic gcd facts derived here from Nat.gauss:
    gcd-invariance under mod (gcd_mod_n) and that a product of coprimes is
    coprime (coprime_mult).  Reuses the residue machinery of EulerFermat.v.

    RELATED: numbertheory/EulerFermat.v (Fermat = Euler at a prime),
    numbertheory/ArithmeticFunctions.v (phi), stdlib/GCD.v (gcd, coprime).

    STATUS: 13 Qed, 0 Admitted, 0 axioms
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
From ToS Require Import stdlib.GCD.
From ToS Require Import numbertheory.PrimeFactorization.
From ToS Require Import numbertheory.ArithmeticFunctions.
From ToS Require Import numbertheory.EulerFermat.

(* ================================================================= *)
(*  Two gcd facts derived from Nat.gauss                              *)
(* ================================================================= *)

(** 1. gcd is invariant under reduction mod n *)
Lemma gcd_mod_n : forall a n, n <> 0 -> Nat.gcd (a mod n) n = Nat.gcd a n.
Proof.
  intros a n Hn.
  assert (Ha : a = a mod n + a / n * n) by (rewrite (Nat.div_mod_eq a n) at 1; ring).
  rewrite (Nat.gcd_comm (a mod n) n). rewrite (Nat.gcd_comm a n).
  rewrite Ha at 2. rewrite Nat.gcd_add_mult_diag_r. reflexivity.
Qed.

(** 2. a product of two coprimes-to-n is coprime to n *)
Lemma coprime_mult : forall n a b,
  Nat.gcd n a = 1 -> Nat.gcd n b = 1 -> Nat.gcd n (a * b) = 1.
Proof.
  intros n a b Ha Hb.
  remember (Nat.gcd n (a * b)) as g eqn:Hg.
  assert (Hgn : Nat.divide g n) by (rewrite Hg; apply Nat.gcd_divide_l).
  assert (Hgab : Nat.divide g (a * b)) by (rewrite Hg; apply Nat.gcd_divide_r).
  assert (Hga : Nat.gcd g a = 1).
  { pose proof (Nat.gcd_divide_l g a) as Hd1.
    pose proof (Nat.gcd_divide_r g a) as Hd2.
    assert (Hdn : Nat.divide (Nat.gcd g a) n) by (apply Nat.divide_trans with g; assumption).
    assert (Hdg : Nat.divide (Nat.gcd g a) (Nat.gcd n a)) by (apply Nat.gcd_greatest; assumption).
    rewrite Ha in Hdg. apply Nat.divide_1_r in Hdg. exact Hdg. }
  assert (Hgb : Nat.divide g b) by (apply (Nat.gauss g a b); [exact Hgab | exact Hga]).
  assert (Hdgb : Nat.divide g (Nat.gcd g b)) by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hgb]).
  assert (Hgcdb : Nat.gcd g b = 1).
  { pose proof (Nat.gcd_divide_l g b) as Hd1.
    pose proof (Nat.gcd_divide_r g b) as Hd2.
    assert (Hdn : Nat.divide (Nat.gcd g b) n) by (apply Nat.divide_trans with g; assumption).
    assert (Hdg : Nat.divide (Nat.gcd g b) (Nat.gcd n b)) by (apply Nat.gcd_greatest; assumption).
    rewrite Hb in Hdg. apply Nat.divide_1_r in Hdg. exact Hdg. }
  rewrite Hgcdb in Hdgb. apply Nat.divide_1_r in Hdgb. exact Hdgb.
Qed.

(* ================================================================= *)
(*  Coprime cancellation mod n                                        *)
(* ================================================================= *)

(** 3. multiplication by a unit is injective mod n *)
Lemma mod_mul_cancel_coprime : forall n a x y, Nat.gcd n a = 1 ->
  (a * x) mod n = (a * y) mod n -> x mod n = y mod n.
Proof.
  intros n a x y Hcop Heq.
  destruct (Nat.le_ge_cases x y) as [Hxy | Hyx].
  - apply (divides_sub_mod_eq x y n Hxy).
    assert (Hd : divides n (a * y - a * x))
      by (apply (mod_eq_divides_sub (a * x) (a * y) n);
            [apply Nat.mul_le_mono_l; exact Hxy | exact Heq]).
    assert (Hrw : a * y - a * x = a * (y - x)) by (rewrite Nat.mul_sub_distr_l; reflexivity).
    rewrite Hrw in Hd.
    apply (proj2 (divides_iff_Ndivide n (y - x))).
    apply (Nat.gauss n a (y - x)).
    + apply (proj1 (divides_iff_Ndivide n (a * (y - x)))). exact Hd.
    + exact Hcop.
  - symmetry. apply (divides_sub_mod_eq y x n Hyx).
    assert (Hd : divides n (a * x - a * y))
      by (apply (mod_eq_divides_sub (a * y) (a * x) n);
            [apply Nat.mul_le_mono_l; exact Hyx | symmetry; exact Heq]).
    assert (Hrw : a * x - a * y = a * (x - y)) by (rewrite Nat.mul_sub_distr_l; reflexivity).
    rewrite Hrw in Hd.
    apply (proj2 (divides_iff_Ndivide n (x - y))).
    apply (Nat.gauss n a (x - y)).
    + apply (proj1 (divides_iff_Ndivide n (a * (x - y)))). exact Hd.
    + exact Hcop.
Qed.

(* ================================================================= *)
(*  The reduced residue system (units mod n)                          *)
(* ================================================================= *)

Definition units (n : nat) : list nat := filter (fun k => coprime_bool n k) (seq 1 n).

(** phi(n) is exactly the number of units (definitional) *)
Lemma phi_eq_length_units : forall n, phi n = length (units n).
Proof. reflexivity. Qed.

(** 4. membership in units(n) *)
Lemma units_spec : forall n k, In k (units n) <-> (1 <= k <= n) /\ Nat.gcd n k = 1.
Proof.
  intros n k. unfold units. rewrite filter_In, in_seq.
  split.
  - intros [Hseq Hcb]. split; [lia |].
    apply coprime_bool_correct in Hcb. unfold coprime, gcd in Hcb. exact Hcb.
  - intros [Hk Hgcd]. split; [lia |].
    apply coprime_bool_correct. unfold coprime, gcd. exact Hgcd.
Qed.

(** 5. units are strictly below n (n itself is not coprime to n) *)
Lemma units_lt : forall n k, 2 <= n -> In k (units n) -> k < n.
Proof.
  intros n k Hn Hin. apply units_spec in Hin. destruct Hin as [[Hk1 Hkn] Hgcd].
  destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite Nat.gcd_diag in Hgcd. lia.
  - lia.
Qed.

(** 6. NoDup of units *)
Lemma units_nodup : forall n, NoDup (units n).
Proof. intros n. unfold units. apply NoDup_filter. apply seq_NoDup. Qed.

(** 7. the product of the units is itself coprime to n *)
Lemma gcd_Nprod_units : forall n l,
  (forall k, In k l -> Nat.gcd n k = 1) -> Nat.gcd n (Nprod l) = 1.
Proof.
  intros n l. induction l as [|x l IH]; intros Hall.
  - replace (Nprod []) with 1 by reflexivity. apply gcd_1_r.
  - replace (Nprod (x :: l)) with (x * Nprod l) by reflexivity.
    apply coprime_mult.
    + apply Hall. left; reflexivity.
    + apply IH. intros k Hk. apply Hall. right; exact Hk.
Qed.

(* ================================================================= *)
(*  Euler's theorem                                                   *)
(* ================================================================= *)

(** EULER'S THEOREM:  a^phi(n) mod n = 1  whenever gcd(n,a) = 1  (n >= 2) *)
Theorem euler_theorem : forall n a, 2 <= n -> Nat.gcd n a = 1 ->
  (a ^ (phi n)) mod n = 1.
Proof.
  intros n a Hn Hcop.
  assert (Hn0 : n <> 0) by lia.
  assert (Ha1 : 1 <= a).
  { destruct a as [|a']; [rewrite Nat.gcd_0_r in Hcop; lia | lia]. }
  (* multiplication by a permutes the units *)
  assert (Hperm : Permutation (map (res a n) (units n)) (units n)).
  { apply Permutation_map_same_l.
    - apply NoDup_map_local.
      + intros x y Hx Hy Hxy.
        assert (Hxy' : (a * x) mod n = (a * y) mod n) by exact Hxy.
        apply (mod_mul_cancel_coprime n a x y Hcop) in Hxy'.
        pose proof (units_lt n x Hn Hx) as Hxlt.
        pose proof (units_lt n y Hn Hy) as Hylt.
        rewrite (Nat.mod_small x n Hxlt) in Hxy'.
        rewrite (Nat.mod_small y n Hylt) in Hxy'.
        exact Hxy'.
      + apply units_nodup.
    - intros z Hz. apply in_map_iff in Hz. destruct Hz as [k [Hfk Hk]].
      unfold res in Hfk. subst z.
      apply units_spec in Hk. destruct Hk as [[Hk1 Hkn] Hgk].
      apply units_spec. split.
      + split.
        * assert (Hne : (a * k) mod n <> 0).
          { intro Hz0.
            assert (Hdivr : divides n (a * k)).
            { apply (proj1 (divides_bool_correct n (a * k) Hn0)).
              unfold divides_bool. rewrite Hz0. reflexivity. }
            apply divides_iff_Ndivide in Hdivr.
            assert (Hgak : Nat.gcd n (a * k) = 1) by (apply coprime_mult; assumption).
            assert (Hnn : Nat.divide n (Nat.gcd n (a * k)))
              by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdivr]).
            rewrite Hgak in Hnn. apply Nat.divide_1_r in Hnn. lia. }
          lia.
        * assert ((a * k) mod n < n) by (apply Nat.mod_upper_bound; exact Hn0). lia.
      + rewrite Nat.gcd_comm. rewrite gcd_mod_n; [| exact Hn0].
        rewrite Nat.gcd_comm. apply coprime_mult; assumption. }
  pose proof (Nprod_perm _ _ Hperm) as Hprodeq.
  assert (Hcong : (Nprod (map (res a n) (units n))) mod n
                = (Nprod (map (Nat.mul a) (units n))) mod n).
  { apply Nprod_map_cong; [exact Hn0 |].
    intros k _. unfold res. rewrite Nat.Div0.mod_mod. reflexivity. }
  pose proof (Nprod_map_mult a (units n)) as Hmult.
  assert (HlenU : length (units n) = phi n) by reflexivity.
  rewrite HlenU in Hmult.
  assert (Hkey : (Nprod (units n)) mod n = (a ^ (phi n) * Nprod (units n)) mod n).
  { rewrite <- Hmult. rewrite <- Hcong. rewrite Hprodeq. reflexivity. }
  assert (Hcop_prod : Nat.gcd n (Nprod (units n)) = 1).
  { apply gcd_Nprod_units. intros k Hk. apply units_spec in Hk. tauto. }
  assert (HX1 : 1 <= a ^ (phi n)).
  { pose proof (Nat.pow_le_mono_l 1 a (phi n) Ha1) as Hpow.
    rewrite Nat.pow_1_l in Hpow. exact Hpow. }
  assert (Hdsub : divides n (a ^ (phi n) * Nprod (units n) - Nprod (units n))).
  { apply (mod_eq_divides_sub (Nprod (units n)) (a ^ (phi n) * Nprod (units n)) n).
    - rewrite <- (Nat.mul_1_l (Nprod (units n))) at 1. apply Nat.mul_le_mono_r. exact HX1.
    - exact Hkey. }
  assert (Hrw : a ^ (phi n) * Nprod (units n) - Nprod (units n)
              = Nprod (units n) * (a ^ (phi n) - 1)) by nia.
  rewrite Hrw in Hdsub.
  assert (HdX : Nat.divide n (a ^ (phi n) - 1)).
  { apply (Nat.gauss n (Nprod (units n)) (a ^ (phi n) - 1)).
    - apply (proj1 (divides_iff_Ndivide n (Nprod (units n) * (a ^ (phi n) - 1)))). exact Hdsub.
    - exact Hcop_prod. }
  apply (proj2 (divides_iff_Ndivide n (a ^ (phi n) - 1))) in HdX.
  destruct HdX as [k Hk].
  assert (HXval : a ^ (phi n) = 1 + k * n) by nia.
  rewrite HXval. rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia.
Qed.

(* ================================================================= *)
(*  Corollaries and concrete checks                                   *)
(* ================================================================= *)

(** 8. concrete: 2^phi(9) mod 9 = 1   (phi(9)=6, 2^6=64=7*9+1) *)
Example euler_2_9 : (2 ^ (phi 9)) mod 9 = 1.
Proof. vm_compute. reflexivity. Qed.

(** 9. concrete: 3^phi(10) mod 10 = 1   (phi(10)=4, 3^4=81) *)
Example euler_3_10 : (3 ^ (phi 10)) mod 10 = 1.
Proof. vm_compute. reflexivity. Qed.

(** 10. concrete: 2^phi(15) mod 15 = 1   (phi(15)=8, 2^8=256=17*15+1) *)
Example euler_2_15 : (2 ^ (phi 15)) mod 15 = 1.
Proof. vm_compute. reflexivity. Qed.

(** 11. phi at a prime equals p-1, so Euler specializes to Fermat there *)
Example phi_7_is_6 : phi 7 = 6.
Proof. vm_compute. reflexivity. Qed.
