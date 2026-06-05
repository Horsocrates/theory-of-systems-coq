(** * ChineseRemainder.v — Chinese Remainder Theorem as ToS System

    Theory of Systems — Number Theory layer (Part XIII, remainder)

    Elements: natural numbers; residues modulo coprime m, n
    Roles:    a pair of residues (mod m, mod n) <-> a single residue (mod m*n)
    Rules:    if gcd(m,n)=1 the systems x≡a (m), x≡b (n) have a unique solution
    Status:   residues mod m*n  <->  pairs of residues mod m and mod n

    The Chinese Remainder Theorem — the structural tool behind multiplicativity
    of the arithmetic functions.  Modular inverses are obtained WITHOUT Bezout,
    by the pigeonhole principle: k |-> (n*k) mod m permutes [0,m), hence hits 1
    (reusing the residue-permutation machinery of EulerFermat / EulerTheorem).
    CRT existence is then the explicit construction a·n·n' + b·m·m'; uniqueness
    is m,n | (x-y) with gcd(m,n)=1 => m*n | (x-y).

    As an application, Euler's totient is MULTIPLICATIVE: phi(m*n)=phi(m)*phi(n)
    for gcd(m,n)=1, proved via the CRT bijection units(m*n) <-> units(m) x units(n)
    (k |-> (k mod m, k mod n)), counted with list_prod.

    RELATED: numbertheory/EulerTheorem.v (mod_mul_cancel_coprime, coprime_mult, phi),
    numbertheory/EulerFermat.v (residue machinery), numbertheory/ArithmeticFunctions.v
    (phi, the concrete multiplicativity instances), stdlib/GCD.v.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
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
From ToS Require Import numbertheory.EulerTheorem.

(* ================================================================= *)
(*  Modular inverse via the pigeonhole principle                      *)
(* ================================================================= *)

(** 1. if gcd(m,n)=1 (m>=2), n has an inverse mod m: some u<m with (n*u) mod m = 1 *)
Lemma mod_inverse_exists : forall m n, 2 <= m -> Nat.gcd m n = 1 ->
  exists u, u < m /\ (n * u) mod m = 1.
Proof.
  intros m n Hm Hcop.
  assert (Hm0 : m <> 0) by lia.
  assert (Hperm : Permutation (map (fun k => (n * k) mod m) (seq 0 m)) (seq 0 m)).
  { apply Permutation_map_same_l.
    - apply NoDup_map_local.
      + intros x y Hx Hy Hxy.
        assert (Hxy' : (n * x) mod m = (n * y) mod m) by exact Hxy.
        apply (mod_mul_cancel_coprime m n x y Hcop) in Hxy'.
        apply in_seq in Hx. apply in_seq in Hy.
        rewrite (Nat.mod_small x m) in Hxy'; [| lia].
        rewrite (Nat.mod_small y m) in Hxy'; [| lia].
        exact Hxy'.
      + apply seq_NoDup.
    - intros z Hz. apply in_map_iff in Hz. destruct Hz as [k [Hfk Hk]].
      apply in_seq in Hk. apply in_seq. subst z.
      assert ((n * k) mod m < m) by (apply Nat.mod_upper_bound; exact Hm0). lia. }
  assert (H1 : In 1 (seq 0 m)) by (apply in_seq; lia).
  apply Permutation_sym in Hperm.
  assert (Hin1 : In 1 (map (fun k => (n * k) mod m) (seq 0 m))).
  { eapply Permutation_in; [exact Hperm | exact H1]. }
  apply in_map_iff in Hin1. destruct Hin1 as [u [Hgu Hu]].
  apply in_seq in Hu. exists u. split; [lia | exact Hgu].
Qed.

(* ================================================================= *)
(*  CRT existence                                                     *)
(* ================================================================= *)

(** 2. existence: a residue agreeing with a mod m and b mod n *)
Theorem crt_exists : forall m n a b, 2 <= m -> 2 <= n -> Nat.gcd m n = 1 ->
  exists x, x mod m = a mod m /\ x mod n = b mod n.
Proof.
  intros m n a b Hm Hn Hcop.
  destruct (mod_inverse_exists m n Hm Hcop) as [un [Hun Hinvn]].
  assert (Hcop' : Nat.gcd n m = 1) by (rewrite Nat.gcd_comm; exact Hcop).
  destruct (mod_inverse_exists n m Hn Hcop') as [um [Hum Hinvm]].
  exists (a * (n * un) + b * (m * um)). split.
  - assert (Hrw : a * (n * un) + b * (m * um) = a * (n * un) + (b * um) * m) by ring.
    rewrite Hrw. rewrite Nat.Div0.mod_add.
    rewrite (Nat.Div0.mul_mod a (n * un)). rewrite Hinvn.
    rewrite Nat.mul_1_r. rewrite Nat.Div0.mod_mod. reflexivity.
  - assert (Hrw : a * (n * un) + b * (m * um) = b * (m * um) + (a * un) * n) by ring.
    rewrite Hrw. rewrite Nat.Div0.mod_add.
    rewrite (Nat.Div0.mul_mod b (m * um)). rewrite Hinvm.
    rewrite Nat.mul_1_r. rewrite Nat.Div0.mod_mod. reflexivity.
Qed.

(* ================================================================= *)
(*  CRT uniqueness                                                    *)
(* ================================================================= *)

(** 3. coprime moduli both dividing d => their product divides d *)
Lemma coprime_divides_mul : forall m n d, Nat.gcd m n = 1 ->
  divides m d -> divides n d -> divides (m * n) d.
Proof.
  intros m n d Hcop [k Hk] Hnd.
  assert (Hnk : divides n k).
  { apply (proj2 (divides_iff_Ndivide n k)).
    apply (Nat.gauss n m k).
    - apply (proj1 (divides_iff_Ndivide n (m * k))). rewrite <- Hk. exact Hnd.
    - rewrite Nat.gcd_comm. exact Hcop. }
  destruct Hnk as [j Hj]. exists j. rewrite Hk, Hj. ring.
Qed.

(** 4. uniqueness (congruence form): agreement mod m and mod n => agreement mod m*n *)
Theorem crt_unique : forall m n x y, Nat.gcd m n = 1 ->
  x mod m = y mod m -> x mod n = y mod n -> x mod (m * n) = y mod (m * n).
Proof.
  intros m n x y Hcop Hm Hn.
  destruct (Nat.le_ge_cases x y) as [Hxy | Hyx].
  - apply (divides_sub_mod_eq x y (m * n) Hxy).
    apply coprime_divides_mul;
      [exact Hcop | apply (mod_eq_divides_sub x y m Hxy Hm)
                  | apply (mod_eq_divides_sub x y n Hxy Hn)].
  - symmetry. apply (divides_sub_mod_eq y x (m * n) Hyx).
    apply coprime_divides_mul;
      [exact Hcop | apply (mod_eq_divides_sub y x m Hyx (eq_sym Hm))
                  | apply (mod_eq_divides_sub y x n Hyx (eq_sym Hn))].
Qed.

(* ================================================================= *)
(*  Concrete checks                                                   *)
(* ================================================================= *)

(** 5. classic example: x ≡ 2 (mod 3), x ≡ 1 (mod 5) is solved by 11 *)
Example crt_3_5 : 11 mod 3 = 2 /\ 11 mod 5 = 1.
Proof. split; vm_compute; reflexivity. Qed.

(** 6. existence holds for that system (via crt_exists) *)
Example crt_3_5_exists : exists x, x mod 3 = 2 mod 3 /\ x mod 5 = 1 mod 5.
Proof. apply crt_exists; [lia | lia | vm_compute; reflexivity]. Qed.

(** 7. uniqueness instance: 11 and 26 agree mod 3 and mod 5, hence mod 15 *)
Example crt_unique_11_26 : 11 mod 15 = 26 mod 15.
Proof. vm_compute. reflexivity. Qed.

(** 8. inverse example: 2 * 8 ≡ 1 (mod 15)  (8 is the inverse of 2 mod 15) *)
Example inverse_2_mod_15 : (2 * 8) mod 15 = 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  Multiplicativity of Euler's totient via the CRT bijection         *)
(* ================================================================= *)

(** polymorphic NoDup-of-injective-map *)
Lemma NoDup_map_inj {A B : Type} : forall (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros f l. induction l as [|a l IH]; simpl; intros Hinj Hnd.
  - constructor.
  - apply NoDup_cons_iff in Hnd as [Hnotin Hndl].
    constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [b [Hfb Hinb]].
      assert (Hab : a = b)
        by (apply (Hinj a b); [left; reflexivity | right; exact Hinb | symmetry; exact Hfb]).
      subst b. apply Hnotin. exact Hinb.
    + apply IH; [intros x y Hx Hy; apply Hinj; right; assumption | exact Hndl].
Qed.

(** NoDup of a Cartesian product of NoDup lists *)
Lemma NoDup_list_prod {A B : Type} : forall (l : list A) (l' : list B),
  NoDup l -> NoDup l' -> NoDup (list_prod l l').
Proof.
  induction l as [|a l IH]; simpl; intros l' Hl Hl'.
  - constructor.
  - apply NoDup_cons_iff in Hl as [Hnotin Hndl].
    apply NoDup_app.
    + apply NoDup_map_inj; [intros y1 y2 _ _ Heq; injection Heq; auto | exact Hl'].
    + apply IH; assumption.
    + intros p Hp1 Hp2. apply in_map_iff in Hp1. destruct Hp1 as [y [Heq Hy]].
      subst p. apply in_prod_iff in Hp2. destruct Hp2 as [Hal _]. apply Hnotin. exact Hal.
Qed.

(** coprimality with a factor of the modulus *)
Lemma coprime_of_mul_l : forall m n k, Nat.gcd (m * n) k = 1 -> Nat.gcd m k = 1.
Proof.
  intros m n k H.
  assert (Hd : Nat.divide (Nat.gcd m k) (Nat.gcd (m * n) k)).
  { apply Nat.gcd_greatest.
    - apply Nat.divide_trans with m; [apply Nat.gcd_divide_l | exists n; ring].
    - apply Nat.gcd_divide_r. }
  rewrite H in Hd. apply Nat.divide_1_r in Hd. exact Hd.
Qed.

Lemma coprime_of_mul_r : forall m n k, Nat.gcd (m * n) k = 1 -> Nat.gcd n k = 1.
Proof. intros m n k H. apply (coprime_of_mul_l n m k). rewrite Nat.mul_comm. exact H. Qed.

(** reduction mod a factor: (x mod (m*n)) mod m = x mod m *)
Lemma mod_mod_mul_l : forall x m n, (x mod (m * n)) mod m = x mod m.
Proof.
  intros x m n.
  apply (divides_sub_mod_eq (x mod (m * n)) x m).
  - apply Nat.Div0.mod_le.
  - assert (Hsub : x - x mod (m * n) = m * n * (x / (m * n)))
      by (pose proof (Nat.div_mod_eq x (m * n)) as Hdm; lia).
    rewrite Hsub. rewrite <- Nat.mul_assoc. apply divides_mul_l.
Qed.

Lemma mod_mod_mul_r : forall x m n, (x mod (m * n)) mod n = x mod n.
Proof. intros x m n. rewrite (Nat.mul_comm m n). apply mod_mod_mul_l. Qed.

(** the CRT pairing k |-> (k mod m, k mod n) *)
Definition crt_pair (m n k : nat) : nat * nat := (k mod m, k mod n).

(** EULER TOTIENT IS MULTIPLICATIVE:  phi(m*n) = phi(m)*phi(n) for gcd(m,n)=1 *)
Theorem phi_mult : forall m n, 2 <= m -> 2 <= n -> Nat.gcd m n = 1 ->
  phi (m * n) = phi m * phi n.
Proof.
  intros m n Hm Hn Hcop.
  assert (Hm0 : m <> 0) by lia. assert (Hn0 : n <> 0) by lia.
  assert (Hmn : 2 <= m * n) by nia. assert (Hmn0 : m * n <> 0) by nia.
  assert (Hperm : Permutation (map (crt_pair m n) (units (m * n)))
                              (list_prod (units m) (units n))).
  { apply NoDup_Permutation.
    - apply NoDup_map_inj; [| apply units_nodup].
      intros x y Hx Hy Hxy. unfold crt_pair in Hxy. injection Hxy as Hxym Hxyn.
      assert (Hmod : x mod (m * n) = y mod (m * n)) by (apply crt_unique; assumption).
      pose proof (units_lt (m * n) x Hmn Hx) as Hxlt.
      pose proof (units_lt (m * n) y Hmn Hy) as Hylt.
      rewrite (Nat.mod_small x (m * n) Hxlt), (Nat.mod_small y (m * n) Hylt) in Hmod.
      exact Hmod.
    - apply NoDup_list_prod; apply units_nodup.
    - intros [am bn]. split.
      + intros Hin. apply in_map_iff in Hin. destruct Hin as [k [Hk Hkin]].
        unfold crt_pair in Hk. injection Hk as Hkm Hkn. subst am bn.
        apply units_spec in Hkin. destruct Hkin as [[Hk1 Hkmn] Hgk].
        assert (Hgkm : Nat.gcd m k = 1) by (apply (coprime_of_mul_l m n k); exact Hgk).
        assert (Hgkn : Nat.gcd n k = 1) by (apply (coprime_of_mul_r m n k); exact Hgk).
        apply in_prod_iff. split.
        * apply units_spec. split.
          -- split.
             ++ assert ((k mod m) <> 0).
                { intro Hz. assert (Hdiv : divides m k).
                  { apply (proj1 (divides_bool_correct m k Hm0)).
                    unfold divides_bool. rewrite Hz. reflexivity. }
                  apply divides_iff_Ndivide in Hdiv.
                  assert (Hg : Nat.divide m (Nat.gcd m k))
                    by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdiv]).
                  rewrite Hgkm in Hg. apply Nat.divide_1_r in Hg. lia. }
                lia.
             ++ assert (k mod m < m) by (apply Nat.mod_upper_bound; exact Hm0). lia.
          -- rewrite Nat.gcd_comm. rewrite (gcd_mod_n k m Hm0). rewrite Nat.gcd_comm. exact Hgkm.
        * apply units_spec. split.
          -- split.
             ++ assert ((k mod n) <> 0).
                { intro Hz. assert (Hdiv : divides n k).
                  { apply (proj1 (divides_bool_correct n k Hn0)).
                    unfold divides_bool. rewrite Hz. reflexivity. }
                  apply divides_iff_Ndivide in Hdiv.
                  assert (Hg : Nat.divide n (Nat.gcd n k))
                    by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdiv]).
                  rewrite Hgkn in Hg. apply Nat.divide_1_r in Hg. lia. }
                lia.
             ++ assert (k mod n < n) by (apply Nat.mod_upper_bound; exact Hn0). lia.
          -- rewrite Nat.gcd_comm. rewrite (gcd_mod_n k n Hn0). rewrite Nat.gcd_comm. exact Hgkn.
      + intros Hin. apply in_prod_iff in Hin. destruct Hin as [Ham Hbn].
        pose proof (units_lt m am Hm Ham) as Hamlt.
        pose proof (units_lt n bn Hn Hbn) as Hbnlt.
        apply units_spec in Ham. destruct Ham as [[Ham1 Hamm] Hgam].
        apply units_spec in Hbn. destruct Hbn as [[Hbn1 Hbnn] Hgbn].
        destruct (crt_exists m n am bn Hm Hn Hcop) as [x [Hxm Hxn]].
        rewrite (Nat.mod_small am m) in Hxm; [| exact Hamlt].
        rewrite (Nat.mod_small bn n) in Hxn; [| exact Hbnlt].
        assert (Hgmx : Nat.gcd m x = 1).
        { rewrite <- Hxm in Hgam. rewrite Nat.gcd_comm in Hgam.
          rewrite (gcd_mod_n x m Hm0) in Hgam. rewrite Nat.gcd_comm in Hgam. exact Hgam. }
        assert (Hgnx : Nat.gcd n x = 1).
        { rewrite <- Hxn in Hgbn. rewrite Nat.gcd_comm in Hgbn.
          rewrite (gcd_mod_n x n Hn0) in Hgbn. rewrite Nat.gcd_comm in Hgbn. exact Hgbn. }
        assert (Hgmnx : Nat.gcd (m * n) x = 1).
        { rewrite Nat.gcd_comm. apply coprime_mult; rewrite Nat.gcd_comm; assumption. }
        apply in_map_iff. exists (x mod (m * n)). split.
        * unfold crt_pair. rewrite mod_mod_mul_l. rewrite mod_mod_mul_r.
          rewrite Hxm, Hxn. reflexivity.
        * apply units_spec. split.
          -- split.
             ++ assert ((x mod (m * n)) <> 0).
                { intro Hz. assert (Hdiv : divides (m * n) x).
                  { apply (proj1 (divides_bool_correct (m * n) x Hmn0)).
                    unfold divides_bool. rewrite Hz. reflexivity. }
                  apply divides_iff_Ndivide in Hdiv.
                  assert (Hg : Nat.divide (m * n) (Nat.gcd (m * n) x))
                    by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdiv]).
                  rewrite Hgmnx in Hg. apply Nat.divide_1_r in Hg. nia. }
                lia.
             ++ assert (x mod (m * n) < m * n) by (apply Nat.mod_upper_bound; exact Hmn0). lia.
          -- rewrite Nat.gcd_comm. rewrite (gcd_mod_n x (m * n) Hmn0).
             rewrite Nat.gcd_comm. exact Hgmnx. }
  apply Permutation_length in Hperm.
  rewrite length_map in Hperm. rewrite length_prod in Hperm.
  rewrite (phi_eq_length_units (m * n)), (phi_eq_length_units m), (phi_eq_length_units n).
  exact Hperm.
Qed.

(** concrete: phi(15) = phi(3)*phi(5) = 2*4 = 8, with gcd(3,5)=1 *)
Example phi_mult_3_5 : phi (3 * 5) = phi 3 * phi 5.
Proof. apply phi_mult; [lia | lia | vm_compute; reflexivity]. Qed.

(** concrete: phi(8*9) = phi(8)*phi(9) = 4*6 = 24, gcd(8,9)=1 *)
Example phi_mult_8_9 : phi (8 * 9) = phi 8 * phi 9.
Proof. apply phi_mult; [lia | lia | vm_compute; reflexivity]. Qed.
