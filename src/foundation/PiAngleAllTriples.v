(** * PiAngleAllTriples.v — the π-incommensurability role-limit for ALL (coprime) Pythagorean triples: the
       general number-theoretic theorem behind PiAngleRoleLimit.v's 2a≡1 criterion.  That criterion was only
       the FIXED-POINT special case.  The real structure: modulo p (p | c), the rotation matrix sends (a,b) to
       2a·(a,b) — an EIGENVECTOR — so Xₙ ≡ a·(2a)^(n−1) (mod p), which is ≢ 0 whenever p ∤ 2a and p ∤ a.  Taking
       the modulus = c itself (coprime to a and 2a for a primitive triple) covers EVERY primitive triple,
       including 5-12-13, 8-15-17, 20-21-29 that the 2a≡1 criterion MISSED.

    -- The eigenvector mechanism (machine-checked) --
      Mod p with p | c: a²+b² = c² ≡ 0, so b² ≡ −a², hence the rotation step on (a,b) gives
        (a·a − b·b, b·a + a·b) = (a²−b², 2ab) ≡ (2a², 2ab) = 2a·(a,b)   (mod p).
      So the integer orbit is (Xₙ, Yₙ) ≡ (2a)^(n−1)·(a,b) (mod p) for n ≥ 1.  If p is coprime to 2a and to a,
      then Xₙ ≡ (2a)^(n−1)·a ≢ 0 (mod p), while cⁿ ≡ 0, so Xₙ ≠ cⁿ — the rotation never returns to the
      identity: infinite order, arccos(a/c)/π ∉ ℚ (a role-limit).

    -- What this is, and (honestly) is NOT --
      IS: ALL coprime Pythagorean triples (modulus = c) give π-incommensurable angles — the full constructive
          shadow of Niven's rational-cosine theorem, generalising PiAngleRoleLimit's single criterion.  The
          coprimality conditions (rel_prime c a, rel_prime c (2a)) hold for every PRIMITIVE triple (c odd,
          gcd(a,c)=1); verified per instance by a gcd computation.
      IS NOT: π's own irrationality (Niven's INTEGRAL proof, real analysis — the wall, not attempted).

    WHAT THE REPO HAS (surveyed): PiAngleRoleLimit.v (the 2a≡1 fixed-point criterion, 3-4-5 & 33-56-65; reused
    here for Rot/Xr/Yr/cpow); RationalRootTest (zpow, rel_prime_zpow).  GAP: the eigenvector generalisation
    covering ALL coprime triples (not just the fixed-point family).  This adds it.

    ============ E/R/R разбор ============
      Elements : целочисленный поворот (Xₙ,Yₙ)×cⁿ; собственный вектор (a,b) с множителем 2a mod p.
      Roles    : конечный порядок = π-соизмеримость (Element); бесконечный = π-несоизмеримость (role-limit).
      Rules    : mod p (p|c): шаг (a,b)↦2a·(a,b) (т.к. a²−b²≡2a²) ⟹ Xₙ≡(2a)^(n−1)·a; coprime(p,2a),(p,a) ⟹ Xₙ≢0 ⟹ Xₙ≠cⁿ.
      ДИАГНОСТИКА (P4): берём модуль = c (для примитивной тройки coprime к a,2a) ⟹ ВСЕ примитивные тройки — углы ∉ πℚ
      (role-limit). Критерий 2a≡1 был лишь неподвижной точкой; собственный вектор — общий механизм. НЕ иррациональность π.
      Уровень: `новая теорема` (общая — все coprime-тройки через собственный вектор; обобщает фикс-точку-критерий) + `синтез` (role-limit).

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (builds on foundation.PiAngleRoleLimit + algebra.RationalRootTest)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia.
From ToS Require Import algebra.RationalRootTest.
From ToS Require Import foundation.PiAngleRoleLimit.
Open Scope Z_scope.

(* ===================================================================== *)
(*  ★ The eigenvector invariant:  (Xₙ,Yₙ) ≡ (2a)^(n−1)·(a,b)  (mod p)      *)
(* ===================================================================== *)

(** ★ Modulo any p | c, the orbit is the (a,b)-eigenline scaled by (2a)^(n−1).  Holds for n ≥ 1 (indexed S k,
    exponent k).  This is the general mechanism — the 2a≡1 fixed point of PiAngleRoleLimit is the case 2a≡1. *)
Lemma rot_mod_eigen : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) ->
  forall k, (p | (Xr a b (S k) - zpow (2 * a) k * a)) /\ (p | (Yr a b (S k) - zpow (2 * a) k * b)).
Proof.
  intros a b c p Hpyth Hpc.
  induction k as [| k IH].
  - rewrite Xr_1, Yr_1. cbn [zpow].
    split; [ replace (a - 1 * a) with 0 by ring | replace (b - 1 * b) with 0 by ring ];
      apply Z.divide_0_r.
  - destruct IH as [HXi HYi].
    change (zpow (2 * a) (S k)) with (2 * a * zpow (2 * a) k).
    split.
    + rewrite Xr_S.
      replace (a * Xr a b (S k) - b * Yr a b (S k) - 2 * a * zpow (2 * a) k * a)
        with (a * (Xr a b (S k) - zpow (2 * a) k * a)
              - b * (Yr a b (S k) - zpow (2 * a) k * b)
              - zpow (2 * a) k * (a * a + b * b)) by ring.
      apply Z.divide_sub_r; [ apply Z.divide_sub_r | ].
      * apply Z.divide_mul_r; exact HXi.
      * apply Z.divide_mul_r; exact HYi.
      * rewrite Hpyth. apply Z.divide_mul_r. apply Z.divide_mul_l. exact Hpc.
    + rewrite Yr_S.
      replace (b * Xr a b (S k) + a * Yr a b (S k) - 2 * a * zpow (2 * a) k * b)
        with (b * (Xr a b (S k) - zpow (2 * a) k * a)
              + a * (Yr a b (S k) - zpow (2 * a) k * b)) by ring.
      apply Z.divide_add_r; apply Z.divide_mul_r; [ exact HXi | exact HYi ].
Qed.

(* ===================================================================== *)
(*  rel_prime helpers                                                      *)
(* ===================================================================== *)

Lemma rp_compute : forall a b, Z.gcd a b = 1 -> rel_prime a b.
Proof. intros a b H. rewrite <- Zgcd_1_rel_prime. exact H. Qed.

Lemma rel_prime_not_div : forall p x, (2 <= p) -> rel_prime p x -> ~ (p | x).
Proof.
  intros p x Hp Hrp Hpx. destruct Hrp as [_ _ Hg].
  pose proof (Hg p (Z.divide_refl p) Hpx) as Hp1.
  apply Zdivide_1 in Hp1. lia.
Qed.

(* ===================================================================== *)
(*  ★★ THE GENERAL THEOREM: any coprime modulus p | c gives infinite order *)
(* ===================================================================== *)

(** ★★ If p | c (p ≥ 2) is coprime to a and to 2a, then the rotation (a,b)/c has INFINITE ORDER — Xₙ ≠ cⁿ for
    every n ≥ 1.  No fixed point or primality needed: just the eigenvector + coprimality.  For a primitive
    triple, p = c works (c coprime to a and 2a). *)
Theorem rotation_inf_order_coprime : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) -> (2 <= p) ->
  rel_prime p (2 * a) -> rel_prime p a ->
  forall n, (1 <= n)%nat -> Xr a b n <> cpow c n.
Proof.
  intros a b c p Hpyth Hpc Hp Hr2a Hra n Hn Heq.
  destruct n as [| k]; [ lia | ].
  destruct (rot_mod_eigen a b c p Hpyth Hpc k) as [HX _].
  pose proof (cpow_div c p (S k) Hpc ltac:(lia)) as Hcp.
  assert (Hpe : (p | (zpow (2 * a) k * a))).
  { replace (zpow (2 * a) k * a)
      with (cpow c (S k) - (Xr a b (S k) - zpow (2 * a) k * a)) by (rewrite Heq; ring).
    apply Z.divide_sub_r; [ exact Hcp | exact HX ]. }
  assert (Hrp : rel_prime p (zpow (2 * a) k * a)).
  { apply rel_prime_mult; [ apply rel_prime_zpow; exact Hr2a | exact Hra ]. }
  exact (rel_prime_not_div p _ Hp Hrp Hpe).
Qed.

(** ★ The angle is a ROLE-LIMIT — the general version (modulus p | c, coprime to a and 2a). *)
Corollary angle_role_limit_general : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) -> (2 <= p) ->
  rel_prime p (2 * a) -> rel_prime p a ->
  ~ pi_commensurable a b c.
Proof.
  intros a b c p Hpyth Hpc Hp Hr2a Hra [n [Hn [HX _]]].
  exact (rotation_inf_order_coprime a b c p Hpyth Hpc Hp Hr2a Hra n Hn HX).
Qed.

(* ===================================================================== *)
(*  The FAMILY: every coprime triple — incl. those the 2a≡1 criterion missed *)
(* ===================================================================== *)

(** ★ 5-12-13 (cos = 5/13): MISSED by 2a≡1 (2·5−1 = 9 ≢ 0 mod 13), caught here via modulus c = 13. *)
Corollary role_limit_5_12_13 : ~ pi_commensurable 5 12 13.
Proof.
  apply (angle_role_limit_general 5 12 13 13);
    [ reflexivity | exists 1; reflexivity | lia | apply rp_compute; reflexivity | apply rp_compute; reflexivity ].
Qed.

(** ★ 8-15-17 (cos = 8/17): via modulus c = 17. *)
Corollary role_limit_8_15_17 : ~ pi_commensurable 8 15 17.
Proof.
  apply (angle_role_limit_general 8 15 17 17);
    [ reflexivity | exists 1; reflexivity | lia | apply rp_compute; reflexivity | apply rp_compute; reflexivity ].
Qed.

(** ★ 20-21-29 (cos = 20/29): via modulus c = 29. *)
Corollary role_limit_20_21_29 : ~ pi_commensurable 20 21 29.
Proof.
  apply (angle_role_limit_general 20 21 29 29);
    [ reflexivity | exists 1; reflexivity | lia | apply rp_compute; reflexivity | apply rp_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The π-incommensurability role-limit for ALL coprime Pythagorean triples:
      (eigenvector) mod p (p|c) the rotation sends (a,b) ↦ 2a·(a,b), so Xₙ ≡ (2a)^(n−1)·a;
      (general)     p|c coprime to a and 2a ⟹ Xₙ ≢ 0 ≡ cⁿ ⟹ infinite order (no fixed point/primality);
      (family)      5-12-13, 8-15-17, 20-21-29 — all role-limits via modulus c (the 2a≡1 criterion missed
                    these); together with 3-4-5 & 33-56-65 (PiAngleRoleLimit) this is the full coprime family.
    So arccos(a/c)/π is a role-limit for every primitive triple (c coprime to a, 2a) — the complete constructive
    shadow of Niven's rational-cosine theorem.  Honest: ANGLES are irrational multiples of π, NOT π itself
    (Niven's integral proof, the wall).  Level: the general eigenvector theorem (the 2a≡1 criterion was only
    the fixed-point case) plus the Element/role-limit reading. *)
Theorem pi_angle_all_triples :
  (forall a b c p, a * a + b * b = c * c -> (p | c) -> (2 <= p) ->
     rel_prime p (2 * a) -> rel_prime p a ->
     forall n, (1 <= n)%nat -> Xr a b n <> cpow c n)
  /\ ~ pi_commensurable 5 12 13
  /\ ~ pi_commensurable 8 15 17
  /\ ~ pi_commensurable 20 21 29.
Proof.
  split; [ exact rotation_inf_order_coprime | ].
  split; [ exact role_limit_5_12_13 | ].
  split; [ exact role_limit_8_15_17 | exact role_limit_20_21_29 ].
Qed.
