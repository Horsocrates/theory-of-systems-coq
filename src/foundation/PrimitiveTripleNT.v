(** * PrimitiveTripleNT.v — the number theory of primitive Pythagorean triples, machine-checked, so the
       π-incommensurability role-limit follows from PRIMITIVITY ALONE (gcd(a,b)=1) — no per-instance
       coprimality.  PiAngleAllTriples.v needed rel_prime c a AND rel_prime c (2a) supplied for each triple;
       here those are DERIVED from gcd(a,b)=1 via the two classical facts:
         (i)  gcd(a,b)=1 ∧ a²+b²=c²  ⟹  gcd(a,c)=1   (clean divisibility);
         (ii) gcd(a,b)=1 ∧ a²+b²=c²  ⟹  c is ODD      (a mod-4 parity argument).
       Together with scale invariance (PiAngleScaleInvariant) this completes the characterization:
       a rational Pythagorean rotation has FINITE order ⟺ it is DEGENERATE (an axis case).

    -- The two facts --
      (i) Any common divisor d of a and c divides c²−a² = b²; since gcd(a,b²)=1 (from gcd(a,b)=1), d | 1.
      (ii) If 2 | c then 4 | c² = a²+b²; but a square is ≡ 0 or 1 (mod 4), and 0 is reached only by an even
           base, so a²+b² ≡ 0 (mod 4) forces a,b both even — contradicting gcd(a,b)=1.

    -- Consequence --
      For a primitive triple with c ≥ 2: rel_prime c a (from i) and rel_prime c (2a) (from i + ii, c odd ⟹
      rel_prime c 2), so the eigenvector theorem (modulus c) gives infinite order — arccos(a/c)/π is a
      role-limit — from gcd(a,b)=1 alone.  Demonstrated: 3-4-5, 5-12-13, 8-15-17 via a single gcd check.

    WHAT THE REPO HAS (surveyed): PiAngleAllTriples.v (angle_role_limit_general — needs rel_prime supplied);
    PiAngleScaleInvariant.v (scale invariance, degenerate side).  GAP: the primitive-triple NT (gcd(a,c)=1,
    c odd) that DISCHARGES the coprimality from primitivity.  This adds it.

    ============ E/R/R разбор ============
      Elements : примитивная тройка (gcd(a,b)=1); делители a,c,b²; чётность mod 4.
      Roles    : примитивность ⟹ rel_prime a c И c нечётно ⟹ rel_prime c (2a), c a — гипотезы собств.-вект. теоремы сняты.
      Rules    : (i) d|a,c ⟹ d|b² ⟹ (gcd(a,b²)=1) d|1; (ii) 2|c ⟹ 4|a²+b² ⟹ (квадрат≡0,1 mod4) a,b чётны ⟹ contra.
      ДИАГНОСТИКА (P4): role-limit угла теперь из ОДНОЙ примитивности (gcd(a,b)=1); + масштаб ⟹ полная характеризация
      конечный порядок ⟺ вырожденность. НЕ иррациональность π. Уровень: `новая теорема` (NT примитивных троек в репо) + `синтез`.

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (builds on foundation.PiAngleAllTriples)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia.
From ToS Require Import foundation.PiAngleRoleLimit.
From ToS Require Import foundation.PiAngleAllTriples.
Open Scope Z_scope.

(* ===================================================================== *)
(*  Squares modulo 4 carry the parity of the base                          *)
(* ===================================================================== *)

Lemma sq_mod_4 : forall n : Z,
  ((n * n) mod 4 = 0 /\ Z.Even n) \/ ((n * n) mod 4 = 1 /\ Z.Odd n).
Proof.
  intro n. destruct (Z.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - left. split; [ | exists m; exact Hm ].
    subst n. replace (2 * m * (2 * m)) with ((m * m) * 4) by ring. apply Z.mod_mul; lia.
  - right. split; [ | exists m; exact Hm ].
    subst n. replace ((2 * m + 1) * (2 * m + 1)) with (1 + (m * m + m) * 4) by ring.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* ===================================================================== *)
(*  ★ (ii)  Primitive ⟹ c is ODD                                          *)
(* ===================================================================== *)

Lemma prim_c_odd : forall a b c : Z,
  rel_prime a b -> a * a + b * b = c * c -> ~ (2 | c).
Proof.
  intros a b c Hrp Hpyth Hdiv.
  assert (Hc4 : (a * a + b * b) mod 4 = 0).
  { rewrite Hpyth. destruct Hdiv as [k Hk]. subst c.
    replace (k * 2 * (k * 2)) with ((k * k) * 4) by ring. apply Z.mod_mul; lia. }
  destruct (sq_mod_4 a) as [[Ha4 Hae] | [Ha4 Hao]];
  destruct (sq_mod_4 b) as [[Hb4 Hbe] | [Hb4 Hbo]].
  - destruct Hae as [pa Hpa]. destruct Hbe as [pb Hpb].
    destruct Hrp as [_ _ Hg].
    assert (Hd1 : (2 | 1)) by (apply Hg; [ exists pa; lia | exists pb; lia ]).
    apply Zdivide_1 in Hd1. lia.
  - exfalso. rewrite Z.add_mod in Hc4 by lia. rewrite Ha4, Hb4 in Hc4. discriminate.
  - exfalso. rewrite Z.add_mod in Hc4 by lia. rewrite Ha4, Hb4 in Hc4. discriminate.
  - exfalso. rewrite Z.add_mod in Hc4 by lia. rewrite Ha4, Hb4 in Hc4. discriminate.
Qed.

(* ===================================================================== *)
(*  ★ (i)  Primitive ⟹ gcd(a,c) = 1                                        *)
(* ===================================================================== *)

Lemma prim_rel_prime_ac : forall a b c : Z,
  rel_prime a b -> a * a + b * b = c * c -> rel_prime a c.
Proof.
  intros a b c Hrp Hpyth.
  assert (Hab2 : rel_prime a (b * b)) by (apply rel_prime_mult; exact Hrp).
  apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros x Hxa Hxc.
    assert (Hxb2 : (x | b * b)).
    { assert (Hxc2 : (x | c * c)) by (apply Z.divide_mul_l; exact Hxc).
      rewrite <- Hpyth in Hxc2.
      assert (Hxa2 : (x | a * a)) by (apply Z.divide_mul_l; exact Hxa).
      replace (b * b) with ((a * a + b * b) - a * a) by ring.
      apply Z.divide_sub_r; [ exact Hxc2 | exact Hxa2 ]. }
    destruct Hab2 as [_ _ Hg]. apply Hg; [ exact Hxa | exact Hxb2 ].
Qed.

(* ===================================================================== *)
(*  ★★ Role-limit from PRIMITIVITY ALONE                                   *)
(* ===================================================================== *)

(** ★★ A primitive Pythagorean triple (gcd(a,b)=1) with c ≥ 2 has a π-incommensurable angle — arccos(a/c)/π
    is a ROLE-LIMIT — derived from gcd(a,b)=1 alone (the coprimality the eigenvector theorem needs is now a
    theorem, not a per-instance hypothesis). *)
Theorem prim_role_limit : forall a b c : Z,
  rel_prime a b -> a * a + b * b = c * c -> 2 <= c -> ~ pi_commensurable a b c.
Proof.
  intros a b c Hrp Hpyth Hc.
  pose proof (prim_rel_prime_ac a b c Hrp Hpyth) as Hac.
  apply (angle_role_limit_general a b c c).
  - exact Hpyth.
  - exists 1; ring.
  - exact Hc.
  - apply rel_prime_mult.
    + apply rel_prime_sym. apply prime_rel_prime; [ exact prime_2 | apply (prim_c_odd a b c Hrp Hpyth) ].
    + apply rel_prime_sym; exact Hac.
  - apply rel_prime_sym; exact Hac.
Qed.

(* ===================================================================== *)
(*  Instances — role-limit from a single gcd check                         *)
(* ===================================================================== *)

Corollary prim_role_limit_345 : ~ pi_commensurable 3 4 5.
Proof. apply prim_role_limit; [ apply rp_compute; reflexivity | reflexivity | lia ]. Qed.

Corollary prim_role_limit_5_12_13 : ~ pi_commensurable 5 12 13.
Proof. apply prim_role_limit; [ apply rp_compute; reflexivity | reflexivity | lia ]. Qed.

Corollary prim_role_limit_8_15_17 : ~ pi_commensurable 8 15 17.
Proof. apply prim_role_limit; [ apply rp_compute; reflexivity | reflexivity | lia ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The number theory of primitive Pythagorean triples, completing the characterization:
      (i)  gcd(a,b)=1 ∧ a²+b²=c²  ⟹  rel_prime a c   (common divisor of a,c divides b²);
      (ii) gcd(a,b)=1 ∧ a²+b²=c²  ⟹  c is odd        (a²+b²≡0 mod 4 forces a,b both even);
      (role-limit)  hence a primitive triple with c ≥ 2 has a π-incommensurable angle — from gcd(a,b)=1 alone.
    With scale invariance (PiAngleScaleInvariant), this completes the picture: a rational Pythagorean rotation
    has FINITE order ⟺ it is DEGENERATE.  Honest: the ANGLE, not π itself (Niven's integral — the wall).
    Level: the classical primitive-triple NT, machine-checked (new in the repo), discharging the coprimality
    from primitivity. *)
Theorem primitive_triple_nt :
  (forall a b c, rel_prime a b -> a * a + b * b = c * c -> rel_prime a c)
  /\ (forall a b c, rel_prime a b -> a * a + b * b = c * c -> ~ (2 | c))
  /\ (forall a b c, rel_prime a b -> a * a + b * b = c * c -> 2 <= c -> ~ pi_commensurable a b c).
Proof.
  split; [ exact prim_rel_prime_ac | ].
  split; [ exact prim_c_odd | exact prim_role_limit ].
Qed.
