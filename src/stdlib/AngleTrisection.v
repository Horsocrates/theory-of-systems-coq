(** * AngleTrisection.v — the angle trisection and the regular heptagon as
      DEGREE-3 role-limits, completing the Greek triad of classical impossibilities
      (with ∛2 / the Delian problem in `CubicRoleLimit.v`).

    Elements: integers p, d (numerator/denominator of a rational root); the finite
              candidate set {±1}; the rational coefficients (L1 + P4)
    Roles:    2cos20° (root of y³−3y−1) and 2cos(2π/7) (root of y³+y²−2y−1) = the
              DEGREE-3 role-limits; the trisection of 60° and the heptagon = the two
              remaining classical Greek impossibilities (with ∛2 = the Delian one)
    Rules:    the monic minimal cubics; the rational root test (a root p/d in lowest
              terms ⟹ d|leading=1 and p|const=±1); coprime ⟹ unit (Gauss)

    THE DEEP POINT — the three classical Greek construction impossibilities are
    exactly three DEGREE-3 role-limits, deeper than the quadratic tier (H8).
      · Doubling the cube — ∛2 (degree 3), `CubicRoleLimit.cbrt2_irrational`.
      · Trisecting the 60° angle — 2cos20° is a root of y³−3y−1 (since cos60°=½ and
        cos3θ=4cos³θ−3cosθ gives 8cos³20°−6cos20°=1, i.e. (2cos20°)³−3(2cos20°)−1=0).
        This monic cubic has NO rational root (`trisection_no_rational`), so cos20° is
        irrational and 60° cannot be trisected by ruler and compass.
      · The regular heptagon — 2cos(2π/7) is a root of y³+y²−2y−1, which has no
        rational root (`heptagon_no_rational`), so the 7-gon is not constructible.
    Each irrationality is proved by the rational root test: a monic integer cubic
    with constant term ±1 can only have ±1 as a rational root (coprime ⟹ unit, via
    Gauss / `coprime_div_cube_unit`), and neither ±1 is a root.  Constructibility
    needs degree a power of 2; 3 ∤ 2ᵏ, so all three escape the constructible
    (degree-2-tower) Element-side.

    ============ E/R/R разбор ============
      Rules (L5): монические кубики y³−3y−1, y³+y²−2y−1; рациональный корневой тест
                  (корень p/d, взаимно просто ⟹ d|1, p|±1); взаимно просто ⟹ единица.
      Roles (L4): 2cos20°, 2cos(2π/7) = role-limit степени 3; трисекция 60° и гептагон
                  = две оставшиеся греческие невозможности (с ∛2 = Делийская).
      Elements  : целые p,d; конечное {±1}; рац. коэффициенты (L1+P4).
    ДИАГНОСТИКА (P4): три греческие невозможности (удвоение куба/трисекция/гептагон) = три
    role-limit СТЕПЕНИ 3, глубже квадратичного тира; построимость требует степень 2ᵏ, 3∤2ᵏ.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qcanon Lia ZArith Znumtheory.
From ToS Require Import stdlib.CubicRoleLimit.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Coprime ⟹ unit: x | y³ with gcd(x,y)=1 ⟹ x = ±1 (Gauss)       *)
(* ================================================================= *)

Lemma coprime_div_cube_unit : forall x y : Z,
  Z.gcd x y = 1 -> (x | y * y * y) -> x = 1 \/ x = -1.
Proof.
  intros x y Hg Hd.
  assert (Hr : rel_prime x y) by (apply Zgcd_1_rel_prime; exact Hg).
  assert (Hr2 : rel_prime x (y * y)) by (apply rel_prime_mult; exact Hr).
  assert (Hr3 : rel_prime x (y * y * y)) by (apply rel_prime_mult; [ exact Hr2 | exact Hr ]).
  assert (Hg3 : Z.gcd x (y * y * y) = 1) by (apply Zgcd_1_rel_prime; exact Hr3).
  assert (Hd1 : (x | 1)).
  { rewrite <- Hg3. apply Z.gcd_greatest; [ apply Z.divide_refl | exact Hd ]. }
  apply Z.divide_1_r in Hd1. exact Hd1.
Qed.

(* ================================================================= *)
(** ** The trisection cubic y³ = 3y + 1 has no rational root          *)
(* ================================================================= *)

(** Z-level, cross-multiplied form (no cancellation needed by the caller). *)
Lemma tri_Z : forall p d : Z,
  0 < d -> Z.gcd p d = 1 ->
  p * p * p * d = (3 * p + d) * (d * d * d) -> False.
Proof.
  intros p d Hd Hg Heq0.
  assert (Hd0 : d <> 0) by lia.
  assert (Heq : p * p * p = (3 * p + d) * (d * d)).
  { apply (Z.mul_cancel_r _ _ d Hd0). rewrite Heq0. ring. }
  assert (Hd3 : d * d * d = p * p * p - 3 * (d * d) * p) by (rewrite Heq; ring).
  assert (Hpd3 : (p | d * d * d)).
  { exists (p * p - 3 * (d * d)). rewrite Hd3. ring. }
  assert (Hdp3 : (d | p * p * p)).
  { exists ((3 * p + d) * d). rewrite Heq. ring. }
  apply coprime_div_cube_unit in Hpd3; [ | exact Hg ].
  assert (Hgd : Z.gcd d p = 1) by (rewrite Z.gcd_comm; exact Hg).
  apply coprime_div_cube_unit in Hdp3; [ | exact Hgd ].
  assert (Hd1 : d = 1) by lia.
  subst d. destruct Hpd3 as [Hp | Hp]; subst p; lia.
Qed.

Open Scope Q_scope.

(** 2cos20° (a root of y³−3y−1) is irrational — 60° cannot be trisected. *)
Theorem trisection_no_rational : ~ (exists q : Q, q * q * q == 3 * q + 1).
Proof.
  intros [q Hq].
  assert (Hr : Qred q * Qred q * Qred q == 3 * Qred q + 1)
    by (rewrite (Qred_correct q); exact Hq).
  pose proof (Qred_identity2 _ (Qred_involutive q)) as Hcop.
  destruct (Qred q) as [p d] eqn:E.
  simpl in Hcop.
  apply (tri_Z p (Z.pos d)).
  - lia.
  - exact Hcop.
  - unfold Qeq in Hr. cbn -[Z.mul Z.add] in Hr. rewrite ?Pos2Z.inj_mul in Hr. nia.
Qed.

(* ================================================================= *)
(** ** The heptagon cubic y³ = −y² + 2y + 1 has no rational root      *)
(* ================================================================= *)

Open Scope Z_scope.

(** Z-level, cross-multiplied form (RHS has denominator d³, so the cross factor
    is d³, and the numerator is already the cleared cubic). *)
Lemma hept_Z : forall p d : Z,
  0 < d -> Z.gcd p d = 1 ->
  p * p * p * (d * d * d)
    = (- (p * p) * d + 2 * p * (d * d) + d * d * d) * (d * d * d) -> False.
Proof.
  intros p d Hd Hg Heq0.
  assert (Hd0 : d * d * d <> 0) by nia.
  assert (Heq : p * p * p = - (p * p) * d + 2 * p * (d * d) + d * d * d).
  { apply (Z.mul_cancel_r _ _ (d * d * d) Hd0). rewrite Heq0. ring. }
  assert (Hd3 : d * d * d = p * p * p + p * p * d - 2 * p * (d * d))
    by (rewrite Heq; ring).
  assert (Hpd3 : (p | d * d * d)).
  { exists (p * p + p * d - 2 * (d * d)). rewrite Hd3. ring. }
  assert (Hdp3 : (d | p * p * p)).
  { exists (- (p * p) + 2 * p * d + d * d). rewrite Heq. ring. }
  apply coprime_div_cube_unit in Hpd3; [ | exact Hg ].
  assert (Hgd : Z.gcd d p = 1) by (rewrite Z.gcd_comm; exact Hg).
  apply coprime_div_cube_unit in Hdp3; [ | exact Hgd ].
  assert (Hd1 : d = 1) by lia.
  subst d. destruct Hpd3 as [Hp | Hp]; subst p; lia.
Qed.

Open Scope Q_scope.

(** 2cos(2π/7) (a root of y³+y²−2y−1) is irrational — the heptagon is not
    constructible by ruler and compass. *)
Theorem heptagon_no_rational : ~ (exists q : Q, q * q * q == - (q * q) + 2 * q + 1).
Proof.
  intros [q Hq].
  assert (Hr : Qred q * Qred q * Qred q == - (Qred q * Qred q) + 2 * Qred q + 1)
    by (rewrite (Qred_correct q); exact Hq).
  pose proof (Qred_identity2 _ (Qred_involutive q)) as Hcop.
  destruct (Qred q) as [p d] eqn:E.
  simpl in Hcop.
  apply (hept_Z p (Z.pos d)).
  - lia.
  - exact Hcop.
  - unfold Qeq in Hr. cbn -[Z.mul Z.add] in Hr. rewrite ?Pos2Z.inj_mul in Hr. nia.
Qed.

(* ================================================================= *)
(** ** Synthesis: the three classical Greek impossibilities           *)
(* ================================================================= *)

(** The three classical Greek construction impossibilities, all DEGREE-3 role-limits:
      (a) doubling the cube — ∛2 ∉ ℚ (from CubicRoleLimit);
      (b) trisecting 60° — 2cos20° ∉ ℚ (root of y³−3y−1);
      (c) the regular heptagon — 2cos(2π/7) ∉ ℚ (root of y³+y²−2y−1). *)
Theorem greek_impossibilities :
  ~ (exists r : Q, r * r * r == 2)
  /\ ~ (exists q : Q, q * q * q == 3 * q + 1)
  /\ ~ (exists q : Q, q * q * q == - (q * q) + 2 * q + 1).
Proof.
  split; [ exact cbrt2_irrational | ].
  split; [ exact trisection_no_rational | exact heptagon_no_rational ].
Qed.
