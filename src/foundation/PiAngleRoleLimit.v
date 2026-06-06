(** * PiAngleRoleLimit.v — the π-incommensurability role-limit, GENERALISED: a criterion (2a ≡ 1 mod p, p | c)
       under which a rational rotation (a/c, b/c) of a Pythagorean triple has INFINITE ORDER — its angle is an
       irrational multiple of π (arccos(a/c) ∉ πℚ).  NivenRationalCosine.v proved this for the single 3-4-5
       rotation via a mod-5 fixed point; this isolates WHY it works (mod-p fixed point ⟺ 2a ≡ 1 mod p) and
       turns it into a general theorem covering an infinite FAMILY (3-4-5 and 33-56-65 both via p = 5, …).

    -- What this is, and (honestly) is NOT --
      IS: the constructive shadow of Niven's theorem — a rational cosine a/c whose ANGLE is π-incommensurable.
          "Does the rational rotation ever return to the identity?" — NO: a role-limit (the return would need
          π-commensurability; over ℚ it never actualises).  So arccos(a/c)/π is a role-limit, NOT an Element.
      IS NOT: π's own irrationality/transcendence.  That is Niven's INTEGRAL proof (∫₀^π xⁿ(π−x)ⁿ sin x /n!) —
          real analysis, outside this 0-axiom ℤ/ℚ frame.  This file proves ANGLES are irrational multiples of
          π, not that π itself is irrational.  The integral proof is the honest wall, not attempted.

    -- The mechanism (mod-p fixed point), machine-checked --
      Rotation over ℤ (scaled by cⁿ): X₀=1, Y₀=0, Xₙ₊₁ = aXₙ − bYₙ, Yₙ₊₁ = bXₙ + aYₙ, with Xₙ² + Yₙ² = c^(2n).
      If p | c and 2a ≡ 1 (mod p), then (Xₙ, Yₙ) ≡ (a, b) (mod p) for all n ≥ 1 — a FIXED POINT (because the
      step sends a²−b²−a = a(2a−1) − c² ≡ 0 and 2ab − b = b(2a−1) ≡ 0 mod p).  Then Xₙ ≡ a ≢ 0 (mod p) while
      cⁿ ≡ 0, so Xₙ ≠ cⁿ: the rotation power is never the identity — infinite order.

    WHAT THE REPO HAS (surveyed): NivenRationalCosine.v (the 3-4-5 case, the mod-5 invariant, the role-limit
    framing); NivenGeneral / ReductionAtlasNiven (Niven's rational-cosine sparseness).  GAP: the GENERAL
    criterion (2a ≡ 1 mod p ⟹ infinite order) and the family it covers, plus the explicit π-commensurability =
    Element / incommensurability = role-limit statement.  This adds it (3-4-5 machinery generalised; no import).

    ============ E/R/R разбор ============
      Elements : целочисленные (Xₙ,Yₙ) поворота (×cⁿ); рациональные точки орбиты (Xₙ/cⁿ,Yₙ/cⁿ).
      Roles    : конечный порядок = π-СОИЗМЕРИМОСТЬ (угол ∈ πℚ, Element — процесс замыкается); бесконечный = π-НЕсоизмеримость (role-limit).
      Rules    : 2a≡1 (mod p), p|c ⟹ (Xₙ,Yₙ)≡(a,b) mod p (неподвижная точка) ⟹ Xₙ≢0 ⟹ Xₙ≠cⁿ ⟹ бесконечный порядок.
      ДИАГНОСТИКА (P4): «возврат поворота в тождество» = role-limit (требует π-соизмеримости, над ℚ не актуализуется);
      рациональный cos=a/c с углом ∉ πℚ — апериодический процесс. НЕ иррациональность π-объекта (интеграл Нивена — стена).
      Уровень: `новая теорема` (общий критерий 2a≡1 mod p ⟹ беск. порядок + семейство; в репо был лишь 3-4-5) + `синтез` (Element/role-limit угла).

    STATUS: 10 Qed, 0 Admitted, 0 axioms  (self-contained: ZArith / Znumtheory / Lia; 3-4-5 machinery generalised)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia.
Open Scope Z_scope.

(* ===================================================================== *)
(*  Integer coordinates of the n-fold (a,b)/c rotation (× cⁿ)              *)
(* ===================================================================== *)

Fixpoint Rot (a b : Z) (n : nat) : Z * Z :=
  match n with
  | O => (1, 0)
  | S k => let (x, y) := Rot a b k in (a * x - b * y, b * x + a * y)
  end.

Definition Xr (a b : Z) (n : nat) : Z := fst (Rot a b n).
Definition Yr (a b : Z) (n : nat) : Z := snd (Rot a b n).

Lemma Xr_S : forall a b n, Xr a b (S n) = a * Xr a b n - b * Yr a b n.
Proof. intros a b n. unfold Xr, Yr. simpl. destruct (Rot a b n) as [x y]. reflexivity. Qed.

Lemma Yr_S : forall a b n, Yr a b (S n) = b * Xr a b n + a * Yr a b n.
Proof. intros a b n. unfold Xr, Yr. simpl. destruct (Rot a b n) as [x y]. reflexivity. Qed.

Lemma Xr_1 : forall a b, Xr a b 1 = a.
Proof. intros a b. unfold Xr. simpl. ring. Qed.

Lemma Yr_1 : forall a b, Yr a b 1 = b.
Proof. intros a b. unfold Yr. simpl. ring. Qed.

(** cⁿ — the magnitude scaling; the rotation returns to the identity iff (Xₙ,Yₙ) = (cⁿ,0). *)
Fixpoint cpow (c : Z) (n : nat) : Z := match n with O => 1 | S k => c * cpow c k end.

Lemma cpow_div : forall c p n, (p | c) -> (1 <= n)%nat -> (p | cpow c n).
Proof.
  intros c p n Hpc Hn. destruct n as [| k]; [ lia | ].
  change (cpow c (S k)) with (c * cpow c k). apply Z.divide_mul_l. exact Hpc.
Qed.

(* ===================================================================== *)
(*  ★ The mod-p fixed point:  (Xₙ,Yₙ) ≡ (a,b) (mod p) for n ≥ 1            *)
(* ===================================================================== *)

(** ★ Under 2a ≡ 1 (mod p) and p | c (with a²+b² = c²), the integer orbit is FIXED at (a,b) modulo p from
    n = 1 on.  This is exactly why 3-4-5's mod-5 invariant works — and now for the whole family. *)
Lemma rot_mod_fixed : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) -> (p | (2 * a - 1)) ->
  forall n, (1 <= n)%nat -> (p | (Xr a b n - a)) /\ (p | (Yr a b n - b)).
Proof.
  intros a b c p Hpyth Hpc Hp2a.
  destruct Hpc as [s Hs]. destruct Hp2a as [w Hw].
  induction n as [| k IH]; intro Hn.
  - lia.
  - destruct k as [| k'].
    + rewrite Xr_1, Yr_1. split; [ exists 0 | exists 0 ]; ring.
    + assert (Hk : (1 <= S k')%nat) by lia.
      destruct (IH Hk) as [[u Hu] [v Hv]].
      assert (HXn : Xr a b (S k') = a + u * p) by lia.
      assert (HYn : Yr a b (S k') = b + v * p) by lia.
      split.
      * rewrite Xr_S, HXn, HYn.
        exists (a * w - s * s * p + a * u - b * v).
        rewrite Hs in Hpyth. nia.
      * rewrite Yr_S, HXn, HYn.
        exists (b * w + b * u + a * v).
        rewrite Hs in Hpyth. nia.
Qed.

(* ===================================================================== *)
(*  ★★ Infinite order: the rotation never returns to the identity         *)
(* ===================================================================== *)

(** p does not divide a (else p | 1 from 2a−1). *)
Lemma not_div_a : forall a p : Z, (2 <= p) -> (p | (2 * a - 1)) -> ~ (p | a).
Proof.
  intros a p Hp Hp2a Hpa.
  assert (Hp1 : (p | 1)).
  { replace 1 with (2 * a - (2 * a - 1)) by ring.
    apply Z.divide_sub_r; [ apply Z.divide_mul_r; exact Hpa | exact Hp2a ]. }
  apply Z.divide_pos_le in Hp1; lia.
Qed.

(** ★★ THE THEOREM: a Pythagorean rotation with a divisor p | c satisfying 2a ≡ 1 (mod p) has INFINITE ORDER —
    Xₙ ≠ cⁿ for every n ≥ 1, so the rotation power is never the identity (angle ∉ πℚ). *)
Theorem rotation_infinite_order : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) -> (p | (2 * a - 1)) -> (2 <= p) ->
  forall n, (1 <= n)%nat -> Xr a b n <> cpow c n.
Proof.
  intros a b c p Hpyth Hpc Hp2a Hp n Hn Heq.
  destruct (rot_mod_fixed a b c p Hpyth Hpc Hp2a n Hn) as [HX _].
  pose proof (cpow_div c p n Hpc Hn) as Hcp.
  (* p | (Xr − a) and Xr = cpow and p | cpow  ⟹  p | a, contradicting not_div_a *)
  assert (Hpa : (p | a)).
  { replace a with (cpow c n - (Xr a b n - a)) by (rewrite Heq; ring).
    apply Z.divide_sub_r; [ exact Hcp | exact HX ]. }
  exact (not_div_a a p Hp Hp2a Hpa).
Qed.

(* ===================================================================== *)
(*  The π-commensurability / role-limit reading                            *)
(* ===================================================================== *)

(** π-COMMENSURABLE = the rational rotation returns to the identity at some finite stage (angle ∈ πℚ, an
    Element — the process closes).  Its negation is the role-limit (angle ∉ πℚ). *)
Definition pi_commensurable (a b c : Z) : Prop :=
  exists n, (1 <= n)%nat /\ Xr a b n = cpow c n /\ Yr a b n = 0.

(** ★ The angle is a ROLE-LIMIT: under the criterion the rotation never closes — arccos(a/c)/π ∉ ℚ. *)
Corollary angle_is_role_limit : forall a b c p : Z,
  a * a + b * b = c * c -> (p | c) -> (p | (2 * a - 1)) -> (2 <= p) ->
  ~ pi_commensurable a b c.
Proof.
  intros a b c p Hpyth Hpc Hp2a Hp [n [Hn [HX _]]].
  exact (rotation_infinite_order a b c p Hpyth Hpc Hp2a Hp n Hn HX).
Qed.

(* ===================================================================== *)
(*  The family: 3-4-5 and 33-56-65 (both via p = 5), …                     *)
(* ===================================================================== *)

(** ★ 3-4-5 (cos = 3/5): infinite order via p = 5 (2·3 − 1 = 5). *)
Corollary role_limit_345 : ~ pi_commensurable 3 4 5.
Proof. apply (angle_is_role_limit 3 4 5 5); [ reflexivity | exists 1; reflexivity | exists 1; reflexivity | lia ]. Qed.

(** ★ 33-56-65 (cos = 33/65): infinite order via p = 5 (2·33 − 1 = 65 = 13·5) — the criterion's reach beyond 3-4-5. *)
Corollary role_limit_33_56_65 : ~ pi_commensurable 33 56 65.
Proof. apply (angle_is_role_limit 33 56 65 5); [ reflexivity | exists 13; reflexivity | exists 13; reflexivity | lia ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The π-incommensurability role-limit, generalised:
      (fixed point) 2a ≡ 1 (mod p), p | c ⟹ (Xₙ,Yₙ) ≡ (a,b) (mod p) for n ≥ 1;
      (infinite)    hence Xₙ ≢ 0 ≡ cⁿ (mod p) ⟹ Xₙ ≠ cⁿ ⟹ the rotation never returns to the identity;
      (role-limit)  so arccos(a/c)/π is a ROLE-LIMIT (angle ∉ πℚ), not an Element — for a whole FAMILY
                    (3-4-5 and 33-56-65 via p = 5, …), generalising NivenRationalCosine's single case.
    This is the constructive shadow of Niven's theorem: a rational cosine with a π-incommensurable angle.
    Honest: this proves ANGLES are irrational multiples of π, NOT that π itself is irrational — π's own
    irrationality is Niven's INTEGRAL proof (real analysis), the wall not attempted here.  Level: a new
    general criterion (only 3-4-5 was in the repo) plus the Element/role-limit reading of the angle. *)
Theorem pi_angle_role_limit :
  (forall a b c p, a * a + b * b = c * c -> (p | c) -> (p | (2 * a - 1)) -> (2 <= p) ->
     forall n, (1 <= n)%nat -> Xr a b n <> cpow c n)
  /\ ~ pi_commensurable 3 4 5
  /\ ~ pi_commensurable 33 56 65.
Proof.
  split; [ exact rotation_infinite_order | ].
  split; [ exact role_limit_345 | exact role_limit_33_56_65 ].
Qed.
