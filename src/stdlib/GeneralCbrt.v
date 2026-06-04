(** * GeneralCbrt.v — the degree-3 surd theorem: ∛n is rational ⟺ n is a perfect cube.
      One degree up from GeneralSqrt.v, by the SAME coprimality engine (a reduced fraction whose
      cube is an integer is itself an integer), showing the finitization engine is DEGREE-UNIFORM:
      the boundary at degree k is "n is a perfect k-th power".  Completes the degree-3 picture of
      CubicRoleLimit.v (which gave ∛2 ∉ ℚ and ∛2 ∉ ℚ[√2]) by putting EVERY non-cube on the
      role-limit side, and opens ∛2,∛3,∛4,∛5,∛6,∛7,∛9,∛10.

    Elements: a reduced fraction (a,b) with gcd a b = 1; the perfect cubes m³; concrete ∛8 = 2
              (Element), ∛2 (role-limit, the same ∛2 as CubicRoleLimit) (L1 + P4)
    Roles:    Element side = n a perfect cube (8=2³, 27=3³) ⟹ ∛n ∈ ℚ; role-limit = n not a
              perfect cube (2,3,4,5,6,7,9,10) ⟹ ∛n ∉ ℚ (non-terminating); seven role-limits in a
              row between the cubes 1 and 8 (∛2…∛7) — denser than between squares
    Rules:    reduce r=p/q (gcd p q = 1); r³=n ⟹ p³=n·q³ ⟹ q | p³; coprimality preserved under
              CUBING (gcd q p³ = 1, rel_prime_mult applied twice) ⟹ q | 1 ⟹ q = 1 ⟹ n = p³

    THE DEEP POINT — the engine is degree-uniform.  "Is ∛n rational?" is the DECIDABLE
    Element-question "is n a perfect cube?".  `reduced_cube_integer`: a reduced fraction whose
    cube is an integer is an integer (b=1) — the SAME mechanism as the square case, only with one
    more `rel_prime_mult` (p³ = (p·p)·p, so coprimality propagates through three factors).  The
    boundary at degree k is uniformly "n is a perfect k-th power"; square (GeneralSqrt) and cube
    (here) are k=2,3 of one argument.  Lifting through Qred, a rational cube is a perfect cube
    (`rational_cube_is_perfect_cube`), so n NOT a perfect cube ⟹ ∛n irrational
    (`not_perfect_cube_irrational`).  ∛2 here is the SAME degree-3 role-limit as CubicRoleLimit's
    (which additionally showed it escapes the degree-2 tier ℚ[√2]) — this file supplies the
    "∛n ∈ ℚ ⟺ cube" side, CubicRoleLimit the "degree-3 ∉ degree-2 extension" side; together the
    finitization boundary is STRATIFIED BY DEGREE (H8), the coprimality engine holding at each.
    Element = n a perfect cube; role-limit = n a non-cube (∛n a non-terminating process).

    ============ E/R/R разбор ============
      Rules (L5): привести r=p/q (gcd p q=1); r³=n ⟹ p³=n·q³ ⟹ q∣p³; взаимная простота под КУБОМ
                  (gcd q p³=1, rel_prime_mult дважды) ⟹ q∣1 ⟹ q=1 ⟹ n=p³.
      Roles (L4): Element = n полный куб (8,27) ⟹ ∛n∈ℚ; role-limit = n не куб (2,3,4,5,6,7,9,10)
                  ⟹ ∛n∉ℚ (нетерминирующий); семь role-limits подряд между кубами 1 и 8.
      Elements  : приведённая дробь (a,b) gcd=1; полные кубы m³; ∛8=2 (Element), ∛2 (role-limit).
    ДИАГНОСТИКА (P4): «рационален ли ∛n?» = «n полный куб?» — РАЗРЕШИМЫЙ Element-вопрос про n. Движок
    ОДНОРОДЕН ПО СТЕПЕНИ: квадрат (GeneralSqrt) и куб — k=2,3 одного аргумента; граница на степени k =
    «n полная k-я степень». ∛2 = тот же degree-3 role-limit, что в CubicRoleLimit (где ещё ∛2∉ℚ[√2]); вместе
    граница финитизации СТРАТИФИЦИРОВАНА ПО СТЕПЕНИ (H8), движок взаимной простоты держит её на каждой степени.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia QArith.
From Stdlib Require Qcanon.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: a reduced fraction with integer cube is an integer         *)
(* ===================================================================== *)

(** ★ A reduced fraction a/b (gcd a b = 1, b > 0) whose cube a³/b³ is an integer n
    (a³ = n·b³) must have denominator b = 1.  Same as the square case, with coprimality
    propagated through three factors (rel_prime_mult twice) — the engine is degree-uniform. *)
Lemma reduced_cube_integer : forall a b n : Z,
  0 < b -> Z.gcd a b = 1 -> a * a * a = n * (b * b * b) -> b = 1.
Proof.
  intros a b n Hpos Hcop Heq.
  assert (Hdiv : (b | a * a * a)) by (exists (n * b * b); rewrite Heq; ring).
  assert (Hrp : rel_prime b a).
  { apply rel_prime_sym. red. rewrite <- Hcop. apply Zgcd_is_gcd. }
  assert (Hrp2 : rel_prime b (a * a)) by (apply rel_prime_mult; exact Hrp).
  assert (Hrp3 : rel_prime b (a * a * a)) by (apply rel_prime_mult; [ exact Hrp2 | exact Hrp ]).
  assert (Hb1 : (b | 1)).
  { destruct Hrp3 as [_ _ Hg]. apply Hg; [ apply Z.divide_refl | exact Hdiv ]. }
  pose proof (Z.divide_pos_le b 1 ltac:(lia) Hb1) as Hle.
  lia.
Qed.

(* ===================================================================== *)
(*  The bridge to ℚ: a rational cube is a perfect cube                     *)
(* ===================================================================== *)

(** ★ If a rational r cubes to the integer n, then n is a perfect cube.  Reduce r to lowest
    terms via Qred, cross-multiply to a³ = n·b³ over ℤ, apply the engine: b = 1, n = a³. *)
Lemma rational_cube_is_perfect_cube : forall (r : Q) (n : Z),
  (r * r * r == inject_Z n)%Q -> exists m : Z, n = m * m * m.
Proof.
  intros r n H.
  remember (Qred r) as r' eqn:Er'.
  assert (Hr' : (r' * r' * r' == inject_Z n)%Q).
  { rewrite Er'. rewrite Qred_correct. exact H. }
  assert (Hcop : Z.gcd (Qnum r') (Z.pos (Qden r')) = 1).
  { rewrite Er'. apply Qcanon.Qred_identity2. apply Qcanon.Qred_involutive. }
  unfold Qeq, Qmult, inject_Z in Hr'. simpl in Hr'.
  rewrite Z.mul_1_r in Hr'. rewrite !Pos2Z.inj_mul in Hr'.
  assert (Hb : Z.pos (Qden r') = 1).
  { apply (reduced_cube_integer (Qnum r') (Z.pos (Qden r')) n).
    - apply Pos2Z.is_pos.
    - exact Hcop.
    - exact Hr'. }
  rewrite Hb in Hr'.
  exists (Qnum r'). lia.
Qed.

(** Hence: if n is NOT a perfect cube, ∛n is irrational. *)
Corollary not_perfect_cube_irrational : forall n : Z,
  (forall m : Z, m * m * m <> n) -> ~ (exists r : Q, (r * r * r == inject_Z n)%Q).
Proof.
  intros n Hns [r Hr].
  destruct (rational_cube_is_perfect_cube r n Hr) as [m Hm].
  apply (Hns m). symmetry. exact Hm.
Qed.

(* ===================================================================== *)
(*  Deciding "n is not a perfect cube" for concrete n                      *)
(* ===================================================================== *)

(** Cube is strictly monotone on the non-negatives (via the factorization
    y³−x³ = (y−x)(y²+xy+x²)). *)
Lemma cube_mono_nonneg : forall x y : Z, 0 <= x -> 0 <= y -> x < y -> x * x * x < y * y * y.
Proof.
  intros x y Hx Hy Hxy.
  assert (Hf : y * y * y - x * x * x = (y - x) * (y * y + x * y + x * x)) by ring.
  assert (0 < y - x) by lia.
  assert (0 < y * y + x * y + x * x) by nia.
  nia.
Qed.

(** No integer cubes to a value strictly between consecutive cubes k³ and (k+1)³. *)
Lemma not_cube_strict : forall m k n : Z,
  0 <= k -> k * k * k < n -> n < (k + 1) * (k + 1) * (k + 1) -> m * m * m <> n.
Proof.
  intros m k n Hk Hlo Hhi Heq.
  assert (Hn : 0 < n) by nia.
  assert (Hm : 0 < m) by nia.
  assert (Hkm : k < m).
  { destruct (Z.le_gt_cases m k) as [H | H]; [ | exact H ].
    exfalso.
    assert (Hle : m * m * m <= k * k * k).
    { destruct (Zle_lt_or_eq _ _ H) as [Hlt | Heqmk].
      - apply Z.lt_le_incl, cube_mono_nonneg; lia.
      - subst k; lia. }
    nia. }
  assert (Hmk : m < k + 1).
  { destruct (Z.le_gt_cases (k + 1) m) as [H | H]; [ | exact H ].
    exfalso.
    assert (Hle : (k + 1) * (k + 1) * (k + 1) <= m * m * m).
    { destruct (Zle_lt_or_eq _ _ H) as [Hlt | Heqmk].
      - apply Z.lt_le_incl, cube_mono_nonneg; lia.
      - subst m; lia. }
    nia. }
  lia.
Qed.

(* ===================================================================== *)
(*  Element side: a perfect cube HAS a rational cube root                   *)
(* ===================================================================== *)

(** ∛8 = 2 ∈ ℚ: a perfect cube's root is an Element. *)
Lemma cbrt8_element : (inject_Z 2 * inject_Z 2 * inject_Z 2 == inject_Z 8)%Q.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit side: the new cube irrationals ∛2, ∛3, ∛5, ∛9               *)
(* ===================================================================== *)

(** ★ ∛2 is irrational — the SAME degree-3 role-limit as CubicRoleLimit (Delian cube-doubling),
    now via the general "non-cube ⟹ irrational" theorem. *)
Theorem cbrt2_role_limit : ~ (exists r : Q, (r * r * r == inject_Z 2)%Q).
Proof. apply not_perfect_cube_irrational. intros m. apply (not_cube_strict m 1 2); lia. Qed.

(** ∛3 is irrational. *)
Theorem cbrt3_role_limit : ~ (exists r : Q, (r * r * r == inject_Z 3)%Q).
Proof. apply not_perfect_cube_irrational. intros m. apply (not_cube_strict m 1 3); lia. Qed.

(** ∛5 is irrational. *)
Theorem cbrt5_role_limit : ~ (exists r : Q, (r * r * r == inject_Z 5)%Q).
Proof. apply not_perfect_cube_irrational. intros m. apply (not_cube_strict m 1 5); lia. Qed.

(** ∛9 is irrational (between the cubes 8 = 2³ and 27 = 3³). *)
Theorem cbrt9_role_limit : ~ (exists r : Q, (r * r * r == inject_Z 9)%Q).
Proof. apply not_perfect_cube_irrational. intros m. apply (not_cube_strict m 2 9); lia. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The degree-3 surd theorem, split by the finitization boundary:
      (a) ENGINE — a reduced fraction with integer cube is an integer
          (`reduced_cube_integer`), so a rational cube is a perfect cube
          (`rational_cube_is_perfect_cube`) — the SAME engine as degree 2, one degree up;
      (b) ELEMENT — a perfect cube has a rational root (∛8 = 2, `cbrt8_element`);
      (c) ROLE-LIMIT — every non-cube is irrational; ∛2, the same degree-3 role-limit as
          CubicRoleLimit (Delian). *)
Theorem general_cbrt_synthesis :
  (forall a b n : Z, 0 < b -> Z.gcd a b = 1 -> a * a * a = n * (b * b * b) -> b = 1)
  /\ (forall (r : Q) (n : Z), (r * r * r == inject_Z n)%Q -> exists m : Z, n = m * m * m)
  /\ (inject_Z 2 * inject_Z 2 * inject_Z 2 == inject_Z 8)%Q
  /\ ~ (exists r : Q, (r * r * r == inject_Z 2)%Q).
Proof.
  split; [ exact reduced_cube_integer | ].
  split; [ exact rational_cube_is_perfect_cube | ].
  split; [ exact cbrt8_element | exact cbrt2_role_limit ].
Qed.
