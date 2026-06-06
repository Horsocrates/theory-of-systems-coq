(** * DecidableBoundaryQ.v — НАПРАВЛЕНИЕ Δ1.2 (по запросу автора 2026-06-06): the finitization boundary
      decision procedure (DecidableBoundary.v / Δ1.1) LIFTED to all of Q -- full decidability of
      "perfect square in Q", with the COMPLETENESS resting on the number theory (a rational whose square
      is an integer is itself an integer = b^2 | a^2 -> b | a, the GeneralSqrt content) proved here.

   The reduction: x = Qnum x / Qden x is a perfect square in Q  <=>  m := Qnum x * Qden x is a perfect
   square in Z (because x = m / Qden x^2, and a/d^2 is a Q-square iff a is a Z-square).  Then the integer
   decision procedure of Δ1.1 decides it:

     ★ is_square_Q_b x = is_square_Z_b (Qnum x * Qden x)   -- vm_compute-decidable;
     ★ is_square_Q_reflect : is_square_Q_b x = true <-> exists s:Q, s*s == x   -- SOUNDNESS + COMPLETENESS.

   Soundness (the easy direction) is a clean witness construction.  Completeness (the hard direction)
   needs: a rational s with s*s == x forces m to be a perfect integer square -- which reduces to the
   classic b^2 | a^2 -> b | a (square_quotient), proved here via gcd cofactors + Gauss's lemma.

   Concrete DECISIONS over Q (machine-computed verdicts):
     -- 1/4 -> is_square_Q_b = true   (Element: (1/2)^2 = 1/4, witness given);
     -- 1/2 -> is_square_Q_b = false  (role-limit: m = 2 is not a perfect square -- DECIDED, and now,
        with completeness, this PROVES 1/2 is not a perfect square in Q, i.e. sqrt(1/2) is a role-limit).

   THE GENUINE NEW CONTENT.  Δ1.1 decided the INTEGER boundary; here the boundary is decided over ALL of
   Q, completeness included -- so "x is/ isn't a perfect square in Q" is now a COMPUTED, PROVEN verdict
   for every rational.  In particular 1/2 is DECIDED (and proven) to be on the role-limit side.  The
   number theory (square_quotient) is the GeneralSqrt content, proved here self-containedly (the repo's
   GeneralSqrt.vo is stale on this machine, so it is replicated rather than imported).

   HONEST SCOPE.  Fully machine-closed, 0 axioms.  The square-root test (Z.sqrt) and the b^2|a^2->b|a
   number theory are standard; the genuine contribution is REALIZING the finitization boundary as a full
   Q decision procedure with both soundness and completeness, and turning the role-limit verdict for 1/2
   from an assertion into a computed + proven fact.  Level: a constructive decision procedure (the
   realization is the new part; the algorithm and the number theory are standard).

   Elements: the rational x; m = Qnum x * Qden x; Z.sqrt m; the boolean verdict.
   Roles:    is_square_Q_b = the Q decider; the Z-square reduction = the bridge; true/false = the verdict.
   Rules:    x is a Q-square <=> m is a Z-square (reduction); decided by Z.sqrt; completeness via b^2|a^2->b|a.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: is_square_Q сделан вычислимым через редукцию x ℚ-квадрат <=> m=Qnum x*Qden x ℤ-квадрат.
     Rules (L5): редукция (x=m/Qden x^2); soundness (легко, witness) + completeness (b^2|a^2->b|a, gcd/Gauss).
     Roles (L4): is_square_Q_b = решатель над ℚ; ℤ-редукция = мост; true/false = вердикт.
     Elements  : x in Q; m=Qnum x*Qden x; Z.sqrt m; bool.
     ОБРАЗУЮЩИЕ: DecidableBoundary (ℤ-решатель Δ1.1); Z.sqrt; Znumtheory (Gauss, gcd) для completeness.
     ВЛОЖЕННЫЕ : каждое x = вложенный вход (m); 1/2 = вложенный role-limit-вердикт (m=2 не квадрат,
                 РЕШЁН+ДОКАЗАН); 1/4 = вложенный Element-вердикт (m=4 квадрат, witness 1/2).
   ДИАГНОСТИКА (P4): граница разрешима над ВСЕМ ℚ (soundness+completeness); 1/2 РЕШЁН role-limit и теперь
   ДОКАЗАН (sqrt(1/2) не в ℚ) через completeness. Теория чисел = GeneralSqrt-содержание, реплицировано
   (stale .vo). Genuine — полная ℚ-разрешимость границы. P4: решатель терминирует (Z.sqrt).

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Bool QArith Znumtheory.
From ToS Require Import foundation.DecidableBoundary.
Open Scope Z_scope.

(* ===================================================================== *)
(*  Number theory: b^2 | a^2 -> b | a, hence m*e^2 a square -> m a square  *)
(* ===================================================================== *)

(** Coprimality is preserved under squaring. *)
Lemma rel_prime_sqr : forall a b, rel_prime a b -> rel_prime (a * a) (b * b).
Proof.
  intros a b H.
  assert (H1 : rel_prime a (b * b)) by (apply rel_prime_mult; exact H).
  assert (H2 : rel_prime (b * b) a) by (apply rel_prime_sym; exact H1).
  assert (H3 : rel_prime (b * b) (a * a)) by (apply rel_prime_mult; exact H2).
  apply rel_prime_sym; exact H3.
Qed.

(** ★ If m * e^2 is a perfect square (e <> 0), then m is a perfect square.  Via gcd cofactors + Gauss. *)
Lemma square_quotient : forall m e : Z,
  e <> 0 -> is_square_Z (m * (e * e)) -> is_square_Z m.
Proof.
  intros m e He [k Hk].
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - exists 0. nia.
  - set (g := Z.gcd k e).
    assert (Hg0 : g <> 0).
    { unfold g. rewrite Z.gcd_eq_0. intros [HH _]. exact (Hk0 HH). }
    assert (Hgn : 0 <= g) by (unfold g; apply Z.gcd_nonneg).
    destruct (Z.gcd_divide_l k e) as [a Ha]. fold g in Ha.
    destruct (Z.gcd_divide_r k e) as [b Hb]. fold g in Hb.
    (* coprime cofactors: Z.gcd a b = 1 *)
    assert (Hrp1 : Z.gcd a b = 1).
    { assert (Hgg : Z.gcd (a * g) (b * g) = Z.gcd a b * g).
      { rewrite (Z.mul_comm a g), (Z.mul_comm b g).
        rewrite Z.gcd_mul_mono_l. rewrite Z.abs_eq by exact Hgn. ring. }
      assert (Heq : g = Z.gcd a b * g) by (rewrite <- Hgg, <- Ha, <- Hb; reflexivity).
      nia. }
    assert (Hrp : rel_prime a b).
    { unfold rel_prime. rewrite <- Hrp1. apply Zgcd_is_gcd. }
    (* cancel g^2: a^2 = m*b^2 *)
    assert (Hab : a * a = m * (b * b)).
    { apply (Z.mul_reg_r _ _ (g * g)); [ nia | ].
      rewrite Ha, Hb in Hk. nia. }
    (* b^2 | a^2 and rel_prime (a^2)(b^2) => b^2 | 1 => b^2 = 1 => m = a^2 *)
    assert (Hdiv : (b * b | a * a)) by (exists m; rewrite Hab; ring).
    assert (Hrpsq : rel_prime (a * a) (b * b)) by (apply rel_prime_sqr; exact Hrp).
    assert (Hbb1 : (b * b | 1)).
    { apply (Gauss (b * b) (a * a) 1).
      - replace (a * a * 1) with (a * a) by ring. exact Hdiv.
      - apply rel_prime_sym; exact Hrpsq. }
    assert (Hb0 : b <> 0).
    { intro Hb0. apply He. rewrite Hb, Hb0. ring. }
    assert (Hbbpos : 0 < b * b) by nia.
    assert (Hle : b * b <= 1) by (apply Z.divide_pos_le; [ lia | exact Hbb1 ]).
    assert (Hbb : b * b = 1) by lia.
    exists a. rewrite Hab, Hbb. ring.
Qed.

(* ===================================================================== *)
(*  The Q decision procedure                                               *)
(* ===================================================================== *)

Open Scope Q_scope.

(** The predicate: x is a perfect square in Q. *)
Definition is_square_Q (x : Q) : Prop := exists s : Q, s * s == x.

(** ★ The decision procedure over Q: reduce to the integer Qnum x * Qden x and decide that. *)
Definition is_square_Q_b (x : Q) : bool :=
  is_square_Z_b (Qnum x * Z.pos (Qden x))%Z.

(** Easy reduction (soundness core): m a Z-square -> x a Q-square. *)
Lemma is_square_Z_to_Q : forall x,
  is_square_Z (Qnum x * Z.pos (Qden x))%Z -> is_square_Q x.
Proof.
  intros x [t Ht]. exists (t # Qden x).
  unfold Qeq, Qmult. simpl. rewrite Pos2Z.inj_mul. rewrite Ht. ring.
Qed.

(** Hard reduction (completeness core): x a Q-square -> m a Z-square.  Via square_quotient. *)
Lemma is_square_Q_to_Z : forall x,
  is_square_Q x -> is_square_Z (Qnum x * Z.pos (Qden x))%Z.
Proof.
  intros x [s Hs].
  unfold Qeq, Qmult in Hs. simpl in Hs. rewrite Pos2Z.inj_mul in Hs.
  apply (square_quotient _ (Z.pos (Qden s))); [ discriminate | ].
  exists (Qnum s * Z.pos (Qden x))%Z.
  transitivity ((Qnum s * Qnum s * Z.pos (Qden x)) * Z.pos (Qden x))%Z.
  - ring.
  - rewrite Hs. ring.
Qed.

(** ★ SOUNDNESS + COMPLETENESS: the Q procedure decides "perfect square in Q". *)
Theorem is_square_Q_reflect : forall x, is_square_Q_b x = true <-> is_square_Q x.
Proof.
  intro x. unfold is_square_Q_b. split.
  - intro H. apply is_square_Z_to_Q. apply is_square_Z_reflect. exact H.
  - intro H. apply is_square_Z_reflect. apply is_square_Q_to_Z. exact H.
Qed.

(* ===================================================================== *)
(*  Concrete DECISIONS over Q (computed + proven verdicts)                 *)
(* ===================================================================== *)

(** ★ 1/4 is DECIDED Element (and is a square: (1/2)^2 = 1/4). *)
Example decide_quarter_element : is_square_Q_b (1 # 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma quarter_is_square : is_square_Q (1 # 4).
Proof. exists (1 # 2). reflexivity. Qed.

(** ★ 1/2 is DECIDED role-limit -- and now PROVEN not a perfect square in Q (sqrt(1/2) is a role-limit),
    via completeness of the procedure (is_square_Q_b (1#2) computes to false). *)
Lemma half_is_role_limit : ~ is_square_Q (1 # 2).
Proof.
  intro H. apply is_square_Q_reflect in H. vm_compute in H. discriminate.
Qed.

(* ===================================================================== *)
(*  Capstone: the finitization boundary is decidable over all of Q         *)
(* ===================================================================== *)

(** The Q-level decidable finitization boundary:
      (★ decision)  is_square_Q_b decides "perfect square in Q" (soundness + completeness);
      (Element)     1/4 is DECIDED Element (true), and (1/2)^2 = 1/4 witnesses it;
      (role-limit)  1/2 is DECIDED role-limit (false) -- and hence PROVEN not a Q-square.
    The finitization boundary, decided over ALL of Q: every rational gets a computed, proven
    Element/role-limit verdict.  1/2 is proven to be on the role-limit side.  Completeness rests on the
    number theory (b^2|a^2 -> b|a), proved here. *)
Theorem decidable_finitization_boundary_Q :
  (forall x, is_square_Q_b x = true <-> is_square_Q x)
  /\ (is_square_Q_b (1 # 4) = true)
  /\ (is_square_Q (1 # 4))
  /\ (~ is_square_Q (1 # 2)).
Proof.
  split; [exact is_square_Q_reflect |].
  split; [exact decide_quarter_element |].
  split; [exact quarter_is_square | exact half_is_role_limit].
Qed.
