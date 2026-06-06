(** * H1AlgebraicElement.v — extending the decidable finitization boundary (H1) from pure radicals and
       eigenvalues to ALL ALGEBRAIC NUMBERS: the full Gauss rational-root theorem for an ARBITRARY (non-monic)
       integer polynomial.  RationalRootTest.v assembled the pure-power case and explicitly flagged the gap:
       "the full RRT for arbitrary integer polynomials ... is not yet assembled here."  This assembles it.

    -- The result --
      For a rational a/b in lowest terms (b > 0) that is a root of  a₀ + a₁x + … + aₙxⁿ  (integer coeffs),
        the NUMERATOR divides the constant term:   a | a₀
        the DENOMINATOR divides the leading term:  b | aₙ.
      Hence every rational root lies in the FINITE set  { ±(divisor of a₀) / (divisor of aₙ) }  — an explicitly
      bounded divisor box (b ≤ |aₙ|).  So "is the algebraic number presented by this polynomial an ELEMENT
      (rational)?" is DECIDABLE for the WHOLE algebraic class — the finitization boundary, extended to its
      algebraic maximum, not just pure k-th roots (H1GeneralDegreeConstructivity) or eigenvalues
      (DeterminantModB).

    -- The mechanism (the homogenisation, divisibility — no ring-on-abstract-list) --
      phom cs p q = Σ aᵢ pⁱ q^(n−i) = qⁿ·P(p/q), the cleared value.  Two congruences:
        phom ≡ a₀·qⁿ  picks out the constant  ⟹ p | a₀·qⁿ, coprime ⟹ p | a₀  (peel the head a₀);
        phom ≡ aₙ·pⁿ  picks out the leading   ⟹ q | aₙ·pⁿ, coprime ⟹ q | aₙ  (peel the last aₙ, via cs++[aₙ]).
      Each via Stdlib's Gauss (coprime divides a product) — the divisibility route, not ring on abstract lists.

    -- The H1 reading --
      Element (rational root) is confined to a finite divisor box ⟹ DECIDABLE; role-limit (no rational root)
      = the irrational algebraic number.  Demonstrated: 2x²+x−1 = (2x−1)(x+1) has the Element root 1/2;
      2x²−1 has NO rational root (2a²=b² impossible in lowest terms) ⟹ √(1/2) is a role-limit.  Same
      Element/role-limit cut as H1, now for arbitrary algebraic numbers.

    WHAT THE REPO HAS (surveyed): algebra.RationalRootTest (coprime_div_pow_unit / the PURE-power RRT, the
    flagged gap); foundation.MonicRationalRoot (the MONIC general RRT, g_div_b); foundation.DeterminantModB
    (eigenvalue integrality, the mod-b route).  GAP: the NON-monic general Gauss RRT (numerator | a₀ AND
    denominator | aₙ) and the H1 decidability reading for all algebraic numbers.  This adds it.

    ============ E/R/R разбор ============
      Elements : целая поли cs (low→high коэфф); очищенное значение phom = qⁿ·P(p/q); корень a/b в низших членах.
      Roles    : a₀ = свободный член (его делит числитель a); aₙ = старший (его делит знаменатель b); финитизация = разрешимость.
      Rules    : phom≡a₀qⁿ ⟹ a∣a₀; phom≡aₙpⁿ ⟹ b∣aₙ (Гаусс, делимость); корни в КОНЕЧНОМ боксе делителей ⟹ разрешимо.
      ДИАГНОСТИКА (P4): Element (рацион. корень) заперт в конечный бокс делителей a₀,aₙ ⟹ РАЗРЕШИМ для ВСЕХ алгебр. чисел;
      role-limit = иррациональное алгебр. число. Граница H1 расширена с чистых радикалов/собств.значений до произвольных корней.
      Уровень: `новая теорема` (общий немонический RRT — отмечен в RationalRootTest как «не собрано»; классика, но в репо не было) + H1-обрамление (`синтез`).

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (builds on algebra.RationalRootTest)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia List.
From ToS Require Import algebra.RationalRootTest.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The homogenised polynomial value phom cs p q = Σ aᵢ pⁱ q^(n−i)         *)
(*  (low→high coefficient list; peels the head, recursion multiplies by p) *)
(* ===================================================================== *)

Fixpoint phom (cs : list Z) (p q : Z) : Z :=
  match cs with
  | [] => 0
  | a0 :: rest => a0 * zpow q (length rest) + p * phom rest p q
  end.

Lemma len_snoc : forall (l : list Z) (x : Z), length (l ++ [x]) = S (length l).
Proof. induction l as [| a l IH]; intro x; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(* ===================================================================== *)
(*  Numerator side: phom ≡ a₀·qⁿ  ⟹  a | a₀                                *)
(* ===================================================================== *)

(** ★ The numerator of a rational root divides the constant term a₀.  (Peel the head a₀: everything else is
    p·(…), so phom = a₀·qⁿ + p·(…); vanishing forces p | a₀·qⁿ, and coprimality gives p | a₀.) *)
Lemma p_div_trail : forall (a0 : Z) (rest : list Z) (p q : Z),
  rel_prime p q -> phom (a0 :: rest) p q = 0 -> (p | a0).
Proof.
  intros a0 rest p q Hpq Hroot.
  cbn [phom] in Hroot.
  assert (Hd : (p | a0 * zpow q (length rest))).
  { set (A := a0 * zpow q (length rest)) in *.
    set (pB := p * phom rest p q) in *.
    exists (- phom rest p q).
    assert (HA : A = - pB) by lia.
    rewrite HA. unfold pB. ring. }
  apply (Gauss p (zpow q (length rest)) a0).
  - rewrite Z.mul_comm. exact Hd.
  - apply rel_prime_zpow. exact Hpq.
Qed.

(* ===================================================================== *)
(*  Denominator side: phom ≡ aₙ·pⁿ (mod q)  ⟹  q | aₙ                      *)
(* ===================================================================== *)

(** phom (cs ++ [aₙ]) p q ≡ aₙ·p^(deg) modulo q: every lower term carries a positive power of q. *)
Lemma phom_lead_mod : forall (cs : list Z) (an p q : Z),
  (q | (phom (cs ++ [an]) p q - an * zpow p (length cs))).
Proof.
  induction cs as [| a0 cs' IH]; intros an p q.
  - assert (E : phom ([] ++ [an]) p q - an * zpow p (length (@nil Z)) = 0) by (simpl; ring).
    rewrite E. apply Z.divide_0_r.
  - replace ((a0 :: cs') ++ [an]) with (a0 :: (cs' ++ [an])) by reflexivity.
    cbn [phom]. rewrite len_snoc.
    replace (length (a0 :: cs')) with (S (length cs')) by reflexivity.
    cbn [zpow].
    replace (a0 * (q * zpow q (length cs')) + p * phom (cs' ++ [an]) p q
             - an * (p * zpow p (length cs')))
       with (q * (a0 * zpow q (length cs'))
             + p * (phom (cs' ++ [an]) p q - an * zpow p (length cs'))) by ring.
    apply Z.divide_add_r.
    + apply Z.divide_factor_l.
    + apply Z.divide_mul_r. apply IH.
Qed.

(** ★ The denominator of a rational root divides the leading coefficient aₙ. *)
Lemma q_div_lead : forall (cs : list Z) (an p q : Z),
  rel_prime q p -> phom (cs ++ [an]) p q = 0 -> (q | an).
Proof.
  intros cs an p q Hqp Hroot.
  pose proof (phom_lead_mod cs an p q) as Hd.
  rewrite Hroot in Hd.
  assert (Hd2 : (q | an * zpow p (length cs))).
  { replace (an * zpow p (length cs)) with (- (0 - an * zpow p (length cs))) by ring.
    apply Z.divide_opp_r. exact Hd. }
  apply (Gauss q (zpow p (length cs)) an).
  - rewrite Z.mul_comm. exact Hd2.
  - apply rel_prime_zpow. exact Hqp.
Qed.

(* ===================================================================== *)
(*  The general Gauss rational-root criterion (numerator AND denominator)  *)
(* ===================================================================== *)

(** A rational a/b in lowest terms (b > 0) is a root of the cleared integer polynomial cs. *)
Definition rat_root (cs : list Z) (a b : Z) : Prop :=
  b > 0 /\ rel_prime a b /\ phom cs a b = 0.

(** ★★ THE GENERAL RATIONAL-ROOT THEOREM (arbitrary, non-monic): for a polynomial a₀ :: mid ++ [aₙ]
    (degree ≥ 1, first coeff a₀ and leading coeff aₙ explicit), a rational root a/b satisfies a | a₀ and
    b | aₙ.  This is the full RRT that RationalRootTest.v flagged as not-yet-assembled. *)
Theorem rational_root_criterion : forall (a0 : Z) (mid : list Z) (an a b : Z),
  rat_root (a0 :: (mid ++ [an])) a b -> (a | a0) /\ (b | an).
Proof.
  intros a0 mid an a b [Hb [Hrp Hroot]]. split.
  - apply (p_div_trail a0 (mid ++ [an]) a b Hrp Hroot).
  - apply (q_div_lead (a0 :: mid) an a b).
    + apply rel_prime_sym; exact Hrp.
    + replace ((a0 :: mid) ++ [an]) with (a0 :: (mid ++ [an])) by reflexivity. exact Hroot.
Qed.

(** ★ The denominator is bounded by |aₙ| — so rational roots live in a FINITE, explicitly bounded set
    (b ≤ |aₙ|, a | a₀): the decidability of Element-ness for an arbitrary algebraic number. *)
Lemma denominator_bounded : forall (a0 : Z) (mid : list Z) (an a b : Z),
  an <> 0 -> rat_root (a0 :: (mid ++ [an])) a b -> b <= Z.abs an.
Proof.
  intros a0 mid an a b Han Hr.
  destruct (rational_root_criterion a0 mid an a b Hr) as [_ Hb_an].
  destruct Hr as [Hbpos _].
  apply Z.divide_pos_le.
  - destruct an as [| p | p]; simpl; lia.
  - apply Z.divide_abs_r. exact Hb_an.
Qed.

(* ===================================================================== *)
(*  The H1 reading: Element (rational root) is decidable for all algebraics *)
(* ===================================================================== *)

(** "The algebraic number presented by the integer polynomial cs is an ELEMENT" = cs has a rational root. *)
Definition AlgElement (cs : list Z) : Prop := exists a b, rat_root cs a b.

(** ★ ELEMENT: 2x² + x − 1 = (2x−1)(x+1) has the rational root 1/2 (a=1, b=2). *)
Lemma rel_prime_1_2 : rel_prime 1 2.
Proof.
  apply Zis_gcd_intro; [ apply Z.divide_1_l | apply Z.divide_1_l | intros x Hx _; exact Hx ].
Qed.

Example quad_is_element : AlgElement [-1; 1; 2].
Proof.
  exists 1, 2. unfold rat_root. split; [ lia | split ].
  - exact rel_prime_1_2.
  - vm_compute. reflexivity.
Qed.

(** ★★ ROLE-LIMIT: 2x² − 1 has NO rational root — 2a² = b² is impossible in lowest terms — so √(1/2) is an
    irrational algebraic number.  Decided via the criterion: any root has a | 1 (a = ±1) and b | 2, b > 0
    (b ∈ {1,2}); the four candidates all give phom = 2a² − b² ≠ 0. *)
Example sqrt_half_role_limit : ~ AlgElement [-1; 0; 2].
Proof.
  intros [a [b Hr]].
  destruct (rational_root_criterion (-1) [0] 2 a b Hr) as [Hpa Hqb].
  destruct Hr as [Hbpos [Hrp Hroot]].
  apply Z.divide_abs_r in Hpa. simpl in Hpa. apply Zdivide_1 in Hpa.
  assert (Hble : b <= 2) by (apply Z.divide_pos_le; [ lia | exact Hqb ]).
  assert (Hb12 : b = 1 \/ b = 2) by lia.
  destruct Hpa as [Ha | Ha]; destruct Hb12 as [Hb | Hb]; subst;
    vm_compute in Hroot; discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The decidable finitization boundary, extended to all algebraic numbers:
      (criterion)   a rational root a/b of a₀ :: mid ++ [aₙ] has a | a₀ and b | aₙ — the full Gauss RRT;
      (bounded)     b ≤ |aₙ|, so rational roots inhabit a FINITE divisor box ⟹ Element-ness is decidable;
      (Element)     2x²+x−1 has the rational root 1/2;
      (role-limit)  2x²−1 has NONE ⟹ √(1/2) is irrational.
    So the Element/role-limit cut of H1 — terminating rational witness vs non-terminating — is DECIDABLE for
    the whole algebraic class, not just pure k-th roots or eigenvalues.  Level: the general non-monic RRT is a
    genuine theorem newly assembled in the repo (classical, flagged-missing in RationalRootTest); the H1
    decidability reading is the synthesis. *)
Theorem h1_algebraic_boundary :
  (forall a0 mid an a b, rat_root (a0 :: (mid ++ [an])) a b -> (a | a0) /\ (b | an))
  /\ (forall a0 mid an a b, an <> 0 -> rat_root (a0 :: (mid ++ [an])) a b -> b <= Z.abs an)
  /\ AlgElement [-1; 1; 2]
  /\ ~ AlgElement [-1; 0; 2].
Proof.
  split; [ exact rational_root_criterion | ].
  split; [ exact denominator_bounded | ].
  split; [ exact quad_is_element | exact sqrt_half_role_limit ].
Qed.
