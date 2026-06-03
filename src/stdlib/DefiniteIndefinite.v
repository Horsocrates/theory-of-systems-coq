(** * DefiniteIndefinite.v — the SIGNATURE of a binary quadratic form decides
      universality: the DEFINITE form x²+y² is SELECTIVE (n ≡ 3 mod 4 is never a sum
      of two squares — a role-limit family), while the INDEFINITE form x²−y² is
      UNIVERSAL (it represents EVERY rational — always an Element).

    Elements: the representable n; the mod-4 residues; the witness ((n+1)/2,(n−1)/2)
              (L1 + P4)
    Roles:    the definite form x²+y² = SELECTIVE (n ≡ 3 mod 4 = a role-limit family,
              no representation) vs the indefinite form x²−y² = UNIVERSAL (represents
              every n, always an Element); the signature decides universality
    Rules:    squares mod 4 ∈ {0,1}; a sum of two squares is never ≡ 3 mod 4 (the
              local obstruction); the indefinite form x²−y² = (x−y)(x+y) factors;
              the signature (definite +,+ vs indefinite +,−)

    THE DEEP POINT — whether a quadratic form represents everything (always Element)
    or is selective (role-limit values) is decided by its SIGNATURE.  This completes
    and generalises `SumTwoSquares.v`.  The DEFINITE form x²+y² is selective: squares
    mod 4 are 0 or 1, so a sum of two squares is ≡ 0, 1 or 2 mod 4 — NEVER 3
    (`sum_two_sq_mod4`).  Hence every n ≡ 3 mod 4 (3, 7, 11, 19, …) is NOT a sum of
    two integer squares (`n3mod4_not_sum`) — a whole role-limit family, the local
    (mod-4) obstruction.  By contrast the INDEFINITE form x²−y² is UNIVERSAL: for any
    rational n, take x=(n+1)/2, y=(n−1)/2, then x²−y² = n (`difference_universal`) —
    every rational is a difference of two rational squares, no exceptions, always an
    Element.  The indefinite form factors as (x−y)(x+y), so representing n is just
    factoring n; the definite form cannot factor over ℚ and inherits a local
    obstruction.  So the SIGNATURE of the form is the Element/role-limit dial: a
    definite form is selective (has role-limit values), an indefinite form is
    universal (all values Element) — the local–global / Hasse-principle flavour, where
    indefinite forms satisfy it trivially and definite forms have local obstructions.

    ============ E/R/R разбор ============
      Rules (L5): квадраты mod 4 ∈{0,1}; сумма двух квадратов mod 4 ≠3; x²−y²=(x−y)(x+y);
                  сигнатура (определённая +,+ vs неопределённая +,−).
      Roles (L4): определённая x²+y² = селективна (n≡3 mod4 = role-limit-семья) vs
                  неопределённая x²−y² = универсальна (каждое n, Element); сигнатура решает.
      Elements  : представимые n; mod-4-вычеты; свидетель (n+1)/2,(n−1)/2 (L1+P4).
    ДИАГНОСТИКА (P4): сигнатура решает Element/role-limit-универсальность — определённая форма
    селективна (n≡3 mod4 role-limit, локальная обструкция), неопределённая универсальна (всё Element,
    факторизуется). Привкус Хассе: неопределённые формы универсальны, определённые имеют локальные обструкции.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The DEFINITE form x²+y² is selective: never ≡ 3 mod 4          *)
(* ================================================================= *)

Lemma sq_mod4 : forall n : Z, (n*n) mod 4 = 0 \/ (n*n) mod 4 = 1.
Proof.
  intro n. rewrite (Z.mul_mod n n 4) by lia.
  pose proof (Z.mod_pos_bound n 4 ltac:(lia)) as Hb.
  destruct (Z.eq_dec (n mod 4) 0) as [E | N0]. { rewrite E. left. reflexivity. }
  destruct (Z.eq_dec (n mod 4) 1) as [E | N1]. { rewrite E. right. reflexivity. }
  destruct (Z.eq_dec (n mod 4) 2) as [E | N2]. { rewrite E. left. reflexivity. }
  assert (E3 : n mod 4 = 3) by lia. rewrite E3. right. reflexivity.
Qed.

(** ★ A sum of two squares is never ≡ 3 mod 4 (the local obstruction). *)
Lemma sum_two_sq_mod4 : forall a b : Z, (a*a + b*b) mod 4 <> 3.
Proof.
  intros a b. rewrite (Z.add_mod (a*a) (b*b) 4) by lia.
  destruct (sq_mod4 a) as [Ha | Ha]; destruct (sq_mod4 b) as [Hb | Hb];
    rewrite Ha, Hb; discriminate.
Qed.

(** Hence every n ≡ 3 mod 4 (3, 7, 11, …) is NOT a sum of two integer squares — a
    whole role-limit family. *)
Theorem n3mod4_not_sum : forall n a b : Z, n mod 4 = 3 -> a*a + b*b <> n.
Proof.
  intros n a b Hn Heq. apply (sum_two_sq_mod4 a b). rewrite Heq. exact Hn.
Qed.

(* ================================================================= *)
(** ** The INDEFINITE form x²−y² is universal: it represents every n  *)
(* ================================================================= *)

Open Scope Q_scope.

(** ★ Every rational is a difference of two rational squares: x=(n+1)/2, y=(n−1)/2
    give x²−y²=n.  The indefinite form is UNIVERSAL — always an Element, no
    obstruction. *)
Theorem difference_universal : forall n : Q, exists x y : Q, x*x - y*y == n.
Proof.
  intro n. exists ((n+1)*(1#2)), ((n-1)*(1#2)). ring.
Qed.

(* ================================================================= *)
(** ** Synthesis                                                      *)
(* ================================================================= *)

(** The signature decides universality:
      (a) a sum of two squares is never ≡ 3 mod 4 (the definite form's local
          obstruction);
      (b) so every n ≡ 3 mod 4 is NOT a sum of two squares — the definite form is
          SELECTIVE (a role-limit family);
      (c) but every rational IS a difference of two squares — the indefinite form is
          UNIVERSAL (always an Element). *)
Theorem definite_indefinite_synthesis :
  (forall a b : Z, ((a*a + b*b) mod 4 <> 3)%Z)
  /\ (forall n a b : Z, (n mod 4 = 3)%Z -> (a*a + b*b <> n)%Z)
  /\ (forall n : Q, exists x y : Q, x*x - y*y == n).
Proof.
  split; [ exact sum_two_sq_mod4 | ].
  split; [ exact n3mod4_not_sum | exact difference_universal ].
Qed.
