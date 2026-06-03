(** * BaseExpansion.v — positional base-b expansions and the rational ⟺ terminating-or-
      periodic dichotomy.  A terminating or eventually-periodic base-b expansion is rational
      (Element, via the geometric-series sum: 0.(3)=1/3, 0.(142857)=1/7); an aperiodic
      expansion is irrational (role-limit: √2's base-10 expansion never terminates).  This
      is the base-b parallel of ContinuedFractions.v (terminating CF ⟺ rational) and
      SternBrocot.v (terminating path ⟺ rational) — the cluster's "terminating process ⟺
      Element" theme on decimal expansions.

    Elements: the rational values 1/3=0.(3), 1/7=0.(142857), 1/11=0.(09); the geometric-sum
              identity (L1 + P4)
    Roles:    Element side = TERMINATING or eventually-PERIODIC expansions = rationals
              (d/(b^L−1) or p/b^k — finite-actual rational values; the geometric sum closes);
              role-limit = APERIODIC expansions = irrationals (√2's base-10 expansion never
              terminates / periodizes)
    Rules:    the geometric series 1+b+…+b^{n−1} = (b^n−1)/(b−1); a period-L block d has value
              d/(b^L−1); a terminating expansion is p/b^k

    THE DEEP POINT — a base-b expansion is a process (nat→digit), and terminating/periodic ⟺
    rational ⟺ Element, exactly as for continued fractions and Stern–Brocot paths.  The
    algebraic backbone is the geometric-series identity (b−1)·(1+b+…+b^{n−1}) = b^n−1
    (`geom_sum`), which makes a periodic block 0.(d) of length L equal the rational
    d/(b^L−1): 0.(3)=3/9=1/3, 0.(09)=9/99=1/11, 0.(142857)=142857/999999=1/7
    (`repeating_third`, `repeating_eleventh`, `repeating_seventh`).  A terminating expansion
    of length k is p/b^k, also rational.  Both are Element-side.  But √2 has NO terminating
    base-10 expansion (`sqrt2_no_finite_expansion`): a terminating expansion p/10^k is
    rational, and √2 is not (`no_rational_sqrt2`).  So √2's base-b expansion is a non-
    terminating, aperiodic process — a role-limit, never a finite rational p/b^k.  Element =
    the periodic/terminating expansions (the rationals); role-limit = the aperiodic boundary
    (the irrationals, e.g. √2).

    ============ E/R/R разбор ============
      Rules (L5): геометрическая сумма 1+b+…+b^{n−1}=(b^n−1)/(b−1); период-L блок d = d/(b^L−1);
                  терминирующее разложение = p/b^k.
      Roles (L4): Element = терминирующие/периодические разложения = рациональные (геом. сумма замыкается);
                  role-limit = апериодические = иррациональные (разложение √2 не терминирует).
      Elements  : рац. значения 1/3,1/7,1/11; тождество геометрической суммы (L1+P4).
    ДИАГНОСТИКА (P4): разложение = процесс nat→цифра; терминирующее/периодическое ⟺ рационально (Element);
    апериодическое ⟺ иррационально (role-limit). Параллель ContinuedFractions/SternBrocot; √2 = нетерминирующий
    процесс, нет p/10^k.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The geometric-series backbone: (b−1)·(1+b+…+b^{n−1}) = b^n − 1         *)
(* ===================================================================== *)

(** b^n. *)
Fixpoint bpow (b : Z) (n : nat) : Z := match n with O => 1 | S m => b * bpow b m end.

(** 1 + b + b² + … + b^{n−1} (Horner form). *)
Fixpoint gsum (b : Z) (n : nat) : Z := match n with O => 0 | S m => 1 + b * gsum b m end.

Lemma gsum_S : forall (b : Z) (n : nat), gsum b (S n) = 1 + b * gsum b n.
Proof. reflexivity. Qed.

Lemma bpow_S : forall (b : Z) (n : nat), bpow b (S n) = b * bpow b n.
Proof. reflexivity. Qed.

(** ★ The geometric-series identity: (b−1)·(1+b+…+b^{n−1}) = b^n − 1.  This makes a periodic
    block 0.(d) of length L equal the rational d/(b^L−1) — the rationality of periodic
    expansions. *)
Lemma geom_sum : forall (b : Z) (n : nat), (b - 1) * gsum b n = bpow b n - 1.
Proof.
  intros b. induction n.
  - simpl. ring.
  - rewrite gsum_S, bpow_S.
    assert (Hgoal : (b - 1) * (1 + b * gsum b n)
                    = (b - 1) + b * ((b - 1) * gsum b n)) by ring.
    rewrite Hgoal, IHn. ring.
Qed.

(* ===================================================================== *)
(*  Element: periodic expansions are rational                            *)
(* ===================================================================== *)

Open Scope Q_scope.

(** 0.(3) = 3/9 = 1/3 in base 10. *)
Lemma repeating_third : 1 # 3 == 3 # 9.
Proof. vm_compute. reflexivity. Qed.

(** 0.(09) = 9/99 = 1/11. *)
Lemma repeating_eleventh : 1 # 11 == 9 # 99.
Proof. vm_compute. reflexivity. Qed.

(** 0.(142857) = 142857/999999 = 1/7. *)
Lemma repeating_seventh : 1 # 7 == 142857 # 999999.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: √2 has no terminating base-10 expansion                  *)
(* ===================================================================== *)

(** ★ √2 has no terminating base-10 expansion: a terminating expansion of length k is the
    rational p/10^k, and no rational squares to 2 (`no_rational_sqrt2`).  So √2's base-b
    expansion is a non-terminating, aperiodic process — a role-limit. *)
Theorem sqrt2_no_finite_expansion : forall (p : Z) (k : nat),
  ~ ((inject_Z p / inject_Z (bpow 10 k)) * (inject_Z p / inject_Z (bpow 10 k)) == 2).
Proof. intros p k. exact (no_rational_sqrt2 _). Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Base-b expansions, split by the finitization boundary:
      (a) the geometric-series identity (b−1)·(1+…+b^{n−1}) = b^n−1 (the backbone of
          periodic-expansion rationality);
      (b) periodic expansions are rational (1/3=0.(3), 1/11=0.(09), 1/7=0.(142857));
      (c) ROLE-LIMIT — √2 has no terminating base-10 expansion (aperiodic, irrational). *)
Theorem base_expansion_synthesis :
  (forall (b : Z) (n : nat), ((b - 1) * gsum b n = bpow b n - 1)%Z)
  /\ (1 # 3 == 3 # 9 /\ 1 # 11 == 9 # 99 /\ 1 # 7 == 142857 # 999999)
  /\ (forall (p : Z) (k : nat),
        ~ ((inject_Z p / inject_Z (bpow 10 k)) * (inject_Z p / inject_Z (bpow 10 k)) == 2)).
Proof.
  split; [ exact geom_sum | ].
  split.
  - split; [ exact repeating_third | split; [ exact repeating_eleventh | exact repeating_seventh ] ].
  - exact sqrt2_no_finite_expansion.
Qed.
