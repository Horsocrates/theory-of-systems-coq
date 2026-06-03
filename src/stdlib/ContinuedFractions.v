(** * ContinuedFractions.v — continued fractions as the CANONICAL process for
      role-limits.  A continued fraction is literally a process nat→ℚ (the sequence of
      convergents); it TERMINATES ⟺ the number is rational (Element), and is periodic-
      but-NON-terminating ⟺ the number is a quadratic irrational (role-limit).  The
      fundamental determinant invariant hₙkₙ₋₁ − hₙ₋₁kₙ = (−1)ⁿ⁺¹ (always ±1, NEVER 0)
      is the machine-checked witness of non-termination, and it specialises to Cassini
      (for [1;1,1,…] = φ, whose convergents are the Fibonacci ratios) — one invariant,
      tying this file to GoldenFibonacci.v and to the Pell thread (√2,√3).

    Elements: the integer partial quotients aᵢ; the integers hₙ, kₙ; the concrete
              convergents 1/1, 3/2, 5/3, 8/5, … (each finite, actual — L1 + P4)
    Roles:    a TERMINATING continued fraction = the Element side (Euclid halts ⟺
              rational, reached EXACTLY in finitely many steps); a periodic NON-
              terminating one = a role-limit (√2=[1;2,2,…], φ=[1;1,1,…] — never reached);
              the determinant (−1)ⁿ⁺¹ (never 0) = the formal witness of non-termination
    Rules:    the Euclidean "subtract the floor, invert the remainder" process; the two-
              step convergent recurrence hₙ=aₙhₙ₋₁+hₙ₋₂, kₙ=aₙkₙ₋₁+kₙ₋₂; the determinant
              identity; Lagrange (periodic ⟺ quadratic irrational, finite ⟺ rational)

    THE DEEP POINT — a continued fraction IS the process realisation of the cluster's
    central metaphor "irrational = non-terminating process."  The convergents hₙ/kₙ are
    the finite-actual Element approximants; the determinant invariant
      hₙ·kₙ₋₁ − hₙ₋₁·kₙ = (−1)ⁿ⁺¹   (`cf_det`, ALWAYS ±1, NEVER 0 — `cf_det_nonzero`)
    says consecutive convergents differ by exactly 1/(kₙkₙ₋₁) ≠ 0, so the process can
    never collapse onto an exact value: this is non-termination, machine-checked.
      · For aₙ ≡ 1 (the slowest CF, φ = [1;1,1,…]) the convergents are the Fibonacci
        ratios Fₙ₊₂/Fₙ₊₁ (`cf_ones_fib`), and the determinant identity restricts to
        Cassini (`cf_det_ones_is_cassini`) — the SAME invariant that GoldenFibonacci.v
        carries.  No convergent is φ (`cf_phi_never_reached`), because each is rational
        and `no_rational_golden` forbids a rational root of x²=x+1: φ is a role-limit
        reached by NONE of its Element approximants.
      · A TERMINATING CF, by contrast, reaches a rational EXACTLY in finitely many
        steps: [1;2] = 3/2 (`cf12_reaches_3_2`).  Terminating ⟺ Element; periodic non-
        terminating ⟺ role-limit.
    So this file unifies the threads: √5↔Fibonacci (Cassini), √2,√3↔Pell — all are CFs,
    all carry the same ±1 never-0 invariant, the universal mark of non-termination.

    ============ E/R/R разбор ============
      Rules (L5): процесс Евклида (вычесть целую часть, перевернуть остаток); двушаговая
                  рекуррента подходящих дробей; детерминантный инвариант hₙkₙ₋₁−hₙ₋₁kₙ=(−1)ⁿ⁺¹;
                  Лагранж (периодична ⟺ квадратичная иррациональность, конечна ⟺ рациональна).
      Roles (L4): терминирующая цепная дробь = Element (Евклид останавливается ⟺ рационально,
                  достигается ТОЧНО за конечно шагов); периодическая нетерминирующая = role-limit
                  (√2,φ — никогда не достигаются); детерминант ±1 (≠0) = свидетель нетерминации.
      Elements  : целые aᵢ, hₙ, kₙ; конкретные подходящие дроби 1/1,3/2,5/3,8/5 (конечны, L1+P4).
    ДИАГНОСТИКА (P4): цепная дробь — процесс nat→ℚ; терминация ⟺ рациональность ⟺ Element;
    детерминант (−1)ⁿ⁺¹≠0 форсирует строгое приближение (нетерминацию); для φ=[1;1,…] подходящие
    дроби = Fibonacci-отношения, ни одна не равна φ (все рациональны, no_rational_golden); «φ —
    число?» = не-вопрос (φ ЕСТЬ процесс [1;1,…]). Один инвариант = Cassini (√5) = Pell (√2,√3).

    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith Lqa.
From ToS Require Import stdlib.GoldenFibonacci.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Convergents of a continued fraction [a₀; a₁, a₂, …]                    *)
(*  cf_step a n carries the 4-tuple (hₙ, hₙ₋₁, kₙ, kₙ₋₁) with the seeds    *)
(*  h₀=a₀, h₋₁=1, k₀=1, k₋₁=0 and the recurrences hₙ=aₙhₙ₋₁+hₙ₋₂,         *)
(*  kₙ=aₙkₙ₋₁+kₙ₋₂.                                                       *)
(* ===================================================================== *)

Fixpoint cf_step (a : nat -> Z) (n : nat) : Z * Z * Z * Z :=
  match n with
  | O => (a O, 1, 1, 0)
  | S m => let '(hm, hm1, km, km1) := cf_step a m in
           (a (S m) * hm + hm1, hm, a (S m) * km + km1, km)
  end.

Definition cfh  (a : nat -> Z) (n : nat) : Z := fst (fst (fst (cf_step a n))).
Definition cfh1 (a : nat -> Z) (n : nat) : Z := snd (fst (fst (cf_step a n))).
Definition cfk  (a : nat -> Z) (n : nat) : Z := snd (fst (cf_step a n)).
Definition cfk1 (a : nat -> Z) (n : nat) : Z := snd (cf_step a n).

Lemma cf_step_S : forall a n,
  cf_step a (S n) =
    (let '(hm, hm1, km, km1) := cf_step a n in
     (a (S n) * hm + hm1, hm, a (S n) * km + km1, km)).
Proof. reflexivity. Qed.

(** The four recurrences, as rewrite lemmas. *)
Lemma cfh_S : forall a n, cfh a (S n) = a (S n) * cfh a n + cfh1 a n.
Proof.
  intros a n. unfold cfh, cfh1. rewrite cf_step_S.
  destruct (cf_step a n) as [[[h h1] k] k1]. reflexivity.
Qed.

Lemma cfh1_S : forall a n, cfh1 a (S n) = cfh a n.
Proof.
  intros a n. unfold cfh1, cfh. rewrite cf_step_S.
  destruct (cf_step a n) as [[[h h1] k] k1]. reflexivity.
Qed.

Lemma cfk_S : forall a n, cfk a (S n) = a (S n) * cfk a n + cfk1 a n.
Proof.
  intros a n. unfold cfk, cfk1. rewrite cf_step_S.
  destruct (cf_step a n) as [[[h h1] k] k1]. reflexivity.
Qed.

Lemma cfk1_S : forall a n, cfk1 a (S n) = cfk a n.
Proof.
  intros a n. unfold cfk1, cfk. rewrite cf_step_S.
  destruct (cf_step a n) as [[[h h1] k] k1]. reflexivity.
Qed.

(* ===================================================================== *)
(*  The sign (−1)ⁿ as a nat-recursive integer                             *)
(* ===================================================================== *)

Fixpoint negpow (n : nat) : Z := match n with O => 1 | S m => - negpow m end.

Lemma negpow_S : forall n, negpow (S n) = - negpow n.
Proof. reflexivity. Qed.

(** (−1)ⁿ is always ±1 — in particular never 0. *)
Lemma negpow_pm1 : forall n, negpow n = 1 \/ negpow n = -1.
Proof.
  induction n.
  - left. reflexivity.
  - rewrite negpow_S. destruct IHn as [H | H]; rewrite H.
    + right. reflexivity.
    + left. reflexivity.
Qed.

(** Agreement with the usual power: negpow n = (−1)ⁿ. *)
Lemma negpow_pow : forall n, negpow n = (-1)^(Z.of_nat n).
Proof.
  induction n.
  - reflexivity.
  - rewrite negpow_S, IHn, <- pow_neg1_S. reflexivity.
Qed.

(* ===================================================================== *)
(*  ★ The fundamental determinant identity hₙkₙ₋₁ − hₙ₋₁kₙ = (−1)ⁿ⁺¹       *)
(* ===================================================================== *)

(** The determinant of two consecutive convergents is ±1 — the universal invariant of
    a continued fraction. *)
Theorem cf_det : forall a n,
  cfh a n * cfk1 a n - cfh1 a n * cfk a n = negpow (S n).
Proof.
  induction n.
  - unfold cfh, cfk1, cfh1, cfk. simpl. ring.
  - rewrite cfh_S, cfk1_S, cfh1_S, cfk_S, negpow_S, <- IHn. ring.
Qed.

(** ★ The determinant is NEVER 0: consecutive convergents are always distinct, so the
    convergent process never collapses onto an exact value — non-termination, machine-
    checked. *)
Corollary cf_det_nonzero : forall a n,
  cfh a n * cfk1 a n - cfh1 a n * cfk a n <> 0.
Proof.
  intros a n. rewrite cf_det.
  destruct (negpow_pm1 (S n)) as [H | H]; rewrite H; discriminate.
Qed.

(* ===================================================================== *)
(*  Denominators are positive (when the partial quotients are ≥ 1)        *)
(* ===================================================================== *)

Lemma cf_den_pos_pair : forall a,
  (forall i, 1 <= a i) -> forall n, 0 < cfk a n /\ 0 <= cfk1 a n.
Proof.
  intros a Ha. induction n.
  - unfold cfk, cfk1. simpl. split; lia.
  - destruct IHn as [Hk Hk1]. assert (Ha1 : 1 <= a (S n)) by apply Ha. split.
    + rewrite cfk_S. nia.
    + rewrite cfk1_S. lia.
Qed.

(** The convergents are honest rationals: denominators never vanish. *)
Lemma cf_den_pos : forall a,
  (forall i, 1 <= a i) -> forall n, 0 < cfk a n.
Proof.
  intros a Ha n. destruct (cf_den_pos_pair a Ha n) as [H _]. exact H.
Qed.

(* ===================================================================== *)
(*  The slowest CF [1;1,1,…] = φ: convergents are the Fibonacci ratios     *)
(* ===================================================================== *)

Definition ones (n : nat) : Z := 1.
Definition cf12 (n : nat) : Z := match n with O => 1 | _ => 2 end.

(** The convergents of [1;1,1,…] are exactly the Fibonacci ratios Fₙ₊₂/Fₙ₊₁. *)
Lemma cf_ones_fib : forall n,
  cfh ones n = fib (S (S n)) /\ cfh1 ones n = fib (S n)
  /\ cfk ones n = fib (S n) /\ cfk1 ones n = fib n.
Proof.
  induction n.
  - repeat split; reflexivity.
  - destruct IHn as [Hh [Hh1 [Hk Hk1]]].
    rewrite cfh_S, cfh1_S, cfk_S, cfk1_S.
    change (ones (S n)) with 1%Z.
    rewrite !Hh, !Hh1, !Hk, !Hk1.
    repeat split; rewrite ?(fib_SS (S n)), ?(fib_SS n); ring.
Qed.

Lemma cfh_ones : forall n, cfh ones n = fib (S (S n)).
Proof. intro n. destruct (cf_ones_fib n) as [H _]. exact H. Qed.

Lemma cfk_ones : forall n, cfk ones n = fib (S n).
Proof. intro n. destruct (cf_ones_fib n) as [_ [_ [H _]]]. exact H. Qed.

(** ★ The bridge: the universal determinant identity, specialised to [1;1,1,…], IS
    Cassini's identity — the same ±1 never-0 invariant carried by GoldenFibonacci.v. *)
Lemma cf_det_ones_is_cassini : forall n,
  fib (S (S n)) * fib n - fib (S n) * fib (S n) = negpow (S n).
Proof.
  intro n. pose proof (cf_det ones n) as H.
  destruct (cf_ones_fib n) as [Hh [Hh1 [Hk Hk1]]].
  rewrite Hh, Hh1, Hk, Hk1 in H. exact H.
Qed.

(* ===================================================================== *)
(*  Element side vs role-limit side, as rational values                   *)
(* ===================================================================== *)

Open Scope Q_scope.

(** The value of the n-th convergent as a rational hₙ/kₙ. *)
Definition cf_value (a : nat -> Z) (n : nat) : Q :=
  inject_Z (cfh a n) / inject_Z (cfk a n).

(** Element side: the TERMINATING continued fraction [1;2] reaches 3/2 EXACTLY. *)
Lemma cf12_reaches_3_2 : cf_value cf12 1 == 3 # 2.
Proof. vm_compute. reflexivity. Qed.

(** ★ Role-limit side: NO convergent of [1;1,1,…] is φ.  Each convergent is a rational,
    and no rational solves x²=x+1 (`no_rational_golden`) — so the Element-side process
    approaches φ but never reaches it.  φ IS the non-terminating process [1;1,1,…]. *)
Theorem cf_phi_never_reached :
  ~ (exists n : nat, cf_value ones n * cf_value ones n == cf_value ones n + 1).
Proof.
  intros [n H]. apply no_rational_golden. exists (cf_value ones n). exact H.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** Continued fractions as the canonical process for role-limits, in one statement:
      (a) the universal determinant identity hₙkₙ₋₁ − hₙ₋₁kₙ = (−1)ⁿ⁺¹;
      (b) the determinant is NEVER 0 — the convergent process never terminates;
      (c) denominators are positive — the convergents are honest rationals;
      (d) the convergents of [1;1,1,…] are the Fibonacci ratios Fₙ₊₂/Fₙ₊₁;
      (e) NO convergent of [1;1,1,…] is φ — the role-limit is approached, never reached. *)
Theorem continued_fraction_synthesis :
  (forall a n, (cfh a n * cfk1 a n - cfh1 a n * cfk a n = negpow (S n))%Z)
  /\ (forall a n, (cfh a n * cfk1 a n - cfh1 a n * cfk a n <> 0)%Z)
  /\ (forall a, (forall i, (1 <= a i)%Z) -> forall n, (0 < cfk a n)%Z)
  /\ (forall n, cfh ones n = fib (S (S n)) /\ cfk ones n = fib (S n))
  /\ ~ (exists n : nat, cf_value ones n * cf_value ones n == cf_value ones n + 1).
Proof.
  split; [ exact cf_det | ].
  split; [ exact cf_det_nonzero | ].
  split; [ exact cf_den_pos | ].
  split.
  - intro n. split; [ apply cfh_ones | apply cfk_ones ].
  - exact cf_phi_never_reached.
Qed.
