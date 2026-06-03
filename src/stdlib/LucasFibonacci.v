(** * LucasFibonacci.v — the Lucas numbers and the √5 Pell form L_n²−5F_n²=4(−1)ⁿ.  The
      Lucas–Fibonacci pair is the integer solution sequence of the "Pell equation for √5"
      (the ℤ[φ] norm form), and L_n/F_n → √5 with error ±4 that is NEVER 0 — so √5 is a
      role-limit.  This completes the surd–Pell triple: √2↔(x²−2y²=±1) (FinitistQM),
      √3↔(x²−3y²=1) (Sqrt3Pell), √5↔(L²−5F²=±4) (here); a companion to GoldenFibonacci's
      φ-Cassini.

    Elements: the integer Lucas numbers L_n = 2,1,3,4,7,11,…; the Fibonacci F_n; the value
              ±4 (L1 + P4)
    Roles:    Element side = the Lucas/Fibonacci integers (the finite-actual solutions of
              the √5 Pell equation L²−5F²=±4); role-limit = √5 itself (L_n/F_n → √5, error
              ±4/F_n² never 0)
    Rules:    the Lucas recurrence L_{n+2}=L_{n+1}+L_n; the closed form L_n=2F_{n+1}−F_n;
              Cassini F_{n+1}²−F_nF_{n+2}=(−1)ⁿ; the identity L_n²−5F_n²=4(−1)ⁿ

    THE DEEP POINT — the Lucas–Fibonacci pair solves the √5 Pell equation, and √5 is the
    role-limit it approximates but never reaches.  With L_n = 2F_{n+1}−F_n (closed form,
    no negative index), the √5 norm identity
        L_n² − 5·F_n² = 4·(−1)ⁿ     (`lucas_fib_identity`)
    follows DIRECTLY from Cassini: L_n²−5F_n² = 4·(F_{n+1}²−F_{n+1}F_n−F_n²)
    = 4·(F_{n+1}²−F_n·F_{n+2}) = 4·(−1)ⁿ.  This is the ℤ[φ] norm form / the "Pell equation
    for √5".  The error is always ±4, NEVER 0 (`lucas_fib_never_5`), so (L_n/F_n)²−5 =
    ±4/F_n² ≠ 0: L_n/F_n approximates √5 but never equals it — √5 is a role-limit, the non-
    terminating process L/F (the same √5 as φ, the icosahedron ④, and GoldenFibonacci).
    Element = the integer Lucas/Fibonacci solutions; role-limit = √5.  This completes the
    surd–Pell triple √2/√3/√5, each surd the role-limit of an integer Pell/norm-form process.

    ============ E/R/R разбор ============
      Rules (L5): рекуррента Люка L_{n+2}=L_{n+1}+L_n; замкнутая форма L_n=2F_{n+1}−F_n; Кассини
                  F_{n+1}²−F_nF_{n+2}=(−1)ⁿ; тождество L_n²−5F_n²=4(−1)ⁿ.
      Roles (L4): Element = целые Люка/Фибоначчи (решения уравнения Пелля для √5 L²−5F²=±4); role-limit
                  = √5 (L_n/F_n→√5, ошибка ±4/F_n² никогда не 0).
      Elements  : целые L_n=2,1,3,4,7; F_n; значение ±4 (L1+P4).
    ДИАГНОСТИКА (P4): пара Люка–Фибоначчи = целочисл. решения Pell-формы для √5; L/F→√5, ошибка ±4 никогда
    не 0 ⟹ √5 role-limit. Завершает триаду √2/√3/√5↔Pell/норм-формы; параллель φ-Кассини; тот же √5, что ④.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import stdlib.GoldenFibonacci.
From ToS Require Import analysis.Sqrt5Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Lucas numbers via the closed form L_n = 2·F_{n+1} − F_n               *)
(* ===================================================================== *)

Definition lucas (n : nat) : Z := 2 * fib (S n) - fib n.

(** The Lucas numbers: 2, 1, 3, 4, 7, 11, … *)
Lemma lucas_values :
  lucas 0 = 2 /\ lucas 1 = 1 /\ lucas 2 = 3 /\ lucas 3 = 4 /\ lucas 4 = 7.
Proof. repeat split; reflexivity. Qed.

(** lucas satisfies the Lucas recurrence L_{n+2} = L_{n+1} + L_n. *)
Lemma lucas_SS : forall n, lucas (S (S n)) = lucas (S n) + lucas n.
Proof.
  intro n. unfold lucas. rewrite (fib_SS (S n)), (fib_SS n). ring.
Qed.

(* ===================================================================== *)
(*  ★ The √5 Pell form: L_n² − 5·F_n² = 4·(−1)ⁿ                            *)
(* ===================================================================== *)

(** ★ The √5 norm identity (the "Pell equation for √5", the ℤ[φ] norm form): it follows
    directly from Cassini, since L_n=2F_{n+1}−F_n gives L_n²−5F_n²=4(F_{n+1}²−F_n·F_{n+2}). *)
Theorem lucas_fib_identity : forall n,
  lucas n * lucas n - 5 * (fib n * fib n) = 4 * (-1)^(Z.of_nat n).
Proof.
  intro n. unfold lucas.
  pose proof (cassini n) as HC.
  rewrite (fib_SS n) in HC.
  nia.
Qed.

(** ★ The error is always ±4, NEVER 0: so (L_n/F_n)²−5 = ±4/F_n² ≠ 0 — L_n/F_n approximates
    √5 but never reaches it (√5 is a role-limit, the non-terminating process L/F). *)
Theorem lucas_fib_never_5 : forall n,
  lucas n * lucas n - 5 * (fib n * fib n) <> 0.
Proof.
  intro n. rewrite lucas_fib_identity.
  destruct (pow_neg1_pm1 n) as [H | H]; rewrite H; lia.
Qed.

(* ===================================================================== *)
(*  Role-limit: √5 itself is irrational                                  *)
(* ===================================================================== *)

(** √5 — the limit of L_n/F_n — is irrational (the role-limit; the same √5 as φ and the
    icosahedron ④). *)
Theorem sqrt5_role_limit : ~ (exists r : Q, (r * r == 5)%Q).
Proof. exact sqrt5_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Lucas–Fibonacci √5 Pell form, split by the finitization boundary:
      (a) the Lucas numbers (2,1,3,4,7) and the Lucas recurrence;
      (b) ★ the √5 Pell form L_n²−5F_n²=4(−1)ⁿ (the integer solution sequence);
      (c) the error is never 0 — L_n/F_n approximates √5 but never reaches it;
      (d) ROLE-LIMIT — √5 is irrational. *)
Theorem lucas_fibonacci_synthesis :
  (forall n, (lucas (S (S n)) = lucas (S n) + lucas n)%Z)
  /\ (forall n, (lucas n * lucas n - 5 * (fib n * fib n) = 4 * (-1)^(Z.of_nat n))%Z)
  /\ (forall n, (lucas n * lucas n - 5 * (fib n * fib n) <> 0)%Z)
  /\ ~ (exists r : Q, (r * r == 5)%Q).
Proof.
  split; [ exact lucas_SS | ].
  split; [ exact lucas_fib_identity | ].
  split; [ exact lucas_fib_never_5 | exact sqrt5_role_limit ].
Qed.
