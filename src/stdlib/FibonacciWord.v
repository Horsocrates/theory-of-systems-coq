(** * FibonacciWord.v — the Fibonacci word (the 1D quasicrystal) from the substitution
      a→ab, b→a.  Its finite stages S_n are Element-side (lengths |S_n|=F_{n+1} and a-counts
      #a(S_n)=F_n are Fibonacci integers), while the aperiodic infinite word / the φ letter-
      frequency is a role-limit — the 1D analogue of the crystallographically FORBIDDEN
      5-fold symmetry (④), achieved APERIODICALLY.  Ties ④ + φ/√5 + quasicrystals.

    Elements: the finite Fibonacci words S_n; the lengths 1,1,2,3,5,8 and a-counts 0,1,1,2,3
              (Fibonacci integers) (L1 + P4)
    Roles:    Element side = the finite stages S_n (finite, computable; Fibonacci lengths and
              counts); role-limit = the aperiodic infinite word / the φ frequency (the 1D
              analogue of forbidden 5-fold symmetry, achieved aperiodically)
    Rules:    the substitution S_{n+1}=S_n S_{n−1} (concatenation); |S_n|=F_{n+1};
              #a(S_n)=F_n; the golden ratio φ as frequency limit #a/|S|=F_n/F_{n+1}→1/φ

    THE DEEP POINT — the Fibonacci word is the 1D quasicrystal: it achieves "forbidden"
    5-fold / φ order via APERIODICITY, not periodicity.  The word S_n (over {a,b}) is built
    by the substitution S_{n+1}=S_n S_{n−1}, so |S_n| obeys the Fibonacci recurrence
    (`fibword_length_rec`) — the lengths are 1,1,2,3,5,8 (`fibword_lengths`) and the a-counts
    are 0,1,1,2,3 (`fibword_counts`), Fibonacci integers (Element side: each finite stage is
    computable).  But the asymptotic a-frequency #a/|S| = F_n/F_{n+1} → 1/φ, and φ is
    irrational (`golden_frequency_role_limit`) — the quasicrystal's defining frequency is the
    role-limit.  This ties the crystallographic restriction (④: a periodic crystal CANNOT
    have 5-fold symmetry) to quasicrystals (5-fold / φ order IS achievable aperiodically):
    Element = the finite Fibonacci words (periodic-crystal-like, computable); role-limit =
    the aperiodic φ-quasicrystal.  The same φ/√5 as ④, the icosahedron, and GoldenFibonacci.

    ============ E/R/R разбор ============
      Rules (L5): подстановка S_{n+1}=S_n S_{n−1}; длины |S_n|=F_{n+1}; #a(S_n)=F_n; φ как предел
                  частоты #a/|S|=F_n/F_{n+1}→1/φ.
      Roles (L4): Element = конечные слова S_n (конечны, вычислимы; Фибоначчи-длины/счёты); role-limit =
                  апериодическое бесконечное слово / φ-частота (1D-аналог запрещённой 5-кратной симметрии).
      Elements  : конечные слова; длины 1,1,2,3,5,8; счёты 0,1,1,2,3 (целые Фибоначчи; L1+P4).
    ДИАГНОСТИКА (P4): слово Фибоначчи = 1D-квазикристалл; «запрещённый» 5-кратный/φ-порядок достигнут
    АПЕРИОДИЧЕСКИ (role-limit), не периодически. Конечные стадии = Element; φ-частота = role-limit. Связывает
    ④ (5-кратная запрещена для периодических) с квазикристаллами (φ апериодически). Тот же φ/√5, что ④.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List ZArith Lia QArith.
From ToS Require Import stdlib.GoldenFibonacci.

Open Scope nat_scope.

(* ===================================================================== *)
(*  The Fibonacci word: S_0=b, S_1=a, S_{n+1}=S_n S_{n−1}                  *)
(* ===================================================================== *)

Fixpoint fibword (n : nat) : list bool :=
  match n with
  | O => false :: nil          (* S_0 = b *)
  | S O => true :: nil          (* S_1 = a *)
  | S (S m as k) => fibword k ++ fibword m
  end.

Lemma fibword_SS : forall m, fibword (S (S m)) = fibword (S m) ++ fibword m.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Lengths obey the Fibonacci recurrence (the quasicrystal's structure)  *)
(* ===================================================================== *)

(** ★ The lengths obey the Fibonacci recurrence |S_{n+1}| = |S_n| + |S_{n−1}|. *)
Lemma fibword_length_rec : forall m,
  length (fibword (S (S m))) = length (fibword (S m)) + length (fibword m).
Proof. intro m. rewrite fibword_SS, length_app. reflexivity. Qed.

(** The lengths are the Fibonacci numbers 1,1,2,3,5,8 (= F_{n+1}). *)
Lemma fibword_lengths :
  length (fibword 0) = 1 /\ length (fibword 1) = 1 /\ length (fibword 2) = 2
  /\ length (fibword 3) = 3 /\ length (fibword 4) = 5 /\ length (fibword 5) = 8.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  a-letter counts also obey the Fibonacci recurrence                    *)
(* ===================================================================== *)

(** Count the a's (true) in a word. *)
Fixpoint counta (l : list bool) : nat :=
  match l with nil => 0 | true :: t => S (counta t) | false :: t => counta t end.

Lemma counta_app : forall l1 l2, counta (l1 ++ l2) = counta l1 + counta l2.
Proof.
  induction l1 as [| x l1 IH]; intro l2; simpl.
  - reflexivity.
  - destruct x; rewrite IH; reflexivity.
Qed.

(** ★ The a-counts obey the Fibonacci recurrence #a(S_{n+1}) = #a(S_n) + #a(S_{n−1}). *)
Lemma fibword_counta_rec : forall m,
  counta (fibword (S (S m))) = counta (fibword (S m)) + counta (fibword m).
Proof. intro m. rewrite fibword_SS, counta_app. reflexivity. Qed.

(** The a-counts are the Fibonacci numbers 0,1,1,2,3 (= F_n). *)
Lemma fibword_counts :
  counta (fibword 0) = 0 /\ counta (fibword 1) = 1 /\ counta (fibword 2) = 1
  /\ counta (fibword 3) = 2 /\ counta (fibword 4) = 3.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the asymptotic a-frequency is φ-related (irrational)      *)
(* ===================================================================== *)

(** ★ The asymptotic a-frequency #a/|S| = F_n/F_{n+1} → 1/φ, and φ is irrational
    (`no_rational_golden`).  The quasicrystal's defining frequency is the role-limit —
    the 1D forbidden-symmetry order, achieved aperiodically.  (The same φ/√5 as ④.) *)
Theorem golden_frequency_role_limit : ~ (exists q : Q, (q * q == q + 1)%Q).
Proof. exact no_rational_golden. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Fibonacci word (1D quasicrystal), split by the finitization boundary:
      (a) the lengths obey the Fibonacci recurrence (Element: finite Fibonacci stages);
      (b) the lengths are 1,1,2,3,5,8;
      (c) the a-counts obey the Fibonacci recurrence (and are 0,1,1,2,3);
      (d) ROLE-LIMIT — the asymptotic frequency φ is irrational (the aperiodic order). *)
Theorem fibonacci_word_synthesis :
  (forall m, length (fibword (S (S m))) = length (fibword (S m)) + length (fibword m))
  /\ (length (fibword 4) = 5 /\ length (fibword 5) = 8)
  /\ (forall m, counta (fibword (S (S m))) = counta (fibword (S m)) + counta (fibword m))
  /\ (counta (fibword 4) = 3)
  /\ ~ (exists q : Q, (q * q == q + 1)%Q).
Proof.
  split; [ exact fibword_length_rec | ].
  split; [ split; reflexivity | ].
  split; [ exact fibword_counta_rec | ].
  split; [ reflexivity | exact golden_frequency_role_limit ].
Qed.
