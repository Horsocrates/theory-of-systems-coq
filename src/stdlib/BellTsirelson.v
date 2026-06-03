(** * BellTsirelson.v — Bell / CHSH and the Tsirelson bound over ℚ: the nonlocal
      VIOLATION is rational (an Element), only the MAXIMUM 2√2 is a role-limit.

    Elements: rational correlations (4/5, −44/125); the local bound 2; the rational
              CHSH violation 344/125; the 3-4-5 Pythagorean angle (L1 + P4)
    Roles:    the local-realistic bound (Element) vs the Tsirelson maximum 2√2
              (role-limit); the rational 3-4-5 config as the Element-side witness of
              genuine nonlocality
    Rules:    the CHSH functional E₀₀+E₀₁+E₁₀−E₁₁; the ±1 constraint (a²=1) ⟹
              classical CHSH² = 4; the quantum correlation = cos(angle); the
              Chebyshev identity cos3θ = 4cos³θ − 3cosθ; (2√2)² = 8

    Bell's theorem, read through the finitization boundary, splits unexpectedly.
      · CLASSICAL BOUND = 2.  For ±1 deterministic local strategies CHSH² = 4
        identically (the cross term b₀²−b₁² vanishes).  The local-realistic bound is
        the rational integer 2 — an Element.
      · THE VIOLATION IS ALREADY AN ELEMENT.  A RATIONAL measurement configuration —
        the 3-4-5 angle (cosθ = 4/5, straight from the Pythagorean triples) — gives
        CHSH = 344/125 ≈ 2.752 > 2, entirely rational.  So beating the classical
        bound needs NO continuum; quantum nonlocality is finitely actual.
      · ONLY THE MAXIMUM IS A ROLE-LIMIT.  The Tsirelson bound 2√2 has (2√2)² = 8,
        irrational (via no_rational_sqrt2) — the EXTREMAL value is a non-terminating
        process.  The continuum enters only at the optimum, not in the violation.

    This dissolves a Bell mystery in our frame: "does quantum nonlocality require the
    continuum?" — NO.  The violation is achievable with rational correlations (an
    Element); √2 appears only in the maximal (Tsirelson) value (a role-limit).  The
    3-4-5 Pythagorean angle delivering the rational violation answers Gisin's
    "Pythagorean no-go" directly: the boundary runs through Bell, with the rational
    statistics and the achievable violation finitely actual and only the optimal
    bound a role-limit.

    ============ E/R/R разбор ============
      Rules (L5): функционал CHSH; a²=1 ⟹ классич²=4; квантовая корреляция = cos;
                  Чебышёв cos3θ=4cos³θ−3cosθ; (2√2)²=8.
      Roles (L4): локально-реалистическая граница (Element) vs максимум Цирельсона
                  (role-limit); рациональное нарушение 3-4-5 = свидетель Element-стороны.
      Elements  : рациональные корреляции (4/5, −44/125), граница 2, нарушение 344/125.
    ДИАГНОСТИКА (P4): нелокальность (превышение 2) конечно-актуальна — достижима
    рациональными корреляциями; только максимум 2√2 = role-limit (√2). Граница финитизации
    проходит сквозь Белл; для нарушения континуум не нужен.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import analysis.Sqrt2Irrational.
Open Scope Q_scope.

(** The CHSH functional on four correlations. *)
Definition chsh (e00 e01 e10 e11 : Q) : Q := e00 + e01 + e10 - e11.

(* ===================================================================== *)
(*  Classical (local-realistic) bound: ±1 strategies give CHSH² = 4       *)
(* ===================================================================== *)

(** Over ℚ, x² = 1 forces x = ±1. *)
Lemma pm1 : forall x : Q, x * x == 1 -> x == 1 \/ x == -(1).
Proof.
  intros x H.
  assert (Hf : (x - 1) * (x + 1) == 0).
  { assert (Hr : (x - 1) * (x + 1) == x * x - 1) by ring.
    rewrite Hr, H. ring. }
  apply Qmult_integral in Hf. destruct Hf as [H1 | H2]; [ left | right ]; lra.
Qed.

(** For ±1 deterministic local outcomes, CHSH² = 4 exactly: the local-realistic
    bound is the rational Element 2.  (Correlations Eᵢⱼ = aᵢ·bⱼ.) *)
Theorem chsh_classical_sq : forall a0 a1 b0 b1 : Q,
  a0*a0 == 1 -> a1*a1 == 1 -> b0*b0 == 1 -> b1*b1 == 1 ->
  chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1) * chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1) == 4.
Proof.
  intros a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1.
  assert (Hid :
    chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1) * chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1)
    == 4 + (a0*a0 - 1) * ((b0+b1)*(b0+b1)) + (a1*a1 - 1) * ((b0-b1)*(b0-b1))
         + (b0*b0 - 1) * (2 + 2*a0*a1) + (b1*b1 - 1) * (2 - 2*a0*a1))
    by (unfold chsh; ring).
  rewrite Hid, Ha0, Ha1, Hb0, Hb1. ring.
Qed.

(* ===================================================================== *)
(*  Quantum: the 3-4-5 angle gives a RATIONAL violation 344/125 > 2       *)
(* ===================================================================== *)

(** The Chebyshev value cos 3θ = 4cos³θ − 3cosθ for the 3-4-5 angle (cosθ = 4/5)
    is the rational −44/125 — the fourth correlation of the violating config. *)
Theorem cos3theta_345 :
  4 * (4#5) * (4#5) * (4#5) - 3 * (4#5) == -(44#125).
Proof. vm_compute. reflexivity. Qed.

(** ★ A RATIONAL quantum configuration beats the classical bound.  The planar
    singlet measurement at the 3-4-5 angle gives correlations (4/5, 4/5, 4/5,
    −44/125), all valid cosines (|E| ≤ 1), and CHSH = 344/125 > 2 — quantum
    nonlocality is finitely actual, no continuum required. *)
Theorem chsh_rational_violation :
  chsh (4#5) (4#5) (4#5) (-(44#125)) == 344#125
  /\ 344#125 > 2
  /\ (-(1) <= 4#5 <= 1) /\ (-(1) <= -(44#125) <= 1).
Proof. repeat split; (vm_compute; reflexivity) || lra. Qed.

(* ===================================================================== *)
(*  Tsirelson: the maximal violation 2√2 is a role-limit                  *)
(* ===================================================================== *)

(** The Tsirelson bound 2√2 has square 8, which has no rational root (via √2) —
    the maximal quantum violation is a role-limit, not a rational number. *)
Theorem tsirelson_role_limit : ~ (exists r : Q, r * r == 8).
Proof.
  intros [r Hr]. apply (no_rational_sqrt2 (r * (1#2))).
  assert (Hs : (r * (1#2)) * (r * (1#2)) == (r * r) * (1#4)) by ring.
  rewrite Hs, Hr. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** Bell over ℚ in one statement: the classical bound is the rational 2 (CHSH²=4),
    a rational 3-4-5 config already violates it (344/125 > 2 — nonlocality is an
    Element), and the maximal violation 2√2 is a role-limit ((2√2)²=8 irrational). *)
Theorem bell_tsirelson_synthesis :
  (forall a0 a1 b0 b1 : Q,
     a0*a0 == 1 -> a1*a1 == 1 -> b0*b0 == 1 -> b1*b1 == 1 ->
     chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1) * chsh (a0*b0) (a0*b1) (a1*b0) (a1*b1) == 4)
  /\ (chsh (4#5) (4#5) (4#5) (-(44#125)) == 344#125 /\ 344#125 > 2)
  /\ ~ (exists r : Q, r * r == 8).
Proof.
  split. exact chsh_classical_sq.
  split. split; [ vm_compute; reflexivity | lra ].
  exact tsirelson_role_limit.
Qed.
