(** * GenerationsPositReduction.v — closing weakness #1 for "exactly 3 generations": the genuine
      COUNT (>=3 for CP) is free, and the "exactly" is reduced to ONE named posit (L4-minimality),
      whose cost is now QUANTIFIED.

    Companion to GaugePositReduction.v.  The Part-C audit found: GenerationsFromL4.v proves the
    LOWER bound >=3 (a genuine count: CP violation needs >=3 generations) but the UPPER bound
    "exactly 3" lives in a COMMENT ("L4: no sufficient reason for a 4th generation") — `L4_stops_at_3`
    only proves the FACTS (n_cp_phases 3 < n_cp_phases 4), not the inference.  Honest subtlety: a 4th
    generation is NOT forbidden by the count (n_cp_phases 4 = 3 > 0 still has CP); stopping at 3 rests
    on L4-minimality + observation.

    This file CLOSES it the same way as the gauge group (closing ≠ zeroing; grounded_needs_posit):
      (1) >=3 for CP is a GENUINE COUNT (`generations_lower_bound`) — no posit beyond the framework;
      (2) L4-minimality is made an EXPLICIT NAMED principle: the generation count is the MINIMUM
          achieving the qualitative feature (CP violation);
      (3) ★ "exactly 3" becomes a UNIQUENESS theorem (`generations_unique`): the minimum achieving CP
          is uniquely 3 — proved from the named L4-minimality posit, not asserted in a comment;
      (4) ★ the posit COST is QUANTIFIED (`exactly_costs_one_more_posit`): "exactly 3" grounds on
          exactly ONE more named posit (L4-minimality) than the bare count ">=3".

    Net: ">=3 for CP" is genuine and free; "exactly 3" is the unique minimum-achieving-CP, riding on
    exactly one explicit named posit (L4-minimality) over the framework floor — counted, not hidden.

    Elements: n_cp_phases / has_cp_violation; the unique generation count 3; the counted posit cost
    Roles:    L4-minimality = the one named posit "exactly 3" rides on; >=3 = genuine count; LEP = Indep
    Rules:    >=3 is forced by the CP-phase count (no posit); exactly 3 = the unique minimum achieving
              CP, given L4-minimality; the upper bound costs exactly +1 named posit

    ============ E/R/R разбор ============
      Rules (L5): ≥3 — генуинный счёт (без постулата); «ровно 3» = уникальный минимум, достигающий CP,
                  при названном L4-min; верхняя граница стоит ровно +1 названный постулат.
      Roles (L4): L4-минимальность = один названный постулат «ровно»; ≥3 = счёт; LEP = Indep.
      Elements  : n_cp_phases/has_cp_violation; `generations_unique`; счёт постулата (+1).
    ДИАГНОСТИКА (P4): 4-е поколение НЕ запрещено счётом; «ровно» = только L4-минимальность (+набл.).
    Закрытие ≠ обнуление: нижняя граница бесплатна, «ровно» стоит ТОЧНО один названный постулат —
    явный и сосчитанный. Квантифицируем цену постулата.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.
From ToS Require Import foundation.GaugePositReduction.  (* reuse is_minimal, Just, grounded, n_posits *)

(* Replicated from foundation/GenerationsFromL4.v to avoid the core-chain stale .vo. *)
Definition n_cp_phases (n_gen : nat) : nat := (n_gen - 1) * (n_gen - 2) / 2.
Definition has_cp_violation (n_gen : nat) : bool := Nat.ltb 0 (n_cp_phases n_gen).

(* ===================================================================== *)
(*  The genuine COUNT: >= 3 generations for CP (no posit)                  *)
(* ===================================================================== *)

Lemma cp_2_false : has_cp_violation 2 = false.
Proof. reflexivity. Qed.

Lemma cp_3_true : has_cp_violation 3 = true.
Proof. reflexivity. Qed.

Lemma no_cp_below_3 : forall n, n <= 2 -> has_cp_violation n = false.
Proof. intros n Hn. destruct n as [|[|[|n']]]; try reflexivity; lia. Qed.

(** ★ The genuine count: CP violation forces >= 3 generations.  This is a forced combinatorial fact
    (no posit beyond the framework) — the honest first-principles part. *)
Lemma generations_lower_bound : forall n, has_cp_violation n = true -> 3 <= n.
Proof.
  intros n Hn. destruct (le_lt_dec n 2) as [Hc|Hc].
  - rewrite (no_cp_below_3 n Hc) in Hn. discriminate.
  - lia.
Qed.

(* ===================================================================== *)
(*  L4-minimality named; "exactly 3" as a UNIQUENESS theorem               *)
(* ===================================================================== *)

(** L4-minimality (named): the generation count is the MINIMUM achieving the qualitative feature
    (CP violation).  (This is the "stop at the minimum sufficient" step, now a precise principle.) *)
Definition L4_minimal_generations (gen : nat) : Prop :=
  is_minimal gen (fun m => has_cp_violation m = true).

(** ★ "exactly 3": the minimum generation count achieving CP violation is UNIQUELY 3 — proved from
    the named L4-minimality posit (was a comment in GenerationsFromL4.v). *)
Theorem generations_unique (gen : nat) :
  L4_minimal_generations gen -> gen = 3.
Proof.
  intros H. unfold L4_minimal_generations, is_minimal in H. destruct H as [HP Hmin].
  assert (Hle : gen <= 3) by (apply Hmin; exact cp_3_true).
  assert (Hge : 3 <= gen).
  { destruct (le_lt_dec gen 2) as [Hc|Hc].
    - rewrite (no_cp_below_3 gen Hc) in HP. discriminate.
    - lia. }
  lia.
Qed.

(** The actual generation count 3 IS the L4-minimal one (witness). *)
Lemma three_is_L4_minimal : L4_minimal_generations 3.
Proof.
  unfold L4_minimal_generations, is_minimal. split.
  - exact cp_3_true.
  - intros m Hm. destruct (le_lt_dec m 2) as [Hc|Hc].
    + rewrite (no_cp_below_3 m Hc) in Hm. discriminate.
    + lia.
Qed.

(* ===================================================================== *)
(*  The posit cost of "exactly", QUANTIFIED                                *)
(* ===================================================================== *)

(* The bare count ">=3" grounds on the framework alone; "exactly 3" adds the L4-minimality posit. *)
Definition framework_posit : Just := Posit.
Definition L4min_posit : Just := Posit.

Definition count_just    : Just := framework_posit.                  (* >=3 : a pure count *)
Definition exactly3_just : Just := Derived framework_posit L4min_posit. (* exactly 3 : + L4-min *)

Lemma count_one_posit : n_posits count_just = 1.
Proof. reflexivity. Qed.

Lemma exactly3_two_posits : n_posits exactly3_just = 2.
Proof. reflexivity. Qed.

(** ★ "exactly 3" costs EXACTLY one more named posit (L4-minimality) than the bare count ">=3".
    The lower bound is free; the upper bound's posit cost is precisely one, now explicit and counted. *)
Lemma exactly_costs_one_more_posit :
  n_posits exactly3_just = S (n_posits count_just).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: weakness #1 closed for the generation count                  *)
(* ===================================================================== *)

(** The posit reduction for "exactly 3 generations":
      (count)     CP violation forces >= 3 generations — genuine, no posit (generations_lower_bound);
      (unique)    the minimum achieving CP is uniquely 3 — proved from L4-minimality (was a comment);
      (witness)   3 is the L4-minimal generation count;
      (cost)      "exactly 3" costs exactly +1 named posit (L4-minimality) over the bare count.
    ">=3" is genuine and free; "exactly 3" rides on exactly one explicit, counted named posit. *)
Theorem generations_posit_reduction :
  (forall n, has_cp_violation n = true -> 3 <= n)
  /\ (forall gen, L4_minimal_generations gen -> gen = 3)
  /\ L4_minimal_generations 3
  /\ (n_posits exactly3_just = S (n_posits count_just)).
Proof.
  split; [ exact generations_lower_bound | ].
  split; [ exact generations_unique | ].
  split; [ exact three_is_L4_minimal | ].
  exact exactly_costs_one_more_posit.
Qed.
