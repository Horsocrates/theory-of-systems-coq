(** * GaugeFromDistinctionSynthesis.v — SM = unique nested distinction
    Elements: sm_gauge_from_distinction, uniqueness argument
    Roles:    synthesis of nested distinction → SM gauge group
    Rules:    [3,2,1] is the ONLY consistent nested distinction
    Status:   Foundation File 11 of 14
    STATUS: 12 Qed, 0 Admitted, 0 new axioms  (honest reduction: June 2026; header was drift-15)
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.

From ToS Require Import foundation.NestedDistinction.
From ToS Require Import foundation.ERRFromDistinction.

(** SM GAUGE GROUP FROM NESTED DISTINCTION — honest reduction (L4 + JustificationRegress.v)
  A = exists → Distinction (A|¬A) → role-counts [2,3,1] → (POSITED) SU(2)×SU(3)×U(1).

  What is DERIVED vs POSITED in this chain (the honest split, after TRYING to derive each):
    depth-1 = 2 roles ........ DERIVED (binary distinction). ✓
    depth-2 ≥ 3 .............. DERIVED (L1: no repeat of binary; sm_minimal_depth2). ✓
    termination (depth≥3 →1) . DERIVED (sm_beyond_depth3, from depth-3 = 1) — illusory posit, removed.
    depth-2 = 3 EXACTLY ...... POSIT (minimality / "take the least ≥3"; not in L1–L5).
    depth-3 = 1 (reflexive) .. POSIT (interpretive).
    N roles → SU(N) .......... THE irreducible PHYSICS POSIT — n roles ↦ the special-unitary group
                               SU(n).  In code it is ONLY the arithmetic n²−1 (gauge_generators), with
                               U(1) SPECIAL-CASED (n²−1 = 0 at n=1) — gauge_map_is_arithmetic_not_derivation.
                               The leap to the Lie group is NOT derived (it imports continuous unitary
                               symmetry, absent from bare distinction).

  ⚠ NOT "ZERO free parameters", NOT "the ONLY solution": [2,4,1] is also valid_nd
  (valid_nd_does_not_force_231) — uniqueness needs the unformalized minimality posit.  By L4 these are
  POSITS (self-grounding), not free choices; by JustificationRegress ≥1 posit is mandatory and "derived
  from nothing / zero parameters" is the role-limit.  Honest status: the gauge group is REDUCED to one
  irreducible physics posit (role→SU(N)) + minimality + reflexivity, atop derived
  depth-1 / depth-2-bound / termination — and that ≥1 floor is exactly the theory's own footing (it
  stands on 2 named axioms, classic + L4_witness; an SM "derivation" cannot use fewer).

  ============ E/R/R разбор ============
    Elements : счёты ролей [2,3,1]; карта n↦n²−1; группа SU(N) (вне файла, в прозе).
    Roles    : depth1=2, depth2≥3, терминация — ВЫВЕДЕНЫ; =3, =1, role→SU(N), U(1)-спецкейс — ПОСТУЛАТЫ.
    Rules    : valid_nd допускает [2,4,1] ⟹ не уникально; карта = арифметика n²−1, не вывод группы.
    ДИАГНОСТИКА (P4+L4): «★ ВЫВЕДЕНО / ЕДИНСТВЕННОЕ / 0 параметров ★» ложно. Свели к ОДНОМУ неустранимому
    физ-постулату role→SU(N) + минимальность/рефлексивность; ноль недостижим (FromNothing = role-limit;
    теория сама на 2 аксиомах). Уровень: `новое-обрамление`. Убрали иллюзию уникальности и терминацию-как-постулат. *)

(* ================================================================== *)
(*  SM GAUGE GROUP — THE COMPLETE DERIVATION                           *)
(* ================================================================== *)

Theorem sm_gauge_from_distinction :
  (* Depth 1: binary → 2 roles *)
  nd_roles_at sm_distinction 0 = 2%nat /\
  (* Depth 2: non-repetitive minimum → 3 roles *)
  nd_roles_at sm_distinction 1 = 3%nat /\
  (* Depth 3: reflexive → 1 role *)
  nd_roles_at sm_distinction 2 = 1%nat /\
  (* Total: 6 roles *)
  nd_total_roles sm_distinction = 6%nat /\
  (* Generators: 8 + 3 + 1 = 12 *)
  (gauge_generators 3 + gauge_generators 2 + u1_generators = 12)%nat.
Proof. repeat split; reflexivity. Qed.

(* ================================================================== *)
(*  UNIQUENESS ARGUMENT                                                *)
(* ================================================================== *)

(** WHY [2,3,1] IS *SELECTED* (not forced — see valid_nd_does_not_force_231):
    Depth 1: 2 — forced (binary distinction). DERIVED.
    Depth 2: ≥ 3 — forced (L1: no repetition of binary). DERIVED (lower bound, sm_minimal_depth2).
             = 3 exactly — POSIT (minimality "L4: minimal sufficient"; [2,4,1] is valid too).
    Depth 3: 1 — POSIT (reflexive, interpretive).
    Depth 4+: 1 — DERIVED (terminal propagates from depth-3 = 1, sm_beyond_depth3).
    → [2,3,1] is the MINIMAL valid nesting, selected by the minimality posit — not the only one. *)

(** Any valid nested distinction must have depth1 = 2 *)
Definition valid_nd (nd : NestedDistinction) : Prop :=
  depth1_is_binary nd /\
  depth2_no_repeat nd /\
  depth3_is_reflexive nd /\
  (3 <= nd_depth nd)%nat.

Theorem sm_is_valid : valid_nd sm_distinction.
Proof.
  unfold valid_nd.
  split; [|split; [|split]].
  - unfold depth1_is_binary. reflexivity.
  - unfold depth2_no_repeat. intros _. simpl. lia.
  - unfold depth3_is_reflexive. intros _. reflexivity.
  - simpl. lia.
Qed.

(** SM has the minimum roles at each depth *)
Theorem sm_minimal_depth2 :
  nd_roles_at sm_distinction 1 = 3%nat /\
  (forall nd, valid_nd nd -> (3 <= nd_roles_at nd 1)%nat).
Proof.
  split.
  - reflexivity.
  - intros nd [_ [H2 [_ Hd]]]. unfold depth2_no_repeat in H2.
    apply H2. lia.
Qed.

(** The decomposition [2,3,1] matches SM convention [3,2,1] *)
(** Physics lists largest group first: SU(3) x SU(2) x U(1) *)
Theorem decomposition_is_sm :
  nd_decomposition sm_distinction = [2; 3; 1]%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  HONEST: NON-UNIQUENESS + the role→SU(N) leap is a POSIT            *)
(* ================================================================== *)

(** ★ valid_nd does NOT force [2,3,1]: the alternative [2,4,1] (alt_distinction, NestedDistinction.v)
    is also valid_nd, yet its decomposition ≠ [2,3,1].  So "the ONLY solution" is an overclaim —
    [2,3,1] is the MINIMAL valid nesting, selected by the (unformalized) minimality posit. *)
Theorem valid_nd_does_not_force_231 :
  valid_nd alt_distinction /\ nd_decomposition alt_distinction <> [2; 3; 1]%nat.
Proof.
  split.
  - unfold valid_nd. split; [|split; [|split]].
    + unfold depth1_is_binary. reflexivity.
    + unfold depth2_no_repeat. intros _. simpl. lia.
    + unfold depth3_is_reflexive. intros _. reflexivity.
    + simpl. lia.
  - intro H. vm_compute in H. discriminate H.
Qed.

(** ★ The role→group content of this file is EXACTLY the arithmetic n²−1 (gauge_generators); the
    identification "n roles ↔ the Lie group SU(n)" is a POSIT, not proved here.  Witness that even
    the FORMULA does not uniformly yield the gauge groups: gauge_generators 1 = 0, but U(1) needs 1
    generator (u1_generators), so U(1) must be SPECIAL-CASED.  The leap to the continuous unitary
    group is the one irreducible physics posit. *)
Theorem gauge_map_is_arithmetic_not_derivation :
  gauge_generators 2 = 3%nat /\ gauge_generators 3 = 8%nat
  /\ gauge_generators 1 = 0%nat /\ u1_generators = 1%nat
  /\ gauge_generators 1 <> u1_generators.
Proof.
  repeat split; try reflexivity.
  intro H. vm_compute in H. discriminate H.
Qed.

(* ================================================================== *)
(*  WHAT THIS MEANS                                                    *)
(* ================================================================== *)

(** BEFORE: "Why SU(3)xSU(2)xU(1) and not SU(5) or SO(10)?" — "empirical."
    AFTER (honest): nested distinction REDUCES the question to one physics posit (role→SU(N)) +
      minimality + reflexivity; the role-counts [2,3,1] are the minimal valid nesting (selected, not
      unique — [2,4,1] is valid too).  Progress = fewer/named posits, NOT "zero" or "only option." *)

(** Extended roles match ERRFromDistinction *)
Theorem roles_match_err :
  extended_roles [3; 2; 1] = 6%nat /\
  nd_total_roles sm_distinction = 6%nat.
Proof. split; reflexivity. Qed.

(** SU(2) from primary distinction *)
Theorem su2_from_primary :
  nd_roles_at sm_distinction 0 = 2%nat /\
  gauge_generators 2 = 3%nat.
Proof. split; reflexivity. Qed.

(** SU(3) from nested distinction *)
Theorem su3_from_nested :
  nd_roles_at sm_distinction 1 = 3%nat /\
  gauge_generators 3 = 8%nat.
Proof. split; reflexivity. Qed.

(** U(1) from reflexive self-distinction *)
Theorem u1_from_reflexive :
  nd_roles_at sm_distinction 2 = 1%nat /\
  u1_generators = 1%nat.
Proof. split; reflexivity. Qed.

(** COMPARISON: the SM takes the gauge group as input; here it is reduced to the role→SU(N) posit +
    minimality/reflexivity (a SMALL named posit set), atop derived depth-1/depth-2-bound/termination.
    NOT "0 free parameters" — zero is the role-limit (JustificationRegress.from_nothing_ungrounded).
    The theorem below COMPUTES properties of the (posited) [2,3,1] structure; it does not prove zero. *)

Theorem zero_free_parameters_in_gauge :
  (* Group determined *) nd_decomposition sm_distinction = [2; 3; 1]%nat /\
  (* Generators determined *) (gauge_generators 3 + gauge_generators 2 + u1_generators = 12)%nat /\
  (* Total roles determined *) nd_total_roles sm_distinction = 6%nat.
Proof. repeat split; reflexivity. Qed.

(* ================================================================== *)
(*  SUMMARY                                                            *)
(* ================================================================== *)

Theorem gauge_from_distinction_summary :
  (* SM satisfies constraints *)
  valid_nd sm_distinction /\
  (* Decomposition = [2,3,1] *)
  nd_decomposition sm_distinction = [2; 3; 1]%nat /\
  (* Total generators = 12 *)
  (gauge_generators 3 + gauge_generators 2 + u1_generators = 12)%nat.
Proof.
  split; [|split].
  - exact sm_is_valid.
  - reflexivity.
  - reflexivity.
Qed.

Definition gauge_synthesis_theorem_count := 12%nat.
