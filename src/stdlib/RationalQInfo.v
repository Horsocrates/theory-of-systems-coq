(** * RationalQInfo.v — ② rational quantum INFORMATION over ℚ: the amplitude
      (role-limit) / probability (Element) split, made into theorems.

    Elements: rational amplitudes (±1 entries of the unnormalised Walsh/Pauli
              vectors), rational Born probabilities (½), the collision
              probability Σp² (Rényi-2, pre-log) — all over ℚ (L1 + P4)
    Roles:    a basis as a MEASUREMENT CONTEXT; mutual unbiasedness (MU) = the
              role of "maximal complementarity / zero mutual information"; the
              √2 NORMALISATION = a role-limit (the would-be unit-vector process,
              never terminating over ℚ)
    Rules:    the Born rule born u v = ⟨u|v⟩²/(⟨u|u⟩⟨v|v⟩) (the amplitude→
              probability map); the MU criterion |⟨a|b⟩|²=½; Σp=1; the Rényi-2
              sum rule coll_Z+coll_X=3/2; the BB84 mismatch disagreement = ½

    THE CENTRAL SPLIT — amplitude = role-limit, probability = Element.  This is
    Palmer's RaQM thesis as an E/R/R theorem.  `WalshQuantum.born` NEVER
    normalises the state vector: it divides by ⟨v|v⟩ only at the END.  For the
    Walsh state w0=(1,1), ⟨w0|w0⟩ = 2; the "normalised" state (1/√2,1/√2) is where
    √2 would live, but `born` SKIPS it — only 2 = (√2)² ever appears, rationally.
    So the Born rule IS the boundary map: it takes a rational amplitude (Element)
    and rational norms (Elements) and returns a rational probability (Element); the
    √2 is virtual, living only in the normalisation `born` bypasses.  Hence
    `amplitude_role_limit_probability_element`: the amplitude layer needs a
    role-limit (√2 ∉ ℚ, `sqrt2_not_in_Q`) yet the probability layer is an Element
    (½ ∈ ℚ).  The continuum of QM lives entirely in the unobserved amplitude layer;
    the observable record (frequencies, complementarity, QBER, collision entropy)
    is ℚ-finite.

    HEADLINE RESULTS (all rational, 0 axioms):
      · `amplitude_role_limit_probability_element` — √2-normalisation is a
        role-limit, but Born probability = ½ is an Element (the split).
      · `complementarity_sharp_flat` — a state sharp in Z (prob 1,0) is flat in
        X (prob ½,½): the information-theoretic core of complementarity.
      · `renyi2_uncertainty` — for ANY nonzero state, coll_Z + coll_X = 3/2: the
        Rényi-2 (collision-probability) uncertainty relation, EXACTLY rational.
        (Shannon/von-Neumann entropy drags in log = a ProcessQ role-limit; the
        ℚ-native uncertainty is the collision probability Σp², an Element.)
      · `bb84_intercept_resend_qber` — basis-mismatch eavesdropping disagrees
        with prob ½ (the MU value), so the averaged QBER = ½·½ = ¼, all rational.
      · `mub_ZX` — Z and X are mutually unbiased (all eight cross-Born = ½).

    ============ E/R/R разбор ============
      Rules (L5): правило Борна = граница (амплитуда→вероятность); MU |⟨a|b⟩|²=½;
                  правило суммы Реньи-2 coll_Z+coll_X=3/2; BB84-расхождение=½.
      Roles (L4): базис = контекст измерения; MU = макс. комплементарность;
                  √2-нормировка = role-limit (незавершающийся процесс единичности).
      Elements  : рациональные амплитуды, вероятности ½, коллизионная вер. Σp² (L1+P4).
    ДИАГНОСТИКА (P4): ② демаркирует квантовую ИНФОРМАЦИЮ. Конечно-актуальное ядро
    (рацвероятности, комплементарность, MUB, QBER, коллизионная энтропия) ⊕ остаток-
    role-limit (нормировка √2, log-энтропия Шеннона/фон Неймана). ГРАНИЦА — правило
    Борна: `born` делит на норму ⟹ √2 не появляется как Element, только (√2)²=2. «Иррац.
    ли амплитуда 1/√2» — не-вопрос: амплитуда ЕСТЬ √2-процесс, её терминус (вероятность) = ½.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.WalshQuantum.
From ToS Require Import analysis.Sqrt2Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Collision probability (Rényi-2, pre-log) — the ℚ-native uncertainty   *)
(* ===================================================================== *)

(** Collision probability of a 2-outcome distribution: Σ p². Rational. *)
Definition coll2 (p q : Q) : Q := p * p + q * q.

(** Collision probability of measuring state v in the Z (position) basis. *)
Definition coll_Z (v : vec) : Q := coll2 (born e0 v) (born e1 v).

(** ...and in the X (Walsh) basis. *)
Definition coll_X (v : vec) : Q := coll2 (born w0 v) (born w1 v).

(* ===================================================================== *)
(*  1. THE CENTRAL SPLIT: amplitude = role-limit, probability = Element   *)
(* ===================================================================== *)

(** The normalisation √2 needed to make the Walsh amplitude a unit vector has
    NO rational value (`sqrt2_not_in_Q` — a role-limit / non-terminating
    process), YET the Born probability `born` actually computes is the rational
    Element ½ — because `born` divides by the norm ⟨v|v⟩=2 instead of by √2. *)
Theorem amplitude_role_limit_probability_element :
  (~ exists r : Q, r * r == 2)        (* amplitude normalisation = role-limit *)
  /\ born e0 w0 == 1#2                  (* yet the Born probability = an Element *)
  /\ born e1 w0 == 1#2.
Proof.
  split; [ exact sqrt2_not_in_Q | split; vm_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(*  2. Complementarity: sharp in Z ⟹ flat in X                           *)
(* ===================================================================== *)

(** The position eigenstate e0 is SHARP in Z (probabilities 1, 0) but maximally
    FLAT in X (probabilities ½, ½). This is the information-theoretic core of
    position↔momentum complementarity, with exactly rational probabilities. *)
Theorem complementarity_sharp_flat :
  born e0 e0 == 1 /\ born e1 e0 == 0 /\
  born w0 e0 == 1#2 /\ born w1 e0 == 1#2.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  3. The Rényi-2 rational uncertainty relation: coll_Z + coll_X = 3/2   *)
(* ===================================================================== *)

(** For ANY nonzero state v, the collision probabilities in the two
    complementary bases sum to EXACTLY 3/2 — a rational, state-independent
    uncertainty relation (the real-state MUB sum rule). `born` self-normalises,
    so no unit-norm hypothesis is needed; only v ≠ 0.  Shannon/von-Neumann
    entropy would drag in log (a role-limit); the collision probability Σp²
    is the ℚ-native Element-valued uncertainty. *)
Theorem renyi2_uncertainty : forall v : vec,
  ~ (dot v v == 0) -> coll_Z v + coll_X v == 3#2.
Proof.
  intros [a b] Hnz.
  unfold dot in Hnz; simpl in Hnz.
  unfold coll_Z, coll_X, coll2, born, dot, e0, e1, w0, w1; simpl.
  field. exact Hnz.
Qed.

(* ===================================================================== *)
(*  4. BB84: intercept-resend QBER = 1/4, from the MU value ½             *)
(* ===================================================================== *)

(** Eavesdropping in the complementary (wrong) basis: Alice sends the Z-eigenstate
    e0; an eavesdropper measuring in X resends a Walsh eigenstate (w0 or w1);
    Bob measuring in Z then disagrees with Alice with probability ½ (the MU value,
    `born e1 w0 = born e1 w1 = ½`). Averaged over the 50% of rounds with basis
    mismatch, the QBER = ½·½ = ¼ — a rational security margin straight from ½. *)
Theorem bb84_intercept_resend_qber :
  born e1 w0 == 1#2 /\ born e1 w1 == 1#2         (* mismatch ⟹ disagree w.p. ½ *)
  /\ (1#2) * born e1 w0 == 1#4.                   (* averaged QBER = ½·½ = ¼ *)
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  5. Z and X are mutually unbiased (symmetric, all cross-Born = ½)      *)
(* ===================================================================== *)

(** The Z (position) and X (Walsh) bases are MUTUALLY UNBIASED: every one of the
    eight cross-Born probabilities equals ½. This is the qubit MUB pair (the
    third MUB, Y, needs ℚ[i] — next step of ②). The MU triad {Z,X,Y} is exactly
    the eigenbasis structure of the Pauli group classified in ① (Clifford). *)
Theorem mub_ZX :
  born e0 w0 == 1#2 /\ born e0 w1 == 1#2 /\
  born e1 w0 == 1#2 /\ born e1 w1 == 1#2 /\
  born w0 e0 == 1#2 /\ born w1 e0 == 1#2 /\
  born w0 e1 == 1#2 /\ born w1 e1 == 1#2.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** Rational quantum information in one statement: the amplitude normalisation is
    a role-limit (√2 ∉ ℚ), yet the Born probability is an Element (½); the
    collision-probability uncertainty relation is exactly the rational 3/2; and
    the BB84 eavesdropping margin is the rational ¼ — all over ℚ, 0 axioms. *)
Theorem rational_qinfo_synthesis :
  (~ exists r : Q, r * r == 2)
  /\ born e0 w0 == 1#2
  /\ (forall v : vec, ~ (dot v v == 0) -> coll_Z v + coll_X v == 3#2)
  /\ (1#2) * born e1 w0 == 1#4.
Proof.
  split. exact sqrt2_not_in_Q.
  split. vm_compute; reflexivity.
  split. exact renyi2_uncertainty.
  vm_compute; reflexivity.
Qed.
