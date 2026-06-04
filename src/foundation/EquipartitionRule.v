(** * EquipartitionRule.v — opening the single L5 residual ("coupling = DOF ratio") and reading its
      устройство the same way: it is a UNIFORM (equipartition) MEASURE over the DOF, whose value is
      FORCED by the principle of indifference (a theorem), and whose irreducible bottom decomposes into
      {indifference (Distinction-affine) + reference-wiring (the model's sector-locality)}.

    KappaFrameworkChain.v reduced the whole κ derivation to the E/R/R laws PLUS one genuine L5 modeling
    rule (the assignment "coupling = DOF ratio").  This file opens THAT rule and reads its structure —
    just as DimensionPositReduction opened "D=4".

    ── The rule's устройство: a uniform measure over the DOF ──
      κ = 1/N        — the per-channel equipartition QUANTUM (N = metric DOF = 10);
      sin²θ_W = k/N  — a subset weight (k = gauge DOF = 3, N = total DOF = 13);
      both are  k × (1/N)  = integer multiples of an equipartition quantum.  The rule IS "equal weight
      per DOF" (a uniform / maximum-entropy measure).

    ── The rule is itself an E/R/R triad ──
      Elements : the DOF counts (3, 10) — forced earlier (Role laws + D);
      Roles    : each DOF = a channel receiving weight;
      Rules    : the weight-assignment = UNIFORM (equipartition) — the rule's own deepest content.

    ── The bottom: the principle of indifference, Distinction-affine ──
      Why uniform?  The principle of indifference / MaxEnt: no DOF is privileged ABSENT a distinction —
      the quantitative shadow of the Distinction primitive (L2: a distinction has two sides; until L4
      assigns a role, neither is privileged ⟹ symmetric ⟹ uniform).  And the VALUE is a THEOREM:
      equal weights + normalization ⟹ value = 1/N is FORCED (`weight_forced`) — exactly as D≤3 was
      forced (Ehrenfest) once P4 was accepted.

    ── HONEST (and weaker than stability→P4) ──
      The L5 rule, opened, is NOT atomic — it is {indifference + reference-wiring}:
        • indifference (equal weights) → Distinction-affine, BUT with a real qualitative→quantitative
          gap: the principle of indifference is genuinely ADDED (parametrization-sensitive), NOT a clean
          theorem from Distinction.  So this affinity is WEAKER than stability→P4 (which had Ehrenfest
          as a genuine theorem);
        • reference-wiring (which DOF set per coupling: κ↔metric, sin²θ↔gauge/total = sector-locality)
          → the model's choice — the genuine irreducible BOTTOM.
      This is the deepest, least-eliminable residual of the κ branch.  We do NOT zero it — we read its
      structure and name its two parts.

    Elements: equipart_quantum; κ and sin²θ as k×(1/N); the rule's 2-part justification tree
    Roles:    indifference = Distinction-affine (with a gap); reference-wiring = the model bottom
    Rules:    the value 1/N is FORCED by equal-weights+normalization (weight_forced); the rule opens
              into exactly two named parts

    ============ E/R/R разбор ============
      Rules (L5): устройство правила = равномерная мера; значение 1/N вынуждено безразличием+нормировкой
                  (`weight_forced`, теорема, как D≤3 из P4); правило вскрывается в два названных куска.
      Roles (L4): безразличие (равные веса) = Различение-родственно (с разрывом качеств→количеств,
                  слабее P4); привязка-референс (κ↔метрика, sin²θ↔gauge/total) = модельная локальность.
      Elements  : equipart_quantum; κ=1/N и sin²θ=k/N; дерево обоснования правила (2 части).
    ДИАГНОСТИКА (P4): единственный L5-остаток НЕ атомарен — {безразличие (Различение-родств.) + референс
    (модель)}. Самое глубокое дно κ-ветки; не обнуляем, но читаем устройство и называем две части.
    Честно: безразличие слабее устойчивости (нет чистой теоремы из Различения; принцип безразличия добавлен).

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Arith Lia.
From ToS Require Import foundation.GaugePositReduction.   (* Just, Posit, Derived, n_posits, grounded *)
From ToS Require Import foundation.KappaPositReduction.   (* kappa, sin2w, kappa_4, sin2w_4, metric_dof, gauge_dof, metric_dof_4 *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The equipartition quantum: equal weight per DOF                         *)
(* ===================================================================== *)

(** The per-DOF uniform weight = 1/n — the equipartition quantum over n channels. *)
Definition equipart_quantum (n : nat) : Q := 1 / inject_Z (Z.of_nat n).

(** ★ The VALUE is forced: equal weights + normalization (N·c = 1) ⟹ the per-channel weight is 1/N.
    Indifference forces the value, just as Ehrenfest forces D≤3 once P4 is accepted. *)
Lemma weight_forced : forall N c : Q, ~ N == 0 -> N * c == 1 -> c == 1 / N.
Proof. intros N c HN Hw. rewrite <- Hw. field. exact HN. Qed.

(** The equipartition quantum is the normalized per-channel weight (the n channels sum to 1). *)
Lemma equipart_quantum_normalizes :
  forall n, ~ inject_Z (Z.of_nat n) == 0 ->
            inject_Z (Z.of_nat n) * equipart_quantum n == 1.
Proof. intros n Hn. unfold equipart_quantum. field. exact Hn. Qed.

(* ===================================================================== *)
(*  κ and sin²θ_W are BOTH equipartition readouts (integer × quantum)       *)
(* ===================================================================== *)

(** ★ κ = the equipartition quantum over the metric DOF (= 1/10): the per-channel uniform weight. *)
Lemma kappa_is_quantum : kappa 4 == equipart_quantum (metric_dof 4).
Proof. rewrite metric_dof_4, kappa_4. vm_compute. reflexivity. Qed.

(** ★ sin²θ_W = (gauge DOF) × (equipartition quantum over total DOF) = 3 × (1/13): a subset weight
    under the SAME uniform measure.  So κ and sin²θ are two readouts of ONE equipartition rule. *)
Lemma sin2w_is_multiple :
  sin2w 4 == inject_Z (Z.of_nat gauge_dof) * equipart_quantum ((gauge_dof + metric_dof 4)%nat).
Proof. rewrite sin2w_4. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The value of κ is forced once indifference is accepted                  *)
(* ===================================================================== *)

Lemma metric4_nonzero : ~ inject_Z (Z.of_nat (metric_dof 4)) == 0.
Proof. rewrite metric_dof_4. intro H. vm_compute in H. discriminate. Qed.

(** ★ Given equal-weight normalization over the metric DOF, the per-channel weight IS κ = 1/10 —
    the value is not chosen, it is FORCED by indifference (the direct analog of "D=4 value forced"). *)
Lemma kappa_forced_by_indifference :
  forall c, inject_Z (Z.of_nat (metric_dof 4)) * c == 1 -> c == kappa 4.
Proof.
  intros c Hw.
  transitivity (1 / inject_Z (Z.of_nat (metric_dof 4))).
  - apply weight_forced; [ exact metric4_nonzero | exact Hw ].
  - rewrite metric_dof_4, kappa_4. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  The rule is NOT atomic: {indifference + reference-wiring}               *)
(* ===================================================================== *)

(* The L5 rule, opened, has internal structure: the indifference principle (Distinction-affine) and
   the reference-wiring (which DOF set per coupling — the model's sector-locality, the genuine bottom). *)
Definition indifference_posit : Just := Posit.  (* equal weights = principle of indifference (Distinction-affine) *)
Definition reference_posit   : Just := Posit.   (* κ↔metric, sin²θ↔gauge/total = sector-locality (model bottom) *)
Definition dof_rule_just : Just := Derived indifference_posit reference_posit.

Lemma dof_rule_grounded : grounded dof_rule_just.
Proof. exact (conj I I). Qed.

(** ★ The single L5 rule OPENS into exactly two named parts — it is not an atomic posit. *)
Lemma dof_rule_two_parts : n_posits dof_rule_just = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the L5 rule's устройство, read through E/R/R                  *)
(* ===================================================================== *)

(** Opening the single L5 rule "coupling = DOF ratio":
      (quantum)  κ = the equipartition quantum over the metric DOF (1/10);
      (subset)   sin²θ_W = gauge × the quantum over the total DOF (3 × 1/13) — same uniform measure;
      (forced)   the value 1/N is FORCED by equal weights + normalization (indifference, a theorem);
      (opens)    the rule is NOT atomic — it decomposes into two named parts {indifference, reference}.
    The rule's устройство is a uniform/equipartition measure; its deepest content (uniformity) is the
    principle of indifference (Distinction-affine), and its genuine irreducible bottom is the model's
    reference-wiring.  This is the deepest residual of the κ branch — read, named, not zeroed. *)
Theorem equipartition_rule_structure :
  kappa 4 == equipart_quantum (metric_dof 4)
  /\ sin2w 4 == inject_Z (Z.of_nat gauge_dof) * equipart_quantum ((gauge_dof + metric_dof 4)%nat)
  /\ (forall N c : Q, ~ N == 0 -> N * c == 1 -> c == 1 / N)
  /\ (forall c, inject_Z (Z.of_nat (metric_dof 4)) * c == 1 -> c == kappa 4)
  /\ n_posits dof_rule_just = 2%nat.
Proof.
  split; [ exact kappa_is_quantum | ].
  split; [ exact sin2w_is_multiple | ].
  split; [ exact weight_forced | ].
  split; [ exact kappa_forced_by_indifference | ].
  exact dof_rule_two_parts.
Qed.
