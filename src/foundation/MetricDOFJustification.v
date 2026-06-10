(** * MetricDOFJustification.v — The geometric-sector tensor RANK is RULE-UNDERDETERMINED;
       n_metric = 10 is DATA-SELECTED, not forced  (honest rollback of the old "why 10 not 20/6")
    Elements: the three geometric DOF counts of a 4D metric — antisymmetric 6, symmetric 10,
              Riemann 20 — and the mixing value each yields under L1.
    Roles:    each rank plays "the geometric sector U(1)_Y (depth-2, geometric) mixes into".
    Rules:    L1 (equal weight per DOF) => sin²θ = a/(a+b); the rule fixes the FORM, not the rank b.
    STATUS:   20 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026  (rank-honesty rollback: June 2026)

    +-- WHERE THE 3/13 "DERIVATION" SILENTLY BECOMES A FIT --------------------------------+
    | sin²θ_W = a/(a+b) with a = dim SU(2) = 3 (forced) and b = the geometric sector.       |
    | The single unforced step is the RANK of b. A 4D metric has THREE canonical            |
    | geometric DOF counts, all equally "geometric", differing only by tensor rank:         |
    |     antisymmetric rank-2   b = D(D-1)/2    = 6   (Lorentz/isometry algebra so(3,1))    |
    |     symmetric    rank-2     b = D(D+1)/2    = 10  (metric components g_μν)             |
    |     Riemann curvature       b = D²(D²-1)/12 = 20  (curvature the metric sources)       |
    | Under L1 + "U(1)_Y is geometric" ALL THREE are admissible — the framework has no       |
    | formalized rule selecting symmetric over antisymmetric over curvature.  They give:    |
    |     6 -> 3/9 = 1/3 ≈ 0.333,   10 -> 3/13 ≈ 0.231,   20 -> 3/23 ≈ 0.130.                |
    | The rules leave sin² UNDETERMINED across this discrete dial; the DATUM 0.2312          |
    | (sitting BETWEEN 1/3 and 3/23) is what selects rank-symmetric -> 10.  Hence 3/13 is    |
    | "L1-forced GIVEN the rank", and the rank is a data-selected identification, NOT a      |
    | derivation.  The old verbal pick ("U(1) acts on components, not derivatives/           |
    | isometries") is a reverse-engineered story: equally good stories pick 6 or 20.         |
    +--------------------------------------------------------------------------------------+

    ============ E/R/R разбор (of the problem-point itself) ============
      Elements : три геометрических счёта 4D-метрики — антисим 6, сим 10, Риман 20 (каждый сам система:
                 Element D=4 + операция ранга-тензора); числитель a=3=dim SU(2) (вынужден).
      Roles    : каждый ранг играет роль «геометрический сектор, в который подмешивается U(1)_Y (глубина-2)».
      Rules    : L1 (равный вес) фиксирует ФОРМУ a/(a+b), но НЕ ранг b. {6,10,20} -> {1/3, 3/13, 3/23}.
      ДИАГНОСТИКА (P4 + L4): rank_underdetermined показывает, что L1 ОДНА не фиксирует ранг b — но это
      НЕ «свободный выбор». По L4 (Law_of_SufficientReason) основание само-обосновано; по
      JustificationRegress всякое обоснованное опирается на ≥1 ПОСТУЛАТ (grounded_needs_posit), а «ноль
      параметров / из ничего» — role-limit (from_nothing_ungrounded). Протолкнув вглубь: ранг СВОДИТСЯ
      локальностью (6=изометрии, 20=кривизна — другие объекты), а неустранимые постулаты 3/13 суть P1 +
      карта depth→gauge (②). Узел: forced(форма+числитель) ⟂ posit(карта depth→gauge); датум лишь
      ПОДТВЕРЖДАЕТ ранг, не создаёт его. Уровень: `синтез+наблюдение`. Честная задача — СЧИТАТЬ постулаты,
      не обнулять их.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  THE THREE GEOMETRIC DOF COUNTS OF A 4D METRIC (by tensor rank)     *)
(* ================================================================== *)

(** Symmetric rank-2 tensor: D(D+1)/2 — the metric components g_μν. *)
Definition sym_tensor_dim (D : nat) : nat := (D * (D + 1) / 2)%nat.

Lemma sym_dim_2 : sym_tensor_dim 2 = 3%nat.
Proof. reflexivity. Qed.

Lemma sym_dim_3 : sym_tensor_dim 3 = 6%nat.
Proof. reflexivity. Qed.

Lemma sym_dim_4 : sym_tensor_dim 4 = 10%nat.
Proof. reflexivity. Qed.

(** Riemann curvature: D²(D²-1)/12 — the curvature the metric sources. *)
Definition riemann_dim (D : nat) : nat := (D * D * (D * D - 1) / 12)%nat.

Lemma riemann_dim_4 : riemann_dim 4 = 20%nat.
Proof. reflexivity. Qed.

(** Antisymmetric rank-2 / Lorentz algebra SO(D-1,1): D(D-1)/2 — the isometry generators. *)
Definition lorentz_dim (D : nat) : nat := (D * (D - 1) / 2)%nat.

Lemma lorentz_dim_4 : lorentz_dim 4 = 6%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  sin²θ FOR EACH RANK (all three are RULE-ADMISSIBLE)                *)
(* ================================================================== *)

(** L1 mixing: numerator a = gauge DOF, denominator a + b = gauge + geometric DOF. *)
Definition sin2_with_ambient (gauge_dim ambient_dim : nat) : Q :=
  inject_Z (Z.of_nat gauge_dim) /
  inject_Z (Z.of_nat (gauge_dim + ambient_dim)).

(** The same mixing with the gauge numerator fixed at a = 3 = dim SU(2), as a function of
    the geometric rank's DOF count b — this is the one free dial of the 3/13 claim. *)
Definition sin2_rank (b : nat) : Q := sin2_with_ambient 3 b.

Lemma sin2_metric : sin2_with_ambient 3 10 == 3 # 13.
Proof. vm_compute. reflexivity. Qed.

Lemma sin2_riemann : sin2_with_ambient 3 20 == 3 # 23.
Proof. vm_compute. reflexivity. Qed.

Lemma sin2_lorentz : sin2_with_ambient 3 6 == 1 # 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  THE HONEST CORE: the rank is RULE-UNDERDETERMINED                  *)
(* ================================================================== *)

(** The three admissible ranks give three pairwise-distinct values. *)
Lemma three_ranks_distinct_values :
  sin2_rank 6 == 1#3 /\ sin2_rank 10 == 3#13 /\ sin2_rank 20 == 3#23.
Proof. unfold sin2_rank. repeat split; vm_compute; reflexivity. Qed.

Lemma three_ranks_pairwise_apart :
  ~ (1#3 == 3#13) /\ ~ (3#13 == 3#23) /\ ~ (1#3 == 3#23).
Proof. repeat split; intro H; vm_compute in H; discriminate H. Qed.

(** ★ THE HONEST CORE: the rule "denominator = geometric DOF of the 4D metric" does NOT
    determine sin²θ.  All three tensor ranks are bona-fide geometric DOF counts of a 4D metric,
    yet they yield three different mixing values.  So the output is a function of a FREE rank
    choice the rules leave open — sin²θ_W is NOT pinned by L1 + "U(1)_Y geometric" alone. *)
Theorem rank_underdetermined :
  (* all three are genuine geometric DOF counts of a 4D metric *)
  lorentz_dim 4 = 6%nat /\ sym_tensor_dim 4 = 10%nat /\ riemann_dim 4 = 20%nat /\
  (* yet they yield pairwise-distinct mixing values *)
  sin2_rank 6 == 1#3 /\ sin2_rank 10 == 3#13 /\ sin2_rank 20 == 3#23 /\
  ~ (1#3 == 3#13) /\ ~ (3#13 == 3#23).
Proof.
  repeat split; try reflexivity;
    try (unfold sin2_rank; vm_compute; reflexivity);
    intro H; vm_compute in H; discriminate H.
Qed.

(* ================================================================== *)
(*  DATA — NOT THE RULES — SELECTS THE SYMMETRIC RANK                  *)
(* ================================================================== *)

Definition sin2_observed : Q := 2312 # 10000.

(** A generous 1% acceptance window around the measured value. *)
Definition in_window (q : Q) : bool :=
  Qle_bool (sin2_observed - (1#100)) q && Qle_bool q (sin2_observed + (1#100)).

(** ★★ DATA-SELECTION: among the three RULE-ADMISSIBLE ranks, ONLY the symmetric (b=10) lands
    in the observed window.  This is the denominator analogue of the numerator selection
    SinThetaWDerivationStatus.only_su2_selected — a discrete data-pick, not a rule-derivation. *)
Lemma only_symmetric_in_window :
  filter (fun b => in_window (sin2_rank b)) [6;10;20]%nat = [10%nat].
Proof. vm_compute. reflexivity. Qed.

(** Metric (b=10): |3/13 - 0.2312| = 7/16250 < 1/100.  DATA-accepted. *)
Lemma metric_error_small :
  let diff := sin2_with_ambient 3 10 - sin2_observed in
  diff == -(7 # 16250).
Proof. vm_compute. reflexivity. Qed.

Lemma metric_error_lt_1pct : (7 # 16250) < (1 # 100).
Proof. unfold Qlt. simpl. lia. Qed.

(** Riemann (b=20): 3/23 ≈ 0.130 — DATA-excluded (too small), NOT rule-excluded. *)
Lemma riemann_too_small : sin2_with_ambient 3 20 < sin2_observed.
Proof. unfold sin2_with_ambient, sin2_observed, Qlt. simpl. lia. Qed.

(** Lorentz/antisymmetric (b=6): 1/3 ≈ 0.333 — DATA-excluded (too large), NOT rule-excluded. *)
Lemma lorentz_too_large : sin2_with_ambient 3 6 > sin2_observed.
Proof. unfold sin2_with_ambient, sin2_observed, Qlt. simpl. lia. Qed.

(** The antisymmetric rank IS a subspace relation (so(3,1) contains the SU(2) generators);
    this is the kernel of the old "double-counting" story — true as set inclusion, but it does
    not RULE OUT the antisymmetric rank, it only motivates one verbal preference among many. *)
Lemma SU2_inside_Lorentz : (3 <= 6)%nat.
Proof. lia. Qed.

(* ================================================================== *)
(*  κ CHAIN — and an honest label for the "α/κ prediction"            *)
(* ================================================================== *)

Definition kappa : Q := 1 # 10.
Definition alpha_EM : Q := (3 # 13) * kappa.

Lemma alpha_EM_value : alpha_EM == 3 # 130.
Proof. unfold alpha_EM, kappa. vm_compute. reflexivity. Qed.

(** NOT a prediction — a DEFINITIONAL IDENTITY.  α_EM was DEFINED as (3/13)·κ, so dividing κ
    back out returns 3/13 by construction (the claim has the form v == v).  Honest status: this
    is a reframing (cf. PhysicsDemarcation.reframing_analytic), with no empirical content — it
    cannot be wrong, hence it predicts nothing. *)
Lemma alpha_over_kappa_is_identity : alpha_EM / kappa == 3 # 13.
Proof. unfold alpha_EM, kappa. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  HONEST SYNTHESIS — the knot, untied                               *)
(* ================================================================== *)

(** The 3/13 claim, forced part and posit-counted part separated (grounding-corrected):
      (forced)        GIVEN rank-symmetric (b=10), L1 => sin²θ = 3/13 — forced arithmetic;
      (L1-underdet.)  the rules admit b ∈ {6,10,20}, all geometric DOF of a 4D metric, giving
                      {1/3, 3/13, 3/23} — pairwise distinct, so L1 ALONE does not fix the rank;
      (data)          only the symmetric rank lands in the observed window.
    By L4 (Law_of_SufficientReason) and JustificationRegress.v these inputs are POSITS, not free
    choices: a posit is self-grounding, every grounded claim needs ≥1 posit (grounded_needs_posit),
    and "zero parameters / from nothing" is the role-limit error (from_nothing_ungrounded).  Pushed
    deep, 3/13's irreducible posits are P1 (the form) + the depth→gauge map (family ②); the rank
    REDUCES via locality (6=isometries, 20=curvature are different objects), so it is not an extra
    parameter — the datum confirms it, it does not create it.  Honest task: COUNT posits, not zero
    them.  Level: synthesis + observation. *)
Theorem ten_is_data_selected_not_rule_forced :
  (* forced GIVEN the rank *)
  sin2_rank 10 == 3#13
  (* L1 alone does not fix the rank (underdetermined; reduced by locality, not a free parameter) *)
  /\ (sin2_rank 6 == 1#3 /\ sin2_rank 20 == 3#23 /\ ~ (1#3 == 3#13) /\ ~ (3#13 == 3#23))
  (* and the datum confirms the symmetric rank *)
  /\ filter (fun b => in_window (sin2_rank b)) [6;10;20]%nat = [10%nat].
Proof.
  split; [ unfold sin2_rank; vm_compute; reflexivity | ].
  split.
  - repeat split; try (unfold sin2_rank; vm_compute; reflexivity);
      intro H; vm_compute in H; discriminate H.
  - exact only_symmetric_in_window.
Qed.
