(** * FinitizationNoCutoff.v — the honest physics reckoning: finitization ≠ a physical cutoff.
      Using CHSH/Tsirelson as the vehicle, this formalizes precisely what physics the ℚ-only /
      finitization view does and does NOT predict.  ToS-finitization (potential infinity:
      role-limits are UNBOUNDED processes) predicts NO measurable deviation from continuum QM —
      the rational CHSH configurations climb from the classical bound 2 toward Tsirelson 2√2 with
      a gap 4/q² that has NO positive floor (q unbounded).  A GRANULAR theory (Palmer/Carroll:
      bounded resolution q ≤ Q) instead predicts a FIXED positive gap ≥ 4/Q² — a falsifiable
      deviation.  So "amplitudes are processes (P4)" does NOT entail "the substrate is granular":
      that needs an extra cutoff axiom ToS rejects.  ToS sits with Gisin (indeterminism / unbounded
      process), against 't Hooft/Carroll/Palmer (granular substrate).

    Elements: the Pell configurations (pₖ,qₖ); the rational CHSH values 2, 14/5, 82/29; the gaps
              4, 4/25, 4/841 (L1 + P4)
    Roles:    Element side = each finite-actual configuration (rational S, finite settings/statistics),
              with S² < 8 strictly; role-limit = 2√2 = √8 (unbounded process, never actualized)
    Rules:    the Pell tower (pₖ²−2qₖ²=−1) climbs from the classical bound 2 to Tsirelson 2√2;
              S² = 8 − 4/qₖ², so the gap is 4/qₖ² and q is unbounded ⟹ gap → 0 with no positive floor

    THE DEEP POINT — finitization ≠ cutoff; the verdict made precise.  Every actual CHSH
    configuration is rational (finite precision), so S is a rational < 2√2 (`chsh_below_tsirelson`:
    pₖ² < 2qₖ², i.e. S² < 8 always — Tsirelson is never reached).  The gap to Tsirelson is exactly
    4/qₖ² (`gap_numerator`: 8qₖ² − 4pₖ² = 4), and q is UNBOUNDED (`q_unbounded`: qₖ ≥ 1 + k), so the
    gap has no positive lower bound — ToS predicts NO deviation from continuum QM.  But a granular
    theory frozen at resolution Q predicts a FIXED gap ≥ 4/Q² > 0 — falsifiable (the concrete tower
    2, 14/5, 82/29 with gaps 4, 4/25, 4/841 shows a Q=5 theory caps S ≤ 14/5, refuted by S≈2.82).
    2√2 = √8 is a role-limit (`tsirelson_role_limit`, no rational squares to 8).  Element = a
    finite-actual rational configuration; role-limit = the unbounded process 2√2 it never reaches.
    The no-go: P4 (finite actuality) ≠ finite substrate.

    ============ E/R/R разбор ============
      Rules (L5): Пелль-башня (pₖ²−2qₖ²=−1) поднимается от классической границы 2 к Цирельсону 2√2;
                  S²=8−4/qₖ², зазор=4/qₖ², q неограничено ⟹ зазор→0 без положительного дна.
      Roles (L4): Element = конечно-актуальная конфигурация (рациональное S, S²<8 строго); role-limit =
                  2√2=√8 (неограниченный процесс, не актуализируется).
      Elements  : Пелль-конфигурации (pₖ,qₖ); S=2,14/5,82/29; зазоры 4,4/25,4/841 (L1+P4).
    ДИАГНОСТИКА (P4): «S=2√2 точно?» = не-вопрос (2√2 role-limit). Зазор 4/qₖ²→0 без дна (q неограничено) ⟹
    ToS предсказывает НУЛЕВОЕ отклонение от КМ (эмпирически = КМ); ГРАНУЛЯРНАЯ теория (q≤Q) предсказывает фиксир.
    зазор ≥4/Q²>0 (фальсифицируемо). No-go: «амплитуды = процессы (P4)» НЕ влечёт «субстрат гранулярен» — нужна
    доп. аксиома обрезания, отвергаемая ToS. Финитизация ≠ обрезание; ToS = эмпирически КМ, отделена от гранулярных.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The Pell tower of rational CHSH configurations climbing to Tsirelson   *)
(* ===================================================================== *)

(** One step of the √2-unit (3+2√2): preserves the form p²−2q². *)
Definition pstep (pq : Z * Z) : Z * Z :=
  (3 * fst pq + 4 * snd pq, 2 * fst pq + 3 * snd pq).

Fixpoint pell (k : nat) : Z * Z :=
  match k with O => (1, 1) | S k' => pstep (pell k') end.

Definition pp (k : nat) : Z := fst (pell k).
Definition qq (k : nat) : Z := snd (pell k).

Lemma pp_S : forall k, pp (S k) = 3 * pp k + 4 * qq k.
Proof. reflexivity. Qed.

Lemma qq_S : forall k, qq (S k) = 2 * pp k + 3 * qq k.
Proof. reflexivity. Qed.

(** ★ The CHSH-configuration invariant: pₖ² − 2qₖ² = −1 for every k. *)
Lemma pell_inv : forall k, pp k * pp k - 2 * (qq k * qq k) = -1.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - rewrite pp_S, qq_S.
    assert (E : (3 * pp k + 4 * qq k) * (3 * pp k + 4 * qq k)
                - 2 * ((2 * pp k + 3 * qq k) * (2 * pp k + 3 * qq k))
                = pp k * pp k - 2 * (qq k * qq k)) by ring.
    rewrite E. exact IH.
Qed.

(** The configuration coordinates are positive (proved jointly). *)
Lemma pell_pos : forall k, 1 <= pp k /\ 1 <= qq k.
Proof.
  induction k as [| k [IHp IHq]].
  - split; reflexivity.
  - rewrite pp_S, qq_S. split; lia.
Qed.

Lemma pp_pos : forall k, 1 <= pp k.
Proof. intros k. apply (pell_pos k). Qed.

Lemma qq_pos : forall k, 1 <= qq k.
Proof. intros k. apply (pell_pos k). Qed.

(* ===================================================================== *)
(*  Tsirelson is never reached, and the gap is exactly 4/q²                *)
(* ===================================================================== *)

(** ★ Every rational configuration stays strictly below Tsirelson: S² < 8, i.e. pₖ² < 2qₖ²
    (from the invariant pₖ²−2qₖ² = −1 < 0).  Tsirelson 2√2 is never attained by an Element. *)
Lemma chsh_below_tsirelson : forall k, pp k * pp k < 2 * (qq k * qq k).
Proof. intros k. pose proof (pell_inv k). lia. Qed.

(** ★ The gap to Tsirelson, at integer scale: 8qₖ² − 4pₖ² = 4 for every k.  Since S² = 4pₖ²/qₖ²,
    this says the gap 8 − S² equals 4/qₖ² exactly — the gap is controlled by 1/q². *)
Lemma gap_numerator : forall k, 8 * (qq k * qq k) - 4 * (pp k * pp k) = 4.
Proof. intros k. pose proof (pell_inv k). lia. Qed.

(* ===================================================================== *)
(*  The resolution q is UNBOUNDED ⟹ the gap has no positive floor          *)
(* ===================================================================== *)

(** The resolution strictly increases each step. *)
Lemma qq_strict_incr : forall k, qq k < qq (S k).
Proof.
  intros k. rewrite qq_S. pose proof (pp_pos k). pose proof (qq_pos k). lia.
Qed.

(** ★ The resolution is UNBOUNDED: qₖ ≥ 1 + k.  Hence the gap 4/qₖ² has NO positive lower bound —
    ToS-finitization imposes no cutoff (no minimum quantum), so it predicts no deviation from QM. *)
Lemma q_unbounded : forall k, 1 + Z.of_nat k <= qq k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - rewrite qq_S, Nat2Z.inj_succ. pose proof (pp_pos k). lia.
Qed.

(* ===================================================================== *)
(*  Concrete tower: classical bound 2 → 14/5 → 82/29 → … → Tsirelson       *)
(* ===================================================================== *)

(** The (signed) CHSH value of a configuration p/q, and its gap to Tsirelson² = 8. *)
Definition S_of (p q : Z) : Q := 2 * inject_Z p / inject_Z q.
Definition gap_of (p q : Z) : Q := 8 - S_of p q * S_of p q.

(** ★ The tower climbs from the classical bound (S=2, gap 4) toward Tsirelson, gap = 4/q²:
      k=0: (1,1)  S=2     gap 4      (the classical/local bound)
      k=1: (7,5)  S=14/5  gap 4/25
      k=2: (41,29) S=82/29 gap 4/841
    The gap strictly shrinks (4 > 4/25 > 4/841): a granular theory frozen at q=5 caps S ≤ 14/5
    (gap 4/25), which experiments reaching S≈2.82 refute; ToS (unbounded q) caps nothing below 2√2. *)
Lemma gap_classical : gap_of 1 1 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_k1 : gap_of 7 5 == 4 # 25.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_k2 : gap_of 41 29 == 4 # 841.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_shrinks_0_1 : (gap_of 7 5 < gap_of 1 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_shrinks_1_2 : (gap_of 41 29 < gap_of 7 5)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Tsirelson itself is a role-limit                                       *)
(* ===================================================================== *)

(** ★ The Tsirelson bound 2√2 = √8 is a role-limit: no rational squares to 8 (else (s/2)²=2).
    So 2√2 is an unbounded process — approached by the rational tower, never actualized. *)
Theorem tsirelson_role_limit : ~ (exists s : Q, (s * s == 8)%Q).
Proof.
  intros [s Hs]. apply sqrt2_not_in_Q. exists (s * (1 # 2))%Q.
  assert (Hr : ((s * (1 # 2)) * (s * (1 # 2)) == (s * s) * (1 # 4))%Q) by ring.
  rewrite Hr, Hs. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis: the honest verdict                                          *)
(* ===================================================================== *)

(** The physics reckoning, made precise:
      (a) Tsirelson is a role-limit (`tsirelson_role_limit`) and is NEVER reached by an Element
          (`chsh_below_tsirelson`: S² < 8 at every configuration);
      (b) the gap is exactly 4/q² (`gap_numerator`) with q UNBOUNDED (`q_unbounded`) — so it has
          no positive floor: ToS-finitization imposes NO cutoff and predicts NO deviation from QM;
      (c) a granular theory (bounded q) would predict a fixed positive gap (the concrete tower
          `gap_classical`/`gap_k1`/`gap_k2` shows the falsifiable caps) — DIFFERENT from ToS.
    Hence finitization ≠ cutoff: P4 (finite actuality) does not entail a finite substrate. *)
Theorem finitization_no_cutoff_synthesis :
  (~ (exists s : Q, (s * s == 8)%Q))
  /\ (forall k, pp k * pp k < 2 * (qq k * qq k))
  /\ (forall k, 8 * (qq k * qq k) - 4 * (pp k * pp k) = 4)
  /\ (forall k, 1 + Z.of_nat k <= qq k)
  /\ (gap_of 41 29 < gap_of 7 5)%Q.
Proof.
  split; [ exact tsirelson_role_limit | ].
  split; [ exact chsh_below_tsirelson | ].
  split; [ exact gap_numerator | ].
  split; [ exact q_unbounded | exact gap_shrinks_1_2 ].
Qed.
