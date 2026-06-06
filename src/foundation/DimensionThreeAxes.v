(** * DimensionThreeAxes.v — deepening hint ③ further: the THIRD axis of "dimension" = finitization.
       DimensionTwoAxes gave (rank, type): the nesting depth (thread ③) and the causal type (sign of Δ,
       GRQFT BIT 1).  The GR↔QFT discriminant bridge has a SECOND bit (GRQFT BIT 2): whether Δ = tr²−4det
       is a PERFECT (rational) SQUARE — rational eigenvalue = ELEMENT (terminates, 0-axiom) vs irrational
       eigenvalue = ROLE-LIMIT (the P4 finitization boundary, the project's flagship axis).  So the full
       dimensional locus is (rank, type, fin) ∈ ℕ × DimType × Fin — WHERE in the hierarchy, WHAT KIND of
       direction, and WHETHER it TERMINATES.

       THE THREE AXES ARE MUTUALLY INDEPENDENT.
         • type does NOT fix fin: within NonCompact (boost, Δ>0) BOTH fin occur — the 3-4-5 boost has
           Δ=9/4=(3/2)² (Element) while the Pell √2 boost has Δ=32 (role-limit: √32=4√2 ∉ ℚ);
         • nesting preserves BOTH Δ-bits (type and fin), so rank is orthogonal to both.
       HONEST NUANCE (exactly GRQFT's "within Δ≥0"): for Δ<0 (Compact) the square predicate is vacuously
       false (a square is never negative), so the fin bit only REFINES the Δ≥0 (Null/NonCompact) sector.

    WHAT THE REPO HAS (surveyed): GRQFTDiscriminantBridge.v (both Δ-bits, the concrete boosts, imported);
    DimensionTwoAxes.v (rank+type, imported); analysis/Sqrt2Irrational.v (sqrt2_not_in_Q, for the √32
    role-limit witness, imported).  No three-axis dimension locus exists — this adds it.

    ============ E/R/R разбор ============
      Elements : локус (rank, type, fin): rank (нить ③), type (знак Δ), fin (квадратность Δ); конкретные
                 бусты b (Δ=9/4 Element) и p (Δ=32 role-limit).
      Roles    : rank = ГДЕ (вложенность); type = КАКОГО РОДА (internal/external); fin = ТЕРМИНИРУЕТ ЛИ
                 (Element/role-limit) — третья независимая координата.
      Rules    : Δ<0 ⟹ квадрат невозможен (fin уточняет лишь Δ≥0); внутри NonCompact оба fin (b Element,
                 p role-limit); вложенность хранит оба Δ-бита ⟹ три оси взаимно ортогональны.
      ДИАГНОСТИКА (P4): полная спецификация измерения = (rank, type, fin) = где × какого рода × терминирует
      ли; тип НЕ фиксирует fin ⟹ fin независим (P4-граница финитизации как третья ось). ЧЕСТНО: fin
      содержателен лишь в Δ≥0; формализую структуру + независимость, НЕ физику. Уровень: `синтез`.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.GRQFTDiscriminantBridge.
From ToS Require Import foundation.DimensionTwoAxes.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The THIRD axis: finitization = Δ a perfect square (Element vs role-limit) *)
(* ===================================================================== *)

(** The finitization type of a direction (GRQFT BIT 2): Element = Δ a rational square (rational eigenvalue,
    terminates) vs RoleLimit = not (irrational eigenvalue, the continuum). *)
Inductive Fin : Set := FElement | FRoleLimit.

(** Δ is a perfect (rational) square — the Element side. *)
Definition disc_is_square (a b c d : Q) : Prop := exists r : Q, r * r == mdisc a b c d.

(** A rational square is never negative (used for the Δ<0 degeneracy). *)
Lemma q_sqr_nonneg : forall r : Q, 0 <= r * r.
Proof.
  intro r. destruct (Qlt_le_dec r 0) as [Hlt | Hge].
  - assert (Heq : r * r == (- r) * (- r)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(** ★ The 3-4-5 boost is ELEMENT: Δ = 9/4 = (3/2)² (reusing GRQFT's boost345_disc_square). *)
Lemma boost345_fin_element : disc_is_square b_a b_b b_c b_d.
Proof. unfold disc_is_square. exists (3#2). exact boost345_disc_square. Qed.

(** ★ The Pell √2 boost is ROLE-LIMIT: Δ = 32 = 16·2, and √32 = 4√2 ∉ ℚ (reusing sqrt2_not_in_Q):
    if r² = 32 then (r/4)² = 2, contradicting the irrationality of √2. *)
Lemma boostP_fin_rolelimit : ~ disc_is_square p_a p_b p_c p_d.
Proof.
  unfold disc_is_square. intros [r Hr]. rewrite boostP_disc in Hr.
  apply sqrt2_not_in_Q. exists (r * (1#4)).
  assert (H : (r * (1#4)) * (r * (1#4)) == (r * r) * (1#16)) by ring.
  rewrite H, Hr. lra.
Qed.

(** ★ Honest nuance (GRQFT "within Δ≥0"): for Δ<0 (Compact) the square predicate is vacuously false —
    a square is never negative.  So the fin bit only REFINES the Δ≥0 (Null/NonCompact) sector. *)
Lemma compact_disc_not_square : forall a b c d, mdisc a b c d < 0 -> ~ disc_is_square a b c d.
Proof.
  intros a b c d Hneg [r Hr]. assert (Hnn := q_sqr_nonneg r). rewrite Hr in Hnn. lra.
Qed.

(** ★★ The type axis does NOT fix the fin axis: two NON-COMPACT (boost) directions, one Element one
    role-limit — fin is a GENUINELY independent third coordinate within the causal (Δ>0) sector. *)
Theorem type_does_not_fix_fin :
  (is_noncompact b_a b_b b_c b_d /\ disc_is_square b_a b_b b_c b_d)
  /\ (is_noncompact p_a p_b p_c p_d /\ ~ disc_is_square p_a p_b p_c p_d).
Proof.
  split; split.
  - exact boost_is_noncompact.
  - exact boost345_fin_element.
  - unfold is_noncompact. exact boostP_hyperbolic.
  - exact boostP_fin_rolelimit.
Qed.

(* ===================================================================== *)
(*  The three-axis dimensional locus (rank, type, fin)                     *)
(* ===================================================================== *)

(** A full dimensional locus: WHERE (nesting rank), WHAT KIND (causal type), WHETHER it TERMINATES (fin). *)
Record DimLocus : Set := mkDL { dl_rank : nat ; dl_type : DimType ; dl_fin : Fin }.

(** The nesting transition on the 3-locus (up one rank). *)
Definition dl_up (X : DimLocus) : DimLocus := mkDL (S (dl_rank X)) (dl_type X) (dl_fin X).

Lemma dl_up_rank : forall X, dl_rank (dl_up X) = S (dl_rank X).
Proof. intro X. reflexivity. Qed.

(** ★ Nesting preserves the TYPE bit (orthogonal to axis 2). *)
Lemma dl_up_preserves_type : forall X, dl_type (dl_up X) = dl_type X.
Proof. intro X. reflexivity. Qed.

(** ★ Nesting preserves the FIN bit (orthogonal to axis 3). *)
Lemma dl_up_preserves_fin : forall X, dl_fin (dl_up X) = dl_fin X.
Proof. intro X. reflexivity. Qed.

(** Apply the nesting step n times: the rank axis spans ℕ at any fixed (type, fin). *)
Fixpoint dl_iter (n : nat) (X : DimLocus) : DimLocus :=
  match n with O => X | S k => dl_up (dl_iter k X) end.

Lemma dl_reach : forall t f n, dl_iter n (mkDL 0%nat t f) = mkDL n t f.
Proof.
  intros t f; induction n as [| k IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** "Dimension" is fully specified by THREE independent axes:
      (rank)   WHERE in the nesting hierarchy (thread ③, open process);
      (type)   WHAT KIND of direction — Δ-sign (internal/gauge vs external/spacetime);
      (fin)    WHETHER it TERMINATES — Δ a perfect square: Element vs role-limit (the P4 boundary);
      (indep₁) type does NOT fix fin: NonCompact splits into Element (Δ=9/4) and role-limit (Δ=32);
      (Δ<0)    the fin bit refines only the Δ≥0 sector (a square is never negative);
      (indep₂) nesting preserves BOTH Δ-bits, so rank is orthogonal to type and fin;
      (span)   the rank axis spans ℕ at any fixed (type, fin).
    So the full dimensional locus is (rank, type, fin) ∈ ℕ × DimType × Fin: where × what-kind × terminates.
    Honest: the 3-axis STRUCTURE and independence, with fin meaningful in the Δ≥0 (causal) sector — NOT a
    physical claim about dimensions. *)
Theorem dimension_three_axes :
  (is_noncompact b_a b_b b_c b_d /\ disc_is_square b_a b_b b_c b_d)
  /\ (is_noncompact p_a p_b p_c p_d /\ ~ disc_is_square p_a p_b p_c p_d)
  /\ (forall a b c d, mdisc a b c d < 0 -> ~ disc_is_square a b c d)
  /\ (forall X, dl_type (dl_up X) = dl_type X /\ dl_fin (dl_up X) = dl_fin X)
  /\ (forall t f n, dl_iter n (mkDL 0%nat t f) = mkDL n t f).
Proof.
  split. exact (proj1 type_does_not_fix_fin).
  split. exact (proj2 type_does_not_fix_fin).
  split. exact compact_disc_not_square.
  split. intro X. split; [ exact (dl_up_preserves_type X) | exact (dl_up_preserves_fin X) ].
  exact dl_reach.
Qed.
