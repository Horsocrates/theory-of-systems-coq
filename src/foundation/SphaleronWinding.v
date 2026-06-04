(** * SphaleronWinding.v — Baryogenesis Phase 1: the B-violation face (Sakharov-1 = P4) realized as a
      DISCRETE winding-number jump.  A sphaleron transition changes the Chern–Simons (winding) number by
      ΔN_CS = ±1 and, through the electroweak anomaly, the baryon count by ΔB = n_gen · ΔN_CS = 3·ΔN_CS
      — a quantized, integer, P4-finite change.  B is NOT conserved (the actual count is dynamic), but
      B−L IS conserved (the genuine invariant role) — which foreshadows the honest gap (Phase 4).

    This fills the FIRST missing face of SakharovERR.v: the B-violation (P4) factor.  In SakharovERR the
    asymmetry is the triad product η = (CP)·(B-violation)·(out-of-equilibrium); here the B-violation face
    is realized with integer/topological teeth (it is genuinely ON: ΔB = 3 ≠ 0).

    ── Physics ──
      The baryon current has an electroweak anomaly: ∂·J_B = (n_gen/32π²) g² W·W̃.  Integrated, the
      baryon-number change across a transition equals n_gen times the change in Chern–Simons number:
        ΔB = n_gen · ΔN_CS,   with ΔN_CS = ±1 for one sphaleron (connecting adjacent vacua).
      n_gen = 3 (DERIVED in ToS: GenerationsPositReduction.generations_unique), so ΔB = ±3 — one baryon
      per generation.  Lepton number shifts identically (ΔL = n_gen·ΔN_CS), so ΔB = ΔL ⟹ Δ(B−L) = 0:
      the sphaleron violates B+L but conserves B−L.

    ── E/R/R reading ──
      Rules (L5):  a DISCRETE jump ΔB = n_gen·ΔN_CS (quantized, not continuous leakage);
      Roles (L4):  the winding number labels the Z-indexed vacuum sectors; the sphaleron connects
                   adjacent sectors; B and L shift together (B+L violated, B−L the invariant role);
      Elements:    the integer winding number (a discrete, P4-finite count); ΔB = 3 (= n_gen, derived).

    HONEST: the sphaleron RATE (∝ α_w⁵ e^{−E_sph/T}) — the magnitude of the B-violation factor — is the
    L5 transport of Phase 2; here we establish the STRUCTURE (the jump is quantized, ΔB = 3 ≠ 0, B−L
    conserved).  The B−L conservation is exactly why the SM struggles to make net B (Phase 4 gap).

    Elements: winding sectors (Z), the sphaleron jump ΔN_CS = ±1, ΔB = n_gen·ΔN_CS
    Roles:    B-violation = the P4 face (count changes); B−L = the conserved invariant role
    Rules:    ΔB = 3·ΔN_CS (discrete, quantized); B not conserved, B−L conserved; quantum = n_gen (derived)

    ============ E/R/R разбор ============
      Rules (L5): дискретный скачок ΔB = n_gen·ΔN_CS (квантовано); B не сохраняется, B−L сохраняется.
      Roles (L4): число намотки метит Z-секторы вакуума; сфалерон соединяет соседние; B,L сдвигаются
                  вместе (B+L нарушено, B−L = инвариантная роль).
      Elements  : целое число намотки (дискретный P4-конечный счёт); ΔB=3 (=n_gen, выведено).
    ДИАГНОСТИКА (P4): B-нарушение = грань P4 триады (актуальный счёт меняется), реализованная
    топологически. Квант ΔB=3 выведен (n_gen из L4). Целочисленность намотки = P4-конечность. B−L
    сохраняется (ΔB=ΔL) — предвещает SM-разрыв (Фаза 4). Заполняет грань P4 SakharovERR реальными зубами.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import foundation.GenerationsPositReduction.  (* generations_unique, L4_minimal_generations *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The generation count (derived) and the baryon/lepton response          *)
(* ===================================================================== *)

(** Number of generations — DERIVED: GenerationsPositReduction.generations_unique (L4-minimality). *)
Definition n_gen : nat := 3%nat.

Lemma n_gen_is_three : n_gen = 3%nat.
Proof. reflexivity. Qed.

(** Baryon-number change across a transition of winding number ΔN_CS: ΔB = n_gen · ΔN_CS (anomaly). *)
Definition delta_B (dncs : Z) : Z := Z.of_nat n_gen * dncs.

(** Lepton number shifts identically (the anomaly is the same for B and L). *)
Definition delta_L (dncs : Z) : Z := Z.of_nat n_gen * dncs.

(* ===================================================================== *)
(*  One sphaleron (ΔN_CS = ±1): ΔB = ±3 — the quantized jump               *)
(* ===================================================================== *)

(** ★ One sphaleron transition (ΔN_CS = 1) changes B by exactly 3 — one baryon per generation. *)
Lemma sphaleron_delta_B : delta_B 1 = 3.
Proof. unfold delta_B, n_gen. lia. Qed.

(** ★ B is NOT conserved: the sphaleron changes it.  This is the P4 face — the actual count is dynamic
    (were this factor 0, SakharovERR.eta_zero_if_no_bviol would give η = 0). *)
Lemma sphaleron_violates_B : delta_B 1 <> 0.
Proof. unfold delta_B, n_gen. lia. Qed.

(** k sphaleron transitions change B by 3k — linear and discrete in the winding number. *)
Lemma multiple_sphalerons : forall k, delta_B k = 3 * k.
Proof. intro k. unfold delta_B, n_gen. lia. Qed.

(* ===================================================================== *)
(*  B−L is conserved: the genuine invariant role (foreshadows the gap)     *)
(* ===================================================================== *)

(** ★ B−L IS conserved: ΔB = ΔL, so Δ(B−L) = 0.  The sphaleron violates B+L but preserves B−L —
    the invariant role.  (This is exactly why net B is hard to generate — the Phase-4 honest gap.) *)
Lemma sphaleron_conserves_BminusL : forall d, delta_B d - delta_L d = 0.
Proof. intro d. unfold delta_B, delta_L, n_gen. lia. Qed.

(* ===================================================================== *)
(*  Winding sectors are Z-indexed (discrete = P4-finite); adjacency        *)
(* ===================================================================== *)

(** A sphaleron connects ADJACENT winding sectors (ΔN_CS = ±1). *)
Definition adjacent (n m : Z) : Prop := m = n + 1 \/ m = n - 1.

Lemma sphaleron_adjacent : forall n, adjacent n (n + 1).
Proof. intro n. left. reflexivity. Qed.

(** ★ Across an adjacent-sector (sphaleron) transition, B changes by exactly ±3 — a discrete quantum. *)
Lemma B_change_across_sphaleron :
  forall n m, adjacent n m -> delta_B (m - n) = 3 \/ delta_B (m - n) = -3.
Proof.
  intros n m [H | H]; subst m.
  - left. unfold delta_B, n_gen. lia.
  - right. unfold delta_B, n_gen. lia.
Qed.

(* ===================================================================== *)
(*  The B-violation quantum IS the derived generation count                *)
(* ===================================================================== *)

(** ★ The baryon-number quantum equals the DERIVED generation count (3): the B-violation jump is not a
    free number — it is n_gen, fixed by L4-minimality (GenerationsPositReduction.generations_unique). *)
Lemma B_quantum_is_generation_count :
  forall gen, L4_minimal_generations gen -> Z.of_nat gen = Z.of_nat n_gen.
Proof. intros gen H. rewrite (generations_unique gen H). reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the B-violation face (P4) realized as a winding jump          *)
(* ===================================================================== *)

(** The sphaleron / winding realization of the B-violation (P4) face:
      (quantum)  one sphaleron (ΔN_CS = 1) gives ΔB = 3 — one baryon per generation;
      (P4 face)  B is NOT conserved (ΔB ≠ 0) — the actual count is dynamic;
      (invariant) B−L IS conserved (ΔB = ΔL) — the genuine invariant role (foreshadows the gap);
      (discrete) k sphalerons give ΔB = 3k — quantized, integer, P4-finite;
      (derived)  the quantum is the DERIVED generation count (3), not a free number.
    The B-violation face of SakharovERR's triad is realized with integer/topological teeth. *)
Theorem sphaleron_winding :
  delta_B 1 = 3
  /\ delta_B 1 <> 0
  /\ (forall d, delta_B d - delta_L d = 0)
  /\ (forall k, delta_B k = 3 * k)
  /\ (forall gen, L4_minimal_generations gen -> Z.of_nat gen = Z.of_nat n_gen).
Proof.
  split; [ exact sphaleron_delta_B | ].
  split; [ exact sphaleron_violates_B | ].
  split; [ exact sphaleron_conserves_BminusL | ].
  split; [ exact multiple_sphalerons | ].
  exact B_quantum_is_generation_count.
Qed.
