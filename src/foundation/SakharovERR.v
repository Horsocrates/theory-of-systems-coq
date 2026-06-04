(** * SakharovERR.v — Baryogenesis Phase 3 (the gem): the THREE Sakharov conditions ARE the E/R/R
      triad of the baryon count.  η_B is a triadic PRODUCT η = (CP)·(B-violation)·(out-of-equilibrium);
      the three conditions map bijectively onto the three E/R/R levels {P4, L2, L5}; the product
      collapses to 0 if ANY factor is 0 (necessity) and is positive if ALL three are (sufficiency).
      This answers "why exactly three Sakharov conditions" — because the triad has exactly three levels.

    Sakharov (1967) gave three necessary conditions for a matter-antimatter asymmetry:
      (1) baryon-number violation, (2) C and CP violation, (3) departure from thermal equilibrium.
    ToS reading: these are not three independent physics inputs — they are the three FACES of one
    structure, the E/R/R triad of the baryon count:

      B-violation       ↔ P4 (Finite Actuality)  : the actual baryon COUNT can change (not frozen);
      C/CP violation    ↔ L2 (Distinction)        : matter ≠ antimatter = the asymmetric distinction;
      out-of-equilibrium↔ L5 (Process / arrow)     : irreversible, ℕ-indexed evolution (never static).

    The generative law (L5) is a triadic PRODUCT: η = cp · bviol · noneq.  Geometrically, η is the
    VOLUME of the E/R/R box with edges (cp, bviol, noneq): a box has nonzero volume iff all three edges
    are nonzero.  So Sakharov necessity = "the box collapses if any edge is 0" and Sakharov sufficiency
    = "positive edges → positive volume" — the three conditions are jointly necessary-and-sufficient
    BECAUSE they are the three orthogonal dimensions of the triad.

    Each face is already a ToS theorem (cited): CP from 3 generations (EtaFromLattice.cp_phase_derived,
    jarlskog_positive), B-violation from the sphaleron/GUT sector (Phase 1, ProcessProtonDecay), out-of-
    equilibrium from the arrow (ThermodynamicArrow).  Here the CP factor is anchored to the REAL derived
    Jarlskog invariant; the other two are carried as positive factors (filled by the later phases).  The
    MAGNITUDE of η_B stays SM-bounded (the honest ~10⁹ gap is Phase 4) — this file is the STRUCTURE.

    Elements: the three Q factors (cp = Jarlskog, bviol, noneq); η = their product
    Roles:    each Sakharov condition ↔ one E/R/R level (P4, L2, L5) — a bijection
    Rules:    η is the triadic product; necessity (any factor 0 ⟹ η=0) + sufficiency (all >0 ⟹ η>0)

    ============ E/R/R разбор ============
      Rules (L5): закон бариогенезиса = триадное произведение η=(CP)(B-нар)(неравн); необходимость
                  (любой множитель 0 ⟹ η=0) + достаточность (все >0 ⟹ η>0); η = объём триадного ящика.
      Roles (L4): B-нар↔P4, CP↔L2, неравн↔L5 — три условия Сахарова биективны трём уровням E/R/R
                  («почему ровно три» = три уровня триады).
      Elements  : три Q-множителя (CP = реальный Ярлског, B-нар, неравн); η = их произведение.
    ДИАГНОСТИКА (P4): три условия Сахарова — не три входа, а три грани ОДНОЙ триады счёта барионов;
    каждая = теорема ToS. η_B = необходимый остаток триады; placeholder подменял L5-произведение —
    здесь обнажаем триадную структуру (необходимость+достаточность). Величина = SM-граница (Фаза 4).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.
From ToS Require Import foundation.EtaFromLattice.   (* jarlskog_estimate, jarlskog_positive, cp_phase_derived *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The three Sakharov conditions ↔ the three E/R/R levels (bijection)      *)
(* ===================================================================== *)

Inductive SakharovCondition := BViolation | CPViolation | OutOfEquilibrium.
Inductive ERRLevel := P4_Actuality | L2_Distinction | L5_Process.

(** Each Sakharov condition IS one E/R/R level. *)
Definition sakharov_err (s : SakharovCondition) : ERRLevel :=
  match s with
  | BViolation       => P4_Actuality    (* the actual baryon count can CHANGE — P4 *)
  | CPViolation      => L2_Distinction  (* matter ≠ antimatter = the asymmetric distinction — L2 *)
  | OutOfEquilibrium => L5_Process      (* irreversible ℕ-indexed process / arrow — L5 *)
  end.

(** ★ The map is INJECTIVE: distinct conditions ↔ distinct levels. *)
Lemma sakharov_err_injective :
  forall s1 s2, sakharov_err s1 = sakharov_err s2 -> s1 = s2.
Proof. intros [] []; simpl; congruence. Qed.

(** ★ The map is SURJECTIVE onto the three levels: every E/R/R level is some Sakharov condition.
    Together with injectivity: a BIJECTION — "why exactly three conditions" = three triad levels. *)
Lemma sakharov_err_surjective :
  forall l, exists s, sakharov_err s = l.
Proof. intros []; [ exists BViolation | exists CPViolation | exists OutOfEquilibrium ]; reflexivity. Qed.

(* ===================================================================== *)
(*  η_B = the triadic product (CP)·(B-violation)·(out-of-equilibrium)       *)
(* ===================================================================== *)

(** The baryon asymmetry is the triadic product — the VOLUME of the E/R/R box. *)
Definition eta_triad (cp bviol noneq : Q) : Q := cp * bviol * noneq.

(* ---- NECESSITY: drop any one face ⟹ η = 0 (the triad/box collapses) ---- *)

(** ★ No CP (the distinction face, L2): η = 0. *)
Lemma eta_zero_if_no_cp : forall b e, eta_triad 0 b e == 0.
Proof. intros. unfold eta_triad. ring. Qed.

(** ★ No B-violation (the actuality face, P4): η = 0. *)
Lemma eta_zero_if_no_bviol : forall c e, eta_triad c 0 e == 0.
Proof. intros. unfold eta_triad. ring. Qed.

(** ★ No out-of-equilibrium (the process face, L5): η = 0. *)
Lemma eta_zero_if_no_noneq : forall c b, eta_triad c b 0 == 0.
Proof. intros. unfold eta_triad. ring. Qed.

(* ---- the necessity converse: a positive η forces each (nonneg) face positive ---- *)

Lemma eta_pos_needs_cp : forall c b e, 0 <= c -> 0 < eta_triad c b e -> 0 < c.
Proof.
  intros c b e Hc Hpos. destruct (Qlt_le_dec 0 c) as [H | H].
  - exact H.
  - exfalso. assert (Hc0 : c == 0) by (apply Qle_antisym; assumption).
    assert (Hcol : eta_triad c b e == 0) by (unfold eta_triad; rewrite Hc0; ring).
    rewrite Hcol in Hpos. exact (Qlt_irrefl 0 Hpos).
Qed.

Lemma eta_pos_needs_bviol : forall c b e, 0 <= b -> 0 < eta_triad c b e -> 0 < b.
Proof.
  intros c b e Hb Hpos. destruct (Qlt_le_dec 0 b) as [H | H].
  - exact H.
  - exfalso. assert (Hb0 : b == 0) by (apply Qle_antisym; assumption).
    assert (Hcol : eta_triad c b e == 0) by (unfold eta_triad; rewrite Hb0; ring).
    rewrite Hcol in Hpos. exact (Qlt_irrefl 0 Hpos).
Qed.

Lemma eta_pos_needs_noneq : forall c b e, 0 <= e -> 0 < eta_triad c b e -> 0 < e.
Proof.
  intros c b e He Hpos. destruct (Qlt_le_dec 0 e) as [H | H].
  - exact H.
  - exfalso. assert (He0 : e == 0) by (apply Qle_antisym; assumption).
    assert (Hcol : eta_triad c b e == 0) by (unfold eta_triad; rewrite He0; ring).
    rewrite Hcol in Hpos. exact (Qlt_irrefl 0 Hpos).
Qed.

(** ★ NECESSITY (combined): a nonzero asymmetry forces ALL THREE faces present.  Drop any one of the
    three E/R/R levels and the asymmetry vanishes — exactly Sakharov's joint necessity. *)
Lemma eta_pos_needs_all : forall c b e,
  0 <= c -> 0 <= b -> 0 <= e -> 0 < eta_triad c b e -> 0 < c /\ 0 < b /\ 0 < e.
Proof.
  intros c b e Hc Hb He Hpos. repeat split.
  - exact (eta_pos_needs_cp c b e Hc Hpos).
  - exact (eta_pos_needs_bviol c b e Hb Hpos).
  - exact (eta_pos_needs_noneq c b e He Hpos).
Qed.

(* ---- SUFFICIENCY: all three faces present ⟹ η > 0 (positive triad volume) ---- *)

(** ★ SUFFICIENCY: all three E/R/R faces positive ⟹ a positive asymmetry (positive box volume). *)
Lemma eta_pos_if_all : forall c b e, 0 < c -> 0 < b -> 0 < e -> 0 < eta_triad c b e.
Proof.
  intros c b e Hc Hb He. unfold eta_triad.
  apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; assumption | assumption ].
Qed.

(* ===================================================================== *)
(*  Anchor: the CP face IS the real derived Jarlskog invariant             *)
(* ===================================================================== *)

(** ★ With the CP face anchored to the REAL derived Jarlskog (EtaFromLattice: 3 generations ⟹ J > 0),
    a positive asymmetry is REALIZED whenever the B-violation and out-of-equilibrium faces are present. *)
Lemma eta_realized_pos : forall K b e,
  0 < b -> 0 < e -> 0 < eta_triad (jarlskog_estimate K) b e.
Proof. intros K b e Hb He. apply eta_pos_if_all; [ apply jarlskog_positive | exact Hb | exact He ]. Qed.

(* ===================================================================== *)
(*  Capstone: the three Sakharov conditions = the E/R/R triad of η_B        *)
(* ===================================================================== *)

(** The Sakharov conditions as the E/R/R triad of the baryon count:
      (bijection)   the three conditions ↔ the three E/R/R levels {P4, L2, L5} (inj + surj);
      (necessity)   dropping any one face — CP (L2), B-violation (P4), out-of-eq (L5) — gives η = 0;
      (sufficiency) all three faces positive ⟹ η > 0 (positive triad-box volume);
      (anchor)      the CP face is the REAL derived Jarlskog (3 generations ⟹ J > 0).
    "Why exactly three Sakharov conditions" = the triad has exactly three levels.  η_B is the necessary
    residue of the E/R/R triad of the baryon count. *)
Theorem sakharov_err_triad :
  (forall s1 s2, sakharov_err s1 = sakharov_err s2 -> s1 = s2)
  /\ (forall l, exists s, sakharov_err s = l)
  /\ (forall b e, eta_triad 0 b e == 0)
  /\ (forall c e, eta_triad c 0 e == 0)
  /\ (forall c b, eta_triad c b 0 == 0)
  /\ (forall c b e, 0 < c -> 0 < b -> 0 < e -> 0 < eta_triad c b e)
  /\ (forall K b e, 0 < b -> 0 < e -> 0 < eta_triad (jarlskog_estimate K) b e).
Proof.
  split; [ exact sakharov_err_injective | ].
  split; [ exact sakharov_err_surjective | ].
  split; [ exact eta_zero_if_no_cp | ].
  split; [ exact eta_zero_if_no_bviol | ].
  split; [ exact eta_zero_if_no_noneq | ].
  split; [ exact eta_pos_if_all | ].
  exact eta_realized_pos.
Qed.
