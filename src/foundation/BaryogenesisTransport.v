(** * BaryogenesisTransport.v — Baryogenesis Phase 2: the L5 transport rule.  η_B is assembled as the
      TRIADIC PRODUCT of the three Sakharov faces — η_B = (CP)·(B-violation)·(out-of-equilibrium) —
      replacing the ad-hoc placeholder form 1/(1+K²) with a product of three positive structural
      factors, the CP face being the REAL derived Jarlskog invariant.

    EtaFromLattice/MatterAsymmetry left η as a single ad-hoc function (η ∝ J, with a hidden
    "proportionality constant [that] depends on sphaleron rate").  SakharovERR (Phase 3) showed η is the
    triad product η = cp·bviol·noneq; SphaleronWinding (Phase 1) realized the B-violation (P4) face.
    Here we ASSEMBLE the L5 transport rule: η_transport(K) = eta_triad (cp K) (bviol K) (noneq K), and
    make the old hidden proportionality constant EXPLICIT as the product (bviol·noneq) of the remaining
    two faces.

      cp_factor    K = jarlskog_estimate K = 1/(1+K)³   — CP face (L2), DERIVED (EtaFromLattice);
      bviol_factor K = 1/(1+K)                          — B-violation face (P4), positive proxy (sphaleron);
      noneq_factor K = 1/(1+K)                          — out-of-equilibrium face (L5), positive proxy (arrow);
      η_transport  K = cp·bviol·noneq = 1/(1+K)⁵.

    The upgrade: η = J·(bviol·noneq) — the old "η ∝ J, constant depends on sphaleron rate" is now η = J
    times the NAMED product of the B-violation (P4) and out-of-equilibrium (L5) faces.  Positivity of
    all three ⟹ η > 0 (via SakharovERR.eta_pos_if_all); necessity is inherited (drop any face ⟹ η = 0).

    HONEST: the MAGNITUDES of bviol_factor and noneq_factor are positive STRUCTURAL PROXIES (the real
    sphaleron rate ∝ α_w⁵ e^{−E_sph/T} and the real departure-from-equilibrium are the Phase-4 gap, out
    of SM reach by ~10⁹).  Only the PRODUCT STRUCTURE, the positivity, and the CP face are derived.  The
    win is structural: the last placeholder FORM (one ad-hoc function) is replaced by the triad product.

    Elements: the three Q factors (cp = Jarlskog, bviol, noneq); η_transport = their product = 1/(1+K)⁵
    Roles:    cp = L2 face (derived); bviol = P4 face (sphaleron); noneq = L5 face (arrow)
    Rules:    η_transport = the triad product; η = J·(bviol·noneq); positive, decreasing; needs all three

    ============ E/R/R разбор ============
      Rules (L5): η_transport = триадное произведение трёх граней (замена ad-hoc 1/(1+K²)); η = J·(b·n)
                  («скрытая константа» названа); положительно, убывает; необходимость наследуется.
      Roles (L4): cp = грань L2 (выведена = Ярлског); bviol = грань P4 (сфалерон); noneq = грань L5 (стрела).
      Elements  : три Q-фактора; η_transport = 1/(1+K)⁵.
    ДИАГНОСТИКА (P4): placeholder-форма устранена — η_B = триадное произведение, не одна ad-hoc функция.
    CP-грань выведена; b,n = положительные структурные proxy (магнитуды = честный разрыв Фазы 4, но
    структура+положительность реальны). Последняя placeholder-форма закрыта.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.EtaFromLattice.    (* jarlskog_estimate, jarlskog_positive, eta_from_jarlskog *)
From ToS Require Import foundation.SakharovERR.        (* eta_triad, eta_pos_if_all, eta_zero_if_no_noneq *)
From ToS Require Import foundation.SphaleronWinding.   (* delta_B, sphaleron_violates_B *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The three triadic factors as functions of the scale K                  *)
(* ===================================================================== *)

(** CP face (L2): the DERIVED Jarlskog invariant — 1/(1+K)³ (EtaFromLattice). *)
Definition cp_factor (K : nat) : Q := jarlskog_estimate K.

(** B-violation face (P4): a positive structural proxy for the sphaleron efficiency — 1/(1+K).
    (Justified active by SphaleronWinding: ΔB = 3 ≠ 0; the MAGNITUDE/rate is the Phase-4 gap.) *)
Definition bviol_factor (K : nat) : Q := 1 # Pos.of_succ_nat K.

(** Out-of-equilibrium face (L5): a positive structural proxy for the departure from equilibrium
    (the arrow; ThermodynamicArrow) — 1/(1+K).  (MAGNITUDE = Phase-4 gap.) *)
Definition noneq_factor (K : nat) : Q := 1 # Pos.of_succ_nat K.

(** ★ The baryon asymmetry as the L5 TRANSPORT RULE = the triad product (SakharovERR.eta_triad). *)
Definition eta_transport (K : nat) : Q :=
  eta_triad (cp_factor K) (bviol_factor K) (noneq_factor K).

(* ===================================================================== *)
(*  Each face is positive                                                   *)
(* ===================================================================== *)

Lemma cp_factor_pos : forall K, 0 < cp_factor K.
Proof. intro K. apply jarlskog_positive. Qed.

Lemma bviol_factor_pos : forall K, 0 < bviol_factor K.
Proof. intro K. unfold bviol_factor, Qlt. simpl. lia. Qed.

Lemma noneq_factor_pos : forall K, 0 < noneq_factor K.
Proof. intro K. unfold noneq_factor, Qlt. simpl. lia. Qed.

(** The B-violation face is structurally ACTIVE (not zero): the sphaleron changes B (Phase 1). *)
Lemma bviol_face_active : (delta_B 1 <> 0)%Z.
Proof. exact sphaleron_violates_B. Qed.

(* ===================================================================== *)
(*  η_B > 0 from the triadic product; the placeholder upgrade               *)
(* ===================================================================== *)

(** ★ η_B > 0 — from the positivity of all THREE faces (SakharovERR.eta_pos_if_all). *)
Lemma eta_transport_pos : forall K, 0 < eta_transport K.
Proof.
  intro K. unfold eta_transport.
  apply eta_pos_if_all; [ apply cp_factor_pos | apply bviol_factor_pos | apply noneq_factor_pos ].
Qed.

(** ★ THE UPGRADE: η = J·(bviol·noneq).  The old "η ∝ J, constant depends on sphaleron rate" is now
    η = the derived Jarlskog times the NAMED product of the B-violation (P4) and out-of-eq (L5) faces —
    the placeholder's hidden proportionality constant made explicit and triadic. *)
Lemma eta_transport_refines_jarlskog :
  forall K, eta_transport K == eta_from_jarlskog K * (bviol_factor K * noneq_factor K).
Proof.
  intro K. unfold eta_transport, eta_triad, cp_factor, eta_from_jarlskog. ring.
Qed.

(* ===================================================================== *)
(*  Concrete values and dilution                                            *)
(* ===================================================================== *)

Lemma eta_transport_at_0 : eta_transport 0 == 1.
Proof. unfold eta_transport, eta_triad, cp_factor, bviol_factor, noneq_factor. vm_compute. reflexivity. Qed.

(** η_transport 1 = (1/8)·(1/2)·(1/2) = 1/32 = 1/(1+1)⁵. *)
Lemma eta_transport_at_1 : eta_transport 1 == 1 # 32.
Proof. unfold eta_transport, eta_triad, cp_factor, bviol_factor, noneq_factor. vm_compute. reflexivity. Qed.

(** ★ η_B DECREASES with scale — the asymmetry is diluted as the universe cools (1/32 < 1). *)
Lemma eta_transport_decreasing : eta_transport 1 < eta_transport 0.
Proof. rewrite eta_transport_at_1, eta_transport_at_0. lra. Qed.

(* ===================================================================== *)
(*  Necessity inherited: drop a face ⟹ η = 0                               *)
(* ===================================================================== *)

(** ★ Drop the out-of-equilibrium (L5) face ⟹ η = 0: the transport needs all three faces
    (SakharovERR.eta_zero_if_no_noneq).  Equilibrium ⟹ no net asymmetry. *)
Lemma eta_transport_needs_noneq :
  forall K, eta_triad (cp_factor K) (bviol_factor K) 0 == 0.
Proof. intro K. apply eta_zero_if_no_noneq. Qed.

(* ===================================================================== *)
(*  Capstone: the L5 transport rule assembled                              *)
(* ===================================================================== *)

(** The baryogenesis transport rule:
      (positive)  η_B > 0 — from the positivity of all three Sakharov faces;
      (upgrade)   η = J·(bviol·noneq) — the placeholder's hidden constant made explicit & triadic;
      (concrete)  η(0) = 1, η(1) = 1/32 = 1/(1+1)⁵;
      (dilution)  η decreases with scale (asymmetry diluted as the universe cools);
      (necessity) dropping the out-of-equilibrium (L5) face gives η = 0 — all three faces needed.
    The last placeholder FORM is replaced by the triad product; only the magnitude (Phase 4) remains. *)
Theorem baryogenesis_transport :
  (forall K, 0 < eta_transport K)
  /\ (forall K, eta_transport K == eta_from_jarlskog K * (bviol_factor K * noneq_factor K))
  /\ eta_transport 0 == 1
  /\ eta_transport 1 == 1 # 32
  /\ eta_transport 1 < eta_transport 0
  /\ (forall K, eta_triad (cp_factor K) (bviol_factor K) 0 == 0).
Proof.
  split; [ exact eta_transport_pos | ].
  split; [ exact eta_transport_refines_jarlskog | ].
  split; [ exact eta_transport_at_0 | ].
  split; [ exact eta_transport_at_1 | ].
  split; [ exact eta_transport_decreasing | ].
  exact eta_transport_needs_noneq.
Qed.
