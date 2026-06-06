(** * TeleportationResourceNoClone.v — deepening hint ② to its limit: WHY the entangled resource is
       necessary, and WHY teleportation is consistent with no-cloning — both from ONE structural fact.

       THE ONE FACT (`psi_blind_fails`): a ψ-BLIND output (a single fixed state, or anything depending
       only on the finite classical outcome) cannot be qst_eq to two DISTINCT states.  From it:

       (a) ENTANGLEMENT IS NECESSARY.  A purely classical reconstruction (Bob outputs g(outcome), with no
           entangled half to act on) is ψ-blind given the outcome, so two distinct states sharing a
           message are not both recovered: the finite (4-valued) classical channel cannot carry the
           continuum of qubit states.  By CONTRAST, the quantum half is ψ-SIGHTED: `bob_pre o` is
           INJECTIVE (the Paulis are bijections), so Bob's entangled half retains ALL of ψ; the 2 bits
           only pick the Pauli frame.  Entanglement = the ψ-sighted channel.

       (b) CONSISTENT WITH NO-CLONING.  A clone would leave ψ with BOTH parties.  Bob gets ψ
           (TeleportationCarrierSwap.teleport_preserves_state), but Alice keeps a ψ-BLIND record (the Bell
           measurement collapses her pair to an outcome-determined state, independent of ψ); so for
           distinct states Alice cannot hold both — the protocol MOVES ψ (one carrier), never COPIES it
           (two).  Same `psi_blind_fails`.  Consistent with ProcessNoCloning (L2).

    WHAT THE REPO HAS (surveyed): TeleportationCarrierSwap.v (the protocol identity, imported here);
    ProcessNoCloning.v (L2: no linear cloner); ProcessEntanglement.v (P1: Bell resource).  No Holevo /
    LOCC / "entanglement necessary" formalization — this fills that gap, lightly.

    ============ E/R/R разбор ============
      Elements : 2 классических бита (конечный алфавит, 4 значения) vs квантовая половинка (континуум);
                 пост-состояние Алисы (коллапс) vs состояние Боба.
      Roles    : бит = выбор паулиевской рамки (конечная Роль); квантовая половинка = носитель ψ (континуум);
                 пост-Алиса = ψ-слепая классическая запись; Боб = ψ.
      Rules    : psi_blind_fails (ψ-слепой выход ≠ двум разным ψ); bob_pre инъективно (ψ-зрячий канал);
                 L2 no-cloning — перенос (один ψ-носитель), не клон (два).
      ДИАГНОСТИКА (P4): континуум ψ нельзя протолкнуть через 4-значный классический канал ⟹ запутанность
      НЕОБХОДИМА как ψ-зрячий канал (биты лишь синхронизируют рамку); ψ-слепая запись Алисы не держит ψ для
      всех ψ ⟹ один ψ-носитель = перенос, согласуется с L2. ЧЕСТНО: формализую СТРУКТУРНУЮ необходимость
      (конечный классический vs континуальный квантовый) и согласованность (move-not-copy), НЕ полную
      info-теоретическую теорему невозможности (Holevo) и НЕ реализуемость. Уровень: `синтез + новое обрамление`.

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (imports only foundation.TeleportationCarrierSwap, itself 0-axiom)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.
From ToS Require Import foundation.TeleportationCarrierSwap.

Open Scope Q_scope.

(* ===================================================================== *)
(*  qst_eq is an equivalence (symmetry + transitivity over componentwise ==) *)
(* ===================================================================== *)

Lemma qst_eq_sym : forall s t, qst_eq s t -> qst_eq t s.
Proof. intros s t [H1 H2]. split; symmetry; assumption. Qed.

Lemma qst_eq_trans : forall s t u, qst_eq s t -> qst_eq t u -> qst_eq s u.
Proof. intros s t u [H1 H2] [H3 H4]. split; [ rewrite H1 | rewrite H2 ]; assumption. Qed.

(* ===================================================================== *)
(*  THE ONE STRUCTURAL FACT: a ψ-blind output can't track two distinct states *)
(* ===================================================================== *)

(** ★ A single fixed output `c` cannot be qst_eq to two DISTINCT states.  (If it were, the two states
    would be qst_eq to each other, by transitivity through c.)  This is the root of both (a) and (b). *)
Lemma psi_blind_fails : forall (c psi1 psi2 : qstate),
  ~ qst_eq psi1 psi2 -> ~ (qst_eq c psi1 /\ qst_eq c psi2).
Proof.
  intros c psi1 psi2 Hne [H1 H2]. apply Hne.
  apply qst_eq_trans with c; [ apply qst_eq_sym; exact H1 | exact H2 ].
Qed.

(* ===================================================================== *)
(*  (a) The quantum half is ψ-SIGHTED: bob_pre is injective (Pauli bijection) *)
(* ===================================================================== *)

(** ★ Bob's entangled half retains ALL of ψ: `bob_pre o` is INJECTIVE for every outcome (the Paulis are
    bijections).  So the continuous state information lives in the QUANTUM channel; the 2 classical bits
    carry only the finite Pauli-frame choice. *)
Lemma bob_pre_injective : forall o psi1 psi2,
  qst_eq (bob_pre o psi1) (bob_pre o psi2) -> qst_eq psi1 psi2.
Proof.
  intros o [a1 b1] [a2 b2]. destruct o;
    unfold bob_pre, pI, pX, pZ, pXZ, qst_eq; simpl; intros [H1 H2]; split; lra.
Qed.

(* ===================================================================== *)
(*  (a) Classical-alone is insufficient: the finite channel can't carry the continuum *)
(* ===================================================================== *)

(** A purely classical reconstruction: Bob outputs g(outcome), with NO entangled half — ψ-blind given o. *)
Definition classical_recover (g : Outcome -> qstate) (o : Outcome) : qstate := g o.

(** ★ Without entanglement: two DISTINCT states that yield the SAME classical message are not both
    recovered — the finite (4-valued) classical channel cannot carry the continuum of qubit states.
    (The ψ-blindness, via `psi_blind_fails`; contrast `bob_pre_injective`.) *)
Theorem classical_alone_fails : forall (g : Outcome -> qstate) (o : Outcome) (psi1 psi2 : qstate),
  ~ qst_eq psi1 psi2 ->
  ~ (qst_eq (classical_recover g o) psi1 /\ qst_eq (classical_recover g o) psi2).
Proof. intros g o psi1 psi2 Hne. unfold classical_recover. apply psi_blind_fails. exact Hne. Qed.

(** Concrete: a constant classical decoder cannot recover both |0⟩=(1,0) and |1⟩=(0,1). *)
Corollary classical_alone_fails_concrete :
  ~ (qst_eq (classical_recover (fun _ => (5#7, 0)) o00) (1, 0)
     /\ qst_eq (classical_recover (fun _ => (5#7, 0)) o00) (0, 1)).
Proof. apply classical_alone_fails. unfold qst_eq; simpl. intros [H _]. lra. Qed.

(* ===================================================================== *)
(*  (b) Consistent with no-cloning: Alice keeps a ψ-BLIND record — move, not copy *)
(* ===================================================================== *)

(** Alice's post-measurement state: the Bell measurement collapses her pair to an outcome-determined
    state, INDEPENDENT of ψ.  Modelled as a fixed ψ-blind representative (the real post-state is the
    outcome's Bell state — equally ψ-blind; only the ψ-independence is load-bearing here). *)
Definition alice_post (o : Outcome) (psi : qstate) : qstate := (1, 0).

Lemma alice_post_psi_blind : forall o psi1 psi2, alice_post o psi1 = alice_post o psi2.
Proof. intros. reflexivity. Qed.

(** ★ Consistent with no-cloning: a CLONE would leave ψ with BOTH parties.  Bob gets ψ
    (teleport_preserves_state); Alice keeps a ψ-BLIND record — so for distinct states Alice cannot hold
    both.  The protocol MOVES ψ (one carrier), never COPIES it (two).  (Same `psi_blind_fails`; the
    dual of ProcessNoCloning's L2.) *)
Theorem teleport_consistent_no_cloning : forall (o : Outcome) (psi1 psi2 : qstate),
  ~ qst_eq psi1 psi2 ->
  ~ (qst_eq (alice_post o psi1) psi1 /\ qst_eq (alice_post o psi2) psi2).
Proof.
  intros o psi1 psi2 Hne [H1 H2].
  apply (psi_blind_fails (alice_post o psi1) psi1 psi2 Hne).
  split; [ exact H1 | unfold alice_post in *; exact H2 ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Deepening hint ② — resource necessity and no-cloning consistency, from one structural fact:
      (ψ-sighted)  the quantum half is injective (`bob_pre_injective`) — it retains all of ψ;
      (classical)  a classical-only (ψ-blind) reconstruction fails to recover distinct states sharing
                   a message — the finite channel can't carry the continuum, so entanglement is NECESSARY;
      (move/copy)  Alice keeps a ψ-blind record, so ψ ends with ONE carrier — a MOVE, consistent with
                   no-cloning (L2).
    Honest: this is the STRUCTURAL necessity (finite classical vs continuum quantum) and the move-not-copy
    consistency, NOT the full Holevo impossibility theorem and NOT a realizability claim. *)
Theorem teleportation_resource_and_noclone :
  (forall o psi1 psi2, qst_eq (bob_pre o psi1) (bob_pre o psi2) -> qst_eq psi1 psi2)
  /\ (forall g o psi1 psi2, ~ qst_eq psi1 psi2 ->
        ~ (qst_eq (classical_recover g o) psi1 /\ qst_eq (classical_recover g o) psi2))
  /\ (forall o psi1 psi2, ~ qst_eq psi1 psi2 ->
        ~ (qst_eq (alice_post o psi1) psi1 /\ qst_eq (alice_post o psi2) psi2)).
Proof.
  split. exact bob_pre_injective.
  split. exact classical_alone_fails.
  exact teleport_consistent_no_cloning.
Qed.
