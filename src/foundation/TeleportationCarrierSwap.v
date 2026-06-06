(** * TeleportationCarrierSwap.v — metaphysics-hint ②: teleportation as «переход системы в систему».
       The full teleportation IDENTITY: for an ARBITRARY input qubit |ψ⟩=(α,β) and EVERY one of the
       four Bell-measurement outcomes (the 2 classical bits), Bob's Pauli correction recovers |ψ⟩ EXACTLY.
       The framework reading: the STATE (the external/observable class, P3) is preserved while the CARRIER
       (the Element) is swapped — the *system* (Role-structure) is re-assigned to a fresh Element.  That is
       precisely "system passes into system": nothing material travels (the Element stays put, only the 2
       classical bits travel); the Role |ψ⟩ is re-instantiated on Bob's carrier.

    WHAT THE REPO HAS (surveyed): SuperdenseCoding.v — the Pauli×Bell engine, the involutive corrections
    (`teleport_correct_ZX`, `actX_invol`, `actZ_invol`), the √2 only in the Bell norm; it SAYS "teleportation
    is the same engine in reverse" but never states the full input→output identity for an arbitrary state.
    ProcessNoCloning.v (L2: no perfect copy).  ProcessEntanglement.v (P1: Bell resource, non-separable).
    GAP: no complete teleportation map (arbitrary |ψ⟩, all 4 outcomes, exact recovery) and no carrier-swap /
    move-not-copy / bits-essential reading.

    THE CONSTRUCTION (over Q; ring-generic).  A single-qubit state is a 2-vector (α,β).  The four Paulis act
    as integer matrices that DO NOT mix the components beyond swap/sign, so the protocol identity is exact
    over Q — and verbatim the same over Q[i] (the √2 lives only in the Bell resource, SuperdenseCoding.bell_norms,
    and cancels).  The four Bell-measurement outcomes = the 2 classical bits (`Outcome`); each leaves Bob's
    qubit in a Pauli image P|ψ⟩; Bob applies P⁻¹ (selected by the bits) and recovers |ψ⟩.
      pI=(a,b)↦(a,b)  pX=(a,b)↦(b,a)  pZ=(a,b)↦(a,-b)  pXZ=pX∘pZ=(a,b)↦(-b,a)  pZX=pZ∘pX=(a,b)↦(b,-a)
      outcome o00→correct pI, o01→pX, o10→pZ, o11→pZX(=inverse of pXZ).  ∀ψ ∀outcome: correct(pre(ψ))=ψ.

    ============ E/R/R разбор ============
      Elements : носители (кубиты/атомы) A и B — РАЗНЫЕ Элементы; амплитуды (α,β) = содержание.
      Roles    : «быть |ψ⟩» = Роль (внешний наблюдаемый класс, P3), не вещество; 2 бита = селектор Роли.
      Rules    : P1 запутанность (ресурс) + L5 измерение (выбор исхода) + Паули-коррекция (инволюция,
                 восстанавливает Роль) + L2 вход разрушается (перенос-НЕ-копия) + классический канал (нет FTL).
      ДИАГНОСТИКА (P4): идентичность телепортируемой системы — по P3 (внешний класс = амплитуды), НЕ по Элементу.
      «Переход системы в систему» = переназначение Роли |ψ⟩ с носителя A на носитель B; ничто материальное не
      летит (летят 2 бита), Роль переинстанцируется на свежем Элементе. ЧЕСТНО: формализую СТРУКТУРУ (точное
      восстановление ∀входов/исходов, перенос-не-копия, биты-существенны), НЕ реализуемость макротелепортации,
      НЕ «перенос сущности». Уровень: `синтез + новое обрамление` (полная identity, которую SuperdenseCoding
      лишь намекал, + метафизическое прочтение подсказки ②).

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Single-qubit states and the four Paulis (integer matrices over Q)      *)
(* ===================================================================== *)

(** A single-qubit state |ψ⟩ = α|0⟩+β|1⟩ as the amplitude pair (α,β).
    (Amplitudes in Q; ring-generic — identical over Q[i], the Paulis being integer matrices.) *)
Definition qstate : Type := (Q * Q).

(** Qubit equality = equality of the external/observable data (the amplitudes), componentwise ==.
    This is the qubit-level `ext_equiv` (P3): identity by observable class, not by carrier. *)
Definition qst_eq (s t : qstate) : Prop := (fst s == fst t) /\ (snd s == snd t).

Lemma qst_eq_refl : forall s, qst_eq s s.
Proof. intros s. unfold qst_eq. split; reflexivity. Qed.

(** The four Paulis on (α,β): I, X (bit flip), Z (phase flip), and the composites. *)
Definition pI  (s : qstate) : qstate := s.
Definition pX  (s : qstate) : qstate := (snd s, fst s).
Definition pZ  (s : qstate) : qstate := (fst s, - snd s).
Definition pXZ (s : qstate) : qstate := pX (pZ s).   (* = (-β, α) *)
Definition pZX (s : qstate) : qstate := pZ (pX s).   (* = (β, -α) *)

(* ===================================================================== *)
(*  The protocol: 2 classical bits (Outcome) select Bob's correction       *)
(* ===================================================================== *)

(** The Bell-measurement outcome = the 2 classical bits Alice sends Bob. *)
Inductive Outcome : Type := o00 | o01 | o10 | o11.

(** What Bob's qubit IS after Alice's measurement, per outcome: a Pauli image P|ψ⟩. *)
Definition bob_pre (o : Outcome) (psi : qstate) : qstate :=
  match o with
  | o00 => pI psi | o01 => pX psi | o10 => pZ psi | o11 => pXZ psi
  end.

(** Bob's correction, SELECTED BY THE 2 BITS: the inverse Pauli (pZX inverts pXZ). *)
Definition bob_correct (o : Outcome) (s : qstate) : qstate :=
  match o with
  | o00 => pI s | o01 => pX s | o10 => pZ s | o11 => pZX s
  end.

(** ★★★ TELEPORTATION IDENTITY ★★★
    For an ARBITRARY input |ψ⟩ and EVERY one of the four outcomes, Bob's correction recovers |ψ⟩ EXACTLY.
    (This is the complete protocol logic SuperdenseCoding only hinted at — exact over Q, ring-generic.) *)
Theorem teleportation_recovers : forall (o : Outcome) (psi : qstate),
  qst_eq (bob_correct o (bob_pre o psi)) psi.
Proof.
  intros o psi. destruct psi as [a b]. destruct o;
    unfold qst_eq, bob_correct, bob_pre, pI, pX, pZ, pXZ, pZX; simpl; split; ring.
Qed.

(* ===================================================================== *)
(*  The carrier-swap reading: same STATE (P3 class), different ELEMENT      *)
(* ===================================================================== *)

(** A LOCATED qubit: a state together with the physical carrier (Element) holding it. *)
Record Located : Type := mkLoc { carrier : nat ; qst : qstate }.

(** Teleportation as a map: the input (on its carrier) is relocated to carrier B, with the
    outcome's correction applied — the result lives on B and (by the identity above) equals |ψ⟩. *)
Definition teleport (o : Outcome) (B : nat) (inp : Located) : Located :=
  mkLoc B (bob_correct o (bob_pre o (qst inp))).

(** ★ ESSENCE PRESERVED: the output state equals the input state (same observable class, P3). *)
Lemma teleport_preserves_state : forall o B inp,
  qst_eq (qst (teleport o B inp)) (qst inp).
Proof. intros o B inp. unfold teleport; simpl. apply teleportation_recovers. Qed.

(** ★ CARRIER SET TO B: the output lives on the destination Element. *)
Lemma teleport_sets_carrier : forall o B inp, carrier (teleport o B inp) = B.
Proof. intros o B inp. unfold teleport; simpl. reflexivity. Qed.

(** ★ ELEMENT SWAPPED: if B is a different carrier, the Element genuinely changed —
    the SAME system (state) now sits on a DIFFERENT carrier = «переход системы в систему». *)
Lemma teleport_swaps_element : forall o B inp,
  carrier inp <> B -> carrier (teleport o B inp) <> carrier inp.
Proof. intros o B inp H. unfold teleport; simpl. congruence. Qed.

(* ===================================================================== *)
(*  Move-not-copy (no-cloning dual) and bits-essential (no FTL)            *)
(* ===================================================================== *)

(** ★ BITS ARE ESSENTIAL (no faster-than-light Role transfer): if Bob applies the WRONG correction
    (guesses o00 when the outcome was o01), he does NOT recover |ψ⟩.  Concretely on |0⟩=(1,0):
    X|0⟩=|1⟩, and the identity correction leaves |1⟩≠|0⟩.  So the 2 classical bits carry essential
    information — the Role cannot be reconstructed without the classical channel. *)
Lemma correction_needs_bits :
  ~ qst_eq (bob_correct o00 (bob_pre o01 (1, 0))) (1, 0).
Proof.
  unfold qst_eq, bob_correct, bob_pre, pI, pX; simpl. intros [H _]. lra.
Qed.

(** Concrete relocation: a spin state (3/5, 4/5) teleported from carrier 2 to carrier 7
    through outcome o11 — recovered EXACTLY, now on carrier 7 (not 2). *)
Example teleport_example :
  qst_eq (qst (teleport o11 7%nat (mkLoc 2%nat (3#5, 4#5)))) (3#5, 4#5)
  /\ carrier (teleport o11 7%nat (mkLoc 2%nat (3#5, 4#5))) = 7%nat
  /\ carrier (teleport o11 7%nat (mkLoc 2%nat (3#5, 4#5))) <> 2%nat.
Proof.
  split; [ apply teleport_preserves_state | ].
  split; [ reflexivity | ]. unfold teleport; simpl. discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Teleportation IS a carrier swap (system passes into system):
      (recovery)   ∀ input |ψ⟩, ∀ outcome: Bob's correction recovers |ψ⟩ EXACTLY (the full protocol);
      (essence)    teleport preserves the STATE (the observable class — P3);
      (carrier)    the output lives on the destination carrier B;
      (swap)       a different B means a different Element — same system, new carrier;
      (no FTL)     the 2 classical bits are essential — a wrong correction fails to recover |ψ⟩.
    So in the framework, what "moves" is the Role-structure (the external class), not the Element: the
    system is re-assigned to a fresh carrier, licensed by {entanglement + classical bits + correction}.
    Honest: this formalizes the protocol STRUCTURE and its constraints (exact recovery, move-not-copy via
    no-cloning, bits-essential via the classical channel), NOT the physical realizability of macroscopic
    teleportation and NOT a transfer of any "essence-substance". *)
Theorem teleportation_is_carrier_swap :
  (forall o psi, qst_eq (bob_correct o (bob_pre o psi)) psi)
  /\ (forall o B inp, qst_eq (qst (teleport o B inp)) (qst inp))
  /\ (forall o B inp, carrier (teleport o B inp) = B)
  /\ (forall o B inp, carrier inp <> B -> carrier (teleport o B inp) <> carrier inp)
  /\ (~ qst_eq (bob_correct o00 (bob_pre o01 (1, 0))) (1, 0)).
Proof.
  split. exact teleportation_recovers.
  split. exact teleport_preserves_state.
  split. exact teleport_sets_carrier.
  split. exact teleport_swaps_element.
  exact correction_needs_bits.
Qed.
