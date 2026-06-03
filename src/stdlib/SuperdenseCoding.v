(** * SuperdenseCoding.v — the Pauli×Bell engine of superdense coding and teleportation
      is Element-side (integer), with √2 only in the resource's normalisation.

      Superdense coding: Alice applies one of the four Paulis {I, X, Z, ZX} to her half
      of a Bell pair |Φ⁺⟩, producing one of four ORTHOGONAL Bell states; Bob distinguishes
      them (2 classical bits in 1 qubit).  Teleportation is the same engine in reverse:
      Bob applies the SAME Pauli to CORRECT (recover |ψ⟩).  The whole protocol LOGIC — the
      encoder bijection, the orthogonal decoder, the involutive correction — is finite
      integer combinatorics (Element side); the only role-limit is the 1/√2 normalisation
      of the Bell states (norm² = 2), which cancels.  Gottesman–Knill in action: these are
      stabiliser protocols, classically tractable, Element-side.

    Elements: the integer Bell vectors (1,0,0,±1), (0,1,±1,0); the dot products 0 and 2;
              the Paulis as integer transforms actX, actZ (L1 + P4)
    Roles:    Element side = orthogonality of the 4 encoded Bell states (integer dot = 0,
              the decodability) + the Pauli bijection (encoder) + the Pauli involution
              (teleport correction); role-limit = the 1/√2 normalisation (norm² = 2)
    Rules:    the Pauli group {I,X,Z,ZX} acting on one half of |Φ⁺⟩; the inner product /
              orthogonality (decoding rule); the involution P²=I (correction rule)

    THE DEEP POINT — the protocol logic is Element-side integer combinatorics; the √2 is
    only a resource dressing.  Represent the (unnormalised) two-qubit states as integer
    4-vectors |q₁q₀⟩ = (a₀₀,a₀₁,a₁₀,a₁₁).  The four Bell states are
      |Φ⁺⟩=(1,0,0,1), |Φ⁻⟩=(1,0,0,−1), |Ψ⁺⟩=(0,1,1,0), |Ψ⁻⟩=(0,1,−1,0).
      · ENCODER (superdense): the four Paulis on the first qubit map |Φ⁺⟩ bijectively to
        the four Bell states — actX|Φ⁺⟩=|Ψ⁺⟩, actZ|Φ⁺⟩=|Φ⁻⟩, actZ(actX|Φ⁺⟩)=|Ψ⁻⟩ — all
        integer permutations/sign-flips (`encode_X/Z/ZX`).
      · DECODER: the four targets are PAIRWISE ORTHOGONAL, integer dot = 0
        (`bell_orthogonal`) — this is exactly what lets Bob recover 2 bits.  The norm is 2
        (`bell_norms`), NOT 1: the 1/√2 needed to make them unit vectors is the role-limit.
      · TELEPORT CORRECTION: the Paulis are involutions (`actX_invol`, `actZ_invol`,
        `teleport_correct_ZX`) — Bob applies the indicated Pauli and recovers |ψ⟩ exactly
        (over ℤ the global phases cancel).
      · ROLE-LIMIT: the Bell normalisation 1/√2 is irrational (`half_not_in_Q`, norm² = 2,
        the same √2 as the T-gate / Hadamard).  It cancels: orthogonality survives
        unnormalised, corrections are integer — the continuum is not needed for the logic.

    ============ E/R/R разбор ============
      Rules (L5): группа Pauli {I,X,Z,ZX} на первом кубите |Φ⁺⟩; скалярное произведение /
                  ортогональность (декодер); инволюция P²=I (коррекция).
      Roles (L4): Element = ортогональность 4 закодированных состояний (целочисл. dot=0,
                  декодируемость) + Pauli-биекция (кодер) + Pauli-инволюция (телепорт-коррекция);
                  role-limit = нормировка 1/√2 (norm²=2), дрессинг запутанности.
      Elements  : целочисл. белловские векторы (1,0,0,±1),(0,1,±1,0); dot 0 и 2; actX/actZ (L1+P4).
    ДИАГНОСТИКА (P4): логика протокола — конечная целочисл. комбинаторика = Element; нормировка 1/√2
    = role-limit-дрессинг, СОКРАЩАЕТСЯ (ортогональность переживает ненормированность, коррекции целочисл.);
    Gottesman–Knill: стабилизаторные протоколы ⟹ классически трактуемы ⟹ Element. ⟨Bell|Bell⟩=2 как в RationalQInfo.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Two-qubit states as integer 4-vectors |q₁q₀⟩ = (a₀₀,a₀₁,a₁₀,a₁₁)       *)
(* ===================================================================== *)

Definition vec4 := (Z * Z * Z * Z)%type.

Definition dot (u v : vec4) : Z :=
  let '(a, b, c, d) := u in let '(a', b', c', d') := v in
  a * a' + b * b' + c * c' + d * d'.

(** The four (unnormalised) Bell states. *)
Definition Phi_plus  : vec4 := (1, 0, 0, 1).
Definition Phi_minus : vec4 := (1, 0, 0, -1).
Definition Psi_plus  : vec4 := (0, 1, 1, 0).
Definition Psi_minus : vec4 := (0, 1, -1, 0).

(** The Pauli actions on the FIRST qubit: actX = X⊗I (flip q₁), actZ = Z⊗I (phase −1 on
    q₁=1).  These are integer permutations / sign-flips — no √2. *)
Definition actX (v : vec4) : vec4 := let '(a, b, c, d) := v in (c, d, a, b).
Definition actZ (v : vec4) : vec4 := let '(a, b, c, d) := v in (a, b, -c, -d).

(* ===================================================================== *)
(*  Decoder: the four Bell states are pairwise orthogonal (integer dot=0) *)
(* ===================================================================== *)

(** ★ The four Bell states are pairwise orthogonal over ℤ — exactly what lets Bob recover
    2 classical bits.  No normalisation needed for orthogonality. *)
Lemma bell_orthogonal :
  dot Phi_plus Phi_minus = 0 /\ dot Phi_plus Psi_plus = 0 /\ dot Phi_plus Psi_minus = 0
  /\ dot Phi_minus Psi_plus = 0 /\ dot Phi_minus Psi_minus = 0 /\ dot Psi_plus Psi_minus = 0.
Proof. repeat split; reflexivity. Qed.

(** The norm² of each Bell state is 2 — NOT 1.  The 1/√2 that would make them unit vectors
    is the role-limit (see `half_not_in_Q`). *)
Lemma bell_norms :
  dot Phi_plus Phi_plus = 2 /\ dot Phi_minus Phi_minus = 2
  /\ dot Psi_plus Psi_plus = 2 /\ dot Psi_minus Psi_minus = 2.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Encoder (superdense): the four Paulis map |Φ⁺⟩ to the four Bell states *)
(* ===================================================================== *)

(** X⊗I encodes |Φ⁺⟩ ↦ |Ψ⁺⟩. *)
Lemma encode_X : actX Phi_plus = Psi_plus.
Proof. reflexivity. Qed.

(** Z⊗I encodes |Φ⁺⟩ ↦ |Φ⁻⟩. *)
Lemma encode_Z : actZ Phi_plus = Phi_minus.
Proof. reflexivity. Qed.

(** (Z⊗I)(X⊗I) encodes |Φ⁺⟩ ↦ |Ψ⁻⟩.  With I↦|Φ⁺⟩, the four Paulis hit the four Bell
    states bijectively — the superdense encoder. *)
Lemma encode_ZX : actZ (actX Phi_plus) = Psi_minus.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Teleport correction: the Paulis are involutions — Bob recovers |ψ⟩    *)
(* ===================================================================== *)

(** X⊗I is its own inverse. *)
Lemma actX_invol : forall v, actX (actX v) = v.
Proof. intros v. destruct v as [[[a b] c] d]. reflexivity. Qed.

(** Z⊗I is its own inverse (the double sign-flip cancels: −(−c) = c). *)
Lemma actZ_invol : forall v, actZ (actZ v) = v.
Proof.
  intros v. destruct v as [[[a b] c] d]. simpl.
  rewrite ?Z.opp_involutive. reflexivity.
Qed.

(** ★ The ZX branch: Bob's qubit is (ZX)|ψ⟩ = actZ(actX|ψ⟩); applying the inverse XZ =
    actX∘actZ recovers |ψ⟩ EXACTLY (over ℤ the −1 phases cancel). *)
Lemma teleport_correct_ZX : forall v, actX (actZ (actZ (actX v))) = v.
Proof.
  intros v. destruct v as [[[a b] c] d]. simpl.
  rewrite ?Z.opp_involutive. reflexivity.
Qed.

(* ===================================================================== *)
(*  Role-limit: the Bell normalisation 1/√2 is irrational                 *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ The Bell normalisation factor 1/√2 has no rational value: no r ∈ ℚ squares to 1/2
    (else (2r)²=2, impossible).  norm² = 2 (`bell_norms`) is the √2 role-limit — the same
    √2 as the T-gate / Hadamard.  The protocol logic is integer; only this dressing names
    √2, and it cancels. *)
Theorem half_not_in_Q : ~ (exists r : Q, r * r == 1 # 2).
Proof.
  intros [r Hr]. apply sqrt2_not_in_Q. exists (2 * r).
  assert (H : (2 * r) * (2 * r) == 4 * (r * r)) by ring.
  rewrite H, Hr. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Pauli×Bell engine, split by the finitization boundary:
      (a) ENCODER — the four Paulis map |Φ⁺⟩ to the four Bell states (Element, integer);
      (b) DECODER — the four Bell states are pairwise orthogonal (Element, integer dot=0);
      (c) CORRECTION — the Paulis are involutions, Bob recovers |ψ⟩ (Element, integer);
      (d) ROLE-LIMIT — the Bell normalisation 1/√2 is irrational (norm² = 2). *)
Theorem superdense_synthesis :
  (actX Phi_plus = Psi_plus /\ actZ Phi_plus = Phi_minus /\ actZ (actX Phi_plus) = Psi_minus)
  /\ (dot Phi_plus Phi_minus = 0 /\ dot Phi_plus Psi_plus = 0 /\ dot Phi_plus Psi_minus = 0
      /\ dot Phi_minus Psi_plus = 0 /\ dot Phi_minus Psi_minus = 0 /\ dot Psi_plus Psi_minus = 0)%Z
  /\ (forall v, actX (actX v) = v) /\ (forall v, actZ (actZ v) = v)
  /\ ~ (exists r : Q, r * r == 1 # 2).
Proof.
  split; [ repeat split; reflexivity | ].
  split; [ exact bell_orthogonal | ].
  split; [ exact actX_invol | ].
  split; [ exact actZ_invol | exact half_not_in_Q ].
Qed.
