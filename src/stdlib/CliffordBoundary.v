(** * CliffordBoundary.v — Clifford = the finitization boundary (direction ①,
      first brick). The single-qubit Clifford gates CLOSE (a finite group, the
      ℚ-finite-actual core); a non-Clifford rational rotation NEVER closes (a
      role-limit). Conjecture: closes-finitely ⟺ Clifford ⟺ classically simulable.

    Elements: the real single-qubit Pauli/Clifford matrices I, X, Z, XZ over ℚ
    Roles:    "Clifford" = the finite gate group that CLOSES (Element, classically
              simulable by Gottesman–Knill); "non-Clifford" = a role-limit gate
              (needs the continuum — where quantum advantage lives)
    Rules:    X²=Z²=I, (XZ)²=−I, (XZ)⁴=I, XZ=−ZX — the real Pauli group is FINITE
              (closes); a non-Z₄ rational rotation (3-4-5) is aperiodic (Niven) —
              it never closes (role-limit)

    THE CONJECTURE (this is brick 1 of direction ①). The finitization boundary —
    Element (closes finitely) vs role-limit (provably never closes) —
    plausibly IS the Clifford / non-Clifford boundary of quantum computation:
      · the Clifford group is FINITE (for fixed n) ⟹ it CLOSES ⟹ Element ⟹
        classically efficiently simulable (Gottesman–Knill);
      · non-Clifford gates (the T-gate, arbitrary continuous phases) generate a
        DENSE/infinite group ⟹ they NEVER close ⟹ role-limit ⟹ where universal
        quantum computation / quantum advantage lives.
    Under this reading a finitist bound on the role-limit's accessibility (P4)
    becomes a bound on achievable advantage — connecting Gottesman–Knill to
    Palmer's RaQM qubit ceiling (~400 qubits) through ONE boundary.

    This file proves the prototype both ways, single-qubit: the real Pauli/Clifford
    gates close (finite order, anticommutation — a group of order 8), while the
    3-4-5 rotation (a non-Clifford rational rotation) is aperiodic by the Niven
    theorem (`rotation_345_aperiodic`, NivenGeneral.v) — it never closes.
    Later bricks: Gaussian-rational ℚ[i] phases (S = a Gaussian unit, closes;
    T's e^{iπ/4} is off the ℚ-grid since cos(π/4)∉ℚ by Niven), the full Clifford
    group's finiteness, and the Gottesman–Knill ⇄ simulability link.

    ============ E/R/R разбор ============
      Rules (L5): X²=Z²=I, (XZ)²=−I, XZ=−ZX (конечная группа замыкается);
                  не-Z₄ поворот апериодичен (не замыкается).
      Roles (L4): Clifford = ЗАВЕРШАЮЩИЙСЯ процесс (конечная группа замыкается →
                  терминус = Element, симулируемо); не-Clifford = role-limit:
                  НЕЗАВЕРШАЮЩИЙСЯ процесс (орбита 3-4-5 не замыкается; внешне —
                  континуум/превосходство).
      Elements  : вещественные Паули-матрицы I,X,Z,XZ над ℚ (L1+P4).
    ДИАГНОСТИКА (P4): граница Клиффорда = граница финитизации. Симулируемое ядро
    (Clifford = ЗАВЕРШАЮЩИЕСЯ процессы → Элементы) ⊕ role-limit (НЕЗАВЕРШАЮЩИЕСЯ
    процессы: орбита 3-4-5 не замыкается; внешне — континуум/превосходство).

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.WalshQuantum.
From ToS Require Import stdlib.NivenGeneral.
Open Scope Q_scope.

(* ===== The real single-qubit Pauli/Clifford gates (XZ = the quarter-turn) === *)

Definition XZm : Mat2 := mul2 Xm Zm.   (* = [[0,-1],[1,0]], the real Y / 90° rotation *)

(* ===== Element side: the Clifford gates CLOSE (a finite group, order 8) ==== *)

(** X² = I and Z² = I : Pauli bit-flip and sign-flip have order 2. *)
Lemma cliff_X_order2 : mat2_eq (mul2 Xm Xm) Im.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma cliff_Z_order2 : mat2_eq (mul2 Zm Zm) Im.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** (XZ)² = −I and (XZ)⁴ = I : the real Y has order 4. *)
Lemma cliff_XZ_squared : mat2_eq (mul2 XZm XZm) (scal2 (-1) Im).
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma cliff_XZ_order4 :
  mat2_eq (mul2 (mul2 (mul2 XZm XZm) XZm) XZm) Im.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** XZ = −ZX : the Clifford anticommutation that makes {±I,±X,±Z,±XZ} a finite
    group of order 8. Finite ⟹ it CLOSES ⟹ the ℚ-finite-actual core (Element). *)
Lemma cliff_anticommute : mat2_eq (mul2 Xm Zm) (scal2 (-1) (mul2 Zm Xm)).
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== The demarcation: Clifford closes (Element) | non-Clifford role-limit == *)

(** Single-qubit prototype of direction ①: the Clifford gates CLOSE (finite
    order + anticommutation ⟹ a finite group, the simulable Element core), while
    the 3-4-5 rotation — a NON-Clifford rational rotation — NEVER closes (Niven
    aperiodicity, a role-limit on the continuum side where advantage lives). *)
Theorem clifford_boundary :
  (* Clifford core CLOSES (finite group of order 8) *)
  mat2_eq (mul2 Xm Xm) Im /\
  mat2_eq (mul2 Zm Zm) Im /\
  mat2_eq (mul2 (mul2 (mul2 XZm XZm) XZm) XZm) Im /\
  mat2_eq (mul2 Xm Zm) (scal2 (-1) (mul2 Zm Xm)) /\
  (* non-Clifford rational rotation NEVER closes (role-limit) *)
  (forall k, ~ Z.divide 5 (c 6 5 (S k))).
Proof.
  repeat split; try (vm_compute; reflexivity).
  exact rotation_345_aperiodic.
Qed.
