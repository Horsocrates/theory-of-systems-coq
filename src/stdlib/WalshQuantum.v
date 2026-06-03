(** * WalshQuantum.v — rational quantum mechanics on the Walsh basis: Palmer's
      "√−1 as a bit-permutation" made concrete. No complex numbers.

    Elements: 2×2 rational matrices (Hadamard H, Pauli X, Z) and rational state
              vectors over ℚ — the single-qubit Walsh-QM
    Roles:    H = the real Walsh/Fourier transform; X = bit-flip (permutation);
              Z = sign-flip (negation); the computational and Walsh bases = the
              position vs Walsh-momentum complementary pair
    Rules:    H² = 2·I (rational involution up to scale); H·X·H = 2·Z (the real
              Hadamard conjugates bit-flip into sign-flip — the role normally
              played by the COMPLEX i); X²=Z²=I (Pauli close, finite order);
              Born(computational | Walsh) = ½ (flat, rational complementarity)

    PALMER'S RaQM puts √−1 not as a transcendental complex unit but as a
    constructive permutation/negation operator on bit-strings. The Walsh-Hadamard
    transform is exactly that: a real, ±1, bit-indexed transform replacing the
    complex Fourier transform. The crown fact here — `hadamard_conjugates_X_to_Z`,
    H·X·H = 2·Z — is the √−1-free heart: where standard QM's Fourier transform
    conjugates a SHIFT (momentum) into a complex PHASE, the real Hadamard
    conjugates the bit-flip X into the sign-flip Z, with NO i at all (H⁻¹ = H/2,
    so the true conjugation is H·X·H⁻¹ = Z). And the computational/Walsh bases are
    maximally complementary with EXACTLY rational Born probabilities ½ — the
    rational position↔momentum complementarity. Everything closes finitely (X,Z
    order 2), so Walsh-QM lives entirely in the ℚ-finite-actual core of the
    finitization boundary (FinitizationBoundary.v) — no role-limits needed.

    ============ E/R/R разбор ============
      Rules (L5): H²=2I; HXH=2Z (бит-флип↦знак-флип, вместо i); Born=½.
      Roles (L4): H=вещественный Фурье/Уолш; X=перестановка; Z=негация;
                  вычислительный/Уолш базисы = позиция/импульс (комплементарны).
      Elements  : 2×2 рациональные матрицы, состояния над ℚ (L1+P4).
    ДИАГНОСТИКА (P4): Walsh-QM целиком в ℚ-конечном ядре (всё замыкается) — √−1
    заменён вещественной ±1-структурой Адамара; никаких role-limits.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
Open Scope Q_scope.

(* ===== 2×2 rational matrices and their algebra ========================= *)

Record Mat2 := mk2 { a00 : Q; a01 : Q; a10 : Q; a11 : Q }.

Definition mul2 (M N : Mat2) : Mat2 :=
  mk2 (a00 M * a00 N + a01 M * a10 N) (a00 M * a01 N + a01 M * a11 N)
      (a10 M * a00 N + a11 M * a10 N) (a10 M * a01 N + a11 M * a11 N).

Definition scal2 (k : Q) (M : Mat2) : Mat2 :=
  mk2 (k * a00 M) (k * a01 M) (k * a10 M) (k * a11 M).

(** Equality of matrices, entrywise up to Qeq. *)
Definition mat2_eq (M N : Mat2) : Prop :=
  a00 M == a00 N /\ a01 M == a01 N /\ a10 M == a10 N /\ a11 M == a11 N.

Definition Hm : Mat2 := mk2 1 1 1 (-1).   (* Walsh / Hadamard transform *)
Definition Xm : Mat2 := mk2 0 1 1 0.       (* bit-flip (permutation)     *)
Definition Zm : Mat2 := mk2 1 0 0 (-1).    (* sign-flip (negation)       *)
Definition Im : Mat2 := mk2 1 0 0 1.

(* ===== Walsh transform = rational involution; Pauli close ============== *)

(** H² = 2·I : the Walsh transform is its own inverse up to the rational
    scale 2 (so H⁻¹ = H/2 — no irrational √2 normalisation needed). *)
Lemma hadamard_involution : mat2_eq (mul2 Hm Hm) (scal2 2 Im).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** X² = I, Z² = I : the bit-flip and sign-flip have order 2 — they CLOSE.
    Walsh-QM is in the ℚ-finite-actual core (Elements), per the boundary. *)
Lemma pauli_X_order2 : mat2_eq (mul2 Xm Xm) Im.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma pauli_Z_order2 : mat2_eq (mul2 Zm Zm) Im.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== ★ The √−1-free mechanism: Hadamard conjugates X to Z ============= *)

(** H·X·H = 2·Z.  Since H⁻¹ = H/2, this is the conjugation H·X·H⁻¹ = Z:
    the REAL Hadamard turns the bit-flip X into the sign-flip Z, exactly the
    role the COMPLEX i plays in standard QM. This is Palmer's "√−1 as a
    bit-permutation/negation", machine-checked over ℚ. *)
Theorem hadamard_conjugates_X_to_Z :
  mat2_eq (mul2 (mul2 Hm Xm) Hm) (scal2 2 Zm).
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== Rational position↔Walsh-momentum complementarity ================ *)

Definition vec := (Q * Q)%type.
Definition dot (u v : vec) : Q :=
  (fst u) * (fst v) + (snd u) * (snd v).

Definition e0 : vec := (1, 0).   Definition e1 : vec := (0, 1).   (* position basis  *)
Definition w0 : vec := (1, 1).   Definition w1 : vec := (1, -1).  (* Walsh basis (rows of H) *)

(** Born probability of a position outcome u from a Walsh state v. *)
Definition born (u v : vec) : Q := (dot u v) * (dot u v) / (dot u u * dot v v).

(** Maximal complementarity: every position outcome of a Walsh eigenstate has
    EXACTLY rational probability ½ — a Walsh-momentum eigenstate is uniformly
    spread over position. The rational analogue of position↔momentum. *)
Theorem walsh_complementarity :
  born e0 w0 == 1#2 /\ born e0 w1 == 1#2 /\
  born e1 w0 == 1#2 /\ born e1 w1 == 1#2.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== Synthesis ======================================================= *)

(** Walsh-QM in one statement: a fully rational single-qubit quantum mechanics
    where √−1 is the real Hadamard (H·X·H = 2Z), the gates close (X²=Z²=I), and
    position/Walsh-momentum are maximally complementary with rational Born ½. *)
Theorem walsh_quantum_synthesis :
  mat2_eq (mul2 Hm Hm) (scal2 2 Im) /\
  mat2_eq (mul2 (mul2 Hm Xm) Hm) (scal2 2 Zm) /\
  mat2_eq (mul2 Xm Xm) Im /\ mat2_eq (mul2 Zm Zm) Im /\
  born e0 w0 == 1#2 /\ born e1 w0 == 1#2.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
