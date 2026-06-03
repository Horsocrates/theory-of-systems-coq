(** * CliffordCeiling.v — the Element-side CEILING of the gate ladder: the Pauli
      group and the phase gate live over ℚ[i] (finite order, 0-axiom), but the
      Clifford step — Hadamard — necessarily actualises the √2 ROLE-LIMIT.

    Elements: the Gaussian rationals 0,±1,±i building I,X,Y,Z,S; their finite
              orders (2 and 4, all dividing 4 = the order of the Z₄ Element i);
              the rational invariant of the gate torsion (L1 + P4)
    Roles:    i = the ELEMENT-extension ℚ→ℚ[i] (i⁴=1, the same Z₄ as SO(2,ℚ));
              1/√2 = the ROLE-LIMIT-extension ℚ→ℚ[√2]; the Pauli/phase gates =
              the gates that fit inside M₂(ℚ[i]) vs Hadamard = the first Clifford
              generator that must leave it
    Rules:    the 2×2 algebra over ℚ[i]; the Pauli relations X²=Y²=Z²=I,
              anticommutation XZ=−ZX; the phase gate S=diag(1,i), S²=Z, S⁴=I; and
              the boundary rule — Hadamard's normalisation s²=1/2

    THE DEEP POINT — the finitization boundary runs THROUGH the gate set, and it
    cuts exactly at Hadamard.  The single-qubit Pauli group {±1,±i}×{I,X,Y,Z} and
    the phase gate S = diag(1,i) have ALL entries in ℚ[i] — they are finite-order
    and finitely actual with NO √2 anywhere: the whole Element side.  The imaginary
    unit i is not a step into the continuum — it is the order-4 Element of Z₄
    (i⁴=1, it CLOSES), the same quarter-turn that is the torsion of SO(2,ℚ) (②④).
    So every gate whose phases are powers of i stays Element-side.

    THE WALL IS HADAMARD.  H = (1/√2)·[[1,1],[1,−1]] needs an entry s with s²=1/2,
    and NO Gaussian rational squares to 1/2 (`no_gaussian_sqrt_half`): if s=(a,b)
    then 2ab=0 and a²−b²=1/2, forcing either a²=1/2 (no rational root, via √2) or
    b²=−1/2 (impossible, a square is ≥0).  Hence H ∉ M₂(ℚ[i]).  Crossing from the
    Pauli/phase gates to the full Clifford group necessarily ACTUALISES the √2
    role-limit — the very √2 that kills the T-gate (①, H2).

    THE CEILING.  The Element-side ceiling of the gate ladder is the ℚ[i] layer
    (Pauli + phase + everything with i-powered phases); universality (Hadamard, T)
    lives past the finitization boundary.  This is the E/R/R reading of
    Gottesman–Knill: the classically-tractable / rational-statistics layer is the
    Element side over ℚ[i]; "magic" and universality require the role-limit √2.

    ============ E/R/R разбор ============
      Rules (L5): алгебра 2×2 над ℚ[i]; X²=Y²=Z²=I, XZ=−ZX; S=diag(1,i), S²=Z,
                  S⁴=I; и правило-граница s²=1/2 (нормировка Адамара).
      Roles (L4): i = Element-расширение ℚ→ℚ[i] (Z₄, i⁴=1) vs 1/√2 =
                  role-limit-расширение; Паули+фаза = гейты внутри M₂(ℚ[i]) vs
                  Адамар = первый генератор Клиффорда, обязанный её покинуть.
      Elements  : гауссовы рациональные 0,±1,±i; конечные порядки 2 и 4 (все делят
                  4 = порядок Z₄-Element i) (L1+P4).
    ДИАГНОСТИКА (P4): граница финитизации проходит ВНУТРИ набора гейтов и режет ровно
    по Адамару. Паули/фаза — конечно-актуальны над ℚ[i] без √2 (Element-сторона); переход
    к Клиффорду (через H) НЕОБХОДИМО актуализирует √2 (role-limit): ~∃g∈ℚ[i], g²=1/2.
    Потолок Element-стороны = слой ℚ[i]; универсальность — за границей. (E/R/R-Готтесман–Книлл.)

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import analysis.Sqrt2Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Gaussian rationals ℚ[i] = (re, im)   (replicated from GaussianMUB.v   *)
(*  to keep this file standalone; same definitions)                       *)
(* ===================================================================== *)

Definition GQ : Type := (Q * Q)%type.
Definition gadd (z w : GQ) : GQ := (fst z + fst w, snd z + snd w).
Definition gmul (z w : GQ) : GQ :=
  (fst z * fst w - snd z * snd w, fst z * snd w + snd z * fst w).
Definition gneg (z : GQ) : GQ := (- fst z, - snd z).
Definition geq (z w : GQ) : Prop := fst z == fst w /\ snd z == snd w.

Definition g0  : GQ := (0, 0).
Definition g1  : GQ := (1, 0).
Definition gi  : GQ := (0, 1).        (* the imaginary unit *)
Definition gn1 : GQ := (-1, 0).       (* −1 *)
Definition gni : GQ := (0, -1).       (* −i *)

(** A helper: every rational square is non-negative (used for the H-wall). *)
Lemma qsq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hlt | Hge].
  - assert (Hr : q * q == (- q) * (- q)) by ring.
    rewrite Hr. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(* ===================================================================== *)
(*  i is the Z₄ Element: i² = −1, i⁴ = 1, but i² ≠ 1 (exact order 4)       *)
(* ===================================================================== *)

(** i² = −1. *)
Lemma gi_sq : geq (gmul gi gi) gn1.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** i⁴ = 1 — the imaginary unit CLOSES: it is the order-4 Element of Z₄. *)
Lemma gi_order4 : geq (gmul (gmul gi gi) (gmul gi gi)) g1.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** i² ≠ 1: the order is EXACTLY 4, not 2.  (With gi_order4: i is genuine Z₄.) *)
Lemma gi_not_invol : ~ geq (gmul gi gi) g1.
Proof.
  intro H. unfold geq in H. destruct H as [H _].
  vm_compute in H. discriminate.
Qed.

(* ===================================================================== *)
(*  ★ The wall: no Gaussian rational squares to 1/2 (Hadamard ∉ M₂(ℚ[i])) *)
(* ===================================================================== *)

(** Hadamard's normalisation needs s with s² = 1/2.  Over ℚ[i] there is none:
    s=(a,b) ⟹ 2ab=0 and a²−b²=1/2 ⟹ either a²=1/2 (no rational root, via √2) or
    b²=−1/2 (impossible).  So H = (1/√2)[[1,1],[1,−1]] is NOT over ℚ[i] — the
    Clifford step actualises the √2 role-limit. *)
Theorem no_gaussian_sqrt_half : ~ (exists g : GQ, geq (gmul g g) (1#2, 0)).
Proof.
  intros [[a b] H]. unfold geq, gmul in H. cbn in H.
  destruct H as [Hre Him].
  (* Hre : a*a - b*b == 1#2 ;  Him : a*b + b*a == 0 *)
  assert (Hab : a * b == 0).
  { assert (Hdup : a * b + b * a == 2 * (a * b)) by ring. lra. }
  apply Qmult_integral in Hab. destruct Hab as [Ha0 | Hb0].
  - (* a == 0 ⟹ b² = −1/2, impossible *)
    assert (Haa : a * a == 0) by (rewrite Ha0; ring).
    assert (Hbb : b * b == -(1#2)) by lra.
    assert (Hnn : 0 <= b * b) by apply qsq_nonneg.
    lra.
  - (* b == 0 ⟹ a² = 1/2 ⟹ (2a)² = 2, no rational root *)
    apply (no_rational_sqrt2 (2 * a)).
    assert (Hbb : b * b == 0) by (rewrite Hb0; ring).
    assert (Haa : a * a == 1#2) by lra.
    assert (Heq : (2 * a) * (2 * a) == 4 * (a * a)) by ring.
    rewrite Heq, Haa. lra.
Qed.

(* ===================================================================== *)
(*  The Pauli group + phase gate as 2×2 matrices over ℚ[i]                *)
(* ===================================================================== *)

Definition M2 : Type := (GQ * GQ * GQ * GQ)%type.   (* row-major (a b / c d) *)

Definition mId : M2 := (g1, g0, g0, g1).
Definition mX  : M2 := (g0, g1, g1, g0).            (* Pauli X *)
Definition mZ  : M2 := (g1, g0, g0, gn1).           (* Pauli Z *)
Definition mY  : M2 := (g0, gni, gi, g0).           (* Pauli Y = [[0,-i],[i,0]] *)
Definition mS  : M2 := (g1, g0, g0, gi).            (* phase gate diag(1,i) *)

Definition mneg (M : M2) : M2 :=
  let '(a,b,c,d) := M in (gneg a, gneg b, gneg c, gneg d).

Definition mmul (M N : M2) : M2 :=
  let '(a,b,c,d) := M in
  let '(e,f,p,q) := N in
  (gadd (gmul a e) (gmul b p),
   gadd (gmul a f) (gmul b q),
   gadd (gmul c e) (gmul d p),
   gadd (gmul c f) (gmul d q)).

Definition meq (M N : M2) : Prop :=
  let '(a,b,c,d) := M in
  let '(e,f,p,q) := N in
  geq a e /\ geq b f /\ geq c p /\ geq d q.

(** X² = I — Pauli X is an involution. *)
Lemma mX_invol : meq (mmul mX mX) mId.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** Z² = I. *)
Lemma mZ_invol : meq (mmul mZ mZ) mId.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** Y² = I. *)
Lemma mY_invol : meq (mmul mY mY) mId.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** XZ = −ZX — the Pauli anticommutation, over ℚ[i] (all entries Elements). *)
Lemma pauli_anticommute_XZ : meq (mmul mX mZ) (mneg (mmul mZ mX)).
Proof. vm_compute; repeat split; reflexivity. Qed.

(** S² = Z — the phase gate squares to Pauli Z (still in ℚ[i]). *)
Lemma mS_sq_is_Z : meq (mmul mS mS) mZ.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** S⁴ = I — the phase gate has order 4 (= the Z₄ Element order; no √2). *)
Lemma mS_order4 : meq (mmul (mmul mS mS) (mmul mS mS)) mId.
Proof. vm_compute; repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis: the ℚ[i] ceiling vs the √2 wall                            *)
(* ===================================================================== *)

(** The gate ladder split by the finitization boundary, in one statement:
      (a) i is the Z₄ Element — i⁴=1 (closes) but i²≠1 (exact order 4);
      (b) the Pauli group and phase gate are finite-order over ℚ[i] — Element side
          (X²=I, S⁴=I, all entries in ℚ[i], NO √2);
      (c) Hadamard's 1/√2 normalisation has no Gaussian-rational root — the
          Clifford step necessarily crosses to the √2 role-limit. *)
Theorem clifford_ceiling_synthesis :
  geq (gmul (gmul gi gi) (gmul gi gi)) g1
  /\ ~ geq (gmul gi gi) g1
  /\ meq (mmul mX mX) mId
  /\ meq (mmul (mmul mS mS) (mmul mS mS)) mId
  /\ ~ (exists s : GQ, geq (gmul s s) (1#2, 0)).
Proof.
  (* peel ONLY the top-level conjunctions — geq/meq are themselves conjunctions,
     so `repeat split` would over-decompose and misorder the goals. *)
  split; [ exact gi_order4 | ].
  split; [ exact gi_not_invol | ].
  split; [ exact mX_invol | ].
  split; [ exact mS_order4 | exact no_gaussian_sqrt_half ].
Qed.
