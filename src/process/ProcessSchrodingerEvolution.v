(** * ProcessSchrodingerEvolution.v — Schrödinger evolution as a process:
      discrete unitary time-stepping conserves probability (Tier 2, Part VI → physics)

    Elements: rational amplitudes ψ_k; finite lattice; time steps n; unitary step U
    Roles:    U = propagator (one step); ψ_n = the state in time; ‖ψ‖² = probability;
              isometry = unitarity (probability preservation)
    Rules:    ψ_{n+1} = U ψ_n; isometry ⟹ ‖ψ_n‖² = ‖ψ_0‖² for all n (by induction);
              a concrete rational unitary step (the 3-4-5 rotation) really preserves norm

    The Schrödinger equation iℏ ∂ψ/∂t = Ĥψ has unitary evolution ψ(t) = e^{−iĤt/ℏ}ψ(0):
    the norm (total probability) is conserved. Over ℚ the exact propagator e^{−iĤt}
    is unavailable (complex exponential, continuous time). The constructive P4 core is
    the DISCRETE evolution ψ_{n+1} = U ψ_n: when one step U is an isometry (‖Uψ‖ = ‖ψ‖,
    the discrete unitarity), probability is conserved at EVERY step, ‖ψ_n‖² = ‖ψ_0‖²,
    proved by induction. We exhibit a concrete rational unitary — the 3-4-5 rotation
    (c = 3/5, s = 4/5, c² + s² = 1) — that genuinely preserves the norm for all states,
    so the evolution process it generates conserves probability for all n. All over ℚ,
    0 axioms.

    HONEST FRONTIER (P4 boundary): the exact propagator e^{−iĤt} (complex exponential,
    continuous time) is a role-limit; the discrete process ψ_n approximates it. The
    energy-conservation refinement and a genuinely Hamiltonian-derived unitary step
    (Cayley / Crank–Nicolson) are next bricks.

    ============ E/R/R разбор ============
      Rules (L5): ψ_{n+1}=Uψ_n; изометрия ⟹ ‖ψ_n‖²=‖ψ_0‖² ∀n; поворот 3-4-5 (c²+s²=1)
                  сохраняет норму ∀ψ.
      Roles (L4): U=роль-пропагатор; ψ_n=роль-состояние во времени; ‖ψ‖²=роль-вероятность;
                  изометрия=роль-унитарность.
      Elements  : рациональные амплитуды ψ_k, конечная решётка, шаги n, унитарный U (L1+P4).
    ДИАГНОСТИКА: дискретная эволюция + сохранение нормы — процессный факт (0 акс); точный
    e^{−iĤt} (комплексная экспонента, континуальное время) = роль-предел, P4-граница.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Discrete evolution: iterate the one-step propagator U.                *)
(* ===================================================================== *)

Fixpoint evolve (U : nat -> nat -> Q) (N : nat) (v : nat -> Q) (n : nat) : nat -> Q :=
  match n with
  | O => v
  | S k => op_apply U (evolve U N v k) N
  end.

Lemma evolve_succ : forall U N v n,
  evolve U N v (S n) = op_apply U (evolve U N v n) N.
Proof. reflexivity. Qed.

(** A one-step propagator is an isometry (discrete unitarity) if it preserves the
    squared norm. *)
Definition Isometry (U : nat -> nat -> Q) (N : nat) : Prop :=
  forall w, seq_inner (op_apply U w N) (op_apply U w N) N == seq_inner w w N.

(* ===================================================================== *)
(*  Probability conservation: an isometric evolution keeps ‖ψ_n‖² = ‖ψ_0‖². *)
(* ===================================================================== *)

Theorem evolution_conserves_norm : forall (U : nat -> nat -> Q) (N : nat),
  Isometry U N ->
  forall (v : nat -> Q) (n : nat),
  seq_inner (evolve U N v n) (evolve U N v n) N == seq_inner v v N.
Proof.
  intros U N HU v n. induction n as [|k IH].
  - cbn [evolve]. reflexivity.
  - cbn [evolve]. rewrite (HU (evolve U N v k)). exact IH.
Qed.

(* ===================================================================== *)
(*  A concrete rational unitary: the 2×2 rotation [[c,−s],[s,c]].          *)
(* ===================================================================== *)

Definition rotation (c s : Q) : nat -> nat -> Q :=
  fun i j => match i, j with
             | O, O       => c
             | O, S O     => - s
             | S O, O     => s
             | S O, S O   => c
             | _, _       => 0
             end.

(** A rotation with c² + s² = 1 is an isometry (preserves the norm) for all states. *)
Lemma rotation_isometry : forall (c s : Q),
  c * c + s * s == 1 -> Isometry (rotation c s) 2.
Proof.
  intros c s H w.
  transitivity ((c * c + s * s) * seq_inner w w 2).
  - unfold seq_inner, op_apply, rotation. cbn [q_sum]. ring.
  - rewrite H. ring.
Qed.

(** The 3-4-5 rotation (c = 3/5, s = 4/5) is unitary: 9/25 + 16/25 = 1. *)
Lemma rotation_345_isometry : Isometry (rotation (3 # 5) (4 # 5)) 2.
Proof. apply rotation_isometry. lra. Qed.

(** Payoff: the 3-4-5 unitary evolution conserves probability for ALL time steps. *)
Corollary evolution_345_conserves_norm : forall (v : nat -> Q) (n : nat),
  seq_inner (evolve (rotation (3 # 5) (4 # 5)) 2 v n)
            (evolve (rotation (3 # 5) (4 # 5)) 2 v n) 2
  == seq_inner v v 2.
Proof.
  intros v n. apply evolution_conserves_norm. exact rotation_345_isometry.
Qed.

Print Assumptions evolution_conserves_norm.
Print Assumptions evolution_345_conserves_norm.
