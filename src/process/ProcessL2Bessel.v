(** * ProcessL2Bessel.v — Best approximation / Bessel for one orthonormal direction
      (F-29 / Riesz–Fischer frontier mechanism, Part VI)

    Elements: coefficient c = ⟨e,f⟩; residual coordinates f − c·e; finite sums
    Roles:    ⟨e,f⟩ = projection coefficient; residual = remainder; Bessel = energy bound
    Rules:    ‖f‖² = ⟨e,f⟩² + ‖f − ⟨e,f⟩e‖² (Pythagoras); ⟨e,f⟩² ≤ ‖f‖² (Bessel)

    Completeness of L² (Riesz–Fischer) and orthonormal-basis theory rest on the
    BEST-APPROXIMATION mechanism: for a unit vector e, projecting f onto e leaves a
    residual r = f − ⟨e,f⟩·e orthogonal to e, and the energy splits
        ‖f‖² = ⟨e,f⟩² + ‖r‖²        (Pythagoras),
    whence the one-direction Bessel inequality ⟨e,f⟩² ≤ ‖f‖². We prove this on the
    process-L² inner product (sequences), exactly and with 0 axioms, via the
    residual-norm identity (a single induction, in the style of the Lagrange
    identity). This is the mechanism on which the full theory is built.

    HONEST FRONTIER (research-level, NOT done here): Bessel for a general
    orthonormal SYSTEM (Σ_{k<K}⟨eₖ,f⟩² ≤ ‖f‖², needs the finite-projection
    double-sum with orthogonality), the Parseval EQUALITY completeness criterion,
    the full Riesz–Fischer with a CONSTRUCTED limit (a Cauchy L²-sequence converges
    — nested processes-of-reals), and the diagonalisation of an ARBITRARY compact
    self-adjoint operator (variational construction; "compactness ⇒ the sup is
    attained" is the hard constructive step). These are where completed-infinity / AC
    enter classically; here we give the constructive one-direction core.

    ============ E/R/R разбор ============
      Rules (L5): ‖f‖²=⟨e,f⟩²+‖r‖² (Пифагор); ⟨e,f⟩²≤‖f‖² (Бессель); остаток ⟂ e.
      Roles (L4): ⟨e,f⟩ = роль-коэффициент; остаток = роль-остаток; Бессель = закон
                  сохранения энергии (коэффициент не больше нормы).
      Elements  : c=⟨e,f⟩, координаты остатка, конечные суммы (L1+P4).
    ДИАГНОСТИКА: полнота/Парсеваль = процессная связь (ряд коэффициентов → норма), не
    свойство завершённого Гильберта; препятствия общего случая (sup-достигается,
    вложенные пределы) — там, где классика использует завершённую ∞/AC.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Residual-norm identity (single induction, à la the Lagrange identity).*)
(*    Σ (fᵢ − c·eᵢ)²  =  Σ fᵢ²  − 2c·Σ eᵢfᵢ  + c²·Σ eᵢ²                    *)
(* ===================================================================== *)

Lemma seq_inner_residual_identity : forall (e f : nat -> Q) (c : Q) (N : nat),
  q_sum (fun i => (f i - c * e i) * (f i - c * e i)) N
  == q_sum (fun i => f i * f i) N
     - 2 * c * q_sum (fun i => e i * f i) N
     + c * c * q_sum (fun i => e i * e i) N.
Proof.
  intros e f c N. induction N as [|k IH]; cbn [q_sum].
  - ring.
  - rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  Pythagoras for one orthonormal direction:                            *)
(*    ⟨e,e⟩ = 1  ⟹  ‖f‖² = ⟨e,f⟩² + ‖f − ⟨e,f⟩·e‖²                       *)
(* ===================================================================== *)

Theorem pythagoras_one : forall (e f : nat -> Q) (N : nat),
  seq_inner e e N == 1 ->
  seq_inner f f N
  == (seq_inner e f N) * (seq_inner e f N)
     + seq_inner (fun m => f m - (seq_inner e f N) * e m)
                 (fun m => f m - (seq_inner e f N) * e m) N.
Proof.
  intros e f N Hunit. unfold seq_inner in *.
  pose proof (seq_inner_residual_identity e f (q_sum (fun i => e i * f i) N) N) as Hres.
  set (c := q_sum (fun i => e i * f i) N) in *.
  rewrite Hres, Hunit. ring.
Qed.

(* ===================================================================== *)
(*  Bessel for one orthonormal direction: ⟨e,f⟩² ≤ ‖f‖².                  *)
(* ===================================================================== *)

Theorem bessel_one : forall (e f : nat -> Q) (N : nat),
  seq_inner e e N == 1 ->
  (seq_inner e f N) * (seq_inner e f N) <= seq_inner f f N.
Proof.
  intros e f N Hunit.
  pose proof (pythagoras_one e f N Hunit) as Hpy.
  assert (Hr : 0 <= seq_inner (fun m => f m - (seq_inner e f N) * e m)
                              (fun m => f m - (seq_inner e f N) * e m) N).
  { unfold seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg. }
  rewrite Hpy. lra.
Qed.

(* Computational sanity: e = standard basis vector |0⟩ (unit), f = (3,4,…);
   ⟨e,f⟩ = 3, ‖f‖²(2) = 9+16 = 25, Bessel: 9 ≤ 25. *)
Example bessel_one_concrete :
  let e := fun n => if Nat.eqb n 0 then 1 else 0 in
  let f := fun n => if Nat.eqb n 0 then 3 else 4 in
  (seq_inner e f 2) * (seq_inner e f 2) == 9 /\ seq_inner f f 2 == 25.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions bessel_one.
