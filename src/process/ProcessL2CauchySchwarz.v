(** * ProcessL2CauchySchwarz.v — General-N Cauchy–Schwarz for the L² inner product
      (F-29 core, Part VI)

    Elements: rational samples f(xᵢ), g(xᵢ); finite inner-product sums
    Roles:    the L² inner product ⟨f,g⟩ = ∫fg as a process value; norm ⟨f,f⟩
    Rules:    Cauchy–Schwarz ⟨f,g⟩² ≤ ⟨f,f⟩·⟨g,g⟩ (Lagrange / sum-of-squares)

    The function-space L² inner product is ⟨f,g⟩ = ∫ f·g ≈ w·Σ_{i<N} f(xᵢ)g(xᵢ).
    The keystone of an inner-product space is the Cauchy–Schwarz inequality. In the
    repository it was proven only for 2-vectors (analysis/L2Space.l2_cauchy_schwarz_2d);
    here we prove it for ARBITRARY N — i.e. for the function-space inner product —
    constructively, with 0 axioms, via the Lagrange identity
        (Σaᵢ²)(Σbᵢ²) − (Σaᵢbᵢ)²  =  Σ_{i<k}(aᵢ·b_k − a_k·bᵢ)²  ≥  0.
    Together with the completeness infrastructure of ProcessL2.v (L2_dist,
    L2_cauchy_seq, L2_complete_bound, L2_is_process) this gives the L²-as-function-
    space core: an inner product, Cauchy–Schwarz, and process completeness. The full
    quotient Hilbert space and orthonormal bases (infinite-dimensional) remain a
    P4-boundary.

    ============ E/R/R разбор ============
      Rules (L5): билинейность ⟨·,·⟩, Коши–Шварц (через SOS ≥ 0); скаляр w ≥ 0.
      Roles (L4): ⟨f,g⟩ = роль-значение скалярного произведения; ⟨f,f⟩ = квадрат
                  нормы (роль-длина); Коши–Шварц = правило-связь между ними.
      Elements  : рациональные выборки f(xᵢ), конечные суммы — конечны (L1+P4).
    ДИАГНОСТИКА: Коши–Шварц общего N — то, что делает L² инородным произведением
    пространством (а не только 2D); бесконечномерный гильбертов L² с ортобазисом —
    P4-граница (завершённое пространство), процессное ядро доказано.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.   (* q_sum, q_sum_nonneg *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Helpers                                                              *)
(* ===================================================================== *)

(** A square is nonnegative. *)
Lemma q_sq_nonneg : forall x : Q, 0 <= x * x.
Proof. intro x. nra. Qed.

(** Lagrange / sum-of-squares identity (single induction, fixed p,q):
    Σ_{i<k} (aᵢ·q − p·bᵢ)²  =  q²·Σaᵢ² − 2pq·Σaᵢbᵢ + p²·Σbᵢ². *)
Lemma sos_identity : forall (a b : nat -> Q) (p q : Q) (k : nat),
  q_sum (fun i => (a i * q - p * b i) * (a i * q - p * b i)) k
  == q * q * q_sum (fun i => a i * a i) k
     - 2 * p * q * q_sum (fun i => a i * b i) k
     + p * p * q_sum (fun i => b i * b i) k.
Proof.
  intros a b p q k. induction k as [|k IH]; cbn [q_sum].
  - ring.
  - rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  Discrete Cauchy–Schwarz (general N) on the inner-product sums.        *)
(* ===================================================================== *)

Lemma q_sum_cauchy_schwarz : forall (a b : nat -> Q) (N : nat),
  (q_sum (fun i => a i * b i) N) * (q_sum (fun i => a i * b i) N)
  <= (q_sum (fun i => a i * a i) N) * (q_sum (fun i => b i * b i) N).
Proof.
  intros a b N. induction N as [|k IH]; cbn [q_sum].
  - lra.
  - pose proof (sos_identity a b (a k) (b k) k) as Hsos.
    assert (Hsos_nn :
      0 <= q_sum (fun i => (a i * b k - a k * b i) * (a i * b k - a k * b i)) k)
      by (apply q_sum_nonneg; intro i; apply q_sq_nonneg).
    set (A := q_sum (fun i => a i * a i) k) in *.
    set (B := q_sum (fun i => b i * b i) k) in *.
    set (C := q_sum (fun i => a i * b i) k) in *.
    (* IH : C * C <= A * B *)
    assert (Hbr : 0 <= b k * b k * A - 2 * (a k) * (b k) * C + a k * a k * B).
    { rewrite <- Hsos. exact Hsos_nn. }
    rewrite Qle_minus_iff.
    assert (Hexp :
      (A + a k * a k) * (B + b k * b k)
        + - ((C + a k * b k) * (C + a k * b k))
      == (A * B + - (C * C))
         + (b k * b k * A - 2 * (a k) * (b k) * C + a k * a k * B)) by ring.
    rewrite Hexp.
    assert (hP : 0 <= A * B + - (C * C)) by (rewrite <- Qle_minus_iff; exact IH).
    lra.
Qed.

(* ===================================================================== *)
(*  The L² inner product on a function, sampled at N points with width w. *)
(*    ⟨f,g⟩ = w · Σ_{i<N} f(xᵢ) g(xᵢ)   ( ≈ ∫ f·g )                       *)
(* ===================================================================== *)

Definition l2_inner (f g : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat) : Q :=
  w * q_sum (fun i => f (pts i) * g (pts i)) N.

(** Symmetry. *)
Lemma l2_inner_sym : forall f g pts w N,
  l2_inner f g pts w N == l2_inner g f pts w N.
Proof.
  intros f g pts w N. unfold l2_inner.
  assert (E : q_sum (fun i => f (pts i) * g (pts i)) N
              == q_sum (fun i => g (pts i) * f (pts i)) N).
  { induction N as [|k IH]; cbn [q_sum]; [ reflexivity | rewrite IH; ring ]. }
  rewrite E. reflexivity.
Qed.

(** The self inner product (squared norm) is nonnegative when w ≥ 0. *)
Lemma l2_self_nonneg : forall f pts w N,
  0 <= w -> 0 <= l2_inner f f pts w N.
Proof.
  intros f pts w N Hw. unfold l2_inner.
  rewrite (Qmult_comm w).
  apply Qmult_le_0_compat; [ | exact Hw ].
  apply q_sum_nonneg. intro i. apply q_sq_nonneg.
Qed.

(* ===================================================================== *)
(*  MAIN: Cauchy–Schwarz for the L² inner product (general N).            *)
(*    ⟨f,g⟩² ≤ ⟨f,f⟩ · ⟨g,g⟩.                                            *)
(* ===================================================================== *)

Theorem l2_cauchy_schwarz : forall f g pts w N,
  0 <= w ->
  (l2_inner f g pts w N) * (l2_inner f g pts w N)
  <= (l2_inner f f pts w N) * (l2_inner g g pts w N).
Proof.
  intros f g pts w N Hw. unfold l2_inner.
  pose proof (q_sum_cauchy_schwarz (fun i => f (pts i)) (fun i => g (pts i)) N) as Hcs.
  cbv beta in Hcs.
  set (P := q_sum (fun i => f (pts i) * g (pts i)) N) in *.
  set (Qf := q_sum (fun i => f (pts i) * f (pts i)) N) in *.
  set (Qg := q_sum (fun i => g (pts i) * g (pts i)) N) in *.
  (* goal: (w*P)*(w*P) <= (w*Qf)*(w*Qg) ;  Hcs : P*P <= Qf*Qg *)
  assert (EL : (w * P) * (w * P) == (P * P) * (w * w)) by ring.
  assert (ER : (w * Qf) * (w * Qg) == (Qf * Qg) * (w * w)) by ring.
  rewrite EL, ER.
  apply Qmult_le_compat_r; [ exact Hcs | apply q_sq_nonneg ].
Qed.

(* ===================================================================== *)
(*  Polarization (sqrt-free): ⟨f+g,f+g⟩ = ⟨f,f⟩ + 2⟨f,g⟩ + ⟨g,g⟩.        *)
(* ===================================================================== *)

Lemma l2_inner_expand : forall f g pts w N,
  l2_inner (fun x => f x + g x) (fun x => f x + g x) pts w N
  == l2_inner f f pts w N + 2 * l2_inner f g pts w N + l2_inner g g pts w N.
Proof.
  intros f g pts w N. unfold l2_inner. cbv beta.
  assert (E : q_sum (fun i => (f (pts i) + g (pts i)) * (f (pts i) + g (pts i))) N
              == q_sum (fun i => f (pts i) * f (pts i)) N
                 + 2 * q_sum (fun i => f (pts i) * g (pts i)) N
                 + q_sum (fun i => g (pts i) * g (pts i)) N).
  { induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ]. }
  rewrite E. ring.
Qed.

(** Polarization for the difference: ⟨f−g,f−g⟩ = ⟨f,f⟩ − 2⟨f,g⟩ + ⟨g,g⟩. *)
Lemma l2_inner_expand_sub : forall f g pts w N,
  l2_inner (fun x => f x - g x) (fun x => f x - g x) pts w N
  == l2_inner f f pts w N - 2 * l2_inner f g pts w N + l2_inner g g pts w N.
Proof.
  intros f g pts w N. unfold l2_inner. cbv beta.
  assert (E : q_sum (fun i => (f (pts i) - g (pts i)) * (f (pts i) - g (pts i))) N
              == q_sum (fun i => f (pts i) * f (pts i)) N
                 - 2 * q_sum (fun i => f (pts i) * g (pts i)) N
                 + q_sum (fun i => g (pts i) * g (pts i)) N).
  { induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ]. }
  rewrite E. ring.
Qed.

(** AM–GM for the inner product (sqrt-free; the Minkowski / completeness tool):
    2⟨f,g⟩ ≤ ⟨f,f⟩ + ⟨g,g⟩, from ⟨f−g,f−g⟩ ≥ 0. *)
Lemma l2_2inner_le : forall f g pts w N,
  0 <= w ->
  2 * l2_inner f g pts w N <= l2_inner f f pts w N + l2_inner g g pts w N.
Proof.
  intros f g pts w N Hw.
  pose proof (l2_self_nonneg (fun x => f x - g x) pts w N Hw) as Hnn.
  rewrite l2_inner_expand_sub in Hnn.
  lra.
Qed.

(* Computational sanity checks. *)
Example l2_inner_orthogonal :
  (* f(x)=x, g(x)=1−x, samples 0,1 : ⟨f,g⟩ = 0·1 + 1·0 = 0 *)
  l2_inner (fun x => x) (fun x => 1 - x)
           (fun i => if Nat.eqb i 0 then 0 else 1) 1 2 == 0.
Proof. vm_compute. reflexivity. Qed.

Example l2_inner_self_sq :
  (* f(x)=x, samples 3,4, width 1 : ⟨f,f⟩ = 9 + 16 = 25 *)
  l2_inner (fun x => x) (fun x => x)
           (fun i => if Nat.eqb i 0 then 3 else 4) 1 2 == 25.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions l2_cauchy_schwarz.
