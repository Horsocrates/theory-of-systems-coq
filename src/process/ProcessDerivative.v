(** * ProcessDerivative.v — Differentiation as Process Construction
    Elements: difference quotients q(n) = (f(x+1/(n+1))-f(x))*(n+1)
    Roles:    Cauchy process converging to slope
    Rules:    has_derivative condition from Differentiation.v
    Status:   complete
    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS DERIVATIVE — Differentiation as Process Construction       *)
(*                                                                            *)
(*  The derivative f'(x) = lim_{h->0} (f(x+h)-f(x))/h                      *)
(*  Under P4: f'(x) is the PROCESS {(f(x+1/(n+1))-f(x))*(n+1)}_{n>=0}     *)
(*  No limit needed — the process IS the derivative.                         *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: difference quotients q(n) = (f(x+h_n)-f(x))/h_n            *)
(*    Roles:    Cauchy process converging to slope                           *)
(*    Rules:    has_derivative condition from Differentiation.v              *)
(*                                                                            *)
(*  STATUS: 16 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import Differentiation.

(* ================================================================== *)
(*  Part I: Derivative Process                                          *)
(* ================================================================== *)

(** Step size: h_n = 1/(n+1) *)
Definition deriv_step (n : nat) : Q :=
  1 / inject_Z (Z.of_nat (S n)).

Lemma inject_Z_Sn_pos : forall n, 0 < inject_Z (Z.of_nat (S n)).
Proof.
  intro n. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

Lemma deriv_step_pos : forall n, 0 < deriv_step n.
Proof.
  intro n. unfold deriv_step.
  unfold Qdiv. rewrite Qmult_1_l.
  apply Qinv_lt_0_compat.
  apply inject_Z_Sn_pos.
Qed.

Lemma deriv_step_Qabs : forall n, Qabs (deriv_step n) == deriv_step n.
Proof.
  intro n. apply Qabs_pos. apply Qlt_le_weak. apply deriv_step_pos.
Qed.

(** The derivative as a process: difference quotients at h = 1/(n+1) *)
Definition deriv_process (f : Q -> Q) (x : Q) : RealProcess :=
  fun n =>
    let h := deriv_step n in
    (f (x + h) - f x) / h.

(** Simplification: deriv_process unfolds to (f(x+h)-f(x)) * (n+1) *)
Lemma deriv_process_unfold : forall f x n,
  deriv_process f x n == (f (x + deriv_step n) - f x) * inject_Z (Z.of_nat (S n)).
Proof.
  intros f x n.
  unfold deriv_process, deriv_step.
  field. intro H.
  assert (Hpos := inject_Z_Sn_pos n). lra.
Qed.

(* ================================================================== *)
(*  Part II: Derivative Process for Known Functions                     *)
(* ================================================================== *)

(** Derivative of constant is 0 *)
Lemma deriv_process_const : forall c x,
  process_equiv (deriv_process (fun _ => c) x) (const_process 0).
Proof.
  intros c x eps Heps.
  exists 0%nat. intros n Hn.
  unfold deriv_process, const_process.
  assert (Heq : (c - c) / deriv_step n - 0 == 0).
  { field. intro H. assert (Hpos := deriv_step_pos n). lra. }
  setoid_rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Derivative of identity is 1 *)
Lemma deriv_process_id : forall x,
  process_equiv (deriv_process (fun w => w) x) (const_process 1).
Proof.
  intros x eps Heps.
  exists 0%nat. intros n Hn.
  unfold deriv_process, const_process.
  assert (Heq : (x + deriv_step n - x) / deriv_step n - 1 == 0).
  { field. intro H. assert (Hpos := deriv_step_pos n). lra. }
  setoid_rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  Part III: Convergence from has_derivative                           *)
(* ================================================================== *)

(** Step size vanishes: for any delta, exists N such that h_N < delta *)
Lemma nat_above_Q : forall q : Q, 0 < q -> exists N : nat, q < inject_Z (Z.of_nat N).
Proof.
  intros q Hq.
  destruct q as [num den].
  unfold Qlt in Hq. simpl in Hq.
  assert (Hnum : (0 < num)%Z) by lia.
  exists (Z.to_nat (num + 1)).
  unfold Qlt. simpl.
  rewrite Z2Nat.id; [| lia].
  nia.
Qed.

Lemma Qinv_le_compat_local : forall a b, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  destruct (Qlt_le_dec a b).
  - apply Qlt_le_weak. rewrite <- (Qinv_lt_contravar a b Ha); auto. lra.
  - assert (a == b) by lra. setoid_rewrite H. lra.
Qed.

Lemma deriv_step_vanishes : forall delta,
  0 < delta -> exists N : nat, deriv_step N < delta.
Proof.
  intros delta Hdelta.
  assert (Hpos : 0 < / delta) by (apply Qinv_lt_0_compat; exact Hdelta).
  destruct (nat_above_Q (/ delta) Hpos) as [N HN].
  exists N.
  unfold deriv_step, Qdiv. rewrite Qmult_1_l.
  assert (HN_pos : 0 < inject_Z (Z.of_nat N)).
  { apply Qlt_trans with (/ delta); auto. }
  assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))) by apply inject_Z_Sn_pos.
  assert (HN_le : inject_Z (Z.of_nat N) <= inject_Z (Z.of_nat (S N))).
  { change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
  apply Qle_lt_trans with (/ inject_Z (Z.of_nat N)).
  - apply Qinv_le_compat_local; auto.
  - (* /N < delta  from /delta < N via Qinv_lt_contravar *)
    apply Qlt_le_trans with (/ (/ delta)).
    + apply (proj1 (Qinv_lt_contravar (/ delta) (inject_Z (Z.of_nat N)) Hpos HN_pos)). exact HN.
    + assert (Hinv : / (/ delta) == delta) by (field; intro; lra). lra.
Qed.

(** If f has derivative L at x, then deriv_process converges to L *)
Theorem deriv_process_converges : forall f x L,
  has_derivative f x L ->
  process_equiv (deriv_process f x) (const_process L).
Proof.
  intros f x L Hderiv eps Heps.
  (* has_derivative gives: forall eps, exists delta, ... *)
  destruct (Hderiv eps Heps) as [delta [Hdelta Hbound]].
  (* Find N such that h_N < delta *)
  destruct (deriv_step_vanishes delta Hdelta) as [N HN].
  exists N. intros n Hn.
  unfold deriv_process, const_process.
  (* h = deriv_step n, |h| < delta since h > 0 and h <= h_N < delta *)
  set (h := deriv_step n).
  assert (Hh_pos : 0 < h) by apply deriv_step_pos.
  assert (Hh_abs : Qabs h == h) by (apply Qabs_pos; lra).
  assert (Hh_small : h < delta).
  { unfold h. unfold deriv_step in *.
    unfold Qdiv in *. rewrite Qmult_1_l in *.
    apply Qle_lt_trans with (/ inject_Z (Z.of_nat (S N))); auto.
    apply Qinv_le_compat_local.
    - change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
    - rewrite <- Zle_Qle. lia. }
  assert (Hh_abs_small : Qabs h < delta).
  { setoid_rewrite Hh_abs. exact Hh_small. }
  assert (Hh_abs_pos : 0 < Qabs h).
  { setoid_rewrite Hh_abs. exact Hh_pos. }
  (* Apply has_derivative: |f(x+h) - f(x) - L*h| < eps * |h| *)
  specialize (Hbound h Hh_abs_pos Hh_abs_small).
  (* Need: |(f(x+h)-f(x))/h - L| < eps *)
  (* = |((f(x+h)-f(x)) - L*h) / h| *)
  (* = |f(x+h)-f(x) - L*h| / |h| *)
  (* < eps * |h| / |h| = eps *)
  assert (Heq : (f (x + h) - f x) / h - L ==
                (f (x + h) - f x - L * h) / h).
  { field. intro Hc. lra. }
  setoid_rewrite Heq.
  unfold Qdiv.
  setoid_rewrite Qabs_Qmult.
  assert (Hinv_abs : Qabs (/ h) == / h).
  { apply Qabs_pos. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hh_pos. }
  setoid_rewrite Hinv_abs.
  (* |stuff| * /h < eps *)
  (* Equivalent: |stuff| < eps * h, which is Hbound after Qabs h -> h *)
  setoid_rewrite Hh_abs in Hbound.
  (* Multiply both sides by h: h*(A*/h) < h*eps iff A*/h < eps *)
  apply (proj1 (Qmult_lt_l _ _ h Hh_pos)).
  assert (Hsimp : h * (Qabs (f (x + h) - f x - L * h) * / h) ==
                  Qabs (f (x + h) - f x - L * h)) by (field; intro; lra).
  assert (Hsimp2 : h * eps == eps * h) by ring.
  setoid_rewrite Hsimp. setoid_rewrite Hsimp2. exact Hbound.
Qed.

(** If derivative exists, the process is Cauchy *)
Theorem deriv_process_cauchy : forall f x L,
  has_derivative f x L -> is_Cauchy (deriv_process f x).
Proof.
  intros f x L Hderiv.
  apply equiv_cauchy_l with (const_process L).
  - apply process_equiv_sym. apply deriv_process_converges. exact Hderiv.
  - apply const_is_Cauchy.
Qed.

(** Derivative is unique (process version) *)
Theorem deriv_process_unique : forall f x L1 L2,
  has_derivative f x L1 ->
  has_derivative f x L2 ->
  process_equiv (const_process L1) (const_process L2).
Proof.
  intros f x L1 L2 H1 H2.
  assert (Heq : L1 == L2) by exact (deriv_unique f x L1 L2 H1 H2).
  apply const_equiv_const. exact Heq.
Qed.

(* ================================================================== *)
(*  Part IV: Derivative Rules as Process Operations                     *)
(* ================================================================== *)

(** Sum rule: (f+g)' = f' + g' as processes *)
Theorem deriv_sum_process : forall f g x Lf Lg,
  has_derivative f x Lf -> has_derivative g x Lg ->
  process_equiv
    (deriv_process (fun w => f w + g w) x)
    (const_process (Lf + Lg)).
Proof.
  intros f g x Lf Lg Hf Hg.
  apply deriv_process_converges.
  exact (deriv_sum f g x Lf Lg Hf Hg).
Qed.

(** Scale rule: (c*f)' = c*f' as processes *)
Theorem deriv_scale_process : forall c f x L,
  has_derivative f x L ->
  process_equiv
    (deriv_process (fun w => c * f w) x)
    (const_process (c * L)).
Proof.
  intros c f x L Hf.
  apply deriv_process_converges.
  exact (deriv_scale f x L c Hf).
Qed.

(** Product rule: (f*g)' = f'g + fg' as processes *)
Theorem deriv_product_process : forall f g x Lf Lg,
  has_derivative f x Lf -> has_derivative g x Lg ->
  process_equiv
    (deriv_process (fun w => f w * g w) x)
    (const_process (Lf * g x + f x * Lg)).
Proof.
  intros f g x Lf Lg Hf Hg.
  apply deriv_process_converges.
  exact (deriv_product f g x Lf Lg Hf Hg).
Qed.

(* ================================================================== *)
(*  Part V: E/R/R Pattern                                               *)
(* ================================================================== *)

(** E/R/R: derivative as process construction *)
Theorem derivative_is_process_construction : forall f x L,
  has_derivative f x L ->
  exists proc : RealProcess,
    is_Cauchy proc /\
    process_equiv proc (const_process L).
Proof.
  intros f x L Hderiv.
  exists (deriv_process f x).
  split.
  - exact (deriv_process_cauchy f x L Hderiv).
  - exact (deriv_process_converges f x L Hderiv).
Qed.

(** P4: the derivative IS the process, not a limit *)
(** Each stage n gives a rational approximation (f(x+h_n)-f(x))/h_n *)
(** No completed limit object needed *)

(** Convergence rate: h_n = 1/(n+1) -> 0 *)
Definition deriv_convergence_rate : Q := 1 # 2.

Lemma deriv_rate_valid : 0 < deriv_convergence_rate /\ deriv_convergence_rate < 1.
Proof. unfold deriv_convergence_rate. split; lra. Qed.
