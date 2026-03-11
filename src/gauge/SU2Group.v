(* ========================================================================= *)
(*        SU(2) GROUP — Quaternion Algebra over Q                           *)
(*                                                                          *)
(*  SU(2) ≅ unit quaternions: q = a₀ + a₁i + a₂j + a₃k with |q|=1.     *)
(*  Over Q: (a₀, a₁, a₂, a₃) ∈ Q⁴ with a₀²+a₁²+a₂²+a₃² ≈ 1.        *)
(*                                                                          *)
(*  Group multiplication = quaternion product (non-commutative!):           *)
(*    Full: (a₀c₀-a₁c₁-a₂c₂-a₃c₃, a₀c₁+a₁c₀+a₂c₃-a₃c₂, ...)      *)
(*                                                                          *)
(*  STATUS: ~30 Qed, 0 Admitted                                            *)
(*  AXIOMS: none (pure rational arithmetic)                                 *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: Quaternion type and operations                                   *)
(* ========================================================================= *)

Record Quaternion := mkQ4 {
  q0 : Q;  (* scalar part *)
  q1 : Q;  (* i component *)
  q2 : Q;  (* j component *)
  q3 : Q;  (* k component *)
}.

(** Component-wise equality *)
Definition qeq (p q : Quaternion) : Prop :=
  q0 p == q0 q /\ q1 p == q1 q /\ q2 p == q2 q /\ q3 p == q3 q.

(** Quaternion multiplication *)
Definition qmul (p q : Quaternion) : Quaternion :=
  mkQ4
    (q0 p * q0 q - q1 p * q1 q - q2 p * q2 q - q3 p * q3 q)
    (q0 p * q1 q + q1 p * q0 q + q2 p * q3 q - q3 p * q2 q)
    (q0 p * q2 q - q1 p * q3 q + q2 p * q0 q + q3 p * q1 q)
    (q0 p * q3 q + q1 p * q2 q - q2 p * q1 q + q3 p * q0 q).

(** Identity quaternion *)
Definition qid : Quaternion := mkQ4 1 0 0 0.

(** Conjugate: q̄ = (a₀, -a₁, -a₂, -a₃) *)
Definition qconj (q : Quaternion) : Quaternion :=
  mkQ4 (q0 q) (-(q1 q)) (-(q2 q)) (-(q3 q)).

(** Norm squared: |q|² = a₀² + a₁² + a₂² + a₃² *)
Definition qnorm_sq (q : Quaternion) : Q :=
  q0 q * q0 q + q1 q * q1 q + q2 q * q2 q + q3 q * q3 q.

(** Addition *)
Definition qadd (p q : Quaternion) : Quaternion :=
  mkQ4 (q0 p + q0 q) (q1 p + q1 q) (q2 p + q2 q) (q3 p + q3 q).

(** Scalar multiplication *)
Definition qscale (c : Q) (q : Quaternion) : Quaternion :=
  mkQ4 (c * q0 q) (c * q1 q) (c * q2 q) (c * q3 q).

(** Negation *)
Definition qneg (q : Quaternion) : Quaternion :=
  mkQ4 (-(q0 q)) (-(q1 q)) (-(q2 q)) (-(q3 q)).

(** Trace (as 2×2 matrix): tr(q) = 2·q₀ *)
Definition qtrace (q : Quaternion) : Q := 2 * q0 q.

(** Unit quaternion *)
Definition is_unit (q : Quaternion) : Prop := qnorm_sq q == 1.

(** Near-identity parametrization *)
Definition near_id (eps a1 a2 a3 : Q) : Quaternion :=
  mkQ4 1 (eps * a1) (eps * a2) (eps * a3).

(* ========================================================================= *)
(*  PART II: Equality properties                                             *)
(* ========================================================================= *)

Lemma qeq_refl : forall q, qeq q q.
Proof.
  intros q. unfold qeq. repeat split; lra.
Qed.

Lemma qeq_sym : forall p q, qeq p q -> qeq q p.
Proof.
  intros p q [H0 [H1 [H2 H3]]]. unfold qeq. repeat split; lra.
Qed.

Lemma qeq_trans : forall p q r, qeq p q -> qeq q r -> qeq p r.
Proof.
  intros p q r [H0 [H1 [H2 H3]]] [K0 [K1 [K2 K3]]].
  unfold qeq. repeat split; lra.
Qed.

(* ========================================================================= *)
(*  PART III: Group properties                                               *)
(* ========================================================================= *)

(** Left identity *)
Lemma qmul_id_l : forall q, qeq (qmul qid q) q.
Proof.
  intros q. unfold qeq, qmul, qid. simpl. repeat split; ring.
Qed.

(** Right identity *)
Lemma qmul_id_r : forall q, qeq (qmul q qid) q.
Proof.
  intros q. unfold qeq, qmul, qid. simpl. repeat split; ring.
Qed.

(** ★ Associativity — the key group axiom ★ *)
Theorem qmul_assoc : forall p q r,
  qeq (qmul (qmul p q) r) (qmul p (qmul q r)).
Proof.
  intros p q r. unfold qeq, qmul. simpl. repeat split; ring.
Qed.

(** Right multiplication by conjugate: q · q̄ = |q|² · 1 *)
Lemma qmul_conj_r : forall q,
  qeq (qmul q (qconj q)) (mkQ4 (qnorm_sq q) 0 0 0).
Proof.
  intros q. unfold qeq, qmul, qconj, qnorm_sq. simpl. repeat split; ring.
Qed.

(** Left multiplication by conjugate: q̄ · q = |q|² · 1 *)
Lemma qmul_conj_l : forall q,
  qeq (qmul (qconj q) q) (mkQ4 (qnorm_sq q) 0 0 0).
Proof.
  intros q. unfold qeq, qmul, qconj, qnorm_sq. simpl. repeat split; ring.
Qed.

(** Conjugation is involutive *)
Lemma qconj_involutive : forall q, qeq (qconj (qconj q)) q.
Proof.
  intros q. unfold qeq, qconj. simpl. repeat split; ring.
Qed.

(* ========================================================================= *)
(*  PART IV: Norm properties                                                 *)
(* ========================================================================= *)

(** Norm squared is non-negative *)
Lemma qnorm_sq_nonneg : forall q, 0 <= qnorm_sq q.
Proof.
  intros q. unfold qnorm_sq.
  assert (H0 : 0 <= q0 q * q0 q) by nra.
  assert (H1 : 0 <= q1 q * q1 q) by nra.
  assert (H2 : 0 <= q2 q * q2 q) by nra.
  assert (H3 : 0 <= q3 q * q3 q) by nra.
  lra.
Qed.

(** ★ Euler four-square identity: |pq|² = |p|²·|q|² ★ *)
Theorem qnorm_mul : forall p q,
  qnorm_sq (qmul p q) == qnorm_sq p * qnorm_sq q.
Proof.
  intros p q. unfold qnorm_sq, qmul. simpl. ring.
Qed.

(** Product of unit quaternions is unit *)
Theorem unit_closed : forall p q,
  is_unit p -> is_unit q -> is_unit (qmul p q).
Proof.
  intros p q Hp Hq. unfold is_unit.
  rewrite qnorm_mul.
  unfold is_unit in Hp, Hq.
  rewrite Hp. rewrite Hq. ring.
Qed.

(** Identity is unit *)
Lemma qid_is_unit : is_unit qid.
Proof.
  unfold is_unit, qnorm_sq, qid. simpl. ring.
Qed.

(** Conjugate of unit is unit *)
Lemma qconj_is_unit : forall q, is_unit q -> is_unit (qconj q).
Proof.
  intros q H. unfold is_unit, qnorm_sq, qconj in *. simpl. lra.
Qed.

(** Norm of conjugate equals norm *)
Lemma qnorm_sq_conj : forall q, qnorm_sq (qconj q) == qnorm_sq q.
Proof.
  intros q. unfold qnorm_sq, qconj. simpl. ring.
Qed.

(* ========================================================================= *)
(*  PART V: Non-commutativity — the key difference from U(1)                *)
(* ========================================================================= *)

(** i = (0,1,0,0), j = (0,0,1,0), k = (0,0,0,1) *)
Definition qi : Quaternion := mkQ4 0 1 0 0.
Definition qj : Quaternion := mkQ4 0 0 1 0.
Definition qk : Quaternion := mkQ4 0 0 0 1.

(** i · j = k *)
Lemma qmul_ij : qeq (qmul qi qj) qk.
Proof.
  unfold qeq, qmul, qi, qj, qk. simpl.
  repeat split; unfold Qeq; simpl; lia.
Qed.

(** j · i = -k *)
Lemma qmul_ji : qeq (qmul qj qi) (qneg qk).
Proof.
  unfold qeq, qmul, qj, qi, qneg, qk. simpl.
  repeat split; unfold Qeq; simpl; lia.
Qed.

(** ★ SU(2) is non-commutative ★ *)
Theorem qmul_noncommutative :
  exists p q, ~ qeq (qmul p q) (qmul q p).
Proof.
  exists qi, qj. intro H.
  destruct H as [_ [_ [_ H3]]].
  (* q3 of i·j = 1, q3 of j·i = -1 *)
  unfold qmul, qi, qj in H3. simpl in H3. lra.
Qed.

(* ========================================================================= *)
(*  PART VI: Trace properties                                                *)
(* ========================================================================= *)

(** ★ Trace is cyclic: tr(pq) = tr(qp) ★ *)
(** This is KEY for gauge invariance of the Wilson action *)
Theorem trace_cyclic : forall p q,
  qtrace (qmul p q) == qtrace (qmul q p).
Proof.
  intros p q. unfold qtrace, qmul. simpl. ring.
Qed.

(** Trace of identity = 2 *)
Lemma qtrace_id : qtrace qid == 2.
Proof.
  unfold qtrace, qid. simpl. ring.
Qed.

(** Trace of conjugate = trace *)
Lemma qtrace_conj : forall q, qtrace (qconj q) == qtrace q.
Proof.
  intros q. unfold qtrace, qconj. simpl. ring.
Qed.

(** q0 of identity *)
Lemma q0_id : q0 qid == 1.
Proof. unfold qid. simpl. lra. Qed.

(* ========================================================================= *)
(*  PART VII: Additional algebraic properties                                *)
(* ========================================================================= *)

(** Addition is commutative *)
Lemma qadd_comm : forall p q, qeq (qadd p q) (qadd q p).
Proof.
  intros p q. unfold qeq, qadd. simpl. repeat split; ring.
Qed.

(** Scalar zero *)
Lemma qscale_zero : forall q, qeq (qscale 0 q) (mkQ4 0 0 0 0).
Proof.
  intros q. unfold qeq, qscale. simpl. repeat split; ring.
Qed.

(** Scalar one *)
Lemma qscale_one : forall q, qeq (qscale 1 q) q.
Proof.
  intros q. unfold qeq, qscale. simpl. repeat split; ring.
Qed.

(** Near-identity at eps=0 is identity *)
Lemma near_id_at_zero : forall a1 a2 a3,
  qeq (near_id 0 a1 a2 a3) qid.
Proof.
  intros a1 a2 a3. unfold qeq, near_id, qid. simpl. repeat split; ring.
Qed.

(** Norm squared of near-identity *)
Lemma near_id_norm_sq : forall eps a1 a2 a3,
  qnorm_sq (near_id eps a1 a2 a3) ==
  1 + eps * eps * (a1 * a1 + a2 * a2 + a3 * a3).
Proof.
  intros. unfold qnorm_sq, near_id. simpl. ring.
Qed.

(** q0 bound for unit quaternions: q0² ≤ 1 *)
Lemma q0_unit_sq_bound : forall q,
  is_unit q -> q0 q * q0 q <= 1.
Proof.
  intros q Hu. unfold is_unit, qnorm_sq in Hu.
  assert (H1 : 0 <= q1 q * q1 q) by nra.
  assert (H2 : 0 <= q2 q * q2 q) by nra.
  assert (H3 : 0 <= q3 q * q3 q) by nra.
  lra.
Qed.

(* ========================================================================= *)
(*  PART VIII: Summary                                                       *)
(* ========================================================================= *)

Theorem su2_group_summary :
  (* Associativity *)
  (forall p q r, qeq (qmul (qmul p q) r) (qmul p (qmul q r))) /\
  (* Identity *)
  (forall q, qeq (qmul qid q) q) /\
  (forall q, qeq (qmul q qid) q) /\
  (* Conjugate gives inverse for unit quaternions *)
  (forall q, qeq (qmul q (qconj q)) (mkQ4 (qnorm_sq q) 0 0 0)) /\
  (* Norm multiplicative *)
  (forall p q, qnorm_sq (qmul p q) == qnorm_sq p * qnorm_sq q) /\
  (* Non-commutativity *)
  (exists p q, ~ qeq (qmul p q) (qmul q p)) /\
  (* Trace cyclic *)
  (forall p q, qtrace (qmul p q) == qtrace (qmul q p)) /\
  (* Unit closure *)
  (forall p q, is_unit p -> is_unit q -> is_unit (qmul p q)).
Proof.
  split; [exact qmul_assoc |].
  split; [exact qmul_id_l |].
  split; [exact qmul_id_r |].
  split; [exact qmul_conj_r |].
  split; [exact qnorm_mul |].
  split; [exact qmul_noncommutative |].
  split; [exact trace_cyclic |].
  exact unit_closed.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(*  ~30 Qed, 0 Admitted                                                     *)
(*                                                                           *)
(*  Part II: qeq_refl, qeq_sym, qeq_trans (3)                             *)
(*  Part III: qmul_id_l, qmul_id_r, qmul_assoc, qmul_conj_r,             *)
(*            qmul_conj_l, qconj_involutive (6)                            *)
(*  Part IV: qnorm_sq_nonneg, qnorm_mul, unit_closed,                      *)
(*           qid_is_unit, qconj_is_unit, qnorm_sq_conj (6)                *)
(*  Part V: qmul_ij, qmul_ji, qmul_noncommutative (3)                     *)
(*  Part VI: trace_cyclic, qtrace_id, qtrace_conj, q0_id (4)              *)
(*  Part VII: qadd_comm, qscale_zero, qscale_one, near_id_at_zero,        *)
(*            near_id_norm_sq, q0_unit_sq_bound (6)                        *)
(*  Part VIII: su2_group_summary, total_count (2)                           *)
(* ========================================================================= *)
