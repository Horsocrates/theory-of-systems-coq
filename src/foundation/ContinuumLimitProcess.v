(** * ContinuumLimitProcess.v — Q1 of the open agenda: can the continuum limit (the causal-set
      Hauptvermutung) be made CONSTRUCTIVE?  Answer, in the P4 sense: YES for the tractable core — the
      continuum length is the LIMIT OF A PROCESS (nat -> Q), approached by the discrete causal-set volume
      with an EXPLICIT rational error < 1/k; each estimate is Element (rational), the limit itself is a
      role-limit (never completed).  The FULL Hauptvermutung (that the 3+1D limit fixes a UNIQUE geometry)
      stays open — that is Q3.

    -- The construction --
      Refine the chain by DENSITY k (a grid of spacing 1/k).  The discrete volume of [0,L) at density k is
      the count of grid points = Qfloor (k*L); the volume ESTIMATE is that count divided by k:
          vol_estimate k L = Qfloor (k*L) / k.
      As k grows, vol_estimate k L approaches L.  The key is an EXPLICIT, two-sided rational bound:
          L - 1/k  <  vol_estimate k L  <=  L,        so      0 <= L - vol_estimate k L < 1/k.
      The error is a definite rational that shrinks like 1/k; the density k is unbounded; so the estimate
      converges to L constructively — even when L itself is irrational (a role-limit never reached).

    -- The P4 reading --
      The "continuum limit" is NOT a completed object you reach; it is a CONVERGENT PROCESS you approach,
      with a controlled (rational, Element) error at every finite stage.  This is exactly the ToS treatment
      of a real as a process (RealProcess := nat -> Q).  So "make the continuum limit constructive" is
      answered: the limit is well-defined AS A PROCESS, with an explicit rate, on the Element side.

    -- HONEST scope --
      This is the 1D measure-convergence (the tractable core), with a rational target L.  It does NOT prove
      the causal-set closeness / Hauptvermutung (that a 3+1D sprinkling determines a UNIQUE continuum
      geometry) — that remains conjectural and is the subject of Q3.  Here: the volume estimate converges
      with explicit rate; the dimensional uniqueness is out of scope.

    Elements: vol_estimate k L = Qfloor(k*L)/k; the sandwich L - 1/k < est <= L; concrete estimates
    Roles:    discrete estimate = Element (rational); continuum length L = role-limit; 1/k = controlled rate
    Rules:    the continuum limit is a convergent process (nat -> Q) with explicit error 1/k

    ============ E/R/R разбор ============
      Rules (L5): континуумный предел В РАМКЕ P4 = сходящийся ПРОЦЕСС (nat->Q), не завершённый объект;
                  оценка объёма Qfloor(k*L)/k приближает длину L с явной ошибкой < 1/k.
      Roles (L4): дискретные оценки (рациональны) = Element; длина L (предел) = role-limit; 1/k = контроль;
                  плотность k = уровень уточнения.
      Elements  : vol_estimate k L := Qfloor(k*L)/k; sandwich L - 1/k < est <= L; конкретные оценки.
    ДИАГНОСТИКА (P4): ДА (в смысле P4): предел = процесс, не объект.  Машинно: оценка сходится к длине с
    ошибкой < 1/k (явная, рациональная), каждый шаг Element, предел role-limit.  Континуум определён КАК
    ПРОЦЕСС (Cauchy), даже когда L сам role-limit.  ЧЕСТНО: 1D мера-сходимость (ядро); полная Hauptvermutung
    (3+1D единственность геометрии) открыта = Q3.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qround Lqa ZArith Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The density and the discrete volume estimate                           *)
(* ===================================================================== *)

(** Refinement density k: a grid of spacing 1/k. *)
Definition kq (k : nat) : Q := inject_Z (Z.of_nat k).

Lemma kq_pos : forall k, (1 <= k)%nat -> 0 < kq k.
Proof. intros k Hk. unfold kq, Qlt; simpl; lia. Qed.

(** The density grows without bound — so the error 1/k can be made smaller than any rational. *)
Lemma kq_unbounded : forall B : Q, exists K, (1 <= K)%nat /\ B < kq K.
Proof.
  intro B. destruct (Qarchimedean B) as [p Hp].
  exists (Pos.to_nat p). split.
  - generalize (Pos2Nat.is_pos p); lia.
  - unfold kq. rewrite positive_nat_Z. exact Hp.
Qed.

(** The discrete causal-set volume of [0,L) at density k, divided by k: count / density. *)
Definition vol_estimate (k : nat) (L : Q) : Q := inject_Z (Qfloor (kq k * L)) / kq k.

(* ===================================================================== *)
(*  The explicit two-sided error bound (the sandwich)                      *)
(* ===================================================================== *)

(** Upper: the estimate never overshoots the true length. *)
Lemma vol_estimate_upper : forall k L, (1 <= k)%nat -> vol_estimate k L <= L.
Proof.
  intros k L Hk.
  assert (Hpos : 0 < kq k) by (apply kq_pos; exact Hk).
  unfold vol_estimate.
  apply Qle_shift_div_r; [ exact Hpos | ].
  rewrite (Qmult_comm L (kq k)). apply Qfloor_le.
Qed.

(** Lower: the estimate is within 1/k below the true length. *)
Lemma vol_estimate_lower : forall k L, (1 <= k)%nat -> L - 1 / kq k < vol_estimate k L.
Proof.
  intros k L Hk.
  assert (Hpos : 0 < kq k) by (apply kq_pos; exact Hk).
  assert (Hne : ~ kq k == 0) by (apply Qnot_eq_sym; apply Qlt_not_eq; exact Hpos).
  unfold vol_estimate.
  apply Qlt_shift_div_l; [ exact Hpos | ].
  assert (Hfl : kq k * L - 1 < inject_Z (Qfloor (kq k * L))).
  { assert (H := Qlt_floor (kq k * L)). rewrite inject_Z_plus in H.
    change (inject_Z 1) with (1 # 1) in H. lra. }
  assert (Heq : (L - 1 / kq k) * kq k == kq k * L - 1) by (field; exact Hne).
  rewrite Heq. exact Hfl.
Qed.

(** ★ The constructive error bound: 0 <= L - estimate < 1/k.  Element error, explicit rate. *)
Lemma continuum_limit_error : forall k L, (1 <= k)%nat ->
  0 <= L - vol_estimate k L /\ L - vol_estimate k L < 1 / kq k.
Proof.
  intros k L Hk. split.
  - assert (H := vol_estimate_upper k L Hk). lra.
  - assert (H := vol_estimate_lower k L Hk). lra.
Qed.

(* ===================================================================== *)
(*  Concrete: estimating the length 10/3                                   *)
(* ===================================================================== *)

(** At density 1 the estimate is 3 (the floor); the error is 1/3 < 1/1. *)
Lemma ex_low : vol_estimate 1 (10 # 3) == 3.
Proof. vm_compute. reflexivity. Qed.

(** At density 3 the grid captures 10/3 exactly. *)
Lemma ex_exact : vol_estimate 3 (10 # 3) == 10 # 3.
Proof. vm_compute. reflexivity. Qed.

Lemma ex_error : (10 # 3) - vol_estimate 1 (10 # 3) == 1 # 3.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the continuum limit is a constructive process                *)
(* ===================================================================== *)

(** The continuum limit, made constructive (in the P4 sense):
      (upper)     the discrete estimate never overshoots: vol_estimate k L <= L;
      (lower)     it is within 1/k below: L - 1/k < vol_estimate k L;
      (rate)      so the error is a definite rational shrinking like 1/k: L - est < 1/k;
      (unbounded) the density k is unbounded, so the error -> 0.
    The continuum length is the limit of a convergent process with an EXPLICIT rational rate — the
    Element-side, P4 reading of "the continuum limit".  (The 3+1D uniqueness / Hauptvermutung is Q3.) *)
Theorem continuum_limit_constructive :
  (forall k L, (1 <= k)%nat -> vol_estimate k L <= L)
  /\ (forall k L, (1 <= k)%nat -> L - 1 / kq k < vol_estimate k L)
  /\ (forall k L, (1 <= k)%nat -> L - vol_estimate k L < 1 / kq k)
  /\ (forall B, exists K, (1 <= K)%nat /\ B < kq K).
Proof.
  split; [ exact vol_estimate_upper | ].
  split; [ exact vol_estimate_lower | ].
  split.
  - intros k L Hk. apply (proj2 (continuum_limit_error k L Hk)).
  - exact kq_unbounded.
Qed.
