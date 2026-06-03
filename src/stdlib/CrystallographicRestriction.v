(** * CrystallographicRestriction.v — ④ SO(3,ℚ): a finite-order rational rotation
      has order ∈ {1,2,3,4,6}; order 5 (the pentagon/icosahedron) is excluded by √5.
      The finitization boundary, one dimension up from ①.

    Elements: the rational trace tr ∈ {−1,0,1,2,3} of a terminating-order rotation;
              the integer trace-sequence c s t k (Niven); orders {1,2,3,4,6} as
              termini (L1 + P4)
    Roles:    a 3D rotation as a PROCESS — its trace-orbit τ_k = tr(Rᵏ)−1 = 2cos(kθ);
              TERMINATING (order 1/2/3/4/6) vs NON-TERMINATING (irrational trace,
              order 5/7/…); the axis ABSORBS the irrational sine (the new 3D role)
    Rules:    tr(R) = 1 + 2cosθ (rational ⟹ only the trace is constrained, NOT sinθ);
              the Chebyshev trace recurrence τ_{k+1} = (2cosθ)·τ_k − τ_{k−1}; the
              Niven obstruction t∤c s t k; and √5 (x²+x−1 has no rational root)

    THE 3D SHIFT — only the TRACE is constrained, not sinθ.  In ① a rational point
    needed BOTH cosθ and sinθ rational.  In SO(3) the rotation MATRIX can be rational
    while sinθ is irrational: the cyclic axis-permutation [[0,0,1],[1,0,0],[0,1,0]] ∈
    SO(3,ℚ) has order 3 (θ=120°, sin120°=√3/2 irrational) yet is rational — the AXIS
    absorbs the irrational sine.  A 3D rotation has eigenvalues 1, e^{±iθ}, so
    tr(R) = 1 + 2cosθ; rationality of R constrains ONLY 2cosθ.  Hence Niven applies to
    cosθ DIRECTLY (through the trace), giving 2cosθ ∈ {−2,−1,0,1,2}, tr ∈ {−1,0,1,2,3},
    order ∈ {1,2,3,4,6}.

    THE √5 OBSTRUCTION — order 5 is a role-limit.  The trace-orbit τ_k = tr(Rᵏ)−1 =
    2cos(kθ) obeys the SAME Chebyshev recurrence as ① (now on the trace), and a direct
    computation gives τ_5 = x⁵−5x³+5x (x := 2cosθ).  Order 5 means τ_5 = 2, and
    τ_5 − 2 = (x−2)(x²+x−1)²; a nontrivial (x≠2) solution forces x²+x−1 = 0, i.e.
    x = 2cos72° = (−1±√5)/2 — IRRATIONAL (`no_rational_sqrt5`).  So NO rational rotation
    has order 5.  As √2 killed the T-gate and √3 the 60°-point in ①, √5 kills the
    pentagon/icosahedron here — the crystallographic restriction is the finitization
    boundary in SO(3).  (Why icosahedral quasicrystals are "non-crystallographic".)

    ============ E/R/R разбор ============
      Rules (L5): tr=1+2cosθ; Чебышёв τ_{k+1}=x·τ_k−τ_{k−1}; Niven t∤c_k; √5 (x²+x−1).
      Roles (L4): вращение = ПРОЦЕСС (след-орбита τ_k); ЗАВЕРШАЮЩИЙСЯ (порядок 1/2/3/4/6)
                  или НЕЗАВЕРШАЮЩИЙСЯ (иррац. след — порядок 5/7/…); ось впитывает sinθ.
      Elements  : рациональный след tr∈{−1,0,1,2,3}; целочисленный c s t k; порядки {1,2,3,4,6}.
    ДИАГНОСТИКА (P4): ④ = граница финитизации в SO(3). Завершающиеся = {1,2,3,4,6}; порядок 5
    (икосаэдр A₅, √5) = role-limit. «Реализуема ли симметрия порядка 5 над ℚ» — не-вопрос:
    √5 ЕСТЬ незавершающийся процесс. В SO(3) ограничен ТОЛЬКО след, не sinθ (ось впитывает).

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.NivenGeneral.
From ToS Require Import analysis.Sqrt5Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The trace sequence τ_k = tr(Rᵏ) − 1 = 2cos(kθ)  (x := 2cosθ)          *)
(* ===================================================================== *)

Fixpoint tau (x : Q) (k : nat) : Q :=
  match k with
  | O => 2
  | S k' =>
    match k' with
    | O => x
    | S j => x * tau x k' - tau x j
    end
  end.

Lemma tau_rec : forall x k, tau x (S (S k)) = x * tau x (S k) - tau x k.
Proof. reflexivity. Qed.

(** τ_5 = x⁵ − 5x³ + 5x  (the 5th Chebyshev trace). *)
Lemma tau5_closed : forall x : Q,
  tau x 5 == x*x*x*x*x - 5*(x*x*x) + 5*x.
Proof.
  intro x.
  change (tau x 5) with (x * tau x 4 - tau x 3).
  change (tau x 4) with (x * tau x 3 - tau x 2).
  change (tau x 3) with (x * tau x 2 - tau x 1).
  change (tau x 2) with (x * tau x 1 - tau x 0).
  change (tau x 1) with x.
  change (tau x 0) with (2:Q).
  ring.
Qed.

(* ===================================================================== *)
(*  ★ Order 5 forces the golden polynomial — hence is impossible over ℚ  *)
(* ===================================================================== *)

(** τ_5 = 2 with x ≠ 2 forces x² + x − 1 = 0: since
    τ_5 − 2 = (x−2)(x²+x−1)², a nontrivial order-5 trace satisfies the golden
    polynomial (x = 2cos72° = (−1±√5)/2). *)
Lemma order5_forces_golden : forall x : Q,
  tau x 5 == 2 -> ~ (x == 2) -> x*x + x - 1 == 0.
Proof.
  intros x H5 Hx.
  rewrite tau5_closed in H5.
  assert (Hfact : (x - 2) * ((x*x + x - 1) * (x*x + x - 1)) == 0).
  { assert (Hr : (x - 2) * ((x*x + x - 1) * (x*x + x - 1))
               == (x*x*x*x*x - 5*(x*x*x) + 5*x) - 2) by ring.
    rewrite Hr. lra. }
  apply Qmult_integral in Hfact. destruct Hfact as [H2 | Hsq].
  - exfalso. apply Hx. lra.
  - apply Qmult_integral in Hsq. destruct Hsq; assumption.
Qed.

(** The golden polynomial x²+x−1 has NO rational root: a root x gives
    (2x+1)² = 5, contradicting √5 ∉ ℚ. *)
Lemma no_rational_golden : ~ (exists x : Q, x*x + x - 1 == 0).
Proof.
  intros [x Hx].
  apply (no_rational_sqrt5 (2*x + 1)).
  assert (Hr : (2*x + 1) * (2*x + 1) == 4 * (x*x + x) + 1) by ring.
  rewrite Hr.
  assert (Hxx : x*x + x == 1) by lra.
  rewrite Hxx. lra.
Qed.

(** ★ No rational rotation has order 5: a nontrivial order-5 trace would be a
    rational root of the golden polynomial, which does not exist (√5). *)
Theorem no_rational_order5 : ~ (exists x : Q, tau x 5 == 2 /\ ~ (x == 2)).
Proof.
  intros [x [H5 Hx]].
  apply no_rational_golden. exists x. exact (order5_forces_golden x H5 Hx).
Qed.

(* ===================================================================== *)
(*  The realizable orders {1,2,3,4,6} DO occur (Niven traces)            *)
(* ===================================================================== *)

(** Orders 1,2,3,4,6 are realised by the Niven traces x = 2cosθ ∈ {2,−2,−1,0,1}
    (tr ∈ {3,−1,0,1,2}): the trace-orbit closes (τ_n = 2) at the right step. *)
Theorem realizable_orders :
  tau 2 1 == 2 /\        (* order 1: θ=0,   tr=3  *)
  tau (-2) 2 == 2 /\     (* order 2: θ=180°, tr=−1 *)
  tau (-1) 3 == 2 /\     (* order 3: θ=120°, tr=0  *)
  tau 0 4 == 2 /\        (* order 4: θ=90°,  tr=1  *)
  tau 1 6 == 2.          (* order 6: θ=60°,  tr=2  *)
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  inject_Z ring-homomorphism facts (local)                             *)
(* ===================================================================== *)

Lemma injZ_mult : forall a b : Z, inject_Z (a * b) == inject_Z a * inject_Z b.
Proof. intros a b. unfold inject_Z, Qmult, Qeq. simpl. ring. Qed.
Lemma injZ_sub : forall a b : Z, inject_Z (a - b) == inject_Z a - inject_Z b.
Proof. intros a b. unfold inject_Z, Qminus, Qplus, Qopp, Qeq. simpl. ring. Qed.
Lemma injZ_1 : inject_Z 1 == 1.
Proof. reflexivity. Qed.
Lemma injZ_2 : inject_Z 2 == 2.
Proof. reflexivity. Qed.
Lemma injZ_inj : forall a b : Z, inject_Z a == inject_Z b -> a = b.
Proof. intros a b H. unfold inject_Z, Qeq in H. simpl in H. lia. Qed.

(* ===================================================================== *)
(*  The Niven bridge for the trace orbit: tᵏ·τ_k = c s t k               *)
(* ===================================================================== *)

Lemma tau_bridge : forall (x : Q) (s t : Z),
  inject_Z s == x * inject_Z t ->
  forall k, inject_Z (tpow t k) * tau x k == inject_Z (c s t k).
Proof.
  intros x s t Hst.
  assert (Hpair : forall k,
    (inject_Z (tpow t k) * tau x k == inject_Z (c s t k)) /\
    (inject_Z (tpow t (S k)) * tau x (S k) == inject_Z (c s t (S k)))).
  { induction k as [|k [IHk IHSk]].
    - split.
      + vm_compute. reflexivity.
      + change (tpow t 1) with (t * 1)%Z.
        change (tau x 1) with x.
        change (c s t 1) with s.
        rewrite (injZ_mult t 1), injZ_1, Hst. ring.
    - split.
      + exact IHSk.
      + rewrite (tau_rec x k).
        rewrite (c_rec s t k).
        rewrite injZ_sub.
        rewrite (injZ_mult s (c s t (S k))).
        rewrite (injZ_mult (t * t) (c s t k)).
        rewrite <- IHSk, <- IHk.
        rewrite Hst.
        change (tpow t (S (S k))) with (t * (t * tpow t k))%Z.
        change (tpow t (S k)) with (t * tpow t k)%Z.
        rewrite !injZ_mult.
        ring. }
  intro k. exact (proj1 (Hpair k)).
Qed.

(* ===================================================================== *)
(*  ★ THE CRYSTALLOGRAPHIC RESTRICTION over ℚ                            *)
(* ===================================================================== *)

(** A finite-order rational rotation of SO(3) has 2cosθ ∈ {−2,−1,0,1,2}, hence
    trace ∈ {−1,0,1,2,3}, hence order ∈ {1,2,3,4,6} — order 5 and all higher
    primes are excluded.  Same mechanism as ①'s capstone, now on the trace:
    finite order ⟹ τ_n = 2 ⟹ t | c s t n ⟹ (niven_general, t≥2 impossible) t=1
    ⟹ 2cosθ ∈ ℤ; with |2cosθ| ≤ 2 the value is one of the five Niven traces. *)
Theorem crystallographic_restriction : forall (x : Q) (s t : Z),
  inject_Z s == x * inject_Z t ->
  (Z.gcd s t = 1)%Z -> (0 < t)%Z ->
  -2 <= x -> x <= 2 ->
  (exists n, (1 <= n)%nat /\ tau x n == 2) ->
  x == -2 \/ x == -1 \/ x == 0 \/ x == 1 \/ x == 2.
Proof.
  intros x s t Hst Hgcd Hpos Hlo Hhi [n [Hn Htau]].
  pose proof (tau_bridge x s t Hst n) as Hbr.
  rewrite Htau in Hbr.
  assert (Hceq : (c s t n = 2 * tpow t n)%Z).
  { apply injZ_inj. rewrite injZ_mult, injZ_2, <- Hbr. ring. }
  assert (Htdiv : (t | c s t n)%Z).
  { rewrite Hceq. apply Z.divide_mul_r. apply tpow_div. exact Hn. }
  assert (Ht1 : t = 1%Z).
  { destruct (Z.le_gt_cases 2 t) as [Ht2 | Ht2]; [ | lia ].
    exfalso. destruct n as [|m]; [ lia | ].
    exact (niven_general s t Hgcd Ht2 m Htdiv). }
  subst t.
  rewrite injZ_1 in Hst.
  assert (Hx : x == inject_Z s) by (rewrite Hst; ring).
  rewrite Hx in Hlo. rewrite Hx in Hhi.
  assert (Hi2n : inject_Z (-2) == -2) by (vm_compute; reflexivity).
  assert (Hi2p : inject_Z 2 == 2) by (vm_compute; reflexivity).
  assert (Hs_lo : (-2 <= s)%Z) by (rewrite Zle_Qle, Hi2n; exact Hlo).
  assert (Hs_hi : (s <= 2)%Z) by (rewrite Zle_Qle, Hi2p; exact Hhi).
  assert (Hs5 : (s = -2 \/ s = -1 \/ s = 0 \/ s = 1 \/ s = 2)%Z) by lia.
  destruct Hs5 as [E | [E | [E | [E | E]]]]; subst s.
  - left.                     rewrite Hx; vm_compute; reflexivity.
  - right; left.              rewrite Hx; vm_compute; reflexivity.
  - right; right; left.       rewrite Hx; vm_compute; reflexivity.
  - right; right; right; left. rewrite Hx; vm_compute; reflexivity.
  - right; right; right; right. rewrite Hx; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The crystallographic restriction over ℚ in one statement: the five Niven
    traces realise orders {1,2,3,4,6}, every finite-order rational rotation is
    one of them, and order 5 is impossible (√5) — all over ℚ, 0 axioms. *)
Theorem crystallographic_synthesis :
  (tau 2 1 == 2 /\ tau (-2) 2 == 2 /\ tau (-1) 3 == 2 /\ tau 0 4 == 2 /\ tau 1 6 == 2)
  /\ ~ (exists x : Q, tau x 5 == 2 /\ ~ (x == 2))
  /\ (forall (x : Q) (s t : Z),
        inject_Z s == x * inject_Z t -> (Z.gcd s t = 1)%Z -> (0 < t)%Z ->
        -2 <= x -> x <= 2 -> (exists n, (1 <= n)%nat /\ tau x n == 2) ->
        x == -2 \/ x == -1 \/ x == 0 \/ x == 1 \/ x == 2).
Proof.
  split. exact realizable_orders.
  split. exact no_rational_order5.
  exact crystallographic_restriction.
Qed.
