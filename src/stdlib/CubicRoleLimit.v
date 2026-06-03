(** * CubicRoleLimit.v — the finitization boundary is STRATIFIED by algebraic
      degree: ∛2 is a DEGREE-3 role-limit, deeper than the quadratic √2/√3/√5 —
      it is not reachable by ANY quadratic extension (∛2 ∉ ℚ[√2]).  The Delian
      problem (doubling the cube) is exactly "requesting a degree-3 Element".

    Elements: integers p, q; the rational coordinates a, b of ℚ[√2]; the rational 2
              (L1 + P4)
    Roles:    ∛2 = the DEGREE-3 role-limit (the Delian / cube-doubling obstruction);
              √2 = the DEGREE-2 role-limit (reached BY ℚ[√2]); ℚ[√2] = the quadratic
              tier that contains √2 but NOT ∛2 — the boundary is graded
    Rules:    2 is prime ⟹ 2|n³⟹2|n; infinite descent on |p|+|q|; the ℚ[√2] cube
              (a+b√2)³ = (a³+6ab²) + (3a²b+2b³)√2; the minimal polynomial x³−2

    THE DEEP POINT — role-limits come in TIERS by algebraic degree, and the
    finitization boundary is not binary but GRADED.  Everything in the cluster so far
    has been a QUADRATIC role-limit: √2 (T-gate), √3 (60°-point), √5 (icosahedron),
    φ — each reachable by ONE quadratic extension of ℚ.  ∛2 is a strictly DEEPER
    role-limit:
      · ∛2 ∉ ℚ (`cbrt2_irrational`): no rational cubes to 2 — by the same infinite
        descent as √2, but on cubes (2|p³⟹2|p, p=2p'⟹q=2q'⟹descend).  This is the
        Delian problem: the cube cannot be doubled by ruler and compass because ∛2 is
        not constructible — it is a non-terminating process of degree 3.
      · ∛2 ∉ ℚ[√2] (`cbrt2_not_in_Qsqrt2`): even ADJOINING the degree-2 role-limit √2
        does not reach ∛2.  If (a+b√2)³=2 then 3a²b+2b³=0 ⟹ b=0 (so a³=2, impossible)
        or a=b=0 (so 0=2, impossible).  A degree-3 role-limit escapes the degree-2
        tier entirely.
      · Yet √2 ∈ ℚ[√2] (`r2_in_Qsqrt2`): the degree-2 surd IS reached by its own
        quadratic extension.  So the tiers are real and nested: ℚ (degree 1) ⊂ ℚ[√2]
        (degree 2, contains √2) ⊄ ∛2 (degree 3).

    So the finitization boundary is stratified: Element (degree 1) ⊂ quadratic
    role-limits (degree 2: √2/√3/√5 — T-gate/60°/icosahedron) ⊂ cubic role-limits
    (degree 3: ∛2 — the Delian problem) ⊂ …  Each tier is a strictly deeper
    non-termination; the classical impossibility theorems are "you are requesting a
    degree-n Element from degree-<n operations".

    ============ E/R/R разбор ============
      Rules (L5): 2 простое ⟹ 2|n³⟹2|n; бесконечный спуск; куб в ℚ[√2]
                  (a+b√2)³=(a³+6ab²)+(3a²b+2b³)√2; минимальный многочлен x³−2.
      Roles (L4): ∛2 = role-limit СТЕПЕНИ 3 (Делийская задача); √2 = role-limit
                  степени 2 (достижим ℚ[√2]); ℚ[√2] = квадратичный тир (содержит √2,
                  НЕ ∛2) — граница градуирована.
      Elements  : целые p,q; рац. координаты a,b у ℚ[√2]; рациональная 2 (L1+P4).
    ДИАГНОСТИКА (P4): граница финитизации СТРАТИФИЦИРОВАНА по степени — Element (ст.1) ⊂
    квадратичные role-limit (ст.2: √2/√3/√5) ⊂ кубические (ст.3: ∛2). ∛2 не достижим
    никаким квадратичным расширением (∛2∉ℚ[√2]); классические теоремы о невозможности =
    «запрос Element степени n из операций степени <n». ∛2 = незавершающийся процесс степени 3.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Znumtheory.

Open Scope Z_scope.

(* ================================================================= *)
(** ** 2 is prime, and 2 | n³ ⟹ 2 | n                                *)
(* ================================================================= *)

(** If 2 divides n*n*n then 2 divides n (2 is prime). *)
Lemma two_div_cube : forall n : Z, (2 | n * n * n) -> (2 | n).
Proof.
  intros n H.
  apply prime_mult in H; [ | exact prime_2 ].   (* H : (2 | n*n) \/ (2 | n) *)
  destruct H as [H | H].
  - apply prime_mult in H; [ | exact prime_2 ]. destruct H; assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** p³ = 2·q³ ⟹ 2 | p and 2 | q                                   *)
(* ================================================================= *)

Lemma cube_eq_2cube_div2 : forall p q : Z,
  p * p * p = 2 * (q * q * q) -> (2 | p) /\ (2 | q).
Proof.
  intros p q Heq.
  assert (Hp : (2 | p)).
  { apply two_div_cube. exists (q * q * q). lia. }
  destruct Hp as [k Hk].   (* p = k * 2 *)
  split.
  - exists k. exact Hk.
  - apply two_div_cube.
    exists (2 * (k * k * k)).
    (* goal: q*q*q = (2*(k*k*k))*2  i.e.  q³ = 4k³, from p=2k and p³=2q³ *)
    assert (H1 : p * p * p = 8 * (k * k * k)) by (rewrite Hk; ring).
    lia.
Qed.

(* ================================================================= *)
(** ** Descent step: divide both p and q by 2                        *)
(* ================================================================= *)

Lemma descent_step_2 : forall p q : Z,
  p * p * p = 2 * (q * q * q) ->
  exists p' q' : Z,
    p = 2 * p' /\ q = 2 * q' /\ p' * p' * p' = 2 * (q' * q' * q').
Proof.
  intros p q Heq.
  destruct (cube_eq_2cube_div2 p q Heq) as [Hp Hq].
  destruct Hp as [p' Hp'].   (* p = p' * 2 *)
  destruct Hq as [q' Hq'].   (* q = q' * 2 *)
  exists p', q'.
  split. lia.
  split. lia.
  assert (H1 : p * p * p = 8 * (p' * p' * p')) by (rewrite Hp'; ring).
  assert (H2 : q * q * q = 8 * (q' * q' * q')) by (rewrite Hq'; ring).
  lia.
Qed.

(* ================================================================= *)
(** ** Infinite descent: p³ = 2·q³ ⟹ p = 0 and q = 0                 *)
(* ================================================================= *)

Lemma descent_to_zero_2 : forall n : nat, forall p q : Z,
  Z.to_nat (Z.abs p + Z.abs q) = n ->
  p * p * p = 2 * (q * q * q) ->
  p = 0 /\ q = 0.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros p q Hn Heq.
  destruct (Z.eq_dec p 0) as [Hp0 | Hpn0].
  - subst p. split; [ reflexivity | ].
    assert (Hq30 : q * q * q = 0) by lia.
    apply Z.mul_eq_0 in Hq30. destruct Hq30 as [Hqq | Hq].
    + apply Z.mul_eq_0 in Hqq. destruct Hqq; assumption.
    + assumption.
  - destruct (Z.eq_dec q 0) as [Hq0 | Hqn0].
    + subst q. exfalso. apply Hpn0.
      assert (Hp30 : p * p * p = 0) by lia.
      apply Z.mul_eq_0 in Hp30. destruct Hp30 as [Hpp | Hp].
      * apply Z.mul_eq_0 in Hpp. destruct Hpp; assumption.
      * assumption.
    + (* Both nonzero: descend *)
      destruct (descent_step_2 p q Heq) as [p' [q' [Hp' [Hq' Heq']]]].
      assert (Hlt : (Z.to_nat (Z.abs p' + Z.abs q') < n)%nat).
      { subst p q n.
        rewrite !Z.abs_mul. simpl (Z.abs 2).
        assert (Hp'nn : 0 <= Z.abs p') by apply Z.abs_nonneg.
        assert (Hq'nn : 0 <= Z.abs q') by apply Z.abs_nonneg.
        assert (Hpq_pos : Z.abs p' + Z.abs q' > 0).
        { destruct (Z.eq_dec p' 0).
          - subst p'. assert (q' <> 0) by lia.
            assert (0 < Z.abs q') by (apply Z.abs_pos; auto). lia.
          - assert (0 < Z.abs p') by (apply Z.abs_pos; auto). lia. }
        apply Z2Nat.inj_lt; lia. }
      destruct (IH _ Hlt p' q' eq_refl Heq') as [Hp'0 Hq'0].
      subst p' q'. split; lia.
Qed.

(* ================================================================= *)
(** ** ∛2 is irrational over Z, then over Q                          *)
(* ================================================================= *)

Theorem cbrt2_irrational_Z : forall p q : Z,
  q <> 0 -> p * p * p <> 2 * (q * q * q).
Proof.
  intros p q Hq Heq.
  assert (H : p = 0 /\ q = 0).
  { apply (descent_to_zero_2 (Z.to_nat (Z.abs p + Z.abs q)) p q).
    - reflexivity.
    - exact Heq. }
  destruct H as [_ Hq0]. contradiction.
Qed.

Open Scope Q_scope.

(** ∛2 ∉ ℚ: no rational cubes to 2.  The Delian role-limit (degree 3). *)
Theorem cbrt2_irrational : ~ (exists r : Q, r * r * r == 2).
Proof.
  intros [r Hr]. destruct r as [p d].
  unfold Qeq in Hr. simpl in Hr.
  (* Hr : (p*p*p*1 = 2 * Z.pos (d*d*d))%Z *)
  assert (Heq2 : (p * p * p = 2 * Z.pos (d * d * d))%Z) by lia.
  assert (Hddd : (Z.pos (d * d * d) = Z.pos d * Z.pos d * Z.pos d)%Z) by lia.
  rewrite Hddd in Heq2.
  apply (cbrt2_irrational_Z p (Z.pos d)).
  - discriminate.
  - exact Heq2.
Qed.

(* ================================================================= *)
(** ** ∛2 ∉ ℚ[√2]: the degree-3 role-limit escapes the degree-2 tier *)
(* ================================================================= *)

Definition RQ : Type := (Q * Q)%type.        (* a + b√2 *)
Definition rmul (z w : RQ) : RQ :=
  (fst z * fst w + 2 * (snd z * snd w), fst z * snd w + snd z * fst w).
Definition req (z w : RQ) : Prop := fst z == fst w /\ snd z == snd w.
Definition rsq (z : RQ) : RQ := rmul z z.
Definition rcube (z : RQ) : RQ := rmul z (rsq z).

Lemma qsq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hlt | Hge].
  - assert (Hr : q * q == (- q) * (- q)) by ring.
    rewrite Hr. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(** √2 IS reached by ℚ[√2]: (0+1·√2)² = 2 — the degree-2 surd is an element here. *)
Lemma r2_in_Qsqrt2 : req (rsq (0, 1)) (2, 0).
Proof. vm_compute. split; reflexivity. Qed.

(** ★ ∛2 ∉ ℚ[√2]: no element of the quadratic extension cubes to 2.
    (a+b√2)³ = (a³+6ab²) + (3a²b+2b³)√2 = 2 ⟹ b(3a²+2b²)=0 ⟹ b=0 (then a³=2,
    impossible by `cbrt2_irrational`) or a=b=0 (then 0=2).  Degree 3 escapes degree 2. *)
Theorem cbrt2_not_in_Qsqrt2 : ~ (exists x : RQ, req (rcube x) (2, 0)).
Proof.
  intros [[a b] H]. red in H. destruct H as [Hre Him].
  unfold rcube, rsq, rmul in Hre, Him. cbn [fst snd] in Hre, Him.
  (* Hre : a*(a*a+2*(b*b)) + 2*(b*(a*b+b*a)) == 2 ;
     Him : a*(a*b+b*a) + b*(a*a+2*(b*b)) == 0 *)
  assert (Him2 : (b * (3 * (a * a) + 2 * (b * b)) == 0)%Q) by (rewrite <- Him; ring).
  apply Qmult_integral in Him2. destruct Him2 as [Hb | Hs].
  - (* b = 0 ⟹ a³ = 2, impossible *)
    rewrite Hb in Hre.
    assert (Ha3 : (a * a * a == 2)%Q) by (rewrite <- Hre; ring).
    apply cbrt2_irrational. exists a. exact Ha3.
  - (* 3a²+2b² = 0 ⟹ a = 0 ⟹ real part 0 = 2 *)
    assert (Hnn1 : 0 <= a * a) by apply qsq_nonneg.
    assert (Hnn2 : 0 <= b * b) by apply qsq_nonneg.
    assert (Haa : (a * a == 0)%Q) by lra.
    apply Qmult_integral in Haa.
    assert (Ha0 : (a == 0)%Q) by (destruct Haa; assumption).
    assert (Hbad : (2 == 0)%Q) by (rewrite <- Hre; rewrite Ha0; ring).
    lra.
Qed.

(* ================================================================= *)
(** ** Synthesis: the stratified boundary                            *)
(* ================================================================= *)

(** The finitization boundary stratified by algebraic degree, in one statement:
      (a) ∛2 ∉ ℚ — the degree-3 role-limit (Delian);
      (b) √2 ∈ ℚ[√2] — the degree-2 surd IS reached by its quadratic extension;
      (c) ∛2 ∉ ℚ[√2] — degree 3 escapes the degree-2 tier entirely. *)
Theorem delian_tier_synthesis :
  ~ (exists r : Q, r * r * r == 2)
  /\ req (rsq (0, 1)) (2, 0)
  /\ ~ (exists x : RQ, req (rcube x) (2, 0)).
Proof.
  split; [ exact cbrt2_irrational | ].
  split; [ exact r2_in_Qsqrt2 | exact cbrt2_not_in_Qsqrt2 ].
Qed.
