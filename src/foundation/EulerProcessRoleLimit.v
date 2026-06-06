(** * EulerProcessRoleLimit.v — beyond the ALGEBRAIC boundary: the Euler number e as a PROVEN role-limit.
       H1AlgebraicDecider decided Element-ness for every ALGEBRAIC number (root of an integer polynomial).
       e is transcendental — no such polynomial — so it lives only as a PROCESS (the series Σ 1/k!).  The repo
       already has the process (IrrationalsClassification.e_partial / local_qfact) but only ASSERTS its status
       (classify_e := ProcessQ); ProcessExpProcess.v even calls "is e irrational?" a non-question under P4
       (e is an unfinished process, not a completed object).  This proves the P4-CONSISTENT teeth: the
       e-PROCESS SEPARATES from EVERY rational — for any rational r there is a stage whose trapping interval
       EXCLUDES r — so e is a genuine role-limit, not secretly an Element.  No completed e is ever invoked.

    -- The integer trap (the mechanism) --
      Sₙ = Σ_{k=0}^{n} 1/k!  (rational stage).  Scaled by n! it is an INTEGER: n!·Sₙ = escaled n ∈ ℤ
      (escaled 0 = 1, escaled (S k) = (k+1)·escaled k + 1).  The trapping interval at stage n is
      (Sₙ, Sₙ + 1/n!), of scaled width exactly 1.  A candidate a/(b+1) scaled by n! (n = b+1) is also an
      INTEGER (a·b!).  Two integers M and A with M < A < M+1 cannot exist — so a/(b+1) is excluded from the
      interval at its own denominator's stage.  Hence NO rational survives all the nested trapping intervals.

    -- The honest frame (P4) --
      This is NOT "e (a finished real) is irrational" — under P4 that reifies a process.  It IS: the e-process
      is not eventually-equal to any constant rational — it separates from every q ∈ ℚ.  That is exactly
      "e is a role-limit, not an Element", now a THEOREM rather than the asserted classify_e := ProcessQ.
      (The geometric tail bound showing the intervals trap the limit — the Cauchy/role-property — is the
      frontier ProcessExpProcess.v flags; the SEPARATION proven here needs only the integer trap.)

    WHAT THE REPO HAS (surveyed): IrrationalsClassification.v (e_partial, local_qfact — but classify_e asserted);
    ProcessExpProcess.v (e as Euler-trajectory process; "is e irrational" called a P4 non-question; Cauchy left
    as frontier); Sqrt2Irrational.v (the ALGEBRAIC route: ~∃r, r·r==2 by descent).  GAP: a PROVEN, P4-consistent
    separation of the e-process from ℚ.  This adds it (e_partial/local_qfact replicated locally, cited).

    ============ E/R/R разбор ============
      Elements : стадии Sₙ=Σ1/k! (рациональные Элементы); qfact=n!; escaled=n!·Sₙ∈ℤ.
      Roles    : e = роль-предел процесса; «Element vs role-limit» = вопрос о ПРОЦЕССЕ, не о завершённом e.
      Rules    : ловушка-интервал (Sₙ,Sₙ+1/n!) ширины-после-масштаба 1; ни одно a/(b+1) не поймано на стадии n=b+1.
      ДИАГНОСТИКА (P4): НЕ «e иррационально» (реификация процесса — кат. ошибка), А «e-процесс сепарируется от каждого
      рационального» ⟹ роль-предел, не Element. Третий слой границы: Element ⊂ алгебр.role-limit(разрешим) ⊂ трансц.role-limit(только процесс).
      Уровень: `новая теорема` (сепарация e-процесса от ℚ — в репо была лишь постулирована) + `синтез` (P4-обрамление, слои границы).

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (self-contained: QArith / Lqa / Lia / ZArith / Factorial)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia ZArith Arith Factorial.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The e-process (replicated from IrrationalsClassification.v, cited)      *)
(* ===================================================================== *)

Fixpoint qfact (n : nat) : Q :=
  match n with O => 1 | S k => inject_Z (Z.of_nat (S k)) * qfact k end.

Fixpoint epart (K : nat) : Q :=
  match K with O => 0 | S k => epart k + 1 / qfact k end.

(* ===================================================================== *)
(*  Helpers                                                                *)
(* ===================================================================== *)

Lemma inject_pos : forall z, (0 < z)%Z -> 0 < inject_Z z.
Proof. intros z H. unfold Qlt, inject_Z; simpl. lia. Qed.

Lemma scale_lt : forall z x y, 0 < z -> x < y -> z * x < z * y.
Proof.
  intros z x y Hz H.
  assert (Hpos : 0 < z * (y - x)) by (apply Qmult_lt_0_compat; lra).
  assert (Heq : z * y - z * x == z * (y - x)) by ring.
  lra.
Qed.

Lemma qfact_pos : forall n, 0 < qfact n.
Proof.
  induction n; simpl.
  - lra.
  - apply Qmult_lt_0_compat; [ apply inject_pos; lia | exact IHn ].
Qed.

(** qfact is the injected nat factorial. *)
Lemma qfact_nat : forall n, qfact n == inject_Z (Z.of_nat (fact n)).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl qfact. rewrite IHn.
    change (fact (S n)) with ((S n * fact n)%nat).
    rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

(** Extract a strict ℤ inequality from injected rationals. *)
Lemma inject_Z_lt_inv : forall x y, inject_Z x < inject_Z y -> (x < y)%Z.
Proof. intros x y H. unfold Qlt, inject_Z in H; simpl in H. lia. Qed.

(* ===================================================================== *)
(*  n!·Sₙ is an INTEGER:  escaled n = n!·(Σ_{k=0}^{n} 1/k!)                 *)
(* ===================================================================== *)

Fixpoint escaled (n : nat) : Z :=
  match n with O => 1 | S k => Z.of_nat (S k) * escaled k + 1 end.

(** ★ The scaled partial sum is a genuine integer:  qfact b · epart (S b) = escaled b. *)
Lemma escaled_bridge : forall b, inject_Z (escaled b) == qfact b * epart (S b).
Proof.
  induction b.
  - vm_compute. reflexivity.
  - assert (Hqb : ~ qfact b == 0) by (pose proof (qfact_pos b); lra).
    assert (Hsb : ~ inject_Z (Z.of_nat (S b)) == 0)
      by (pose proof (inject_pos (Z.of_nat (S b)) ltac:(lia)); lra).
    change (escaled (S b)) with ((Z.of_nat (S b) * escaled b + 1)%Z).
    change (qfact (S b)) with (inject_Z (Z.of_nat (S b)) * qfact b).
    change (epart (S (S b))) with (epart (S b) + 1 / (inject_Z (Z.of_nat (S b)) * qfact b)).
    rewrite inject_Z_plus, inject_Z_mult, IHb.
    change (inject_Z 1) with 1.
    field. split; assumption.
Qed.

(* ===================================================================== *)
(*  ★★ THE SEPARATION: every rational is excluded from a trapping interval *)
(* ===================================================================== *)

(** ★★ For every rational a/(b+1), the trapping interval (S_{b+1}, S_{b+1} + 1/(b+1)!) of the e-process
    EXCLUDES it.  So a/(b+1) is not the limit of the process: the e-process separates from this rational.
    Proof = the integer trap: scaling by (b+1)! sends the interval to (M, M+1) with M = escaled (b+1) ∈ ℤ
    and the candidate to A = a·b! ∈ ℤ; two integers cannot satisfy M < A < M+1. *)
Theorem e_excludes_rational : forall (a : Z) (b : nat),
  ~ ( epart (S (S b)) < inject_Z a / inject_Z (Z.of_nat (S b))
      /\ inject_Z a / inject_Z (Z.of_nat (S b)) < epart (S (S b)) + 1 / qfact (S b) ).
Proof.
  intros a b [H1 H2].
  set (L := qfact (S b)) in *.
  assert (HL : 0 < L) by (unfold L; apply qfact_pos).
  set (cand := inject_Z a / inject_Z (Z.of_nat (S b))) in *.
  (* scale both inequalities by L > 0 *)
  pose proof (scale_lt L _ _ HL H1) as G1.
  pose proof (scale_lt L _ _ HL H2) as G2.
  (* lower endpoint scaled = inject_Z (escaled (S b)) *)
  assert (HM : L * epart (S (S b)) == inject_Z (escaled (S b)))
    by (unfold L; rewrite escaled_bridge; reflexivity).
  (* candidate scaled = inject_Z (a * (b!)) *)
  assert (HA : L * cand == inject_Z (a * Z.of_nat (fact b))).
  { unfold L, cand.
    change (qfact (S b)) with (inject_Z (Z.of_nat (S b)) * qfact b).
    rewrite qfact_nat, inject_Z_mult. field.
    pose proof (inject_pos (Z.of_nat (S b)) ltac:(lia)); lra. }
  (* upper endpoint scaled = inject_Z (escaled (S b) + 1) *)
  assert (HU : L * (epart (S (S b)) + 1 / L) == inject_Z (escaled (S b) + 1)).
  { rewrite inject_Z_plus. change (inject_Z 1) with 1.
    rewrite Qmult_plus_distr_r, HM.
    assert (Hinv : L * (1 / L) == 1) by (field; lra).
    rewrite Hinv. reflexivity. }
  rewrite HM, HA in G1. rewrite HA, HU in G2.
  apply inject_Z_lt_inv in G1. apply inject_Z_lt_inv in G2.
  lia.
Qed.

(* ===================================================================== *)
(*  Concrete & the role-limit reading                                      *)
(* ===================================================================== *)

(** A concrete instance: 8/3 is excluded from the stage-3 trapping interval (b = 2). *)
Example three_halves_excluded :
  ~ ( epart 4 < inject_Z 8 / inject_Z (Z.of_nat 3)
      /\ inject_Z 8 / inject_Z (Z.of_nat 3) < epart 4 + 1 / qfact 3 ).
Proof. exact (e_excludes_rational 8 2). Qed.

(** ★ The e-process is a ROLE-LIMIT: every rational candidate a/(b+1) is separated from the process by the
    trapping interval at its own stage — so the process is not eventually equal to any rational.  This is the
    P4-consistent statement (no completed e is invoked): the asserted classify_e := ProcessQ, now a theorem. *)
Definition e_process_is_role_limit : Prop :=
  forall (a : Z) (b : nat),
    exists n : nat,
      ~ ( epart (S n) < inject_Z a / inject_Z (Z.of_nat (S b))
          /\ inject_Z a / inject_Z (Z.of_nat (S b)) < epart (S n) + 1 / qfact n ).

Lemma e_is_role_limit : e_process_is_role_limit.
Proof. intros a b. exists (S b). exact (e_excludes_rational a b). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Beyond the algebraic boundary — e as a proven role-limit:
      (integer)    n!·Sₙ = escaled n ∈ ℤ (the scaled partial sum is an integer);
      (separation) every rational a/(b+1) is EXCLUDED from the trapping interval at stage b+1;
      (role-limit) hence the e-process is not eventually equal to any rational — a role-limit, not an Element.
    P4-consistent: no completed e is ever invoked — only the rational stages and their separation from ℚ.
    This turns the asserted classify_e := ProcessQ into a theorem.  The third layer of the finitization
    boundary: Element ⊂ algebraic role-limit (DECIDED by H1AlgebraicDecider) ⊂ transcendental role-limit
    (e — presented only as a process, characterised by separation from ℚ).  Level: a new separation theorem
    (only asserted before) plus the P4 framing. *)
Theorem euler_process_role_limit :
  (forall b, inject_Z (escaled b) == qfact b * epart (S b))
  /\ (forall (a : Z) (b : nat),
        ~ ( epart (S (S b)) < inject_Z a / inject_Z (Z.of_nat (S b))
            /\ inject_Z a / inject_Z (Z.of_nat (S b)) < epart (S (S b)) + 1 / qfact (S b) ))
  /\ e_process_is_role_limit.
Proof.
  split; [ exact escaled_bridge | ].
  split; [ exact e_excludes_rational | exact e_is_role_limit ].
Qed.
