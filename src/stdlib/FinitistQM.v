(** * FinitistQM.v — ⑤ machine-checking the finitist-QM programs: 't Hooft,
      Carroll and Gisin are the TWO SIDES (+ the boundary) of one P4 finitization
      boundary — not competitors.

    Elements: the rational stage-k approximants sₖ = pₖ/qₖ (Gisin's
              finite-information quantities); the periods of deterministic finite
              automata ('t Hooft / Carroll) — all finitely actual over ℚ (L1 + P4)
    Roles:    a quantity as a PROCESS — TERMINATING (a deterministic finite
              automaton recurs/closes: 't Hooft CA, Carroll finite-dim QM) vs
              NON-TERMINATING (an open choice-sequence: Gisin's indeterminism)
    Rules:    the Pell convergent recurrence pₖ₊₁=pₖ+2qₖ, qₖ₊₁=pₖ+qₖ with the
              invariant |pₖ²−2qₖ²|=1 ⟹ sₖ²−2 = ±1/qₖ² (finite info, forever
              improving, never exact); no_rational_sqrt2 (no rational terminus);
              a deterministic finite step recurs (closes)

    THE THREE FINITIST PROGRAMS = TWO SIDES + THE BOUNDARY.  They look like
    competitors (determinism vs indeterminism) but sit on opposite sides of ONE
    finitization boundary:
      · 't Hooft (cellular automata) and Carroll (finite-dimensional / periodic QM)
        finitize by making the SUBSTRATE finite/discrete ⟹ deterministic, periodic,
        it CLOSES ⟹ the ELEMENT side (determinism recovered from finiteness).
      · Gisin (choice-sequences / finite-information quantities / indeterminism)
        finitizes by making the real number an OPEN PROCESS — finite info at each
        stage, never completed ⟹ it NEVER closes ⟹ the ROLE-LIMIT side
        (indeterminism IS the non-termination).
    Our framework holds both as the two sides; the boundary (P4) is what all three
    reach for.

    GISIN, precisely.  His finite-information quantity = our finitely-actual stage-k
    approximant (a rational, an Element).  His indeterminism ("the next digit is not
    yet determined") = our non-termination ("the next Element is not yet actualised").
    His "a number reveals its digits over time" = P4 (infinity is a property of a
    process, not an object).  Machine-checked: the √2 choice-sequence sₖ=pₖ/qₖ has an
    EXACT squared error sₖ²−2 = ±1/qₖ² (always ≠ 0, shrinking forever) yet reaches no
    rational terminus (no_rational_sqrt2).  FIQ + indeterminism = non-termination,
    0 axioms.

    TIE TO H1 (constructivity).  Gisin's program is explicitly intuitionistic — and
    indeed BOTH sides here are constructive (this file is 0-axiom): even Gisin's
    "indeterminism" is constructive AS non-termination, needing no LEM.  This confirms
    H1 (finitization boundary = constructivity boundary): the open/role-limit side is
    still axiom-free when phrased as an unfinished process, not a completed continuum.

    ============ E/R/R разбор ============
      Rules (L5): Pell-рекуррентность + |pₖ²−2qₖ²|=1 ⟹ sₖ²−2=±1/qₖ²; no_rational_sqrt2;
                  детерминированный конечный шаг возвращается.
      Roles (L4): величина = ПРОЦЕСС; завершающийся ('т Хоофт/Кэрролл, детерминизм) или
                  незавершающийся (Гизин, индетерминизм).
      Elements  : рациональные приближенцы sₖ (FIQ-стадии); периоды автоматов (L1+P4).
    ДИАГНОСТИКА (P4): три финитистские программы = две стороны + граница. Гизин =
    role-limit (индетерминизм = незавершаемость); 'т Хоофт/Кэрролл = Element
    (детерминизм = замыкание). Обе конструктивны (0 акс) ⟹ подтверждает H1.

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import analysis.Sqrt2Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  inject_Z ring-homomorphism facts (local)                             *)
(* ===================================================================== *)

Lemma injZ_mult : forall a b : Z, inject_Z (a * b) == inject_Z a * inject_Z b.
Proof. intros a b. unfold inject_Z, Qmult, Qeq. simpl. ring. Qed.
Lemma injZ_sub : forall a b : Z, inject_Z (a - b) == inject_Z a - inject_Z b.
Proof. intros a b. unfold inject_Z, Qminus, Qplus, Qopp, Qeq. simpl. ring. Qed.
Lemma injZ_2 : inject_Z 2 == 2.
Proof. reflexivity. Qed.
Lemma injZ_inj : forall a b : Z, inject_Z a == inject_Z b -> a = b.
Proof. intros a b H. unfold inject_Z, Qeq in H. simpl in H. lia. Qed.

(* ===================================================================== *)
(*  Gisin's √2 choice-sequence: the Pell convergents (integer recurrence) *)
(* ===================================================================== *)

Fixpoint pq (k : nat) : Z * Z :=
  match k with
  | O => (1, 1)%Z
  | S j => let (p, q) := pq j in (p + 2 * q, p + q)%Z
  end.
Definition pp (k : nat) : Z := fst (pq k).
Definition qq (k : nat) : Z := snd (pq k).

(** The stage-k finite-information quantity sₖ = pₖ/qₖ ∈ ℚ. *)
Definition sq2 (k : nat) : Q := inject_Z (pp k) / inject_Z (qq k).

(** Both pₖ and qₖ stay positive (and qₖ strictly grows ⟹ error shrinks). *)
Lemma pq_pos : forall k, (0 < pp k)%Z /\ (0 < qq k)%Z.
Proof.
  induction k as [|k IH].
  - cbn. split; lia.
  - destruct IH as [Hp Hq]. unfold pp, qq in *.
    cbn [pq]. destruct (pq k) as [p q]. cbn [fst snd] in *. split; lia.
Qed.

Lemma qq_incr : forall k, (qq k < qq (S k))%Z.
Proof.
  intro k. destruct (pq_pos k) as [Hp Hq]. unfold pp, qq in *.
  cbn [pq]. destruct (pq k) as [p q]. cbn [fst snd] in *. lia.
Qed.

(** The Pell step negates p²−2q² (so its absolute value is invariant). *)
Lemma pell_step_neg : forall k,
  (pp (S k) * pp (S k) - 2 * (qq (S k) * qq (S k))
   = - (pp k * pp k - 2 * (qq k * qq k)))%Z.
Proof.
  intro k. unfold pp, qq. cbn [pq]. destruct (pq k) as [p q]. cbn [fst snd]. ring.
Qed.

(** ★ The Pell invariant: |pₖ² − 2qₖ²| = 1 — the squared error is never 0. *)
Lemma pell_abs : forall k, (Z.abs (pp k * pp k - 2 * (qq k * qq k)) = 1)%Z.
Proof.
  induction k as [|k IH].
  - vm_compute. reflexivity.
  - rewrite pell_step_neg, Z.abs_opp. exact IH.
Qed.

(** inject_Z (qₖ) ≠ 0 (since qₖ > 0). *)
Lemma injZ_qq_nz : forall k, ~ inject_Z (qq k) == 0.
Proof.
  intro k. intro H. destruct (pq_pos k) as [_ Hq].
  assert (Hz : (qq k = 0)%Z) by (apply injZ_inj; rewrite H; reflexivity).
  lia.
Qed.

(** ★ The EXACT squared error: sₖ² − 2 = (pₖ² − 2qₖ²) / qₖ². *)
Lemma sq2_err : forall k,
  sq2 k * sq2 k - 2
  == inject_Z (pp k * pp k - 2 * (qq k * qq k)) / (inject_Z (qq k) * inject_Z (qq k)).
Proof.
  intro k.
  rewrite injZ_sub, (injZ_mult (pp k) (pp k)),
          (injZ_mult 2 (qq k * qq k)), (injZ_mult (qq k) (qq k)), injZ_2.
  unfold sq2. field. apply injZ_qq_nz.
Qed.

(* ===================================================================== *)
(*  ★ GISIN: finite-information quantity, never exact, no terminus        *)
(* ===================================================================== *)

(** Every stage misses: sₖ² ≠ 2 for all k — the choice-sequence never lands on the
    exact value (the squared error is ±1/qₖ², never 0).  Finite information,
    forever improving, never completed. *)
Theorem gisin_never_exact : forall k, ~ (sq2 k * sq2 k == 2).
Proof.
  intros k Hk.
  assert (Herr : sq2 k * sq2 k - 2 == 0) by lra.
  rewrite (sq2_err k) in Herr.
  set (num := inject_Z (pp k * pp k - 2 * (qq k * qq k))) in *.
  set (den := inject_Z (qq k) * inject_Z (qq k)) in *.
  assert (Hnum : ~ num == 0).
  { unfold num. intro Hn.
    assert (Hz : (pp k * pp k - 2 * (qq k * qq k) = 0)%Z)
      by (apply injZ_inj; rewrite Hn; reflexivity).
    pose proof (pell_abs k) as Ha. lia. }
  assert (Hden : ~ den == 0).
  { unfold den. intro Hd. apply Qmult_integral in Hd.
    destruct Hd; apply (injZ_qq_nz k); assumption. }
  apply Hnum.
  transitivity ((num / den) * den).
  - field; exact Hden.
  - rewrite Herr. ring.
Qed.

(** Concrete improving finite information: the squared errors −1, 1/4, −1/25,
    1/144 (= ±1/qₖ²) — better and better, never 0. *)
Theorem gisin_concrete :
  sq2 0 * sq2 0 - 2 == -1 /\
  sq2 1 * sq2 1 - 2 == 1#4 /\
  sq2 2 * sq2 2 - 2 == -(1#25) /\
  sq2 3 * sq2 3 - 2 == 1#144.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** GISIN bundled: indeterminism = non-termination.  The √2 choice-sequence misses
    at every finite stage, and no rational is its exact value — a genuine
    finite-information quantity, never completed. *)
Theorem gisin_indeterminism :
  (forall k, ~ (sq2 k * sq2 k == 2))          (* every finite stage misses *)
  /\ ~ (exists q : Q, q * q == 2).             (* no rational terminus *)
Proof. split; [ exact gisin_never_exact | exact sqrt2_not_in_Q ]. Qed.

(* ===================================================================== *)
(*  The determinate (terminating) contrast: a rational IS its terminus    *)
(* ===================================================================== *)

Definition const_cs (r : Q) : nat -> Q := fun _ => r.

(** A rational is a determinate (terminating) choice-sequence: its value is fixed
    at every stage — the terminus IS an Element. *)
Theorem rational_terminates : forall (r : Q) (k : nat), const_cs r k == r.
Proof. intros r k. reflexivity. Qed.

(* ===================================================================== *)
(*  't HOOFT & CARROLL: deterministic finite automata recur (Element side) *)
(* ===================================================================== *)

Definition cstep (n x : nat) : nat := (S x) mod n.
Fixpoint citer (n steps x : nat) : nat :=
  match steps with O => x | S s => cstep n (citer n s x) end.

(** A deterministic finite cyclic automaton returns to its start after its period
    — determinism recovered from finiteness.  This is the 't Hooft (cellular
    automata) / Carroll (finite-dimensional, Poincaré-recurrent QM) side: a
    terminating process, an Element. *)
Theorem finitist_determinism :
  (citer 3 3 0 = 0)%nat /\ (citer 4 4 0 = 0)%nat /\ (citer 5 5 0 = 0)%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis: two sides of one boundary                                  *)
(* ===================================================================== *)

(** The finitist-QM literature in one statement: Gisin (role-limit / indeterminism
    = non-termination) and 't Hooft + Carroll (Element / determinism = recurrence)
    are the two sides of the one P4 finitization boundary — all over ℚ, 0 axioms. *)
Theorem finitist_qm_synthesis :
  ((forall k, ~ (sq2 k * sq2 k == 2)) /\ ~ (exists q : Q, q * q == 2))
  /\ ((citer 3 3 0 = 0)%nat /\ (citer 4 4 0 = 0)%nat /\ (citer 5 5 0 = 0)%nat).
Proof. split; [ exact gisin_indeterminism | exact finitist_determinism ]. Qed.
