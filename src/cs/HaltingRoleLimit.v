(** * HaltingRoleLimit.v — Computation as Process + the halting boundary as a ROLE-LIMIT
      Opening file of the Computer-Science branch of the Theory of Systems.

      Two complementary views of the SAME E/R/R act:

      (A) Computation as Process (Element side, terminating, 0 axioms).
          A machine = (Config, step, halted): a step relation on configurations plus a
          halt status.  `run n` unfolds it to FINITE depth (P4).  We prove the Element-side
          facts: run is a function (determinism), halting is absorbing, ordered halting is
          monotone, and — crucially — BOUNDED halting `halts_in n` is DECIDABLE.

      (B) The halting boundary (role-limit side, undecidability via diagonalisation).
          UNBOUNDED halting `halts := exists n, halts_in n` cannot be decided by any program
          of a self-applicable language.  The engine is one diagonal: `b <> negb b`
          (= circular_dep_is_paradox, Roles.v §XII) — the very diagonal the project uses for
          uncountability in settheory/ProcessDiagonal.v.

    Conceptual neighbours (cited, not duplicated):
      - foundation/P4_Eliminates_Pi11.v : Program := nat, a TOTAL universal `eval_program`
        (no halting).  Here we ADD the partiality/halting dimension it omits, with 0 axioms
        (the abstraction is discharged as section hypotheses, not a Parameter).
      - foundation/GravityH1Decision.v  : boundedness of a process = "the halting problem in
        disguise"; a SOUND-but-not-total classifier.  Here the halting problem is explicit.
      - Roles.v §XII                    : every paradox = circular status `s = f s`, f
        fixpoint-free.  no_halting_decider IS that pattern with f = negb.

    Elements: configurations (Config); programs-as-carriers (Prog) at the boundary
    Roles:    `halted` = the STATUS a config acquires under the rules; `Decides D` = the
              halting-oracle role; halting is a role-LIMIT (the a->infinity completion of run)
    Rules:    `step` = the L5-ordered transition; `run n` = finite-depth unfolding (P4)

    ============ E/R/R разбор ============
      Rules (L5): step — упорядоченный переход; именно ПОРЯДОК шагов (L5) делает
                  последовательность конфигураций ВЫЧИСЛЕНИЕМ, а не произвольным списком.
                  run n — развёртка на КОНЕЧНУЮ глубину n (P4): «бесконечность есть свойство
                  процесса, не объекта».
      Roles (L4): halted — это СТАТУС (что конфигурация СТАЛА после применения правил),
                  не роль (различение Status != Role, Roles.v §IX).  Решатель остановки
                  `Decides D` — роль-оракул.  Остановка `halts` — РОЛЬ-ПРЕДЕЛ: завершение
                  процесса run в пределе по всем n.
      Elements  : конкретные конфигурации; на границе — программы-коды (Prog), несущие
                  само-применимость (ср. Program := nat в P4_Eliminates_Pi11.v).
    ДИАГНОСТИКА (P4): ОГРАНИЧЕННАЯ остановка halts_in n (фикс. бюджет n) — Element-сторона:
      РАЗРЕШИМА, булева, 0 аксиом, терминирует.  НЕОГРАНИЧЕННАЯ остановка halts = exists n …
      — role-limit-сторона: взять её как разрешимый объект = категориальная ошибка
      (реификация role-limit в Element).  Неразрешимость = честное «role-limit нельзя
      финитизировать в Element-решатель».  Единственный вход — SelfProgrammable
      (язык строит диагональную программу для оракула) = Тьюринг-полнота; role-limit живёт
      РОВНО в этой гипотезе: без само-применимости (примитивная рекурсия) остановка
      разрешима — противоречия нет.  ТА ЖЕ диагональ (b != negb b), что доказывает
      несчётность (ProcessDiagonal.v) и все парадоксы (Roles.v §XII).

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool.

(* ===================================================================== *)
(*  PART A — COMPUTATION AS PROCESS (Element side)                        *)
(*                                                                         *)
(*  E = Config (what is transformed) | R(rule) = step (how, L5-ordered)   *)
(*  R(role/status) = halted (the result-status under the rules)           *)
(* ===================================================================== *)

Section ComputationAsProcess.

  Variable Config : Type.
  Variable step   : Config -> Config.   (* the Rule: one ordered transition (L5) *)
  Variable halted : Config -> bool.      (* the Status: has a result been reached? *)

  (** Run the machine for [n] steps — FINITE depth (P4).  Form "run k, then maybe one
      more step" so that halting is manifestly absorbing and monotone. *)
  Fixpoint run (n : nat) (c : Config) : Config :=
    match n with
    | O    => c
    | S k  => let c' := run k c in if halted c' then c' else step c'
    end.

  (** A computation HALTS within budget [n] iff its config is halted after [n] steps. *)
  Definition halts_in (n : nat) (c : Config) : Prop := halted (run n c) = true.

  (** Full (unbounded) halting — the ROLE-LIMIT: completion of run over all budgets. *)
  Definition halts (c : Config) : Prop := exists n, halts_in n c.

  (** Divergence — never reaches a result-status at any finite depth. *)
  Definition diverges (c : Config) : Prop := forall n, halted (run n c) = false.

  (** Definitional unfolding of one step (used as a rewrite). *)
  Lemma run_S : forall n c,
    run (S n) c = (if halted (run n c) then run n c else step (run n c)).
  Proof. reflexivity. Qed.

  (** Once halted, the configuration is a FIXED POINT of further running. *)
  Lemma run_absorb : forall n c,
    halted (run n c) = true -> run (S n) c = run n c.
  Proof. intros n c H. rewrite run_S, H. reflexivity. Qed.

  (** Halting is MONOTONE in the budget: a result, once reached, persists. *)
  Lemma halts_in_S : forall n c, halts_in n c -> halts_in (S n) c.
  Proof. unfold halts_in. intros n c H. rewrite run_S, H. exact H. Qed.

  Lemma halts_in_mono : forall c n m,
    (n <= m)%nat -> halts_in n c -> halts_in m c.
  Proof.
    intros c n m Hle H. induction Hle.
    - exact H.
    - apply halts_in_S. exact IHHle.
  Qed.

  (** ★ ELEMENT SIDE: BOUNDED halting is DECIDABLE — a constructive boolean decision
      for any fixed budget [n].  (Contrast PART C: UNBOUNDED halting is not.) *)
  Lemma bounded_halting_decidable : forall n c,
    {halts_in n c} + {~ halts_in n c}.
  Proof.
    intros n c. unfold halts_in.
    destruct (halted (run n c)).
    - left. reflexivity.
    - right. discriminate.
  Qed.

  (** Halting and divergence are exclusive: a process is not both. *)
  Lemma halts_not_diverges : forall c, halts c -> diverges c -> False.
  Proof.
    intros c [n Hn] Hdiv. unfold halts_in in Hn.
    specialize (Hdiv n). rewrite Hdiv in Hn. discriminate.
  Qed.

End ComputationAsProcess.

(* --- Concrete instances: a halting machine and a diverging one --------- *)

(** Countdown: step = pred, halted = (· =? 0).  From 3 it reaches the result 0. *)
Example countdown_halts :
  halts nat Nat.pred (fun n => Nat.eqb n 0) 3.
Proof. exists 4. vm_compute. reflexivity. Qed.

(** Increment with no halt-status: finite at every step, never a result (a role-limit). *)
Example incr_diverges :
  diverges nat S (fun _ => false) 0.
Proof. intro n. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — THE DIAGONAL ENGINE (one diagonal for everything)            *)
(* ===================================================================== *)

(** The fixpoint-free core: negation has no fixed point.  This is the bool case of
    circular_dep_is_paradox (Roles.v §XII) — the seed of every paradox AND of every
    diagonal undecidability/uncountability result. *)
Lemma negb_no_fixpoint : forall b : bool, b <> negb b.
Proof. intros [] H; discriminate. Qed.

(** Cantor's diagonal, representation-independent: no [g : A -> (A -> bool)] is
    surjective.  This SAME engine drives uncountability (settheory/ProcessDiagonal.v)
    and — in PART C — the undecidability of halting. *)
Theorem cantor_no_surjection :
  forall (A : Type) (g : A -> (A -> bool)),
    ~ (forall f : A -> bool, exists a, g a = f).
Proof.
  intros A g Hsurj.
  destruct (Hsurj (fun x => negb (g x x))) as [a Ha].
  pose proof (f_equal (fun h : A -> bool => h a) Ha) as E. simpl in E.
  (* E : g a a = negb (g a a) *)
  exact (negb_no_fixpoint (g a a) E).
Qed.

(* ===================================================================== *)
(*  PART C — THE HALTING BOUNDARY (role-limit side)                       *)
(*                                                                         *)
(*  Representation-independent: for ANY self-applicable programming system *)
(*  there is no halting decider.  0 axioms — the abstraction discharges as *)
(*  universally-quantified hypotheses (NOT a Parameter).                   *)
(* ===================================================================== *)

Section HaltingBoundary.

  Variable Prog  : Type.
  Variable Halts : Prog -> Prog -> Prop.   (* Halts p q : program p halts on input q *)

  (** A halting decider: a program-level boolean oracle that is correct. *)
  Definition Decides (D : Prog -> Prog -> bool) : Prop :=
    forall p q, D p q = true <-> Halts p q.

  (** Self-programmability: the language can express the DIAGONAL program for D
      ("run D on (q,q); halt iff D says q does NOT halt on q").  This is the only
      computational input — Turing-completeness — and the role-limit lives here. *)
  Definition SelfProgrammable (D : Prog -> Prog -> bool) : Prop :=
    exists diag : Prog, forall q, Halts diag q <-> D q q = false.

  (** ★ NO HALTING DECIDER.  A correct decider for a self-applicable system is
      impossible: feeding it the diagonal forces  D diag diag = negb (D diag diag). *)
  Theorem no_halting_decider :
    forall D, Decides D -> SelfProgrammable D -> False.
  Proof.
    intros D Hdec [diag Hdiag].
    destruct (Hdec diag diag) as [Hd1 Hd2].   (* Hd1: D..=true -> Halts;  Hd2: Halts -> D..=true *)
    destruct (Hdiag diag) as [Hg1 Hg2].       (* Hg1: Halts -> D..=false; Hg2: D..=false -> Halts *)
    destruct (Bool.bool_dec (D diag diag) true) as [Et | Ef].
    - (* D diag diag = true *)
      assert (Halts diag diag) as HH by (apply Hd1; exact Et).
      pose proof (Hg1 HH) as Hf. rewrite Et in Hf. discriminate.
    - (* D diag diag = false *)
      apply Bool.not_true_is_false in Ef.
      assert (Halts diag diag) as HH by (apply Hg2; exact Ef).
      pose proof (Hd2 HH) as Ht. rewrite Ef in Ht. discriminate.
  Qed.

  (** Contrapositive packagings of the boundary. *)
  Corollary no_total_halting_oracle :
    ~ exists D, Decides D /\ SelfProgrammable D.
  Proof. intros [D [H1 H2]]. exact (no_halting_decider D H1 H2). Qed.

  Corollary decidable_implies_not_self_programmable :
    forall D, Decides D -> ~ SelfProgrammable D.
  Proof. intros D Hdec Hsp. exact (no_halting_decider D Hdec Hsp). Qed.

End HaltingBoundary.

(* ===================================================================== *)
(*  SYNTHESIS                                                              *)
(* ===================================================================== *)

(** THE ELEMENT / ROLE-LIMIT CUT, made precise:
      - bounded_halting_decidable : halts_in n  is DECIDABLE   (Element side, PART A)
      - no_halting_decider        : halts        is NOT         (role-limit, PART C)
    Same shape as GravityH1Decision.v ("finite at every level, unbounded only in the
    limit").  Computability = the finitization boundary OF the project, made algorithmic.

    ONE diagonal underlies both PART C and uncountability (ProcessDiagonal.v): the core
    is negb_no_fixpoint = circular_dep_is_paradox (Roles.v §XII).  CS's central negative
    results are the project's existing diagonal engine, redeployed. *)

Print Assumptions cantor_no_surjection.
Print Assumptions no_halting_decider.
