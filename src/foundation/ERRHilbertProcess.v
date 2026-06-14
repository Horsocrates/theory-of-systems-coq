(** * ERRHilbertProcess.v — core E/R/R anchor for the Hilbert tier: the Hilbert space of ToS is a
      PROCESS (Element at each finite stage), and "completed Hilbert space as an object" = the
      completeness axiom = actualization of a role-limit = the SUSPENSION OF P4.  A completed continuum
      is a CATEGORICAL ERROR in ToS.

    The repository ALREADY realizes the Hilbert tier as a process (no completeness axiom):
      * src/process_qm/HilbertAsProcess.v — "Hilbert = P4 process {Q^N}, NOT completed object; complete
        inner product space = AXIOM vs process = no axiom of completeness; at each N finite linear
        algebra over Q" (10 Qed, 0 axioms);
      * src/physics/QObservable.v — an observable = a process nat -> QMat of symmetric matrices,
        "purely constructive over Q" (0 axioms);
      * src/stdlib/ProcessHilbert(Synthesis).v, src/process/ProcessL2HilbertSynthesis.v.
    This file is the CORE-level demarcation that those concrete files realize: it states, at the
    abstract dimension-process level, exactly where the demand for a "completed space" sits — and
    proves it is the role-limit, never an Element, so its actualization is the axiom (¬P4).

    The dimension process: stage N has dimension N (the {Q^N} ladder).
      ★ stage_is_finite           — every stage is a FINITE, actual object (Element-side, Species I);
      ★ dimension_unbounded       — the process never terminates: dimension grows past every bound
                                    ("infinite-dimensional" = a non-terminating process);
      ★ no_finite_completion      — NO single finite object caps all stages: the completion is a
                                    role-limit (Species II), not any stage;
      ★ completion_demands_actualization — each stage is P4-finite, but the completion is NOT — to
                                    posit it as an object is to actualize the role-limit = the
                                    completeness axiom = ¬P4.

    ============================== E/R/R разбор ==============================
    (this разбор answers Task #126: "what requires a completed space")
    Rules (the generative rule first):
      (1) "infinite-dimensional" = the dimension process never terminates;
      (2) at each finite stage everything is finite, exact over Q (HilbertAsProcess) — Element-side;
      (3) "completed space as an object" = the never-terminating process declared a finished object =
          the completeness axiom = actualization of the role-limit = the suspension of P4.
    Roles (L4): the dimension grows (unbounded); at each N the inner product / norm is exact over Q
      (HilbertAsProcess, the ip_ lemmas); the completion would be a single bound over all stages.
    Elements (L1+P4): the stages of the Hilbert process (Q^N at each N — finite, actual); the
      dimension process hdim.
    P4 diagnostic (could it be otherwise?):
      no — each stage is P4-finite (an Element); the completion is unbounded, capped by no finite stage
      (no_finite_completion) — it is the role-limit of an unbounded process.  To assert the completed
      Hilbert space AS an object is to actualize that role-limit = to posit a finite bound the process
      provably exceeds (false) or an actual infinity (P4 forbids).  So "completed space" requires
      EXACTLY the completeness axiom = ¬P4.  A completed continuum is a categorical error in ToS.
    Honesty wall:
      the theorems are an ELEMENTARY nat skeleton (an unbounded process has no finite completion).  The
      genuine content is the E/R/R + P4 FRAMING and the demarcation it makes precise — pointing at the
      concrete 0-axiom realizations (HilbertAsProcess, QObservable, ProcessHilbert) as the honest
      Hilbert tier, and at RoleLimitSpecies / the H1 finitization boundary as the same dichotomy
      (Element-stage / role-limit-completion).  This CORRECTS the earlier loose phrasing "state space
      as a completed continuum": ToS never has it — Hilbert is a process; the completion is the
      role-limit, and only its actualization costs the axiom.  0 axioms.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.

(* ===================================================================== *)
(*  THE HILBERT TIER AS A DIMENSION PROCESS                               *)
(* ===================================================================== *)

(** Stage N of the Hilbert process has dimension N — the {Q^N} ladder (HilbertAsProcess). *)
Definition hdim (N : nat) : nat := N.

(** ★ ELEMENT-SIDE: every stage is a FINITE, actual object (a concrete dimension) — at each N the
    Hilbert process is finite linear algebra over Q (HilbertAsProcess), Species I. *)
Lemma stage_is_finite : forall N : nat, exists d : nat, hdim N = d.
Proof. intro N. exists N. reflexivity. Qed.

(** ★★ The process NEVER TERMINATES: the dimension grows past every bound — "infinite-dimensional"
    is a non-terminating process, not a finished object. *)
Lemma dimension_unbounded : forall B : nat, exists N : nat, (B < hdim N)%nat.
Proof. intro B. exists (S B). unfold hdim. lia. Qed.

(** A "completed Hilbert space AS AN OBJECT" = a single finite dimension D bounding ALL stages. *)
Definition completed_as_object : Prop := exists D : nat, forall N : nat, (hdim N <= D)%nat.

(** ★★ NO FINITE COMPLETION: no single object caps the process — the completion is the role-limit
    (Species II) of an unbounded process, realized at no stage. *)
Lemma no_finite_completion : ~ completed_as_object.
Proof. intros [D HD]. specialize (HD (S D)). unfold hdim in HD. lia. Qed.

(* ===================================================================== *)
(*  THE P4 DEMARCATION                                                     *)
(* ===================================================================== *)

(** ★★ Each stage is P4-finite (an Element); the completion is NOT (it exceeds every finite bound).
    So to posit the completed Hilbert space AS an object is to actualize the role-limit — that is the
    completeness axiom, the suspension of P4.  The process pays no axiom; the completion does. *)
Theorem completion_demands_actualization :
  (forall N : nat, exists d : nat, hdim N = d)   (* stages: P4-finite, Element-side *)
  /\ ~ completed_as_object.                       (* completion: not P4-finite — needs the axiom *)
Proof. split; [ exact stage_is_finite | exact no_finite_completion ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE HILBERT TIER IS A PROCESS, NOT A COMPLETED OBJECT:
      (Element)     every stage is finite and actual (finite Q-linear algebra at each N);
      (process)     the dimension is unbounded — "infinite-dimensional" = a non-terminating process;
      (role-limit)  no finite object completes it — the completion is the role-limit, never a stage.
    Hence "completed space" requires the completeness axiom (= actualization = ¬P4); a completed
    continuum is a categorical error in ToS.  Concretely realized 0-axiom by HilbertAsProcess /
    QObservable. *)
Theorem err_hilbert_is_process :
  (forall N : nat, exists d : nat, hdim N = d)
  /\ (forall B : nat, exists N : nat, (B < hdim N)%nat)
  /\ ~ (exists D : nat, forall N : nat, (hdim N <= D)%nat).
Proof.
  split; [ exact stage_is_finite | ].
  split; [ exact dimension_unbounded | exact no_finite_completion ].
Qed.

Print Assumptions err_hilbert_is_process.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  5 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Core E/R/R anchor (Task #126): the Hilbert tier of ToS is a PROCESS       *)
(*  {Q^N} (stage_is_finite — Element at each finite N; dimension_unbounded —   *)
(*  non-terminating; no_finite_completion — the completion is a role-limit,    *)
(*  realized at no stage).  completion_demands_actualization: positing the     *)
(*  completed space AS an object = actualizing the role-limit = the            *)
(*  completeness axiom = ¬P4.  Capstone err_hilbert_is_process.  CORRECTS the  *)
(*  earlier "state space as a completed continuum": ToS never has it.  The     *)
(*  concrete 0-axiom realizations already in repo — HilbertAsProcess (H =      *)
(*  process, no completeness axiom), QObservable (observable = process), and   *)
(*  ProcessHilbert; same dichotomy as RoleLimitSpecies / the H1 finitization   *)
(*  boundary.  HONEST: elementary nat skeleton; the value is the P4            *)
(*  demarcation + the link to the concrete process-Hilbert files.             *)
(* ========================================================================= *)
