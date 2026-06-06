(** * ComputationModel.v — the computation arena as ONE object; the capstone synthesis
      Synthesis file of the Computer-Science branch (Part XV).

      The cs/ branch proved its facts across several files with Section-quantified machines
      and abstract domains.  Here we (a) bundle a computation model into ONE record
      `CompModel`, restating the Element-side decidability ON that object, and (b) collect the
      whole Element / role-limit picture into ONE capstone theorem
      `computation_is_finitization_boundary`:

        (1) ELEMENT side  — on ANY machine, BOUNDED halting is decidable (terminating, P4);
        (2) ROLE-LIMIT    — ONE diagonal, FOUR faces (number / program / set / complexity);
        (3) ROOT          — Lawvere's fixed-point theorem, of which all four faces are instances.

      Nothing new is assumed: this is pure consolidation of cs/HaltingRoleLimit,
      BoundaryDecidability, KolmogorovRoleLimit, LawvereFixedPoint — 0 axioms.

    Reuses (consolidation, not restatement):
      - cs/HaltingRoleLimit.v     : run / halts_in / halts, bounded_halting_decidable, negb_no_fixpoint.
      - cs/BoundaryDecidability.v : ElementDrawn / RoleLimitDrawn, rational_split.
      - cs/KolmogorovRoleLimit.v  : one_boundary_four_faces.
      - cs/LawvereFixedPoint.v    : lawvere_fixed_point, point_surjective.

    Elements: concrete machines (the countdown instance); bounded runs
    Roles:    CompModel = the computation ARENA (object); Element/role-limit = roles of a
              decision-criterion; a decider = role-oracle
    Rules:    a model bundles step (L5-order) + halted (status); the boundary = ONE rule
              (terminates <-> Element); the diagonal defeats every total decider

    ============ E/R/R разбор ============
      Rules (L5): CompModel связывает step (L5-порядок переходов) и halted (статус) в ОДИН
                  объект-арену; капстоун = граница «терминирует ⟺ Element» как одно правило.
      Roles (L4): CompModel — арена (объект); Element / role-limit — роли критерия-решения;
                  решатель — роль-оракул; корень — неподвижная точка Ловера.
      Elements  : конкретные машины (countdown); ограниченные прогоны run n.
    ДИАГНОСТИКА (P4): ОДНА арена несёт ОБЕ стороны границы — ограниченная остановка РАЗРЕШИМА
      (Element, cm_bounded_decidable), безграничная/сложность/несчётность — role-limit (одна
      диагональ, four faces), корень — Ловер.  Реифицировать role-limit-сторону в Element-решатель
      = категориальная ошибка (диагональ запрещает).  Вычисление = граница финитизации проекта,
      ставшая алгоритмической и собранная в один объект.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool.
From ToS Require Import cs.HaltingRoleLimit.
From ToS Require Import cs.BoundaryDecidability.
From ToS Require Import cs.KolmogorovRoleLimit.
From ToS Require Import cs.LawvereFixedPoint.

(* ===================================================================== *)
(*  PART A — THE ARENA AS ONE OBJECT (Element side, bundled)              *)
(* ===================================================================== *)

(** A computation model: configurations, an L5-ordered step, a halt-status. *)
Record CompModel := mkCompModel {
  cm_config : Type;
  cm_step   : cm_config -> cm_config;
  cm_halted : cm_config -> bool;
}.

(** Halting within a finite budget, on the arena. *)
Definition cm_halts_in (M : CompModel) (n : nat) (c : cm_config M) : Prop :=
  halts_in (cm_config M) (cm_step M) (cm_halted M) n c.

(** Full (unbounded) halting — the role-limit completion. *)
Definition cm_halts (M : CompModel) (c : cm_config M) : Prop :=
  halts (cm_config M) (cm_step M) (cm_halted M) c.

(** ★ ELEMENT SIDE on the arena: bounded halting is DECIDABLE for any machine, any budget. *)
Theorem cm_bounded_decidable :
  forall (M : CompModel) (n : nat) (c : cm_config M),
    {cm_halts_in M n c} + {~ cm_halts_in M n c}.
Proof.
  intros M n c. unfold cm_halts_in. apply bounded_halting_decidable.
Qed.

(* --- A concrete inhabitant of the arena: the countdown machine ---------- *)

Definition countdown : CompModel :=
  mkCompModel nat Nat.pred (fun n => Nat.eqb n 0).

Example countdown_halts_cm : cm_halts countdown 3.
Proof. unfold cm_halts. exists 4%nat. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — THE CAPSTONE: computation = the finitization boundary        *)
(* ===================================================================== *)

(** ★ One theorem gathering the whole picture: the Element side is decidable on every
    machine; the role-limit side is one diagonal in four faces; the root is Lawvere. *)
Theorem computation_is_finitization_boundary :
  (* (1) ELEMENT: bounded halting decidable on any machine (terminating, P4);
        Prop-level here, with the computational {_}+{_} version in cm_bounded_decidable *)
  (forall (M : CompModel) (n : nat) (c : cm_config M),
     cm_halts_in M n c \/ ~ cm_halts_in M n c)
  /\
  (* (2) ROLE-LIMIT: one diagonal, four faces (number / program / set / complexity) *)
  ((forall b : bool, b <> negb b)
   /\ ElementDrawn rational_split
   /\ (forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
         (forall dec : Prog -> bool, exists diag, Halts diag diag <-> dec diag = false) ->
         RoleLimitDrawn (fun q => Halts q q))
   /\ (forall (A : Type) (g : A -> (A -> bool)), ~ (forall f, exists a, g a = f))
   /\ (forall (Obj : Type) (Complex : Obj -> Prop),
         (forall dec : Obj -> bool, exists d, Complex d <-> dec d = false) ->
         RoleLimitDrawn Complex))
  /\
  (* (3) ROOT: Lawvere's fixed-point theorem (every face is its instance) *)
  (forall (A B : Type) (phi : A -> (A -> B)),
     point_surjective phi -> forall f : B -> B, exists b, f b = b).
Proof.
  split; [| split].
  - intros M n c. destruct (cm_bounded_decidable M n c) as [H | H]; [left | right]; exact H.
  - exact one_boundary_four_faces.
  - exact lawvere_fixed_point.
Qed.

(** Computation, gathered: ONE arena (CompModel) carries both sides of the project's
    finitization boundary — the terminating/bounded is Element (decidable), the
    unbounded/self-referential is role-limit (one diagonal, four faces, root Lawvere).
    This is Part XV's spine: «вычислимое = граница финитизации, ставшая алгоритмической». *)

Print Assumptions cm_bounded_decidable.
Print Assumptions computation_is_finitization_boundary.
