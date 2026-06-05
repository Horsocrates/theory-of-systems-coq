(** * GravityH1Decision.v — a machine-checked SOUND CLASSIFIER (witnessed sort) that DERIVES, from
      each observable's continuum-refinement behaviour, whether it is Element (finite continuum value)
      or RoleLimit (divergent) — the H1 finitization criterion turned into a decision over gravity's
      observables, then applied to sort the three pathologies as RoleLimit while the safe observables
      land Element.  This is the engine GravityFinitization.v lacked: there the side was HAND-TAGGED by
      a match; here the side is PROVEN from the process.

    -- What is genuinely new vs GravityFinitization.v --
      GravityFinitization assigned `grav_side` by hand (a match on a constructor).  Here an observable is
      a PROCESS obs : nat -> Q (its lattice value as the cutoff is refined toward the continuum), and the
      side is DERIVED:  Bounded obs  => Element (the continuum value exists, finite);
                        Unbounded obs => RoleLimit (no finite continuum value = a pathology).
      The two classes are PROVEN DISJOINT (soundness of the sort), and the three pathologies are concrete
      Q-processes with machine-proven unboundedness (all reducing to one Archimedean lemma).

    -- HONEST: this is NOT a total decider --
      Boundedness of an arbitrary process is undecidable (it is the halting problem in disguise), so there
      is no total oracle.  What is built is a SOUND criterion with explicit witnesses, instantiated on the
      archetypal gravity observables.  The criterion never misclassifies (disjointness theorem); it is
      simply not total.  That is the honest scope.

    -- The H1 / P4 content --
      Each pathology is FINITE at every finite refinement level (a definite rational; any finite prefix is
      bounded) and UNBOUNDED only in the completed continuum.  So the divergence lives purely in the
      role-limit (the a -> 0 completion); stopping at a finite level (P4) keeps the observable well-defined.
      The classifier reads off exactly this: the pathological observables are the ones whose continuum
      process escapes every bound.

    Elements: concrete Q-processes — cutoff n = n (growing), const c (flat); each pathology dominates cutoff
    Roles:    Bounded = Element (safe); Unbounded = RoleLimit (pathology); the two are disjoint (soundness)
    Rules:    classify by continuum-refinement behaviour; finite at every level, unbounded only in the limit

    ============ E/R/R разбор ============
      Rules (L5): правило сортировки — наблюдаемая классифицируется по поведению её процесса уточнения к
                  континууму: ОГРАНИЧЕН => Element (конечное континуумное значение), НЕОГРАНИЧЕН => RoleLimit
                  (значения нет = патология).  H1: role-limit = незавершаемость; здесь инвариант = ограниченность.
      Roles (L4): две ВЗАИМОИСКЛЮЧАЮЩИЕ стороны.  Безопасные (Ньютон 1/r^2 при фикс. r, плотность вакуума/мода)
                  = Element; три патологии (UV~Lambda, Lambda-сумма~Lambda^4, сингулярность 1/r при r->0)
                  = RoleLimit.  Доказанная дизъюнктность = роли не пересекаются (soundness сортировки).
      Elements  : конкретные Q-процессы; каждая патология мажорирует cutoff => Unbounded (через 1 арх. лемму).
    ДИАГНОСТИКА (P4): это НЕ тотальный решатель (ограниченность произвольного процесса неразрешима = halting);
    это ЗДРАВЫЙ критерий со СВИДЕТЕЛЯМИ на архетипах.  Ключевой H1-факт: патология КОНЕЧНА на каждом конечном
    уровне (любой конечный префикс ограничен), НЕОГРАНИЧЕНА лишь в завершённом континууме => P4 (остановка на
    конечном уровне) сохраняет определённость.  Сортировка ВЫВОДИТ сторону из доказанного поведения процесса --
    шаг над ручной разметкой GravityFinitization.v.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Observables as continuum-refinement processes                          *)
(* ===================================================================== *)

(** An observable = its lattice value as the cutoff is refined toward the continuum (n = refinement
    level; higher n = closer to a -> 0). *)
Definition Obs := nat -> Q.

(** The canonical growing scale: cutoff n = n (the inverse lattice spacing Lambda ~ 1/a at level n). *)
Definition cutoff : Obs := fun n => inject_Z (Z.of_nat n).

(** Element / safe witness: the refinement process is BOUNDED — the continuum value stays finite. *)
Definition Bounded (f : Obs) : Prop := exists M : Q, forall n, f n <= M.

(** RoleLimit / pathology witness: the refinement process is UNBOUNDED — no finite continuum value. *)
Definition Unbounded (f : Obs) : Prop := forall B : Q, exists n, B < f n.

(* ---- the Archimedean engine: naturals are cofinal in Q ---- *)
Lemma arch_nat : forall B : Q, exists n : nat, B < inject_Z (Z.of_nat n).
Proof.
  intro B. destruct (Qarchimedean B) as [p Hp].
  exists (Pos.to_nat p). unfold inject_Z. rewrite positive_nat_Z. exact Hp.
Qed.

Lemma cutoff_unbounded : Unbounded cutoff.
Proof. intro B. destruct (arch_nat B) as [n Hn]. exists n. exact Hn. Qed.

(** Anything that pointwise dominates the cutoff is itself unbounded. *)
Lemma dominates_cutoff_unbounded :
  forall f, (forall n, cutoff n <= f n) -> Unbounded f.
Proof.
  intros f Hdom B. destruct (cutoff_unbounded B) as [n Hn].
  exists n. apply Qlt_le_trans with (cutoff n); [ exact Hn | apply Hdom ].
Qed.

(** SOUNDNESS core: no process is both Bounded and Unbounded. *)
Lemma bounded_unbounded_exclusive : forall f, Bounded f -> Unbounded f -> False.
Proof.
  intros f [M HM] Hub. destruct (Hub M) as [n Hn].
  exact (Qlt_not_le _ _ Hn (HM n)).
Qed.

Lemma const_bounded : forall c, Bounded (fun _ => c).
Proof. intro c. exists c. intro n. apply Qle_refl. Qed.

(** Every finite prefix of the cutoff is bounded — "finite at every realized level". *)
Lemma cutoff_prefix_bounded :
  forall N, exists M, forall n, (n <= N)%nat -> cutoff n <= M.
Proof.
  intro N. exists (cutoff N). intros n Hn. unfold cutoff.
  rewrite <- Zle_Qle. lia.
Qed.

(* ===================================================================== *)
(*  The gravity observables and their three pathologies                    *)
(* ===================================================================== *)

(* Safe (Element): cutoff-independent / bounded. *)
Definition newton_obs : Obs := fun _ => 1.            (* Newton 1/r^2 at fixed r: cutoff-independent *)
Definition vac_density_obs : Obs := fun _ => 1 # 2.   (* per-mode vacuum density: bounded O(1) *)

(* Pathologies (RoleLimit): each dominates the growing cutoff. *)
Definition uv_obs : Obs := cutoff.                                (* UV self-energy ~ Lambda *)
Definition lambda_obs : Obs := cutoff.                            (* vacuum mode-sum ~ Lambda^4 >= Lambda *)
Definition sing_obs : Obs := fun n => inject_Z (Z.of_nat (S n)).  (* 1/r at shell r = 1/(n+1) *)

Lemma uv_unbounded : Unbounded uv_obs.
Proof. apply dominates_cutoff_unbounded. intro n. apply Qle_refl. Qed.

Lemma lambda_unbounded : Unbounded lambda_obs.
Proof. apply dominates_cutoff_unbounded. intro n. apply Qle_refl. Qed.

Lemma sing_unbounded : Unbounded sing_obs.
Proof.
  apply dominates_cutoff_unbounded. intro n. unfold cutoff, sing_obs.
  rewrite <- Zle_Qle. lia.
Qed.

(** H1 for a pathology (UV as exemplar): UNBOUNDED in the continuum, yet FINITE at every realized level
    (every finite prefix is bounded).  The divergence is purely the role-limit; P4 keeps it defined. *)
Lemma h1_pathology_uv :
  Unbounded uv_obs
  /\ (forall N, exists M, forall n, (n <= N)%nat -> uv_obs n <= M).
Proof.
  split.
  - exact uv_unbounded.
  - intro N. unfold uv_obs. apply cutoff_prefix_bounded.
Qed.

(* ===================================================================== *)
(*  The classifier and the sort                                            *)
(* ===================================================================== *)

Inductive Side := Element | RoleLimit.

Definition classified (f : Obs) (s : Side) : Prop :=
  match s with Element => Bounded f | RoleLimit => Unbounded f end.

(** The sort never misclassifies: no observable is classified both ways. *)
Lemma sort_disjoint : forall f, ~ (classified f Element /\ classified f RoleLimit).
Proof. intros f [HE HR]. exact (bounded_unbounded_exclusive f HE HR). Qed.

(** The gravity sort: the two safe observables land Element; the three pathologies land RoleLimit —
    each side DERIVED from the process's proven boundedness / unboundedness, not assigned by hand. *)
Theorem gravity_sort :
  classified newton_obs Element
  /\ classified vac_density_obs Element
  /\ classified uv_obs RoleLimit
  /\ classified lambda_obs RoleLimit
  /\ classified sing_obs RoleLimit.
Proof.
  unfold classified, newton_obs, vac_density_obs. repeat split.
  - apply const_bounded.
  - apply const_bounded.
  - exact uv_unbounded.
  - exact lambda_unbounded.
  - exact sing_unbounded.
Qed.
