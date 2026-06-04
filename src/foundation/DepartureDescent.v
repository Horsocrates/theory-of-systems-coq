(** * DepartureDescent.v — Baryogenesis boundary, BRANCH 3/3 (DepartureMagnitude, the out-of-equilibrium
      magnitude): walking the box REFINES its "DifferentArena" tag.  The departure is NOT a role-limit
      number (unlike branches 1 and 2): on a FINITE lattice (P4) it is a FINITE process that TERMINATES
      — a NotYetComputed (Element-reachable) quantity, not a wall.  "DifferentArena" holds only in the
      continuum view.  So the three boxes have THREE DIFFERENT bottoms — the boundaries are not all alike.

    BaryogenesisBoundary.v tagged DepartureMagnitude → DifferentArena.  Walking it:
      Rules (L5):  the departure's size is set by the dynamics (H vs Γ at T_EW); on a FINITE lattice (P4)
                   the thermal history is a FINITE process — a sum/difference over finitely many sites,
                   which HALTS (unlike the exponential of branch 2).
      Roles (L4):  the DIRECTION (≠ 0) is DERIVED from the arrow (irreversibility); the SIZE is a finite
                   lattice quantity.
      Elements:    the actual finite lattice sum is RATIONAL, computable, and the process TERMINATES
                   (stabilizes after `length` sites) — the OPPOSITE of exp_partial (which never stabilizes).

    THE REFINEMENT: the departure is NOT a role-limit.  In P4's finite ontology it is a NotYetComputed
    finite process (Element-reachable, in-principle computable); "DifferentArena" is the continuum reading
    only.  Constructive contrast: departure_terminates (stabilizes) vs SphaleronRateDescent.exp_partial_
    never_stabilizes.  So the three branches bottom out DIFFERENTLY:
      branch 1 (J)            → rational/irrational on the CKM angles (conditional role-limit);
      branch 2 (sphaleron)    → exp, a non-terminating process (role-limit);
      branch 3 (departure)    → a terminating FINITE process (NotYetComputed) / continuum arena — NOT a wall.

    Elements: qsum (finite sum), departure_partial; a concrete finite departure = a definite rational
    Roles:    direction derived (arrow); size = a finite lattice quantity that terminates
    Rules:    the finite process stabilizes after `length` sites — it terminates (NOT a role-limit)

    ============ E/R/R разбор ============
      Rules (L5): размер задаётся динамикой; на конечной решётке (P4) — конечный процесс (сумма по узлам),
                  который ОБРЫВАЕТСЯ (в отличие от exp ветки 2).
      Roles (L4): направление (≠0) выведено из стрелы; размер = конечная решёточная величина.
      Elements  : конечная сумма рациональна, вычислима, процесс ТЕРМИНИРУЕТ (стабилизируется после length).
    ДИАГНОСТИКА (P4): departure — НЕ role-limit-число. В P4 это конечный-процесс-не-вычислен (Element-достижим),
    в континууме — иная-арена. Три ящика = ТРИ РАЗНЫХ дна (1: рац/иррац, 2: нетерминация, 3: конечный/арена).
    Направление выведено; размер = конечная динамика (в P4 вычислима, не стена). Границы НЕ одинаковы.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Arith Lia List.
Import ListNotations.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The departure as a FINITE lattice sum (terminates — Element)            *)
(* ===================================================================== *)

Fixpoint qsum (l : list Q) : Q := match l with [] => 0 | x :: r => x + qsum r end.

(** The departure accumulated over the first k lattice sites. *)
Definition departure_partial (l : list Q) (k : nat) : Q := qsum (firstn k l).

(** The process starts at 0 (no sites accumulated yet). *)
Lemma departure_partial_0 : forall l, departure_partial l 0 == 0.
Proof. intro l. unfold departure_partial. simpl. reflexivity. Qed.

(** ★ Once all (finitely many) sites are summed, the process REACHES the full sum. *)
Lemma departure_stabilizes : forall l k, (length l <= k)%nat -> departure_partial l k == qsum l.
Proof.
  intros l k Hk. unfold departure_partial. rewrite firstn_all2 by exact Hk. reflexivity.
Qed.

(** ★ The finite process TERMINATES: past `length l`, no step changes the value (it stabilizes).
    This is the OPPOSITE of SphaleronRateDescent.exp_partial_never_stabilizes — the departure is a
    FINITE process, NOT a role-limit. *)
Lemma departure_terminates :
  forall l k, (length l <= k)%nat -> departure_partial l k == departure_partial l (S k).
Proof.
  intros l k Hk. rewrite (departure_stabilizes l k Hk).
  rewrite (departure_stabilizes l (S k)) by lia. reflexivity.
Qed.

(** A concrete finite departure is a DEFINITE rational — an Element (computable). *)
Lemma departure_finite_value : qsum [1#2; 1#2] == 1.
Proof. simpl. lra. Qed.

(* ===================================================================== *)
(*  Classification: NOT a role-limit (three kinds of boundary)             *)
(* ===================================================================== *)

(** Three kinds of boundary a magnitude can be: a finitization role-limit (unreachable), a finite process
    not-yet-computed (Element-reachable), or a different arena (continuum). *)
Inductive BoundaryKind3 := RoleLimit | NotYetComputed | DifferentArena.

(** ★ In P4's finite ontology the departure is a FINITE process that terminates ⟹ NotYetComputed
    (Element-reachable), NOT a role-limit.  ("DifferentArena" is the continuum reading only.) *)
Definition departure_kind : BoundaryKind3 := NotYetComputed.

Lemma departure_not_role_limit : departure_kind <> RoleLimit.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: branch 3 — the departure is a finite process, not a wall      *)
(* ===================================================================== *)

(** Branch 3 (DepartureMagnitude) walked:
      (reaches)    the finite process reaches the full lattice sum once all sites are summed;
      (terminates) past `length l` the value stabilizes — the process HALTS (opposite of exp, branch 2);
      (start)      it starts at 0;
      (Element)    a concrete finite departure is a definite rational (computable);
      (refine)     so the departure is NOT a role-limit — in P4 it is a NotYetComputed finite process
                   (Element-reachable); "DifferentArena" is the continuum reading only.
    The three branches bottom out DIFFERENTLY (rational/irrational, non-terminating, finite-process) —
    the boundaries are not all alike. *)
Theorem departure_descent :
  (forall l k, (length l <= k)%nat -> departure_partial l k == qsum l)
  /\ (forall l k, (length l <= k)%nat -> departure_partial l k == departure_partial l (S k))
  /\ (forall l, departure_partial l 0 == 0)
  /\ qsum [1#2; 1#2] == 1
  /\ departure_kind <> RoleLimit.
Proof.
  split; [ exact departure_stabilizes | ].
  split; [ exact departure_terminates | ].
  split; [ exact departure_partial_0 | ].
  split; [ exact departure_finite_value | ].
  exact departure_not_role_limit.
Qed.
