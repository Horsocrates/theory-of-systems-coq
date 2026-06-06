(** * CascadeBoundary.v — SYNTHESIS: the turbulent cascade IS an instance of the H1 finitization
      boundary.  Tying foundation/ScaleHierarchyTransfer.v (the inter-level flux primitive) and
      foundation/ShellCascadeNS.v (the NS dyadic shell cascade) together: at EVERY finite truncation N
      the cascade is wholly Element-side (energy conserved, enstrophy a finite, monotone, non-negative
      rational); the alpha=2 wall lives ONLY in the closure N -> infinity, as a role-limit.

   -- Element side (every finite N): a closed cascade conserves total energy exactly (inherited); the
      truncated enstrophy Omega_N = total_ns_enstrophy a N is a NON-DECREASING, non-negative, finite
      rational (a monotone process).  Everything is computable and exact at each truncation.
   -- Role-limit side (the closure N -> infinity): the dyadic scale tower 2^n is UNBOUNDED, so the
      monotone enstrophy process runs over an unbounded hierarchy; whether it stays BOUNDED in the
      closure is exactly the alpha=2 wall (cf. foundation/NSBoundDescent.v) -- and that is the
      role-limit, UNDECIDED here.  (If bounded, the process is Cauchy -- the regularity case; cf.
      MonotoneConvergence.v.  Whether it is bounded is the open problem.)
   -- The H1 boundary: truncation = Element, closure = role-limit, disjoint.  The cascade sits exactly
      on the finitization boundary -- Element at every level, role-limit only at the closure.

   HONEST SCOPE.  This CLASSIFIES the cascade as an H1 instance and proves the Element-side facts
   (conservation, monotone non-negative finite enstrophy) plus the unboundedness of the scale tower
   (the role-limit lives only in the closure).  It does NOT decide boundedness of the enstrophy in the
   closure -- that IS the alpha=2 wall, located here, NOT crossed.  Relocate, not cross.

   Elements: the truncation index N; the monotone enstrophy process Omega_N; the two H1 sides.
   Roles:    Omega_N = a monotone process (the wall-carrier); the H1 sides (TruncationElement /
             ClosureRoleLimit).
   Rules:    truncation => Element (conserved, monotone finite enstrophy); closure => role-limit
             (unbounded tower; boundedness = the open wall); the two sides are disjoint (H1 sorts).

   ============ E/R/R разбор ============
     Rules (L5): классификация: усечение => Element, замыкание => role-limit, дизъюнктны; энстрофия не убывает.
     Roles (L4): энстрофия Omega_N = монотонный процесс (носитель стены); стороны H1.
     Elements  : индекс усечения N; процесс Omega_N; две стороны H1.
   ДИАГНОСТИКА (P4): каскад ЕСТЬ инстанс H1 -- Element на каждом конечном N, role-limit только в замыкании.
   Энстрофия = монотонный процесс; ограниченность-в-замыкании = стена alpha=2 = role-limit, не решена.
   Локализуем, НЕ пересекаем. Родная математика каскадов = H1.

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith QArith.Qabs ZArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ScaleHierarchyTransfer.
From ToS Require Import foundation.ShellCascadeNS.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Element side: the enstrophy is a monotone, non-negative finite process *)
(* ===================================================================== *)

Lemma kdyad_nonneg : forall n, 0 <= kdyad n.
Proof.
  intro n. unfold kdyad. change 0 with (inject_Z 0).
  rewrite <- Zle_Qle. apply Nat2Z.is_nonneg.
Qed.

Lemma wdyad_nonneg : forall n, 0 <= wdyad n.
Proof. intro n. unfold wdyad. apply Qmult_le_0_compat; apply kdyad_nonneg. Qed.

(** Squares are non-negative over Q (local, avoids version-specific lemma names). *)
Lemma q_sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. destruct (Qlt_le_dec x 0) as [H|H].
  - apply Qlt_le_weak in H.
    assert (Hn : 0 <= - x) by lra.
    pose proof (Qmult_le_0_compat (- x) (- x) Hn Hn) as Hp.
    assert (Heq : (- x) * (- x) == x * x) by ring.
    rewrite Heq in Hp. exact Hp.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma shell_enstrophy_nonneg : forall a n, 0 <= shell_enstrophy a n.
Proof.
  intros a n. unfold shell_enstrophy.
  apply Qmult_le_0_compat; [ apply wdyad_nonneg | apply q_sq_nonneg ].
Qed.

(** ★ The truncated enstrophy is NON-NEGATIVE at every truncation. *)
Lemma total_ns_enstrophy_nonneg : forall a N, 0 <= total_ns_enstrophy a N.
Proof.
  intros a N. unfold total_ns_enstrophy. induction N as [|n IH].
  - simpl. lra.
  - rewrite shell_sum_S. pose proof (shell_enstrophy_nonneg a n). lra.
Qed.

(** ★ The truncated enstrophy is a MONOTONE (non-decreasing) process in the truncation N:
    each new shell adds a non-negative term.  Omega_N <= Omega_{N+1}. *)
Theorem enstrophy_monotone : forall a N,
  total_ns_enstrophy a N <= total_ns_enstrophy a (S N).
Proof.
  intros a N. unfold total_ns_enstrophy. rewrite shell_sum_S.
  pose proof (shell_enstrophy_nonneg a N). lra.
Qed.

(** Concrete: the witness enstrophy is monotone (an instance of the general theorem). *)
Example enstrophy_monotone_witness :
  total_ns_enstrophy a_ex 2 <= total_ns_enstrophy a_ex 3.
Proof. apply enstrophy_monotone. Qed.

(* ===================================================================== *)
(*  The H1 finitization boundary of the cascade                            *)
(* ===================================================================== *)

(** The two sides of the cascade's finitization boundary. *)
Inductive CascadeSide := TruncationElement | ClosureRoleLimit.

(** Every finite truncation N is on the Element side (conserved, monotone finite enstrophy). *)
Definition truncation_side (N : nat) : CascadeSide := TruncationElement.
(** The closure N -> infinity is on the role-limit side (unbounded tower; boundedness = the open wall). *)
Definition closure_side : CascadeSide := ClosureRoleLimit.

(** ★ H1 SORTS: the truncation (Element) and the closure (role-limit) are DISJOINT.
    The cascade is Element at every finite level; the wall lives only at the closure. *)
Lemma h1_cascade_disjoint : forall N, truncation_side N <> closure_side.
Proof. intro N. unfold truncation_side, closure_side. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the cascade as an H1 instance (Element at N, role-limit at oo) *)
(* ===================================================================== *)

(** The finitization boundary of the turbulent cascade:
      (Element, finite N)  a closed cascade conserves energy; the enstrophy is monotone and
                           non-negative -- a finite rational process at every truncation;
      (role-limit, closure) the dyadic scale tower 2^n is unbounded, so the monotone enstrophy runs
                           over an unbounded hierarchy -- its boundedness in the closure is the alpha=2
                           wall, located but NOT crossed;
      (H1)                 truncation (Element) and closure (role-limit) are disjoint.
    The turbulent cascade IS an instance of the H1 finitization boundary: Element at every level,
    role-limit only at the closure.  This closes the cascade unit (primitive + instance + boundary)
    as native cascade mathematics over Q. *)
Theorem cascade_finitization_boundary :
  (forall Pi N, closed_cascade Pi N -> shell_sum (cascade_injection Pi) N == 0)
  /\ (forall a N, total_ns_enstrophy a N <= total_ns_enstrophy a (S N))
  /\ (forall a N, 0 <= total_ns_enstrophy a N)
  /\ (forall M, exists n, (M < Nat.pow 2 n)%nat)
  /\ (forall N, truncation_side N <> closure_side).
Proof.
  split; [exact closed_cascade_conserves |].
  split; [exact enstrophy_monotone |].
  split; [exact total_ns_enstrophy_nonneg |].
  split; [exact cascade_scales_unbounded |].
  exact h1_cascade_disjoint.
Qed.
