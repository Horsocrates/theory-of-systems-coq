(** * ScaleHierarchyTransfer.v — the MISSING PRIMITIVE: inter-level energy FLUX on a finite scale
      hierarchy over Q.  ToS has a level ORDER (level_lt, level_strong_induction) but, until now, NO
      inter-level transfer/flux of any kind (SystemMorphism.v: "cross-level = future work"; Roles.v:
      "Roles don't cross levels").  A cascade is exactly inter-level flux on a hierarchy of levels.
      This file gives the level hierarchy its missing PAYLOAD: a flux between adjacent shells and the
      conservation law it obeys, derived (0 axioms) by telescoping -- the discrete continuity equation.

   -- Shells n = 0..N-1 (a finite hierarchy), amplitude a_n in Q, dyadic scale k_n = 2^n.
   -- The inter-shell current Pi : nat -> Q ("Pi n" = energy current flowing UP into shell n).  The net
      energy injected into shell n by the cascade is the flux divergence  Pi n - Pi (S n)
      (in from below at interface n, out to above at interface n+1).
   -- CONSERVATION (telescoping continuity): the total injection over shells 0..N-1 collapses to the
      boundary currents,  sum (Pi n - Pi (S n)) = Pi 0 - Pi N.  A CLOSED cascade (no boundary current,
      Pi 0 = Pi N = 0) injects ZERO net energy: internal transfer conserves total energy exactly.
   -- The OPEN top current Pi N is the energy flowing to scales ABOVE the truncation -- as N -> infinity
      this is the anomalous-dissipation / wall direction (role-limit).

   HONEST SCOPE.  This is the reusable inter-level FLUX primitive the level order lacked -- finite,
   rational, 0-axiom.  It RELOCATES the cascade wall (alpha=2 / anomalous dissipation) as the open top
   current toward the role-limit N -> infinity; it does NOT cross it (the closure / supercritical sum is
   the open problem, cf. foundation/NSBoundDescent.v).  Relocate, not cross.

   Elements: shell amplitudes a_n in Q; the inter-shell current Pi; the flux divergence; finite sums.
   Roles:    shells n=0..N-1 = the scale ladder (k_n = 2^n); interfaces = coupling sites; Pi = the
             inter-level current; each shell = an E/R/R system.
   Rules:    conservation = telescoping continuity: net injection sums to the boundary currents
             Pi 0 - Pi N; a closed cascade conserves total energy (= 0 net injection).

   ============ E/R/R разбор ============
     Rules (L5): правило переноса/сохранения: вброс в оболочку n = Pi n - Pi(S n) (дивергенция);
                 суммарный вброс ТЕЛЕСКОПИРУЕТ к граничным токам Pi 0 - Pi N; закрытый каскад => 0.
     Roles (L4): оболочки n=0..N-1 -- ролевая лестница (масштаб 2^n); интерфейсы -- сцепления; Pi -- ток.
     Elements  : амплитуды a_n in Q; ток Pi; дивергенция; конечные суммы.
   ДИАГНОСТИКА (P4): каскад = ПРОЦЕСС (конечен на каждом N = Element, верхний ток Pi N = ток к role-limit
   N->oo). Впервые level-иерархия получает НАГРУЗКУ (поток+сохранение). Честно: перелокализует стену
   (верхний ток к замыканию), НЕ пересекает. Зеркало level_lt/sum_fd -- родня, не импорт (робастность).

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Shells: a finite hierarchy indexed by depth n : nat (mirrors level)    *)
(* ===================================================================== *)

(** Dyadic scale ladder: shell n sits at scale k_n = 2^n. *)
Definition shell_scale (n : nat) : nat := Nat.pow 2 n.

(** Summation over shells 0..N-1 (the integration over the hierarchy; mirrors sum_Q_ns). *)
Fixpoint shell_sum (f : nat -> Q) (N : nat) : Q :=
  match N with O => 0 | S k => shell_sum f k + f k end.

Lemma shell_sum_S : forall f N, shell_sum f (S N) == shell_sum f N + f N.
Proof. intros. reflexivity. Qed.

(** Extensionality of the hierarchy sum (reusable for the instances). *)
Lemma shell_sum_congr : forall (f g : nat -> Q) N,
  (forall i, f i == g i) -> shell_sum f N == shell_sum g N.
Proof.
  intros f g N H. induction N as [|n IH].
  - reflexivity.
  - rewrite !shell_sum_S. rewrite IH. rewrite (H n). reflexivity.
Qed.

(** ★ The telescoping identity -- the discrete continuity / summation-by-parts core,
    the GENERATOR of every conservation law on the hierarchy (mirrors sum_fd). *)
Lemma shell_telescope : forall (g : nat -> Q) N,
  shell_sum (fun n => g (S n) - g n) N == g N - g 0%nat.
Proof.
  intros g N. induction N as [|n IH].
  - simpl. ring.
  - rewrite shell_sum_S. cbv beta. rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  The MISSING PRIMITIVE: inter-shell energy flux + its conservation law  *)
(* ===================================================================== *)

(** Energy stored at shell n, and total energy of shells 0..N-1. *)
Definition shell_energy (a : nat -> Q) (n : nat) : Q := a n * a n.
Definition total_energy (a : nat -> Q) (N : nat) : Q := shell_sum (shell_energy a) N.

(** ★ Net energy injected into shell n by the cascade = the flux divergence Pi n - Pi (S n)
    (current in from below at interface n minus current out to above at interface n+1).
    THIS is the inter-level transfer ToS's level order previously lacked. *)
Definition cascade_injection (Pi : nat -> Q) (n : nat) : Q := Pi n - Pi (S n).

(** ★ TELESCOPING CONTINUITY: the total energy injected by the cascade over shells 0..N-1 collapses
    to the boundary currents Pi 0 - Pi N.  Internal transfer cancels; only the boundaries count. *)
Theorem cascade_total_injection : forall (Pi : nat -> Q) N,
  shell_sum (cascade_injection Pi) N == Pi 0%nat - Pi N.
Proof.
  intros Pi N. induction N as [|n IH].
  - simpl. ring.
  - rewrite shell_sum_S. rewrite IH. unfold cascade_injection. ring.
Qed.

(** A cascade is CLOSED (energy-conserving) if no current crosses the outer boundaries:
    nothing enters the bottom (Pi 0 = 0) and nothing leaves the top (Pi N = 0). *)
Definition closed_cascade (Pi : nat -> Q) (N : nat) : Prop :=
  Pi 0%nat == 0 /\ Pi N == 0.

(** ★ CONSERVATION: a closed cascade injects ZERO net energy -- total energy is conserved.
    The flux only MOVES energy between shells; nothing is created or destroyed internally. *)
Theorem closed_cascade_conserves : forall (Pi : nat -> Q) N,
  closed_cascade Pi N ->
  shell_sum (cascade_injection Pi) N == 0.
Proof.
  intros Pi N [H0 HN]. rewrite cascade_total_injection. rewrite H0, HN. ring.
Qed.

(** ★ The role-limit direction: for a forcing-free cascade (Pi 0 = 0) the truncated hierarchy loses
    exactly the top current Pi N to scales ABOVE the truncation.  As N -> infinity, Pi N is the flux
    toward the role-limit (anomalous dissipation / the alpha=2 wall) -- located here, NOT crossed. *)
Lemma cascade_top_flux_is_loss : forall (Pi : nat -> Q) N,
  Pi 0%nat == 0 ->
  shell_sum (cascade_injection Pi) N == - Pi N.
Proof.
  intros Pi N H0. rewrite cascade_total_injection. rewrite H0. ring.
Qed.

(** Concrete witness: a 3-shell closed cascade (currents 0, 1/2, 1/3, 0) conserves energy exactly. *)
Definition Pi_ex (n : nat) : Q := match n with O => 0 | S O => 1#2 | S (S O) => 1#3 | _ => 0 end.
Example closed_cascade_witness : shell_sum (cascade_injection Pi_ex) 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the inter-level transfer primitive (the level order's payload) *)
(* ===================================================================== *)

(** The scale-hierarchy transfer primitive -- the inter-level FLUX the level order lacked:
      (telescope) the inter-shell injection telescopes to the boundary currents Pi 0 - Pi N;
      (closed)    a closed cascade (no boundary current) conserves total energy exactly;
      (role-limit) a forcing-free truncation loses exactly the top current Pi N to the scales above --
                  the flux toward the role-limit N -> infinity, located but NOT crossed.
    This is the level hierarchy finally carrying a payload (energy, with a conservation law). *)
Theorem scale_hierarchy_transfer : forall (Pi : nat -> Q) N,
  (shell_sum (cascade_injection Pi) N == Pi 0%nat - Pi N)
  /\ (closed_cascade Pi N -> shell_sum (cascade_injection Pi) N == 0)
  /\ (Pi 0%nat == 0 -> shell_sum (cascade_injection Pi) N == - Pi N).
Proof.
  intros Pi N. split; [| split].
  - exact (cascade_total_injection Pi N).
  - exact (closed_cascade_conserves Pi N).
  - exact (cascade_top_flux_is_loss Pi N).
Qed.
