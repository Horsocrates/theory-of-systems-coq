(** * ShellCascadeNS.v — FIRST INSTANCE of the inter-level transfer primitive
      (foundation/ScaleHierarchyTransfer.v): the Navier-Stokes turbulent energy cascade as a DYADIC
      SHELL MODEL over Q.  Shells sit at dyadic scales k_n = 2^n; energy flows between adjacent shells
      (the cascade); the internal transfer CONSERVES total energy (Element, inherited from the
      primitive); and the supercritical enstrophy weight w_n = k_n^2 = 4^n together with the unbounded
      scale ladder LOCATE the alpha=2 wall as the role-limit of the closure N -> infinity.

   -- Dyadic ladder: k_n = 2^n (kdyad), so k_{n+1} = 2 k_n; enstrophy weight w_n = k_n^2 = 4^n, so
      w_{n+1} = 4 w_n.  The enstrophy Omega = sum w_n a_n^2 is the DANGEROUS quantity (vortex-stretching
      weight) -- finite rational at each truncation N (Element).
   -- Conservation (Element): a closed dyadic shell cascade conserves total energy exactly -- inherited
      from closed_cascade_conserves.  The nonlinear shell coupling redistributes energy across scales
      without creating/destroying it (the shell-model analogue of B_antisym / triple_sum = 0).
   -- The wall (role-limit): the cascade reaches EVERY scale (2^n -> infinity) and the enstrophy weight
      4^n grows without bound; whether the amplitudes decay fast enough to keep Omega bounded as
      N -> infinity is the supercritical race -- the alpha=2 wall (cf. foundation/NSBoundDescent.v),
      i.e. the role-limit of the closure.  Located here, NOT crossed.

   HONEST SCOPE.  A faithful Element-side shell model: dyadic scales over Q, exact energy conservation
   of the internal cascade, finite rational energy/enstrophy at every truncation.  It RELOCATES the
   alpha=2 wall as the N -> infinity closure of the scale hierarchy; it does NOT cross it (boundedness
   of the enstrophy in the closure is the open problem).  Relocate, not cross.  The conservation is
   GENERIC (any closed flux conserves); the NS-specific content is the dyadic ladder + the supercritical
   4^n weight + the unbounded scales locating the wall.

   Elements: shell amplitudes a_n in Q; dyadic scale k_n = 2^n; enstrophy weight w_n = 4^n; a concrete
             4-shell witness.
   Roles:    the dyadic shell ladder (k_n) = the scale roles; w_n = k_n^2 = the enstrophy/dissipation
             weight (the dangerous role); the cascade flux = inter-shell transfer.
   Rules:    cascade conserves energy (closed => 0, inherited); ladder k_{n+1}=2k_n, w_{n+1}=4w_n;
             scales unbounded => the closure N->oo is the supercritical wall (role-limit).

   ============ E/R/R разбор ============
     Rules (L5): каскад = межоболочечный перенос (инстанс cascade_injection); сохранение (закрытый=>0)
                 наследуется; дядическая лестница k_{n+1}=2k_n, w_{n+1}=4w_n.
     Roles (L4): дядические оболочки k_n=2^n (масштаб-лестница); w_n=k_n^2 -- вес энстрофии (опасная роль).
     Elements  : амплитуды a_n in Q; масштаб 2^n; вес 4^n; конкретный 4-оболочечный свидетель.
   ДИАГНОСТИКА (P4): каскад = процесс; конечн. N = Element (сохранённая энергия + конечная энстрофия);
   неограниченные масштабы (2^n->oo, вес 4^n->oo) => замыкание N->oo = supercritical-стена alpha=2
   (NSBoundDescent) = role-limit. Локализуем, НЕ пересекаем. Нагрузка примитива -> реальная турбулентность.

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ScaleHierarchyTransfer.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The dyadic scale ladder of the turbulent cascade: k_n = 2^n            *)
(* ===================================================================== *)

Definition kdyad (n : nat) : Q := inject_Z (Z.of_nat (Nat.pow 2 n)).

(** ★ Dyadic ladder: each shell's scale is double the previous -- k_{n+1} = 2 k_n. *)
Lemma kdyad_doubles : forall n, kdyad (S n) == 2 * kdyad n.
Proof.
  intro n. unfold kdyad.
  replace (Nat.pow 2 (S n)) with (2 * Nat.pow 2 n)%nat by reflexivity.
  rewrite Nat2Z.inj_mul, inject_Z_mult.
  assert (Hc : inject_Z (Z.of_nat 2) == 2) by (vm_compute; reflexivity).
  rewrite Hc. reflexivity.
Qed.

(** Enstrophy / dissipation weight w_n = k_n^2 = 4^n -- the DANGEROUS (vortex-stretching) weight. *)
Definition wdyad (n : nat) : Q := kdyad n * kdyad n.

(** ★ The enstrophy weight quadruples each shell -- w_{n+1} = 4 w_n (supercritical growth). *)
Lemma wdyad_quadruples : forall n, wdyad (S n) == 4 * wdyad n.
Proof. intro n. unfold wdyad. rewrite !kdyad_doubles. ring. Qed.

(* ===================================================================== *)
(*  The scales run to infinity: the cascade reaches every shell            *)
(* ===================================================================== *)

Lemma pow2_ge_succ : forall n, (S n <= Nat.pow 2 n)%nat.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - replace (Nat.pow 2 (S n)) with (2 * Nat.pow 2 n)%nat by reflexivity. lia.
Qed.

(** ★ The cascade reaches EVERY scale: for any bound M there is a shell with k_n = 2^n > M.
    The hierarchy is unbounded -- its closure N -> infinity is the role-limit. *)
Lemma cascade_scales_unbounded : forall M, exists n, (M < Nat.pow 2 n)%nat.
Proof. intro M. exists (S M). pose proof (pow2_ge_succ (S M)). lia. Qed.

(* ===================================================================== *)
(*  Enstrophy: the dangerous quantity, finite rational at each truncation  *)
(* ===================================================================== *)

Definition shell_enstrophy (a : nat -> Q) (n : nat) : Q := wdyad n * (a n * a n).
Definition total_ns_enstrophy (a : nat -> Q) (N : nat) : Q := shell_sum (shell_enstrophy a) N.

(* ===================================================================== *)
(*  Concrete 4-shell witness (Kolmogorov-flat enstrophy spectrum)          *)
(* ===================================================================== *)

(** Decaying amplitudes a_n = 1, 1/2, 1/4, 0 (then 0). *)
Definition a_ex (n : nat) : Q :=
  match n with O => 1 | S O => 1#2 | S (S O) => 1#4 | _ => 0 end.

(** A closed cascade current: Pi = 0, 1/4, 1/8, 0 (Pi 0 = 0 and Pi 3 = 0, so closed at N=3). *)
Definition Pi_ns (n : nat) : Q :=
  match n with O => 0 | S O => 1#4 | S (S O) => 1#8 | _ => 0 end.

(** Witness 1: the closed shell cascade conserves total energy (0 net injection). *)
Example ns_witness_conserves : shell_sum (cascade_injection Pi_ns) 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Witness 2: the total energy of the truncation is a finite rational, 21/16. *)
Example ns_witness_energy : total_energy a_ex 4 == 21#16.
Proof. vm_compute. reflexivity. Qed.

(** Witness 3: the enstrophy is finite (Element) -- and FLAT: exactly 1 per shell => 3 total.
    The flat (marginal) enstrophy spectrum is the supercritical edge of the alpha=2 wall. *)
Example ns_witness_enstrophy : total_ns_enstrophy a_ex 4 == 3.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the NS cascade as a dyadic shell hierarchy over Q            *)
(* ===================================================================== *)

(** The shell-model instance of the inter-level transfer primitive:
      (ladder)     dyadic scales double (k_{n+1}=2k_n), enstrophy weight quadruples (w_{n+1}=4w_n);
      (Element)    a closed dyadic shell cascade conserves total energy exactly (inherited);
      (role-limit) the cascade reaches every scale (2^n unbounded) -- the closure N -> infinity, with
                   weight 4^n, is the supercritical alpha=2 wall, located but NOT crossed.
    The level hierarchy's inter-level flux, instantiated to real turbulence. *)
Theorem shell_cascade_ns :
  (forall n, kdyad (S n) == 2 * kdyad n)
  /\ (forall n, wdyad (S n) == 4 * wdyad n)
  /\ (forall Pi N, closed_cascade Pi N -> shell_sum (cascade_injection Pi) N == 0)
  /\ (forall M, exists n, (M < Nat.pow 2 n)%nat).
Proof.
  split; [exact kdyad_doubles |].
  split; [exact wdyad_quadruples |].
  split; [exact closed_cascade_conserves |].
  exact cascade_scales_unbounded.
Qed.
