(** * ProcessEVT.v — Extreme Value Theorem as Process Construction
    Elements: grid values M(n) = max of f on the grid of n+1 cells, and
              grid maximizers x*(n) = argmax on that grid
    Roles:    M -- Cauchy process approaching the supremum;
              x* -- a process in [a,b], NOT Cauchy in general
              (EVT_ArgmaxNotCauchy.v)
    Rules:    grid refinement — one more cell at each stage, keep the max
    Status:   complete
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS EVT — Extreme Value Theorem as Process Construction        *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: grid values M(n) and grid maximizers x*(n)                   *)
(*    Roles:    M -- Cauchy process approaching the supremum;                *)
(*              x* -- a process in [a,b], not Cauchy in general              *)
(*    Rules:    grid refinement — evaluate f at grid, keep max               *)
(*                                                                            *)
(*  STATUS: 10 Qed, 0 Admitted                                              *)
(*  AXIOMS: none (EVT_ERR itself needs no classic since Nov 2026)            *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import EVT_ERR.

(* ================================================================== *)
(*  Part I: Cauchy Compatibility                                       *)
(* ================================================================== *)

(** EVT_ERR.is_Cauchy uses (m > N), ProcessCore uses (N <= m) *)
Lemma evt_cauchy_to_process : forall R,
  EVT_ERR.is_Cauchy R -> ProcessCore.is_Cauchy R.
Proof.
  intros R Hgt eps Heps.
  assert (Hgt' : eps > 0) by lra.
  destruct (Hgt eps Hgt') as [N HN].
  exists (S N). intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma process_cauchy_to_evt : forall R,
  ProcessCore.is_Cauchy R -> EVT_ERR.is_Cauchy R.
Proof.
  intros R Hle eps Heps.
  assert (Hlt : 0 < eps) by lra.
  destruct (Hle eps Hlt) as [N HN].
  exists N. intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma evt_cauchy_compat : forall R,
  EVT_ERR.is_Cauchy R <-> ProcessCore.is_Cauchy R.
Proof.
  intro R. split; [apply evt_cauchy_to_process | apply process_cauchy_to_evt].
Qed.

(* ================================================================== *)
(*  Part II: EVT in ProcessCore Language                               *)
(* ================================================================== *)

(** The sup_process is Cauchy (ProcessCore version) *)
Theorem sup_process_cauchy : forall f a b,
  a < b ->
  EVT_ERR.uniformly_continuous_on f a b ->
  ProcessCore.is_Cauchy (sup_process f a b).
Proof.
  intros f a b Hab Hcont.
  apply evt_cauchy_to_process.
  exact (sup_process_is_Cauchy f a b Hab Hcont).
Qed.

(** The argmax_process stays in [a,b] *)
Lemma argmax_in_interval_process : forall f a b,
  a < b ->
  ProcessCore.in_interval a b (argmax_process f a b).
Proof.
  intros f a b Hab n.
  apply argmax_in_interval.
  - lia.
  - lra.
Qed.

(** EVT restated with ProcessCore types -- the whole content of EVT_complete:
    a Cauchy process of values M, a process of points c inside [a,b] where
    the values are attained, and the majorant property: every f x, x in
    [a,b], is eventually below M n + eps.
    Until Nov 2026 the conclusion did not mention f. *)
Theorem process_EVT : forall (f : ContinuousFunction) (a b : Q),
  a < b ->
  EVT_ERR.uniformly_continuous_on f a b ->
  exists (M c : RealProcess),
    ProcessCore.is_Cauchy M /\
    ProcessCore.in_interval a b c /\
    (forall n : nat, f (c n) == M n) /\
    (forall x : Q, a <= x <= b ->
       forall eps : Q, 0 < eps ->
         exists N : nat, forall n : nat, (N <= n)%nat -> f x <= M n + eps).
Proof.
  intros f a b Hab Hcont.
  destruct (EVT_complete f a b Hab Hcont) as [M [c [HM [Hc [Hfc Hle]]]]].
  exists M, c. split; [| split; [| split]].
  - apply evt_cauchy_to_process. exact HM.
  - intro n. exact (Hc n).
  - intro n. exact (Hfc n).
  - intros x Hx eps Heps.
    destruct (Hle x Hx eps Heps) as [N HN].
    exists (S N). intros n Hn. apply HN. lia.
Qed.

(* ================================================================== *)
(*  Part III: E/R/R Annotation                                         *)
(* ================================================================== *)

(** The EVT pattern, about the processes BY NAME: the grid maxima form a
    Cauchy process, the grid maximizers stay in [a,b], and the n-th value
    bounds f on the whole n-th grid.
    Until Nov 2026: [exists sup_proc, is_Cauchy sup_proc]. *)
Theorem evt_is_process_construction : forall f a b,
  a < b -> EVT_ERR.uniformly_continuous_on f a b ->
    ProcessCore.is_Cauchy (sup_process f a b) /\
    ProcessCore.in_interval a b (argmax_process f a b) /\
    (forall n y, List.In y (grid_list a b (S n)) -> f y <= sup_process f a b n).
Proof.
  intros f a b Hab Hcont. split; [| split].
  - apply sup_process_cauchy; assumption.
  - apply argmax_in_interval_process; assumption.
  - intros n y Hy. unfold sup_process. apply grid_value_le_max; [lia | exact Hy].
Qed.

(** The rate of the EVT process.  Stage n takes the grid of n+1 cells, its
    step is (b-a)/(n+1): there is NO fixed ratio between stages (the constant
    [evt_convergence_rate := 1 # 2], tied to nothing, stood here until
    Nov 2026).  The actual estimate, for a function with Lipschitz constant K:
    the n-th value is within K * (b-a)/(n+1) of every value of f on [a,b]. *)
Theorem evt_lipschitz_rate : forall f a b n x K,
  a < b -> a <= x <= b -> 0 <= K ->
  (forall y z, a <= y <= b -> a <= z <= b -> Qabs (f y - f z) <= K * Qabs (y - z)) ->
  f x <= sup_process f a b n + K * ((b - a) / inject_Z (Z.of_nat (S n))).
Proof.
  intros f a b n x K Hab Hx HK Hlip. unfold sup_process.
  assert (Hn : (S n > 0)%nat) by lia.
  destruct (near_grid_point a b (S n) x Hab Hn Hx) as [k [Hkn Hdist]].
  assert (Hgp_in : a <= grid_point a b (S n) k <= b).
  { apply grid_point_in_interval; [apply Qlt_le_weak; exact Hab | exact Hkn | exact Hn]. }
  pose proof (Hlip x (grid_point a b (S n) k) Hx Hgp_in) as Hf.
  assert (Hgp_le_max : f (grid_point a b (S n) k) <= max_on_grid f a b (S n)).
  { apply grid_value_le_max; [exact Hn |]. apply grid_point_in_list; [exact Hn | exact Hkn]. }
  assert (Hmul : K * Qabs (x - grid_point a b (S n) k) <= K * ((b - a) / inject_Z (Z.of_nat (S n)))).
  { rewrite (Qmult_comm K (Qabs (x - grid_point a b (S n) k))).
    rewrite (Qmult_comm K ((b - a) / inject_Z (Z.of_nat (S n)))).
    apply Qmult_le_compat_r; assumption. }
  apply Qabs_Qle_condition in Hf. destruct Hf as [_ Hhi].
  lra.
Qed.

(** Where 1/2 does live on a grid: the number of cells doubled -- the step halved. *)
Lemma evt_step_halves_on_doubling : forall a b n,
  (b - a) / inject_Z (Z.of_nat (S (2 * n + 1))) ==
  (1 # 2) * ((b - a) / inject_Z (Z.of_nat (S n))).
Proof.
  intros a b n.
  assert (E : inject_Z (Z.of_nat (S (2 * n + 1))) == 2 * inject_Z (Z.of_nat (S n))).
  { unfold Qeq, inject_Z, Qmult. simpl Qnum. simpl Qden. lia. }
  rewrite E. field.
  intro H. assert (Hp : 0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia). lra.
Qed.

(** Grid refinement: at depth n, we have (n+1) sample points *)
(** Finer grid => better approximation to supremum *)
(** Under P4: the supremum IS the process sup_process, not its limit *)
(** Every stage gives a valid approximation: once the step of the n-th grid
    is below the modulus delta that uniform continuity gives for eps, the
    n-th value is within eps of every f x on [a,b].  No completed supremum.
    Until Nov 2026: [forall q, is_Cauchy (const_process q)]. *)
Theorem evt_p4_interpretation : forall f a b n x delta eps,
  a < b -> EVT_ERR.uniformly_continuous_on f a b ->
  a <= x <= b -> eps > 0 ->
  (b - a) / inject_Z (Z.of_nat (S n)) < delta ->
  (forall y z, a <= y <= b -> a <= z <= b -> Qabs (y - z) < delta -> Qabs (f y - f z) < eps) ->
  f x < sup_process f a b n + eps.
Proof.
  intros f a b n x delta eps Hab Hcont Hx Heps Hstep Hmod.
  unfold sup_process.
  apply (f_bounded_by_grid_max f a b (S n) x delta); try assumption. lia.
Qed.
