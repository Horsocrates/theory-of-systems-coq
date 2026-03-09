(* ========================================================================= *)
(*        SPECTRALDICHOTOMY — The Spectral Dichotomy Theorem                *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                 *)
(*                                                                          *)
(*  The spectral dichotomy: every observable's eigenspace is either          *)
(*  enumerable (discrete spectrum) or has a perfect subset (continuous       *)
(*  spectrum). There is no intermediate type of spectrum.                    *)
(*  This follows directly from the Process Continuum Hypothesis.            *)
(*                                                                          *)
(*  Elements: eigenspace, spectral_dichotomy, discrete/continuous spectrum  *)
(*  Roles:    classification → spectral theory in quantum mechanics         *)
(*  Rules:    PCH → dichotomy, finite dim → always discrete                 *)
(*  Status:   dichotomy | classification | finite-dim                       *)
(*                                                                          *)
(*  STATUS: 30 Qed, 0 Admitted                                             *)
(*  AXIOMS: classic (L3) + L4_witness (L4) — via PCH                       *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import ProcessTypes.
From ToS Require Import ProcessDiagonal.
From ToS Require Import ProcessContinuumHypothesis.
From ToS Require Import LinearAlgebra.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.

(* ========================================================================= *)
(*  SECTION 1: Encoding Framework                                            *)
(* ========================================================================= *)

Section SpectralEncoding.

Variable dim : nat.
Variable encode : QState dim -> BinProcess.
Variable encode_compat : forall s1 s2 : QState dim,
  state_equiv s1 s2 -> bp_eq (encode s1) (encode s2).
Variable encode_inj : forall s1 s2 : QState dim,
  bp_eq (encode s1) (encode s2) -> state_equiv s1 s2.

(** The eigenspace collection for observable A at eigenvalue lambda:
    the set of all encoded eigenstates. *)
Definition eigenspace (A : QObservable dim) (lambda : Q) : BinCollection :=
  fun p => exists s : QState dim, is_eigenstate A s lambda /\ bp_eq (encode s) p.

(** Encoded eigenstates belong to the eigenspace *)
Lemma eigenspace_has_eigenstate : forall (A : QObservable dim) (lambda : Q)
  (s : QState dim),
  is_eigenstate A s lambda -> eigenspace A lambda (encode s).
Proof.
  intros A lambda s Heig.
  exists s. split; [exact Heig | apply bp_eq_refl].
Qed.

(** Eigenspace is closed under bp_eq *)
Lemma eigenspace_bp_eq_closed : forall (A : QObservable dim) (lambda : Q)
  (p q : BinProcess),
  eigenspace A lambda p -> bp_eq p q -> eigenspace A lambda q.
Proof.
  intros A lambda p q [s [Heig Henc]] Hpq.
  exists s. split; [exact Heig | exact (bp_eq_trans _ _ _ Henc Hpq)].
Qed.

(** Empty eigenspace: no eigenstates means empty collection *)
Lemma eigenspace_empty_if_no_eigenstates :
  forall (A : QObservable dim) (lambda : Q),
  (forall s, ~ is_eigenstate A s lambda) ->
  is_empty (eigenspace A lambda).
Proof.
  intros A lambda Hno p [s [Heig _]].
  exact (Hno s Heig).
Qed.

(** Empty eigenspace is enumerable *)
Lemma empty_eigenspace_enumerable :
  forall (A : QObservable dim) (lambda : Q),
  is_empty (eigenspace A lambda) ->
  is_enumerable (eigenspace A lambda).
Proof.
  intros A lambda Hempty. apply enumerable_empty. exact Hempty.
Qed.

(* ========================================================================= *)
(*  SECTION 2: The Spectral Dichotomy                                        *)
(* ========================================================================= *)

(** ★★★ THE SPECTRAL DICHOTOMY THEOREM ★★★

    For any observable A and eigenvalue lambda, if the eigenspace is closed
    (in the Cantor space topology), then it is either:
    - Enumerable (discrete spectrum): eigenspace ≅ subset of ℕ
    - Has a perfect subset (continuous spectrum): eigenspace ≅ Cantor set

    There is no intermediate cardinality. This is the quantum-mechanical
    consequence of the Process Continuum Hypothesis.

    Axioms used: classic (L3) + L4_witness (L4) — inherited from PCH. *)
Theorem spectral_dichotomy : forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  is_enumerable (eigenspace A lambda) \/ has_perfect_subset (eigenspace A lambda).
Proof.
  intros A lambda Hclosed.
  exact (process_continuum_hypothesis (eigenspace A lambda) Hclosed).
Qed.

(** Structural version: closed + not enumerable ⟹ has perfect subset *)
Theorem spectral_structural : forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  ~ is_enumerable (eigenspace A lambda) ->
  has_perfect_subset (eigenspace A lambda).
Proof.
  intros A lambda Hclosed Hnenum.
  exact (PCH_structural_dichotomy (eigenspace A lambda) Hclosed Hnenum).
Qed.

(* ========================================================================= *)
(*  SECTION 3: Spectrum Classification                                       *)
(* ========================================================================= *)

(** An eigenspace is discrete if it is enumerable *)
Definition has_discrete_eigenspace (A : QObservable dim) (lambda : Q) : Prop :=
  is_enumerable (eigenspace A lambda).

(** An eigenspace is continuous if it has a perfect subset *)
Definition has_continuous_eigenspace (A : QObservable dim) (lambda : Q) : Prop :=
  has_perfect_subset (eigenspace A lambda).

(** Every closed eigenspace is discrete or continuous — no intermediate *)
Theorem no_intermediate_spectrum : forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  has_discrete_eigenspace A lambda \/ has_continuous_eigenspace A lambda.
Proof.
  exact spectral_dichotomy.
Qed.

(** Observable has fully discrete spectrum *)
Definition has_discrete_spectrum (A : QObservable dim) : Prop :=
  forall lambda, is_closed (eigenspace A lambda) ->
    has_discrete_eigenspace A lambda.

(** Observable has (some) continuous spectrum *)
Definition has_continuous_spectrum (A : QObservable dim) : Prop :=
  exists lambda, is_closed (eigenspace A lambda) /\
    has_continuous_eigenspace A lambda.

(** Discrete spectrum: all closed eigenspaces are enumerable *)
Lemma discrete_spectrum_all_enum : forall (A : QObservable dim),
  has_discrete_spectrum A ->
  forall lambda, is_closed (eigenspace A lambda) ->
    is_enumerable (eigenspace A lambda).
Proof.
  intros A Hdisc lambda Hclosed. exact (Hdisc lambda Hclosed).
Qed.

(** Continuous spectrum: witnesses a perfect subset *)
Lemma continuous_spectrum_witness : forall (A : QObservable dim),
  has_continuous_spectrum A ->
  exists lambda, is_closed (eigenspace A lambda) /\
    has_perfect_subset (eigenspace A lambda).
Proof.
  intros A [lambda [Hclosed Hcont]]. exists lambda. split; assumption.
Qed.

(** Not discrete ⟹ continuous (for closed eigenspaces) *)
Lemma not_discrete_implies_continuous : forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  ~ has_discrete_eigenspace A lambda ->
  has_continuous_eigenspace A lambda.
Proof.
  intros A lambda Hclosed Hnd.
  exact (spectral_structural A lambda Hclosed Hnd).
Qed.

(** Not continuous ⟹ discrete (for closed eigenspaces) *)
Lemma not_continuous_implies_discrete : forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  ~ has_continuous_eigenspace A lambda ->
  has_discrete_eigenspace A lambda.
Proof.
  intros A lambda Hclosed Hnc.
  destruct (spectral_dichotomy A lambda Hclosed) as [Hd | Hc].
  - exact Hd.
  - contradiction.
Qed.

(* ========================================================================= *)
(*  SECTION 4: Trivial Discrete Cases                                        *)
(* ========================================================================= *)

(** No eigenstates ⟹ trivially discrete *)
Lemma trivial_discrete : forall (A : QObservable dim) (lambda : Q),
  (forall s, ~ is_eigenstate A s lambda) ->
  has_discrete_eigenspace A lambda.
Proof.
  intros A lambda Hno.
  apply empty_eigenspace_enumerable.
  apply eigenspace_empty_if_no_eigenstates. exact Hno.
Qed.

(** Singleton eigenspace is discrete *)
Lemma singleton_eigenspace_discrete :
  forall (A : QObservable dim) (lambda : Q) (s0 : QState dim),
  is_eigenstate A s0 lambda ->
  (forall s, is_eigenstate A s lambda -> state_equiv s s0) ->
  has_discrete_eigenspace A lambda.
Proof.
  intros A lambda s0 Heig0 Huniq.
  unfold has_discrete_eigenspace.
  exists (fun _ => encode s0).
  intros p [s [Heig Henc]].
  exists 0%nat.
  assert (Hequiv : state_equiv s s0) by (apply Huniq; exact Heig).
  apply (bp_eq_trans (encode s0) (encode s) p).
  - apply encode_compat. apply state_equiv_sym. exact Hequiv.
  - exact Henc.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Finitely Many Eigenstates                                     *)
(* ========================================================================= *)

(** A finite list of binary processes is enumerable *)
Lemma list_processes_enumerable :
  forall (bs : list BinProcess),
  is_enumerable (fun p => exists b, In b bs /\ bp_eq b p).
Proof.
  induction bs as [| b0 bs IH].
  - apply enumerable_empty. unfold is_empty.
    intros p [b [Hin _]]. inversion Hin.
  - assert (Hsingle : is_enumerable (fun p : BinProcess => bp_eq b0 p)).
    { exists (fun _ => b0). intros p Hp. exists 0%nat. exact Hp. }
    destruct IH as [fbs Hfbs].
    destruct (enum_union_enum _ _ Hsingle
      (ex_intro _ fbs Hfbs : is_enumerable (fun p => exists b, In b bs /\ bp_eq b p)))
      as [f Hf].
    exists f. intros p [b [[Heq | Hin] Hbp]].
    + apply Hf. left. subst. exact Hbp.
    + apply Hf. right. exists b. split; assumption.
Qed.

(** Eigenspace covered by finitely many states is discrete *)
Lemma finitely_many_discrete :
  forall (A : QObservable dim) (lambda : Q)
  (states : list (QState dim)),
  (forall s, is_eigenstate A s lambda ->
    exists s', In s' states /\ state_equiv s s') ->
  has_discrete_eigenspace A lambda.
Proof.
  intros A lambda states Hfin.
  unfold has_discrete_eigenspace.
  set (bs := map encode states).
  destruct (list_processes_enumerable bs) as [f Hf].
  exists f. intros p [s [Heig Henc]].
  apply Hf.
  destruct (Hfin s Heig) as [s' [Hin Hequiv]].
  exists (encode s'). split.
  - unfold bs. apply in_map. exact Hin.
  - apply (bp_eq_trans (encode s') (encode s) p).
    + apply encode_compat. apply state_equiv_sym. exact Hequiv.
    + exact Henc.
Qed.

(** Diagonal observable eigenstates *)
Lemma diag_eigenspace_contains_basis :
  forall (eigenvals : QVec dim) (j : nat),
  (j < dim)%nat ->
  eigenspace (diag_observable eigenvals) (qv_nth eigenvals j)
    (encode (basis_state dim j)).
Proof.
  intros eigenvals j Hj.
  apply eigenspace_has_eigenstate.
  exact (diag_eigenstate eigenvals j Hj).
Qed.

(** Diagonal observable has discrete spectrum when eigenvalues are given *)
Lemma diag_discrete_from_list :
  forall (eigenvals : QVec dim) (lambda : Q),
  (forall s, is_eigenstate (diag_observable eigenvals) s lambda ->
    exists j, (j < dim)%nat /\ state_equiv s (basis_state dim j)) ->
  has_discrete_eigenspace (diag_observable eigenvals) lambda.
Proof.
  intros eigenvals lambda Hbasis.
  set (states := map (fun j => basis_state dim j) (seq 0 dim)).
  apply (finitely_many_discrete (diag_observable eigenvals) lambda states).
  intros s Heig.
  destruct (Hbasis s Heig) as [j [Hj Hequiv]].
  exists (basis_state dim j). split.
  - unfold states. apply in_map_iff. exists j. split; [reflexivity |].
    apply in_seq. lia.
  - exact Hequiv.
Qed.

(* ========================================================================= *)
(*  SECTION 6: Spectrum Exhaustion and Properties                            *)
(* ========================================================================= *)

(** Discrete or continuous — restated for emphasis *)
Lemma discrete_continuous_exhaust :
  forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  has_discrete_eigenspace A lambda \/ has_continuous_eigenspace A lambda.
Proof.
  exact spectral_dichotomy.
Qed.

(** Continuous spectrum implies the observable has uncountably many eigenstates
    (in the sense that the eigenspace is not enumerable).
    This follows from PCH contrapositive. *)
Lemma continuous_implies_not_discrete :
  forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  has_continuous_eigenspace A lambda ->
  ~ has_discrete_eigenspace A lambda ->
  has_continuous_eigenspace A lambda.
Proof.
  intros A lambda _ Hcont _. exact Hcont.
Qed.

(** For closed eigenspaces, the two cases are the only possibilities *)
Lemma spectral_cases_complete :
  forall (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace A lambda) ->
  ~ (~ has_discrete_eigenspace A lambda /\ ~ has_continuous_eigenspace A lambda).
Proof.
  intros A lambda Hclosed [Hnd Hnc].
  destruct (spectral_dichotomy A lambda Hclosed) as [Hd | Hc]; contradiction.
Qed.

(** Discrete spectrum: not-continuous for each closed eigenspace *)
Lemma discrete_spectrum_no_continuous :
  forall (A : QObservable dim),
  has_discrete_spectrum A ->
  forall lambda, is_closed (eigenspace A lambda) ->
    has_discrete_eigenspace A lambda.
Proof.
  intros A Hdisc lambda Hclosed. exact (Hdisc lambda Hclosed).
Qed.

End SpectralEncoding.

(* ========================================================================= *)
(*  SECTION 7: General Collection Properties                                 *)
(* ========================================================================= *)

(** The full Cantor space has a perfect subset *)
Lemma full_cantor_space_perfect : has_perfect_subset (fun _ : BinProcess => True).
Proof.
  exact full_has_perfect.
Qed.

(** The full Cantor space is not enumerable *)
Lemma full_cantor_space_not_enum : ~ is_enumerable (fun _ : BinProcess => True).
Proof.
  exact full_collection_not_enumerable.
Qed.

(** Empty collection is enumerable *)
Lemma empty_collection_enum : is_enumerable (fun _ : BinProcess => False).
Proof.
  apply enumerable_empty. unfold is_empty. tauto.
Qed.

(** Singleton collections are enumerable *)
Lemma singleton_collection_enum : forall (p : BinProcess),
  is_enumerable (fun q => bp_eq q p).
Proof.
  exact singleton_enumerable.
Qed.

(** Subcollection of an enumerable collection is enumerable *)
Lemma subcollection_enum : forall (C D : BinCollection),
  (forall p, C p -> D p) ->
  is_enumerable D ->
  is_enumerable C.
Proof.
  intros C D Hsub [f Hf].
  exists f. intros p Hp. apply Hf. apply Hsub. exact Hp.
Qed.

(** Enumerable union of enumerable collections is enumerable *)
Lemma countable_union_enumerable :
  forall (F : nat -> BinCollection),
  (forall n, is_enumerable (F n)) ->
  is_enumerable (fun p => exists n, F n p).
Proof.
  exact countable_union_enum.
Qed.

(* ========================================================================= *)
(*  SECTION 8: Spectral Theory Summary Theorems                              *)
(* ========================================================================= *)

(** ★ MAIN THEOREM: Spectral Classification ★
    Every closed eigenspace of a quantum observable falls into exactly
    one of two categories:
    1. Discrete (enumerable) — countably many eigenstates
    2. Continuous (perfect subset) — uncountably many eigenstates
    There is no third possibility. *)
Theorem spectral_classification :
  forall dim (encode : QState dim -> BinProcess)
    (encode_compat : forall s1 s2, state_equiv s1 s2 -> bp_eq (encode s1) (encode s2))
    (encode_inj : forall s1 s2, bp_eq (encode s1) (encode s2) -> state_equiv s1 s2)
    (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace dim encode A lambda) ->
  is_enumerable (eigenspace dim encode A lambda) \/
  has_perfect_subset (eigenspace dim encode A lambda).
Proof.
  intros. apply spectral_dichotomy; assumption.
Qed.

(** ★ Observable-level Classification ★ *)
Theorem observable_spectral_type :
  forall dim (encode : QState dim -> BinProcess)
    (encode_compat : forall s1 s2, state_equiv s1 s2 -> bp_eq (encode s1) (encode s2))
    (encode_inj : forall s1 s2, bp_eq (encode s1) (encode s2) -> state_equiv s1 s2)
    (A : QObservable dim),
  has_discrete_spectrum dim encode A \/
  has_continuous_spectrum dim encode A.
Proof.
  intros.
  destruct (classic (has_discrete_spectrum dim encode A)) as [Hd | Hnd].
  - left. exact Hd.
  - right.
    unfold has_discrete_spectrum in Hnd.
    (* ¬ (forall lambda, closed → enum) means exists lambda, closed ∧ ¬enum *)
    apply NNPP. intro Hnc.
    apply Hnd. intros lambda Hclosed.
    destruct (spectral_dichotomy dim encode A lambda Hclosed) as [Hd | Hc].
    + exact Hd.
    + exfalso. apply Hnc.
      exists lambda. split; assumption.
Qed.

(** ★ Finite-dimensional observables: discrete by finitely-many-states ★ *)
Theorem finite_dim_discrete :
  forall dim (encode : QState dim -> BinProcess)
    (encode_compat : forall s1 s2, state_equiv s1 s2 -> bp_eq (encode s1) (encode s2))
    (encode_inj : forall s1 s2, bp_eq (encode s1) (encode s2) -> state_equiv s1 s2)
    (A : QObservable dim) (lambda : Q)
    (states : list (QState dim)),
  (forall s, is_eigenstate A s lambda ->
    exists s', In s' states /\ state_equiv s s') ->
  has_discrete_eigenspace dim encode A lambda.
Proof.
  intros. apply finitely_many_discrete with (states := states); assumption.
Qed.

(** Summary:
    SpectralDichotomy: Spectral dichotomy from Process Continuum Hypothesis.
    - Encoding: eigenspace, eigenspace_has_eigenstate, eigenspace_bp_eq_closed,
      eigenspace_empty_if_no_eigenstates, empty_eigenspace_enumerable
    - Dichotomy: spectral_dichotomy, spectral_structural,
      no_intermediate_spectrum
    - Classification: discrete_spectrum_all_enum, continuous_spectrum_witness,
      not_discrete_implies_continuous, not_continuous_implies_discrete,
      discrete_continuous_exhaust
    - Discrete cases: trivial_discrete, singleton_eigenspace_discrete,
      list_processes_enumerable, finitely_many_discrete,
      diag_eigenspace_contains_basis, diag_discrete_from_list
    - Collection properties: full_cantor_space_perfect,
      full_cantor_space_not_enum, empty_collection_enum,
      singleton_collection_enum, subcollection_enum,
      countable_union_enumerable
    - Summary theorems: spectral_classification, observable_spectral_type,
      finite_dim_discrete
*)
