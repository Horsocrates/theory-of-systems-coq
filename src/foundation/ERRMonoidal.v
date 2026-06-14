(** * ERRMonoidal.v — the SYMMETRIC MONOIDAL structure on the category of systems (the next layer
      toward categorical QM), plus a concrete DAGGER on the amplitude tier — with the honest wall at
      dagger-COMPACT (cups/caps/duals need the Hilbert/sqrt-2 structure).

    ERRComposition.v gave the product on OBJECTS (fs_product) and the morphism category.  This file
    upgrades that to a genuine MONOIDAL category: the product becomes a BIFUNCTOR (tensor on
    morphisms), with a UNIT object and a SYMMETRY (braiding).  Then a small DAGGER on the Q-amplitude
    tier (transpose), shown to preserve the entanglement measure.  The honest wall is dagger-COMPACT:
    cups/caps (where Bell states and teleportation live, Abramsky-Coecke) need the amplitude/inner-
    product structure FUSED with the monoidal one — the sqrt-2/Hilbert wall.

    (A) MONOIDAL on the system category (relational tier):
      ★ I_sys        — the unit object (a one-element equivalence-system).
      ★ err_tensor   — tensor on MORPHISMS: f (X) g acts as (f x, g y), preserving prod_rel.  With
                       tensor_id / tensor_comp it is a BIFUNCTOR (both by reflexivity, like the
                       category laws — the monoidal structure is forced, not chosen).
      ★ braid        — the SYMMETRY A(X)B -> B(X)A (swap the pair); braid_involutive (braid o braid = id).
      ★ state_of_product_factors — every STATE of a product (morphism I -> A(X)B) is a pair = a product
                       state: at the relational tier there are NO entangled STATES; entanglement lives
                       in the Roles (ERREntanglement) or the amplitude tier (ERREntanglementMeasure).
                       This LOCATES the wall precisely.

    (B) DAGGER on the amplitude tier (Q-correlation matrices, from ERREntanglementMeasure):
      ★ dag E        — transpose (dag E x y = E y x); dag_involutive (dag o dag = id, pointwise).
      ★ q_det_dag    — the entanglement measure is DAGGER-INVARIANT (det of transpose = det).
      ★ factorizable_dag — separability is DAGGER-STABLE (transpose of f(X)g is g(X)f).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) (X) (tensor) is the rule for ASSEMBLING systems into a composite — a BIFUNCTOR (objects via
          fs_product, morphisms via err_tensor; preserves id and composition);
      (2) assembly is SYMMETRIC (braid: A(X)B ~ B(X)A, involutive) with a UNIT (I_sys);
      (3) on the amplitude tier, DAGGER (transpose) reverses an amplitude — involutive, and PRESERVES
          the measure q_det and separability.
    Roles (L4): err_tensor = (X) on morphisms; braid = symmetry; I_sys = unit; dag = dagger; the
      bifunctor / involution laws.
    Elements (L1+P4): the systems A, B, ...; their products; the unit; the Q-amplitude matrices.
    P4 diagnostic (could it be otherwise?):
      the monoidal laws (bifunctoriality, symmetry involution) are FORCED by the product structure
      (reflexivity), not chosen; the dagger preserves q_det because det is transpose-invariant (ring).
    Honesty wall:
      this is the symmetric monoidal SKELETON ((X)-bifunctor + unit + symmetry) — NOT full coherence
      (associator pentagon/triangle: standard, not proved) and NOT compact-closed (no cups/caps/duals).
      state_of_product_factors shows WHY: at the relational tier every state of a product is a pair (a
      product state) — there are NO entangled STATES here.  A genuine dagger-COMPACT category
      (Abramsky-Coecke: Bell states = cups, teleportation = snake equations) needs the amplitude/
      inner-product structure FUSED with the monoidal one — the sqrt-2/Hilbert wall.  So: monoidal
      (category) and dagger (amplitude) are each available; fusing them into dagger-compact is the
      honest wall.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From ToS Require Import TheoryOfSystems_Core_ERR.       (* FunctionalSystem, fs_*, get_*, L1/L2 *)
From ToS Require Import foundation.ERRComposition.      (* ERRMorphism, err_*, fs_product, prod_rel *)
From ToS Require Import foundation.ERREntanglementMeasure.  (* QCorr, q_det, factorizable *)

Open Scope Q_scope.

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  (A) MONOIDAL on the system category                                    *)
(* ===================================================================== *)

(** The UNIT object: a one-element equivalence-system. *)
Definition I_sys : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := unit;
            fs_relations := (fun _ _ => True); fs_functional := _;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
  split; [ | split ]; intros; exact I.
Defined.

(** ★ TENSOR on MORPHISMS: f (X) g acts componentwise (f x, g y), preserving prod_rel. *)
Definition err_tensor {L} {A A' B B' : FunctionalSystem L}
  (HA : fs_constitution A = EquivalenceConstitution)
  (HA' : fs_constitution A' = EquivalenceConstitution)
  (HB : fs_constitution B = EquivalenceConstitution)
  (HB' : fs_constitution B' = EquivalenceConstitution)
  (f : ERRMorphism A A') (g : ERRMorphism B B')
  : ERRMorphism (fs_product A B HA HB) (fs_product A' B' HA' HB').
Proof.
  refine (@mkERRMorphism L (fs_product A B HA HB) (fs_product A' B' HA' HB')
            (fun p => (err_map f (fst p), err_map g (snd p))) _).
  intros x y H. destruct H as [Ha Hb]. split.
  - exact (err_pres f (fst x) (fst y) Ha).
  - exact (err_pres g (snd x) (snd y) Hb).
Defined.

(** ★★ (X) preserves identities: id (X) id = id (bifunctor law 1). *)
Lemma tensor_id : forall {L} (A B : FunctionalSystem L) HA HB,
  err_morph_eq (err_tensor HA HA HB HB (err_id A) (err_id B)) (err_id (fs_product A B HA HB)).
Proof. intros L A B HA HB x. destruct x as [a b]. reflexivity. Qed.

(** ★★ (X) preserves composition: (f' o f) (X) (g' o g) = (f' (X) g') o (f (X) g) (bifunctor law 2). *)
Lemma tensor_comp : forall {L} (A A' A'' B B' B'' : FunctionalSystem L)
  HA HA' HA'' HB HB' HB''
  (f : ERRMorphism A A') (f' : ERRMorphism A' A'')
  (g : ERRMorphism B B') (g' : ERRMorphism B' B''),
  err_morph_eq
    (err_tensor HA HA'' HB HB'' (err_comp f f') (err_comp g g'))
    (err_comp (err_tensor HA HA' HB HB' f g) (err_tensor HA' HA'' HB' HB'' f' g')).
Proof. intros. intro x. reflexivity. Qed.

(** ★ The SYMMETRY (braiding): A (X) B -> B (X) A by swapping the pair. *)
Definition braid {L} (A B : FunctionalSystem L)
  (HA : fs_constitution A = EquivalenceConstitution)
  (HB : fs_constitution B = EquivalenceConstitution)
  : ERRMorphism (fs_product A B HA HB) (fs_product B A HB HA).
Proof.
  refine (@mkERRMorphism L (fs_product A B HA HB) (fs_product B A HB HA)
            (fun p => (snd p, fst p)) _).
  intros x y H. destruct H as [Ha Hb]. split; [ exact Hb | exact Ha ].
Defined.

(** ★★ The symmetry is INVOLUTIVE: braid o braid = id. *)
Lemma braid_involutive : forall {L} (A B : FunctionalSystem L) HA HB,
  err_morph_eq (err_comp (braid A B HA HB) (braid B A HB HA)) (err_id (fs_product A B HA HB)).
Proof. intros L A B HA HB x. destruct x as [a b]. reflexivity. Qed.

(** ★★★ Every STATE of a product factors: a morphism I -> A (X) B picks a PAIR (a, b) = a product
    state.  At the relational tier there are NO entangled STATES — entanglement lives in the Roles
    (ERREntanglement) or the amplitude tier (ERREntanglementMeasure).  This LOCATES the wall. *)
Lemma state_of_product_factors : forall (A B : FunctionalSystem L2) HA HB
  (s : ERRMorphism I_sys (fs_product A B HA HB)),
  exists (a : get_Elements A) (b : get_Elements B), err_map s tt = (a, b).
Proof.
  intros A B HA HB s.
  exists (fst (err_map s tt)), (snd (err_map s tt)).
  apply surjective_pairing.
Qed.

(* ===================================================================== *)
(*  (B) DAGGER on the amplitude tier (Q-correlation matrices)             *)
(* ===================================================================== *)

(** The DAGGER = transpose of the amplitude matrix. *)
Definition dag (E : QCorr) : QCorr := fun x y => E y x.

(** ★ The dagger is INVOLUTIVE (pointwise, no funext needed). *)
Lemma dag_involutive : forall E x y, dag (dag E) x y == E x y.
Proof. intros E x y. unfold dag. reflexivity. Qed.

(** ★★ The entanglement measure is DAGGER-INVARIANT: det of the transpose = det. *)
Lemma q_det_dag : forall E, q_det (dag E) == q_det E.
Proof. intro E. unfold q_det, dag. ring. Qed.

(** ★★ Separability is DAGGER-STABLE: the transpose of f (X) g is g (X) f. *)
Lemma factorizable_dag : forall E, factorizable E -> factorizable (dag E).
Proof.
  intros E [f [g Hfg]]. exists g, f. intros x y. unfold dag. rewrite Hfg. ring.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The category of systems is SYMMETRIC MONOIDAL (relational tier) with a DAGGER on the
    amplitude tier:
      (bifunctor)   (X) preserves identities and composition;
      (symmetry)    the braiding is involutive;
      (no ent.state) every state of a product factors (entanglement is not in states here);
      (dagger)      the entanglement measure is transpose-invariant and separability transpose-stable.
    Monoidal (category) and dagger (amplitude) are each available; fusing them into dagger-COMPACT
    (cups/caps, Bell-states-as-cups) is the honest sqrt-2/Hilbert wall. *)
Theorem err_monoidal :
  (forall (L : Level) (A B : FunctionalSystem L) HA HB,
     err_morph_eq (err_tensor HA HA HB HB (err_id A) (err_id B)) (err_id (fs_product A B HA HB)))
  /\ (forall (L : Level) (A A' A'' B B' B'' : FunctionalSystem L) HA HA' HA'' HB HB' HB''
        (f : ERRMorphism A A') (f' : ERRMorphism A' A'')
        (g : ERRMorphism B B') (g' : ERRMorphism B' B''),
        err_morph_eq
          (err_tensor HA HA'' HB HB'' (err_comp f f') (err_comp g g'))
          (err_comp (err_tensor HA HA' HB HB' f g) (err_tensor HA' HA'' HB' HB'' f' g')))
  /\ (forall (L : Level) (A B : FunctionalSystem L) HA HB,
        err_morph_eq (err_comp (braid A B HA HB) (braid B A HB HA)) (err_id (fs_product A B HA HB)))
  /\ (forall (A B : FunctionalSystem L2) HA HB (s : ERRMorphism I_sys (fs_product A B HA HB)),
        exists a b, err_map s tt = (a, b))
  /\ (forall E, q_det (dag E) == q_det E)
  /\ (forall E, factorizable E -> factorizable (dag E)).
Proof.
  split; [ intros L A B HA HB; apply tensor_id | ].
  split; [ intros L A A' A'' B B' B'' HA HA' HA'' HB HB' HB'' f f' g g'; apply tensor_comp | ].
  split; [ intros L A B HA HB; apply braid_involutive | ].
  split; [ intros A B HA HB s; apply state_of_product_factors | ].
  split; [ intros E; apply q_det_dag | intros E HE; apply factorizable_dag; exact HE ].
Qed.

Print Assumptions state_of_product_factors.
Print Assumptions err_monoidal.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The category of systems made SYMMETRIC MONOIDAL + a DAGGER on the          *)
(*  amplitude tier.  (A) I_sys (unit object); err_tensor ((X) on morphisms);   *)
(*  tensor_id / tensor_comp (BIFUNCTOR, reflexivity); braid (symmetry) +       *)
(*  braid_involutive; state_of_product_factors (every state of a product is a  *)
(*  pair => NO entangled states at the relational tier — locates the wall).    *)
(*  (B) dag (transpose); dag_involutive; q_det_dag (measure DAGGER-INVARIANT); *)
(*  factorizable_dag (separability DAGGER-STABLE).  Capstone err_monoidal.     *)
(*  HONEST: symmetric monoidal SKELETON (no associator coherence proof, no     *)
(*  compact closure); dagger-COMPACT (cups/caps, Bell=cup, teleportation=snake)*)
(*  needs amplitude/inner-product FUSED with monoidal = sqrt-2/Hilbert wall.   *)
(* ========================================================================= *)
