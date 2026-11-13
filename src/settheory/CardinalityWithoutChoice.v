(** * CardinalityWithoutChoice.v — Cardinality comparison as E/R/R roles
    Elements: types (carriers), points
    Roles:    injection (A <= B), surjection, bijection (A ~= B) as comparison-roles
    Rules:    <= is a preorder (refl + trans); Schroeder-Bernstein gives
              antisymmetry (=> bijection); Cantor (G1) gives no maximal cardinality
    STATUS:   21 Qed, 0 Admitted, no axioms of its own.  By the compiler:
              preorder laws, Cantor bound, the *_definite theorems and
              split_iff_choice -- closed; cardinal_antisym, bijects_sym,
              no_maximal_in_injection_order -- classic and/or L4_witness;
              surjection_has_section, surjects_injects_back -- L4_witness.
    Author:   Horsocrates | Date: June 2026; boundary section Nov 2026

    E/R/R reading: "cardinality" is not a completed cardinal-OBJECT (no aleph),
    but a ROLE a carrier plays under a comparison-RULE. The injection order <=
    composes and is antisymmetric up to bijection (Schroeder-Bernstein).
    "No maximal cardinality" = no carrier surjects onto its own bool-power
    (general Cantor, 0 axioms).

    WHERE CHOICE ENTERS (Nov 2026; the earlier note here was wrong).
    Elements: witnesses of existence statements.
    Roles:    the UNIQUE witness (the preimage under an injection or a
              bijection) vs. ONE witness AMONG MANY (a point of a fibre of a
              surjection).
    Rules:    antisymmetry and the inversion of a bijection need only the
              extraction of the unique witness: cardinal_antisym_definite,
              bijects_sym_definite are proved from excluded middle and that
              extraction taken as PREMISES, and are closed under the global
              context.  The converse bridge surjects(A,B) => injects(B,A)
              needs a witness in every fibre.  L4_witness as declared puts no
              uniqueness condition, so it DOES give the bridge
              (surjects_injects_back; the compiler reports L4_witness alone).
              "Every surjection has a right inverse" is equivalent to
              functional choice over families (split_iff_choice, closed).
              So the boundary of choice runs INSIDE L4: unique witness on one
              side, arbitrary witness on the other.
*)

From ToS Require Import SchroederBernstein_ERR.
From ToS Require Import settheory.CantorTheoremGeneral.

(* ===================== Comparison roles ===================== *)

Definition injects (A B : Type) : Prop :=
  exists f : A -> B, forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition surjects (A B : Type) : Prop :=
  exists f : A -> B, forall b : B, exists a : A, f a = b.

Definition bijects (A B : Type) : Prop :=
  exists f : A -> B,
    (forall a1 a2, f a1 = f a2 -> a1 = a2) /\ (forall b, exists a, f a = b).

(* ===================== <= is a preorder (0 axioms) ===================== *)

Lemma injects_refl : forall A, injects A A.
Proof. intros A. exists (fun a => a). intros a1 a2 H. exact H. Qed.

Lemma injects_trans : forall A B C, injects A B -> injects B C -> injects A C.
Proof.
  intros A B C [f Hf] [g Hg].
  exists (fun a => g (f a)).
  intros a1 a2 H. apply Hf. apply Hg. exact H.
Qed.

(* surjection is also a preorder (0 axioms) *)

Lemma surjects_refl : forall A, surjects A A.
Proof. intros A. exists (fun a => a). intros b. exists b. reflexivity. Qed.

Lemma surjects_trans : forall A B C, surjects A B -> surjects B C -> surjects A C.
Proof.
  intros A B C [f Hf] [g Hg].
  exists (fun a => g (f a)).
  intros c. destruct (Hg c) as [b Hb]. destruct (Hf b) as [a Ha].
  exists a. rewrite Ha. exact Hb.
Qed.

(* ===================== bijection: equivalence-like (0 axioms) ============ *)

Lemma bijects_refl : forall A, bijects A A.
Proof.
  intros A. exists (fun a => a). split.
  - intros a1 a2 H. exact H.
  - intros b. exists b. reflexivity.
Qed.

Lemma bijects_trans : forall A B C, bijects A B -> bijects B C -> bijects A C.
Proof.
  intros A B C [f [fi fs]] [g [gi gs]].
  exists (fun a => g (f a)). split.
  - intros a1 a2 H. apply fi. apply gi. exact H.
  - intros c. destruct (gs c) as [b Hb]. destruct (fs b) as [a Ha].
    exists a. rewrite Ha. exact Hb.
Qed.

(* bijection forgets to both an injection and a surjection (0 axioms) *)

Lemma bijects_injects : forall A B, bijects A B -> injects A B.
Proof. intros A B [f [fi _]]. exists f. exact fi. Qed.

Lemma bijects_both : forall A B, bijects A B -> injects A B /\ surjects A B.
Proof.
  intros A B [f [fi fs]]. split.
  - exists f. exact fi.
  - exists f. exact fs.
Qed.

(* ============ Antisymmetry of <= via Schroeder-Bernstein =============== *)
(* classic + L4_witness by the compiler; the proof uses L4 only for a     *)
(* unique witness -- see cardinal_antisym_definite below.                 *)

Theorem cardinal_antisym :
  forall A B, injects A B -> injects B A -> bijects A B.
Proof.
  intros A B [f Hf] [g Hg].
  destruct (@Schroeder_Bernstein A B f g Hf Hg) as [h [hi hs]].
  exists h. split; [exact hi | exact hs].
Qed.

(* ============ No maximal cardinality, via general Cantor (0 axioms) ===== *)

Theorem no_maximal_cardinality :
  forall X : Type, ~ surjects X (X -> bool).
Proof.
  intros X [f Hf].
  exact (cantor_no_surjection f Hf).
Qed.

(* ========================================================================= *)
(*  Nov 2026: WHERE CHOICE ENTERS -- the unique witness vs. an arbitrary one  *)
(* ========================================================================= *)

From ToS Require Import ToS_Axioms.

(** The two principles antisymmetry needs, as statements (not axioms). *)
Definition ExcludedMiddle : Prop := forall P : Prop, P \/ ~ P.
Definition UniqueWitness : Type :=
  forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

(* ---- 1. What needs only the unique witness (closed under the global context) ---- *)

Theorem cardinal_antisym_definite :
  ExcludedMiddle -> UniqueWitness ->
  forall A B, injects A B -> injects B A -> bijects A B.
Proof.
  intros EM DD A B [f Hf] [g Hg].
  destruct (@Schroeder_Bernstein_definite EM DD A B f g Hf Hg) as [h [hi hs]].
  exists h. split; [exact hi | exact hs].
Qed.

(* a bijection is inverted by extracting unique preimages *)
Theorem bijects_sym_definite :
  UniqueWitness -> forall A B : Type, bijects A B -> bijects B A.
Proof.
  intros DD A B [f [fi fs]].
  assert (Hu : forall b : B, exists! a : A, f a = b).
  { intro b. destruct (fs b) as [a Ha]. exists a. split.
    - exact Ha.
    - intros a' Ha'. apply fi. rewrite Ha, Ha'. reflexivity. }
  exists (fun b => proj1_sig (DD A (fun a => f a = b) (Hu b))).
  split.
  - intros b1 b2 H.
    rewrite <- (proj2_sig (DD A (fun a => f a = b1) (Hu b1))).
    rewrite <- (proj2_sig (DD A (fun a => f a = b2) (Hu b2))).
    rewrite H. reflexivity.
  - intro a. exists (f a). apply fi.
    exact (proj2_sig (DD A (fun a0 => f a0 = f a) (Hu (f a)))).
Qed.

(* every carrier embeds into its bool-power (the characteristic function of a point) *)
Theorem injects_into_bool_power_definite :
  ExcludedMiddle -> UniqueWitness -> forall X : Type, injects X (X -> bool).
Proof.
  intros EM DD X.
  exists (fun x y => if em_inf EM DD (x = y) then true else false).
  intros x1 x2 H.
  assert (H1 : (if em_inf EM DD (x1 = x1) then true else false)
             = (if em_inf EM DD (x2 = x1) then true else false)).
  { exact (f_equal (fun p : X -> bool => p x1) H). }
  destruct (em_inf EM DD (x1 = x1)) as [_ | Hn].
  - destruct (em_inf EM DD (x2 = x1)) as [E | _].
    + symmetry. exact E.
    + discriminate H1.
  - exfalso. apply Hn. reflexivity.
Qed.

(* no maximal cardinality in the INJECTION order: above every carrier there
   is a strictly greater one *)
Theorem no_maximal_in_injection_order_definite :
  ExcludedMiddle -> UniqueWitness ->
  forall X : Type, exists Y : Type, injects X Y /\ ~ injects Y X.
Proof.
  intros EM DD X. exists (X -> bool). split.
  - exact (injects_into_bool_power_definite EM DD X).
  - intro Hback.
    destruct (cardinal_antisym_definite EM DD X (X -> bool)
                (injects_into_bool_power_definite EM DD X) Hback) as [h [_ hs]].
    apply (no_maximal_cardinality X). exists h. exact hs.
Qed.

(* ---- 2. The same under the two logical assumptions of the formalization ---- *)

Theorem bijects_sym : forall A B : Type, bijects A B -> bijects B A.
Proof. exact (bijects_sym_definite (@L4_definite)). Qed.

Theorem no_maximal_in_injection_order :
  forall X : Type, exists Y : Type, injects X Y /\ ~ injects Y X.
Proof. exact (no_maximal_in_injection_order_definite classic (@L4_definite)). Qed.

(* ---- 3. The bridge surjection -> injection: an ARBITRARY witness ---- *)

(* every surjection has a right inverse: L4_witness applied to each fibre *)
Theorem surjection_has_section :
  forall (A B : Type) (f : A -> B),
    (forall b : B, exists a : A, f a = b) ->
    exists g : B -> A, forall b : B, f (g b) = b.
Proof.
  intros A B f Hf.
  exists (fun b => proj1_sig (L4_witness (fun a => f a = b) (Hf b))).
  intro b. exact (proj2_sig (L4_witness (fun a => f a = b) (Hf b))).
Qed.

Theorem surjects_injects_back :
  forall A B : Type, surjects A B -> injects B A.
Proof.
  intros A B [f Hf].
  destruct (surjection_has_section A B f Hf) as [g Hg].
  exists g. intros b1 b2 H.
  rewrite <- (Hg b1), <- (Hg b2), H. reflexivity.
Qed.

(* ---- 4. "Every surjection has a right inverse" IS functional choice ---- *)

Definition functional_choice : Prop :=
  forall (I X : Type) (R : I -> X -> Prop),
    (forall i, exists x, R i x) -> exists f : I -> X, forall i, R i (f i).

Definition surjections_split : Prop :=
  forall (A B : Type) (f : A -> B),
    (forall b, exists a, f a = b) -> exists g : B -> A, forall b, f (g b) = b.

Theorem choice_gives_split : functional_choice -> surjections_split.
Proof.
  intros FC A B f Hf.
  exact (FC B A (fun b a => f a = b) Hf).
Qed.

Theorem split_gives_choice : surjections_split -> functional_choice.
Proof.
  intros SS I X R HR.
  pose (S := {p : I * X | R (fst p) (snd p)}).
  pose (pi := fun s : S => fst (proj1_sig s)).
  assert (Hpi : forall i, exists s, pi s = i).
  { intro i. destruct (HR i) as [x Hx].
    exists (exist (fun p : I * X => R (fst p) (snd p)) (i, x) Hx). reflexivity. }
  destruct (SS S I pi Hpi) as [g Hg].
  exists (fun i => snd (proj1_sig (g i))).
  intro i.
  pose proof (proj2_sig (g i)) as H. cbv beta in H.
  pose proof (Hg i) as E. unfold pi in E.
  rewrite E in H. exact H.
Qed.

Theorem split_iff_choice : surjections_split <-> functional_choice.
Proof. split; [apply split_gives_choice | apply choice_gives_split]. Qed.

(* Axiom audit (expected output in comments). *)
Print Assumptions cardinal_antisym_definite.            (* Closed under the global context *)
Print Assumptions bijects_sym_definite.                 (* Closed under the global context *)
Print Assumptions no_maximal_in_injection_order_definite. (* Closed under the global context *)
Print Assumptions split_iff_choice.                     (* Closed under the global context *)
Print Assumptions surjects_injects_back.                (* L4_witness *)
Print Assumptions cardinal_antisym.                     (* classic + L4_witness *)
