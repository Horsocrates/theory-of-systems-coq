(** * CardinalityWithoutChoice.v — Cardinality comparison as E/R/R roles
    Elements: types (carriers), points
    Roles:    injection (A <= B), surjection, bijection (A ~= B) as comparison-roles
    Rules:    <= is a preorder (refl + trans); Schroeder-Bernstein gives
              antisymmetry (=> bijection); Cantor (G1) gives no maximal cardinality
    STATUS:   10 Qed, 0 Admitted; axiom cost = exactly Schroeder-Bernstein's
              (classic + L4_witness), localized to cardinal_antisym; the
              preorder laws and the Cantor bound are 0-axiom.
    Author:   Horsocrates | Date: June 2026

    E/R/R reading: "cardinality" is not a completed cardinal-OBJECT (no aleph),
    but a ROLE a carrier plays under a comparison-RULE. The injection order <=
    composes and is antisymmetric up to bijection (Schroeder-Bernstein, WITHOUT
    choice). "No maximal cardinality" = no carrier surjects onto its own
    bool-power (general Cantor, 0 axioms).

    HONEST BOUNDARY: the converse bridge surjects(A,B) => injects(B,A) (pick a
    preimage for each b : B) is EXACTLY the Axiom of Choice and is NOT proven
    here. With only L4_witness one inverts a BIJECTION (unique preimages), not
    an arbitrary surjection. So antisymmetry rests on Schroeder-Bernstein
    (classic + L4_witness), NOT on AC; the surjection-to-injection direction
    stays a documented role-limit.
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
(* classic + L4_witness (inherited from SchroederBernstein_ERR), NOT AC.   *)

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
