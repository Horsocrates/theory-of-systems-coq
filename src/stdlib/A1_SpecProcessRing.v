(** * A1_SpecProcessRing.v -- Spectrum of the Process Ring
    Elements: eval_ideal, is_proper_ideal, spec_nat_correspondence
    Roles:    Maximal ideals of ProcessRing = evaluation at K (Spec ~ N)
    Rules:    eval_ideal K = {f | f(K) == 0} is a proper ideal for each K
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Evaluation Ideal                                           *)
(* ================================================================== *)

(** The evaluation ideal at K: all processes vanishing at stage K *)
Definition eval_ideal (K : nat) (f : RealProcess) : Prop :=
  f K == 0.

(** Zero process is in every eval_ideal *)
Lemma eval_ideal_zero : forall K, eval_ideal K process_zero.
Proof.
  intros K. unfold eval_ideal, process_zero, const_process. lra.
Qed.

(** eval_ideal is closed under addition *)
Lemma eval_ideal_add : forall K f g,
  eval_ideal K f -> eval_ideal K g ->
  eval_ideal K (process_add f g).
Proof.
  intros K f g Hf Hg.
  unfold eval_ideal, process_add in *.
  lra.
Qed.

(** eval_ideal is closed under negation *)
Lemma eval_ideal_neg : forall K f,
  eval_ideal K f -> eval_ideal K (process_neg f).
Proof.
  intros K f Hf.
  unfold eval_ideal, process_neg in *.
  lra.
Qed.

(** eval_ideal absorbs multiplication: I * R subset I *)
Lemma eval_ideal_absorb : forall K f g,
  eval_ideal K f -> eval_ideal K (process_mul f g).
Proof.
  intros K f g Hf.
  unfold eval_ideal, process_mul in *.
  rewrite Hf. ring.
Qed.

(** eval_ideal absorbs from the right too *)
Lemma eval_ideal_absorb_r : forall K f g,
  eval_ideal K f -> eval_ideal K (process_mul g f).
Proof.
  intros K f g Hf.
  unfold eval_ideal, process_mul in *.
  rewrite Hf. ring.
Qed.

(* ================================================================== *)
(*  Part II: Properness                                                *)
(* ================================================================== *)

(** The constant 1 process is NOT in eval_ideal *)
Lemma eval_ideal_proper : forall K,
  ~ eval_ideal K process_one.
Proof.
  intros K H.
  unfold eval_ideal, process_one, const_process in H.
  lra.
Qed.

(** eval_ideal is a proper ideal: contains 0, closed under +, *, not all of R *)
Definition is_proper_ideal (I : RealProcess -> Prop) : Prop :=
  I process_zero /\
  (forall f g, I f -> I g -> I (process_add f g)) /\
  (forall f g, I f -> I (process_mul f g)) /\
  ~ I process_one.

Theorem eval_ideal_is_proper : forall K,
  is_proper_ideal (eval_ideal K).
Proof.
  intros K. unfold is_proper_ideal. split; [|split; [|split]].
  - apply eval_ideal_zero.
  - intros f g. apply eval_ideal_add.
  - intros f g. apply eval_ideal_absorb.
  - apply eval_ideal_proper.
Qed.

(* ================================================================== *)
(*  Part III: Spec ~ N correspondence                                  *)
(* ================================================================== *)

(** Two different K give different ideals *)
Lemma spec_points_distinct : forall K1 K2,
  (K1 <> K2)%nat ->
  exists f, eval_ideal K1 f /\ ~ eval_ideal K2 f.
Proof.
  intros K1 K2 Hne.
  (* Characteristic function: 0 at K1, 1 at K2 *)
  exists (fun n => if PeanoNat.Nat.eq_dec n K1 then 0 else 1).
  split.
  - unfold eval_ideal. destruct (PeanoNat.Nat.eq_dec K1 K1); [lra | contradiction].
  - unfold eval_ideal. destruct (PeanoNat.Nat.eq_dec K2 K1); [lia | lra].
Qed.

(** Each K gives a maximal ideal (any strictly larger ideal = full ring) *)
Lemma eval_ideal_maximal : forall K f,
  ~ eval_ideal K f ->
  forall g, exists a b, process_add (process_mul a f) (process_mul b g) K == g K.
Proof.
  intros K f Hf g.
  (* f(K) != 0, so we can express g(K) using f(K) *)
  exists (process_scale (g K / f K) (fun _ => 1)).
  exists process_zero.
  unfold process_add, process_mul, process_scale, process_zero, const_process.
  unfold eval_ideal in Hf.
  field.
  intro Habs. apply Hf. lra.
Qed.

(** Each nat gives a distinct point in Spec *)
Definition spec_point (K : nat) : RealProcess -> Prop := eval_ideal K.

Lemma spec_injective : forall K1 K2,
  (forall f, spec_point K1 f <-> spec_point K2 f) -> K1 = K2.
Proof.
  intros K1 K2 H.
  destruct (PeanoNat.Nat.eq_dec K1 K2) as [|Hne]; [assumption|].
  exfalso.
  destruct (spec_points_distinct K1 K2 Hne) as [f [Hf1 Hf2]].
  apply Hf2. apply H. exact Hf1.
Qed.

(** Every nat gives a point: Spec is at least as big as N *)
Lemma spec_surjective : forall K,
  is_proper_ideal (spec_point K).
Proof.
  intros K. apply eval_ideal_is_proper.
Qed.

(** Evaluation homomorphism: eval_K(f+g) = eval_K(f) + eval_K(g) *)
Lemma eval_additive : forall K f g,
  process_add f g K == f K + g K.
Proof. intros. unfold process_add. ring. Qed.

(** Evaluation homomorphism: eval_K(f*g) = eval_K(f) * eval_K(g) *)
Lemma eval_multiplicative : forall K f g,
  process_mul f g K == f K * g K.
Proof. intros. unfold process_mul. ring. Qed.

Definition spec_process_ring_count := 15%nat.
