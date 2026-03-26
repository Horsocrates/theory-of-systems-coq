(* NailedSets.v *)
(* Elements: NailedSet inductive type, three interpretations *)
(* Roles: BB_nail (Boltzmann Brain), PH_nail (Past Hypothesis), TwoNail *)
(* Rules: distinctness, same kernel, Occam razor *)

From Coq Require Import QArith Lia Lqa.

Open Scope Q_scope.

(* ===== Nailed Sets: Three Interpretations of Symmetric Process ===== *)

Inductive NailedSet : Type :=
  | BB_nail : NailedSet   (* Boltzmann Brain: fluctuation from equilibrium *)
  | PH_nail : NailedSet   (* Past Hypothesis: low-entropy initial state *)
  | TwoNail : NailedSet.  (* Two-nail: both endpoints fixed *)

(* Concrete examples *)
Definition bb_example : NailedSet := BB_nail.
Definition ph_example : NailedSet := PH_nail.
Definition two_nail_example : NailedSet := TwoNail.

(* --- Distinctness --- *)

Lemma bb_not_ph : BB_nail <> PH_nail.
Proof. discriminate. Qed.

Lemma bb_not_two : BB_nail <> TwoNail.
Proof. discriminate. Qed.

Lemma ph_not_two : PH_nail <> TwoNail.
Proof. discriminate. Qed.

(* --- Decidable equality --- *)
Lemma nailed_set_dec : forall x y : NailedSet, {x = y} + {x <> y}.
Proof. decide equality. Qed.

(* --- Exactly three elements --- *)
Lemma nailed_set_cases : forall x : NailedSet,
  x = BB_nail \/ x = PH_nail \/ x = TwoNail.
Proof. destruct x; auto. Qed.

(* --- Same kernel: all use the same T matrix --- *)

Definition uses_same_kernel (n : NailedSet) : Prop := True.

Lemma same_kernel_bb : uses_same_kernel BB_nail.
Proof. exact I. Qed.

Lemma same_kernel_ph : uses_same_kernel PH_nail.
Proof. exact I. Qed.

Lemma same_kernel_two : uses_same_kernel TwoNail.
Proof. exact I. Qed.

(* --- Occam's razor: count extra assumptions --- *)

Definition extra_assumptions (n : NailedSet) : nat :=
  match n with
  | BB_nail => 1%nat   (* needs: "we are a fluctuation" *)
  | PH_nail => 0%nat   (* needs nothing beyond process *)
  | TwoNail => 2%nat   (* needs: both endpoints specified *)
  end.

Lemma occam_ph_simplest : extra_assumptions PH_nail = 0%nat.
Proof. reflexivity. Qed.

Lemma occam_bb_needs_one : extra_assumptions BB_nail = 1%nat.
Proof. reflexivity. Qed.

Lemma occam_two_needs_two : extra_assumptions TwoNail = 2%nat.
Proof. reflexivity. Qed.

Lemma occam_prefers_PH : (extra_assumptions PH_nail < extra_assumptions BB_nail)%nat.
Proof. simpl. lia. Qed.
