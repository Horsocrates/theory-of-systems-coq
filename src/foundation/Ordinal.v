(** * Ordinal.v — Ordinal Arithmetic + epsilon_0
    Elements: Ordinals (OZero, OSucc, OLim)
    Roles:    Arithmetic operations, ordering, embedding
    Rules:    Structural recursion, well-ordering
    STATUS:   24 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    P4 perspective: ordinals are PROCESSES.
    OLim f = limit of a process f : nat -> Ord.
    epsilon_0 = limit of the tower process omega, omega^omega, omega^omega^omega, ...
*)

From Stdlib Require Import Lia ZArith List.
Import ListNotations.

(* ================================================================= *)
(* ORDINAL TYPE                                                       *)
(* ================================================================= *)

Inductive Ord : Set :=
  | OZero : Ord
  | OSucc : Ord -> Ord
  | OLim  : (nat -> Ord) -> Ord.

(* Embedding nat into Ord *)
Fixpoint nat_to_ord (n : nat) : Ord :=
  match n with O => OZero | S n' => OSucc (nat_to_ord n') end.

(* omega = first limit ordinal *)
Definition omega : Ord := OLim nat_to_ord.

(* Addition: a + 0 = a, a + Sb = S(a+b), a + lim f = lim(a + f(n)) *)
Fixpoint ord_add (a b : Ord) : Ord :=
  match b with
  | OZero => a
  | OSucc b' => OSucc (ord_add a b')
  | OLim f => OLim (fun n => ord_add a (f n))
  end.

(* Multiplication *)
Fixpoint ord_mul (a b : Ord) : Ord :=
  match b with
  | OZero => OZero
  | OSucc b' => ord_add (ord_mul a b') a
  | OLim f => OLim (fun n => ord_mul a (f n))
  end.

(* Exponentiation *)
Fixpoint ord_exp (base exp : Ord) : Ord :=
  match exp with
  | OZero => OSucc OZero
  | OSucc e' => ord_mul (ord_exp base e') base
  | OLim f => OLim (fun n => ord_exp base (f n))
  end.

(* omega-tower: omega, omega^omega, omega^omega^omega, ... *)
Fixpoint omega_tower (n : nat) : Ord :=
  match n with O => omega | S n' => ord_exp omega (omega_tower n') end.

(* epsilon_0 = sup{omega, omega^omega, omega^omega^omega, ...} *)
Definition epsilon_0 : Ord := OLim omega_tower.

(* Ordering *)
Inductive ord_lt : Ord -> Ord -> Prop :=
  | lt_zero_succ : forall a, ord_lt OZero (OSucc a)
  | lt_succ_mono : forall a b, ord_lt a b -> ord_lt (OSucc a) (OSucc b)
  | lt_to_lim : forall a f n, ord_lt a (f n) -> ord_lt a (OLim f)
  | lt_succ_to_lim : forall a f,
      (exists n, ord_lt a (f n)) -> ord_lt (OSucc a) (OLim f).

(* ================================================================= *)
(* ARITHMETIC IDENTITIES                                              *)
(* ================================================================= *)

Lemma ord_add_zero_r : forall a, ord_add a OZero = a.
Proof. simpl. reflexivity. Qed.

Lemma ord_add_succ_r : forall a b, ord_add a (OSucc b) = OSucc (ord_add a b).
Proof. simpl. reflexivity. Qed.

(** Stage-wise equality of ordinals.  A limit ordinal [OLim f] is a PROCESS
    [f : nat -> Ord]; two limits are the same when their processes agree at
    every stage.  Leibniz equality [OLim f = OLim g] from stage-wise agreement
    would need functional extensionality -- an axiom ToS does not assume --
    so the two identities that pass through a limit are stated up to [ord_eq]. *)
Inductive ord_eq : Ord -> Ord -> Prop :=
  | oeq_zero : ord_eq OZero OZero
  | oeq_succ : forall a b, ord_eq a b -> ord_eq (OSucc a) (OSucc b)
  | oeq_lim  : forall f g, (forall n, ord_eq (f n) (g n)) -> ord_eq (OLim f) (OLim g).

Lemma ord_eq_refl : forall a, ord_eq a a.
Proof.
  induction a as [| a' IH | f IH].
  - constructor.
  - constructor. exact IH.
  - constructor. exact IH.
Qed.

Lemma ord_eq_sym : forall a b, ord_eq a b -> ord_eq b a.
Proof.
  intros a b H. induction H as [| a b _ IH | f g _ IH].
  - constructor.
  - constructor. exact IH.
  - constructor. exact IH.
Qed.

Lemma ord_eq_trans : forall a b c, ord_eq a b -> ord_eq b c -> ord_eq a c.
Proof.
  intros a b c Hab. revert c.
  induction Hab as [| a b _ IH | f g _ IH]; intros c Hbc.
  - exact Hbc.
  - inversion Hbc; subst. constructor. apply IH. assumption.
  - inversion Hbc; subst. constructor. intro n. apply IH. match goal with H : forall n, ord_eq (g n) _ |- _ => apply H end.
Qed.

(** Leibniz-equal ordinals are stage-wise equal (the converse is the funext step). *)
Lemma ord_eq_of_eq : forall a b, a = b -> ord_eq a b.
Proof. intros a b H. subst. apply ord_eq_refl. Qed.

Lemma ord_add_zero_l : forall a, ord_eq (ord_add OZero a) a.
Proof.
  induction a as [| a' IH | f IH]; simpl.
  - constructor.
  - constructor. exact IH.
  - constructor. exact IH.
Qed.

Lemma ord_mul_zero_r : forall a, ord_mul a OZero = OZero.
Proof. simpl. reflexivity. Qed.

Lemma ord_mul_one_r : forall a, ord_eq (ord_mul a (OSucc OZero)) a.
Proof.
  intros a. simpl. apply ord_add_zero_l.
Qed.

Lemma ord_exp_zero : forall a, ord_exp a OZero = OSucc OZero.
Proof. simpl. reflexivity. Qed.

(* ================================================================= *)
(* CONSTRUCTORS                                                       *)
(* ================================================================= *)

Lemma ord_succ_injective : forall a b, OSucc a = OSucc b -> a = b.
Proof. intros a b H. injection H. auto. Qed.

Lemma ord_succ_ne_zero : forall a, OSucc a <> OZero.
Proof. intros a H. discriminate H. Qed.

(* ================================================================= *)
(* EMBEDDING                                                          *)
(* ================================================================= *)

Lemma nat_to_ord_injective : forall m n, nat_to_ord m = nat_to_ord n -> m = n.
Proof.
  induction m as [| m' IH]; destruct n as [| n']; simpl; intros H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - f_equal. apply IH. injection H. auto.
Qed.

(* ================================================================= *)
(* ORDERING FACTS                                                     *)
(* ================================================================= *)

Lemma nat_to_ord_lt_succ : forall n, ord_lt (nat_to_ord n) (nat_to_ord (S n)).
Proof.
  induction n as [| n' IH]; simpl.
  - apply lt_zero_succ.
  - apply lt_succ_mono. exact IH.
Qed.

Lemma nat_lt_omega : forall n, ord_lt (nat_to_ord n) omega.
Proof.
  intros n. unfold omega.
  apply lt_to_lim with (n := S n).
  apply nat_to_ord_lt_succ.
Qed.

Lemma ord_lt_zero_one : ord_lt OZero (OSucc OZero).
Proof. apply lt_zero_succ. Qed.

(* ================================================================= *)
(* LIMIT ORDINAL PROPERTIES                                          *)
(* ================================================================= *)

Lemma omega_is_limit : forall a, omega <> OSucc a.
Proof. unfold omega. intros a H. discriminate H. Qed.

Lemma epsilon_0_is_limit : forall a, epsilon_0 <> OSucc a.
Proof. unfold epsilon_0. intros a H. discriminate H. Qed.

Lemma ord_zero_ne_omega : OZero <> omega.
Proof. unfold omega. discriminate. Qed.

(* ================================================================= *)
(* CONCRETE COMPUTATIONS                                              *)
(* ================================================================= *)

Lemma nat_to_ord_3 : nat_to_ord 3 = OSucc (OSucc (OSucc OZero)).
Proof. simpl. reflexivity. Qed.

Lemma ord_add_concrete : ord_add (nat_to_ord 2) (nat_to_ord 3) = nat_to_ord 5.
Proof. simpl. reflexivity. Qed.

Lemma ord_mul_concrete : ord_mul (nat_to_ord 2) (nat_to_ord 3) = nat_to_ord 6.
Proof. simpl. reflexivity. Qed.

Lemma omega_tower_0 : omega_tower 0 = omega.
Proof. simpl. reflexivity. Qed.

Lemma omega_tower_1 : omega_tower 1 = ord_exp omega omega.
Proof. simpl. reflexivity. Qed.
