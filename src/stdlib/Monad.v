(** * Monad.v — Monads as Computation Patterns in ToS

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: monadic values (wrapped computations)
    Roles:    return -> Constructor, bind -> Sequencer
    Rules:    left identity + right identity + associativity (monad laws)
    Status:   pure | effectful | composed

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Import ListNotations.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import stdlib.TOption.

(* ========================================================================= *)
(*                    PART I: MONAD RECORD                                   *)
(* ========================================================================= *)

(** A Monad bundles a type constructor with return and bind operations,
    an extensional equality, and proofs of the three monad laws. *)
Record Monad := mkMonad {
  m_type : Type -> Type;
  m_return : forall A, A -> m_type A;
  m_bind : forall A B, m_type A -> (A -> m_type B) -> m_type B;
  m_eq : forall A, m_type A -> m_type A -> Prop;
  m_eq_refl : forall A (x : m_type A), m_eq A x x;
  m_eq_sym : forall A (x y : m_type A), m_eq A x y -> m_eq A y x;
  m_eq_trans : forall A (x y z : m_type A),
    m_eq A x y -> m_eq A y z -> m_eq A x z;
  m_left_id : forall A B (a : A) (f : A -> m_type B),
    m_eq B (m_bind A B (m_return A a) f) (f a);
  m_right_id : forall A (m : m_type A),
    m_eq A (m_bind A A m (m_return A)) m;
  m_assoc : forall A B C (m : m_type A)
    (f : A -> m_type B) (g : B -> m_type C),
    m_eq C (m_bind B C (m_bind A B m f) g)
           (m_bind A C m (fun x => m_bind B C (f x) g));
}.

(* ========================================================================= *)
(*                    PART II: DERIVED OPERATIONS                            *)
(* ========================================================================= *)

(** Kleisli composition: sequence two monadic functions. *)
Definition kleisli (M : Monad) (A B C : Type)
  (f : A -> m_type M B) (g : B -> m_type M C) (x : A) : m_type M C :=
  m_bind M B C (f x) g.

(** Monadic map (fmap): lift a pure function into the monad. *)
Definition m_map (M : Monad) (A B : Type) (f : A -> B) (m : m_type M A) : m_type M B :=
  m_bind M A B m (fun x => m_return M B (f x)).

(* ========================================================================= *)
(*                    PART III: OPTION MONAD INSTANCE                        *)
(* ========================================================================= *)

(** Helper: option bind for the monad instance. *)
Definition option_bind (A B : Type) (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

(** Theorem 1: Option left identity. *)
Theorem option_left_id : forall (A B : Type) (a : A) (f : A -> option B),
  option_bind A B (Some a) f = f a.
Proof. intros. reflexivity. Qed.

(** Theorem 2: Option right identity. *)
Theorem option_right_id : forall (A : Type) (o : option A),
  option_bind A A o (@Some A) = o.
Proof. intros. destruct o; reflexivity. Qed.

(** Theorem 3: Option associativity. *)
Theorem option_assoc : forall (A B C : Type) (o : option A)
  (f : A -> option B) (g : B -> option C),
  option_bind B C (option_bind A B o f) g =
  option_bind A C o (fun x => option_bind B C (f x) g).
Proof. intros. destruct o; reflexivity. Qed.

(** The Option Monad instance. *)
Definition OptionMonad : Monad := mkMonad
  option
  (fun A x => Some x)
  option_bind
  (fun A => @eq (option A))
  (fun A x => eq_refl)
  (fun A x y H => eq_sym H)
  (fun A x y z H1 H2 => eq_trans H1 H2)
  option_left_id
  option_right_id
  option_assoc.

(* ========================================================================= *)
(*                    PART IV: LIST MONAD INSTANCE                           *)
(* ========================================================================= *)

(** Helper: list bind = flat_map. *)
Definition list_bind (A B : Type) (l : list A) (f : A -> list B) : list B :=
  flat_map f l.

(** Theorem 4: List left identity. *)
Theorem list_left_id : forall (A B : Type) (a : A) (f : A -> list B),
  list_bind A B [a] f = f a.
Proof. intros. unfold list_bind. simpl. rewrite app_nil_r. reflexivity. Qed.

(** Theorem 5: List right identity. *)
Theorem list_right_id : forall (A : Type) (l : list A),
  list_bind A A l (fun x => [x]) = l.
Proof.
  intros. unfold list_bind. induction l as [| h t IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(** Theorem 6: List associativity. *)
Theorem list_assoc : forall (A B C : Type) (l : list A)
  (f : A -> list B) (g : B -> list C),
  list_bind B C (list_bind A B l f) g =
  list_bind A C l (fun x => list_bind B C (f x) g).
Proof.
  intros. unfold list_bind. induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite flat_map_app. f_equal. exact IH.
Qed.

(** The List Monad instance. *)
Definition ListMonad : Monad := mkMonad
  list
  (fun A x => [x])
  list_bind
  (fun A => @eq (list A))
  (fun A x => eq_refl)
  (fun A x y H => eq_sym H)
  (fun A x y z H1 H2 => eq_trans H1 H2)
  list_left_id
  list_right_id
  list_assoc.

(* ========================================================================= *)
(*                    PART V: RESULT MONAD INSTANCE                          *)
(* ========================================================================= *)

(** Helper: result bind for the monad instance. Error type fixed to nat. *)
Definition result_bind (A B : Type)
  (r : TResult A nat) (f : A -> TResult B nat) : TResult B nat :=
  match r with TOk a => f a | TErr e => TErr e end.

(** Theorem 7: Result left identity. *)
Theorem result_left_id : forall (A B : Type) (a : A) (f : A -> TResult B nat),
  result_bind A B (TOk a) f = f a.
Proof. intros. reflexivity. Qed.

(** Theorem 8: Result right identity. *)
Theorem result_right_id : forall (A : Type) (r : TResult A nat),
  result_bind A A r (@TOk A nat) = r.
Proof. intros. destruct r; reflexivity. Qed.

(** Theorem 9: Result associativity. *)
Theorem result_assoc : forall (A B C : Type) (r : TResult A nat)
  (f : A -> TResult B nat) (g : B -> TResult C nat),
  result_bind B C (result_bind A B r f) g =
  result_bind A C r (fun x => result_bind B C (f x) g).
Proof. intros. destruct r; reflexivity. Qed.

(** The Result Monad instance (error type = nat). *)
Definition ResultMonad : Monad := mkMonad
  (fun A => TResult A nat)
  (fun A x => TOk x)
  result_bind
  (fun A => @eq (TResult A nat))
  (fun A x => eq_refl)
  (fun A x y H => eq_sym H)
  (fun A x y z H1 H2 => eq_trans H1 H2)
  result_left_id
  result_right_id
  result_assoc.

(* ========================================================================= *)
(*                    PART VI: KLEISLI PROPERTIES                            *)
(* ========================================================================= *)

(** Theorem 10: Kleisli composition is associative. *)
Theorem kleisli_assoc : forall (M : Monad) (A B C D : Type)
  (f : A -> m_type M B) (g : B -> m_type M C) (h : C -> m_type M D) (x : A),
  m_eq M D (kleisli M A B D f (kleisli M B C D g h) x)
           (kleisli M A C D (kleisli M A B C f g) h x).
Proof.
  intros. unfold kleisli.
  apply m_eq_sym.
  apply (m_assoc M B C D (f x) g h).
Qed.

(** Theorem 11: return is left identity for Kleisli composition. *)
Theorem kleisli_id_left : forall (M : Monad) (A B : Type)
  (f : A -> m_type M B) (x : A),
  m_eq M B (kleisli M A A B (m_return M A) f x) (f x).
Proof.
  intros. unfold kleisli.
  apply (m_left_id M A B x f).
Qed.

(** Theorem 12: return is right identity for Kleisli composition. *)
Theorem kleisli_id_right : forall (M : Monad) (A B : Type)
  (f : A -> m_type M B) (x : A),
  m_eq M B (kleisli M A B B f (m_return M B) x) (f x).
Proof.
  intros. unfold kleisli.
  apply (m_right_id M B (f x)).
Qed.

(* ========================================================================= *)
(*                    PART VII: FUNCTOR (MAP) PROPERTIES                     *)
(* ========================================================================= *)

(** Theorem 13: m_map with identity = identity (up to m_eq). *)
Theorem m_map_id : forall (M : Monad) (A : Type) (m : m_type M A),
  m_eq M A (m_map M A A (fun x => x) m) m.
Proof.
  intros. unfold m_map.
  apply (m_right_id M A m).
Qed.

(** Theorem 14: option m_map distributes over composition. *)
Theorem option_map_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) (o : option A),
  option_bind A C o (fun x => Some (g (f x))) =
  option_bind B C (option_bind A B o (fun x => Some (f x))) (fun y => Some (g y)).
Proof. intros. destruct o; reflexivity. Qed.

(** Theorem 15: list m_map distributes over composition. *)
Theorem list_map_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
  list_bind A C l (fun x => [g (f x)]) =
  list_bind B C (list_bind A B l (fun x => [f x])) (fun y => [g y]).
Proof.
  intros. unfold list_bind. induction l as [| h t IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(** Theorem 16: result m_map distributes over composition. *)
Theorem result_map_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) (r : TResult A nat),
  result_bind A C r (fun x => TOk (g (f x))) =
  result_bind B C (result_bind A B r (fun x => TOk (f x))) (fun y => TOk (g y)).
Proof. intros. destruct r; reflexivity. Qed.

(** Theorem 17: bind (return a) f = f a (monad left-id restated at record level). *)
Theorem bind_return : forall (M : Monad) (A B : Type) (a : A) (f : A -> m_type M B),
  m_eq M B (m_bind M A B (m_return M A a) f) (f a).
Proof.
  intros. apply (m_left_id M A B a f).
Qed.

(* ========================================================================= *)
(*                    PART VIII: CONCRETE COMPUTATIONS                       *)
(* ========================================================================= *)

(** Theorem 18: Concrete option bind: Some 42 >>= (fun n => Some (n+1)) = Some 43. *)
Theorem option_bind_some_42 :
  option_bind nat nat (Some 42) (fun n => Some (n + 1)) = Some 43.
Proof. reflexivity. Qed.

(** Theorem 19: Concrete option bind: None >>= f = None. *)
Theorem option_bind_none_example :
  option_bind nat nat None (fun n => Some (n + 1)) = None.
Proof. reflexivity. Qed.

(** Theorem 20: Concrete list bind: flat_map over singleton list. *)
Theorem list_bind_singleton :
  list_bind nat nat [3] (fun n => [n; n * 2]) = [3; 6].
Proof. reflexivity. Qed.
