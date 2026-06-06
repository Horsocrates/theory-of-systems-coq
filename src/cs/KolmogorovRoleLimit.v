(** * KolmogorovRoleLimit.v — Kolmogorov complexity as the FOURTH face of the boundary
      Bridge file of the Computer-Science branch (Part XV) toward information (Part XVI).

      Two complementary views of the SAME E/R/R act, mirroring HaltingRoleLimit:

      (A) Описуемость в бюджете (Element side, terminating, counting).
          A decompressor `decode : nat -> nat` reads a program-code into the object it
          describes; `desc_within x n` = "x is produced by some program of size <= n".
          The Element-side fact is INCOMPRESSIBILITY: at any budget n the short programs
          are FEW (a finite list), so some object is NOT describable within n — a pure
          pigeonhole/counting fact, 0 axioms.  (No machine-invariance is claimed: K here is
          model-relative — exactly the honest scope.)

      (B) Невычислимость сложности (role-limit side, the Kolmogorov/Berry diagonal).
          The "complexity" boundary (x is complex) cannot be drawn by any terminating
          decider WHEN the model admits the self-negating diagonal (the Berry/Chaitin
          obstruction) — this is RoleLimitDrawn, an INSTANCE of the universal
          `diagonal_defeats_decider` (BoundaryDecidability.v), i.e. the SAME negb-diagonal
          that drives halting (PROGRAM) and Cantor (SET).  Kolmogorov is the FOURTH face.

    Reuses (genuine unification, not restatement):
      - cs/HaltingRoleLimit.v     : negb_no_fixpoint, cantor_no_surjection.
      - cs/BoundaryDecidability.v : ElementDrawn / RoleLimitDrawn, diagonal_defeats_decider,
                                    rational_split / discriminant_element_drawn,
                                    halting_role_limit_drawn, one_boundary_three_faces.
      - cs/LawvereFixedPoint.v    : the categorical root these faces share (cited).

    Elements: program-codes (nat) and objects (nat); the decompressor decode
    Roles:    `desc_within` budget-role (P4); `Complex` = a role-LIMIT (K = the minimum
              over all programs, not an Element-object); a decider = role-oracle (Status != Role)
    Rules:    `desc_within x n` — finite-budget describability rule (P4);
              the Berry/Chaitin diagonal = the same b <> negb b that defeats every decider

    ============ E/R/R разбор ============
      Rules (L5): desc_within x n — описуемость В БЮДЖЕТЕ n (P4: бесконечность есть свойство
                  процесса перебора, не объекта).  Диагональ Берри/Чейтина — то же правило
                  b <> negb b, что и в halting/Cantor.
      Roles (L4): Complex / несжимаемость — РОЛЬ-ПРЕДЕЛ (колмогоровская K есть минимум по ВСЕМ
                  программам — не Element-объект); декодер/решатель — роль-оракул (Status != Role).
      Elements  : конкретные программы-коды (nat) и объекты (nat); сам decode.
    ДИАГНОСТИКА (P4): ОГРАНИЧЕННАЯ описуемость desc_within x n — Element-сторона: коротких
      программ КОНЕЧНО, потому НЕ всё описуемо коротко (incompressible_exists, счёт, 0 акс).
      НЕВЫЧИСЛИМОСТЬ сложности — role-limit-сторона: взять тотальный K-оракул = реификация
      role-limit в Element = категориальная ошибка; запрещена ТОЙ ЖЕ диагональю
      (diagonal_defeats_decider), что halting и Кантор.  Колмогоров — ЧЕТВЁРТАЯ грань одной
      границы (число/программа/множество/сложность), один диагональный движок (корень — Ловер).
      Честно: K модель-относительна (инвариантность к машине НЕ заявляется).

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool Lia.
From ToS Require Import cs.HaltingRoleLimit.
From ToS Require Import cs.BoundaryDecidability.

(* ===================================================================== *)
(*  PART A — DESCRIBABILITY WITHIN A BUDGET; INCOMPRESSIBILITY (Element)  *)
(*                                                                         *)
(*  Model-relative: decode p = the object that program-code p describes.   *)
(*  Short programs are FEW -> not every object compresses (pigeonhole).    *)
(* ===================================================================== *)

Section IncompressibilityCounting.

  Variable decode : nat -> nat.   (* the decompressor: program-code -> object *)

  (** x is describable within budget n: some program of size <= n outputs it. *)
  Definition desc_within (x n : nat) : Prop :=
    exists p, (p <= n)%nat /\ decode p = x.

  (** The largest object produced by any program of size <= n (finite scan). *)
  Fixpoint maxd (n : nat) : nat :=
    match n with
    | O   => decode O
    | S k => Nat.max (decode (S k)) (maxd k)
    end.

  Lemma decode_le_maxd : forall p n, (p <= n)%nat -> (decode p <= maxd n)%nat.
  Proof.
    intros p n. revert p. induction n as [| k IH]; intros p Hp.
    - assert (Hp0 : p = 0) by lia. subst p. simpl. apply Nat.le_refl.
    - simpl. destruct (Nat.eq_dec p (S k)) as [-> | Hne].
      + apply Nat.le_max_l.
      + assert (Hpk : (p <= k)%nat) by lia.
        apply Nat.le_trans with (m := maxd k).
        * apply IH. exact Hpk.
        * apply Nat.le_max_r.
  Qed.

  (** ★ ELEMENT SIDE: at every budget n SOME object is incompressible — short programs
      cannot describe everything.  Pure counting (the image of [0..n] is finite). *)
  Theorem incompressible_exists : forall n, exists x, ~ desc_within x n.
  Proof.
    intro n. exists (S (maxd n)). intros [p [Hp Hd]].
    pose proof (decode_le_maxd p n Hp) as Hle. rewrite Hd in Hle. lia.
  Qed.

End IncompressibilityCounting.

(* ===================================================================== *)
(*  PART B — UNCOMPUTABILITY OF COMPLEXITY (role-limit, one diagonal)     *)
(*                                                                         *)
(*  The complexity boundary, when the model admits the self-negating       *)
(*  (Berry/Chaitin) diagonal, is RoleLimitDrawn — the SAME engine          *)
(*  diagonal_defeats_decider that defeats halting and Cantor.              *)
(* ===================================================================== *)

(** ★ NO COMPLEXITY DECIDER.  For any domain whose "is complex" criterion has, against
    EVERY candidate decider, a self-negating witness, the criterion is role-limit-drawn.
    This is the Kolmogorov face — literally an instance of diagonal_defeats_decider. *)
Theorem kolmogorov_role_limit_drawn :
  forall (Obj : Type) (Complex : Obj -> Prop),
    (forall dec : Obj -> bool, exists d, Complex d <-> dec d = false) ->
    RoleLimitDrawn Complex.
Proof.
  intros Obj Complex Hdiag. apply diagonal_defeats_decider. exact Hdiag.
Qed.

(** Contrapositive packaging: an Element-drawn (decidable) complexity criterion has no
    self-negating diagonal — the boundary cannot be both. *)
Corollary complexity_decidable_no_diagonal :
  forall (Obj : Type) (Complex : Obj -> Prop),
    ElementDrawn Complex ->
    ~ (forall dec : Obj -> bool, exists d, Complex d <-> dec d = false).
Proof.
  intros Obj Complex Hel Hdiag.
  exact (kolmogorov_role_limit_drawn Obj Complex Hdiag Hel).
Qed.

(* ===================================================================== *)
(*  SYNTHESIS — ONE boundary, now FOUR faces, ONE diagonal               *)
(* ===================================================================== *)

(** ★ The capstone extends BoundaryDecidability.one_boundary_three_faces with the
    Kolmogorov face: number (Element) / program / set / complexity (all role-limit), all
    driven by the single negb-diagonal (root: Lawvere). *)
Theorem one_boundary_four_faces :
  (* shared engine: negation has no fixed point *)
  (forall b : bool, b <> negb b)
  (* NUMBER: discriminant boundary is Element-drawn (decidable) *)
  /\ ElementDrawn rational_split
  (* PROGRAM: self-halting boundary is role-limit-drawn, given self-application *)
  /\ (forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
        (forall dec : Prog -> bool, exists diag, Halts diag diag <-> dec diag = false) ->
        RoleLimitDrawn (fun q => Halts q q))
  (* SET: boolean-predicate space is not enumerable (Cantor) *)
  /\ (forall (A : Type) (g : A -> (A -> bool)), ~ (forall f, exists a, g a = f))
  (* KOLMOGOROV: complexity boundary is role-limit-drawn, given the Berry/Chaitin diagonal *)
  /\ (forall (Obj : Type) (Complex : Obj -> Prop),
        (forall dec : Obj -> bool, exists d, Complex d <-> dec d = false) ->
        RoleLimitDrawn Complex).
Proof.
  repeat split.
  - exact negb_no_fixpoint.
  - exact discriminant_element_drawn.
  - exact halting_role_limit_drawn.
  - exact cantor_no_surjection.
  - exact kolmogorov_role_limit_drawn.
Qed.

(** Kolmogorov complexity = the project's finitization boundary in the information arena:
    the bounded/short description is Element (incompressible_exists is a counting fact);
    the complexity criterion itself is role-limit — defeated by the one diagonal that also
    defeats halting and Cantor.  This is the bridge to Part XVI (Shannon): «information =
    structural quantity», with K its model-relative, uncomputable extreme. *)

Print Assumptions incompressible_exists.
Print Assumptions one_boundary_four_faces.

(* ===================================================================== *)
(*  Summary: 5 Qed, 0 Admitted, 0 axioms                                 *)
(*    decode_le_maxd, incompressible_exists (Element/counting);          *)
(*    kolmogorov_role_limit_drawn, complexity_decidable_no_diagonal,     *)
(*    one_boundary_four_faces (role-limit / synthesis)                   *)
(* ===================================================================== *)
