(** * RiceRoleLimit.v — Rice's theorem: every non-trivial semantic property is a role-limit
      Phase 4 of the Computer-Science branch.  Reuses the Phase-1 engine diagonal_defeats_decider
      (BoundaryDecidability.v) — so HALTING, CANTOR and RICE are ONE diagonal.

      A SEMANTIC property P depends only on a program's behaviour (it respects semantic equivalence
      ≡, `P_extensional`).  NON-TRIVIAL: some program has it (p_yes), some doesn't (p_no).  Then no
      decider for P exists — for ANY sufficiently programmable language.

      The construction (Kleene's recursion theorem, taken as the discharged programmability
      hypothesis `RiceDiagonal`, NOT an axiom): against any candidate decider dec, build a program
      d that behaves like p_no when dec says "d has P" and like p_yes when dec says "d lacks P".
      By extensionality, P d <-> dec d = false — exactly the diagonal that defeats every decider.

      Contrast (Rice's non-triviality is necessary): a TRIVIAL (always-true) property IS decidable
      (Element-drawn, decider = const true) — `trivial_property_element_drawn`.

    Reuses cs/BoundaryDecidability.v (ElementDrawn, RoleLimitDrawn, diagonal_defeats_decider).
    Honest level: classical (Rice 1951); the contribution is reusing the project's own diagonal
    engine + the role-limit framing.  0 axioms (programmability is a discharged hypothesis).

    Elements: programs (Prog) and their semantics (the computed function)
    Roles:    a semantic property P = a behaviour-classifier (not syntactic); a decider for P = a
              role-oracle (Status != Role)
    Rules:    extensionality (P respects ≡) + recursion (the diagonal program against any decider)

    ============ E/R/R разбор ============
      Rules (L5): экстенсиональность (P уважает ≡) + рекурсия Клини (диагональная программа против
                  любого решателя) = тот же negb-движок, что defeats deciders.
      Roles (L4): семантическое свойство P — классификатор по ПОВЕДЕНИЮ, не синтаксису; решатель P —
                  роль-оракул.
      Elements  : программы (Prog) и их семантика (вычисляемая функция).
    ДИАГНОСТИКА (P4): нетривиальное семантическое свойство — role-limit (тем же
      diagonal_defeats_decider, что halting в Ф1) ⟹ Райс = halting = Кантор = ОДИН движок;
      тривиальное (всегда-истинно) — Element (решатель = const true).  Программируемость
      (RiceDiagonal = рекурсия) — СНИМАЕМАЯ гипотеза, не аксиома.  Честно: классика (1951); вклад —
      переиспользование собственного движка + role-limit-обрамление.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Bool.
From ToS Require Import cs.BoundaryDecidability.

(** A trivial (always-true) property IS decidable — Rice's non-triviality is necessary. *)
Lemma trivial_property_element_drawn :
  forall (Q : Type) (Triv : Q -> Prop),
    (forall x, Triv x) -> ElementDrawn Triv.
Proof.
  intros Q Triv Hall. exists (fun _ => true). intro x. split.
  - intro. apply Hall.
  - intro. reflexivity.
Qed.

Section Rice.

  Variable Prog : Type.
  Variable sem_equiv : Prog -> Prog -> Prop.     (* ≡ : same computed function *)
  Variable P : Prog -> Prop.                       (* a semantic property *)

  (** P is SEMANTIC: it depends only on behaviour (respects ≡). *)
  Hypothesis P_extensional : forall p q, sem_equiv p q -> (P p <-> P q).

  (** NON-TRIVIAL: a witness with P and a witness without P. *)
  Variable p_yes p_no : Prog.
  Hypothesis P_yes : P p_yes.
  Hypothesis P_no  : ~ P p_no.

  (** Programmability (Kleene's recursion theorem), as a discharged hypothesis: against [dec],
      a program [d] behaving like p_no if dec d = true, like p_yes if dec d = false. *)
  Definition RiceDiagonal (dec : Prog -> bool) : Prop :=
    exists d, (dec d = true  -> sem_equiv d p_no)
           /\ (dec d = false -> sem_equiv d p_yes).

  (** Programmability + extensionality + non-triviality give the diagonal P d <-> dec d = false. *)
  Lemma rice_diagonal_exists :
    forall dec, RiceDiagonal dec -> exists d, P d <-> dec d = false.
  Proof.
    intros dec [d [Hyes Hno]]. exists d. split.
    - intro HPd. destruct (Bool.bool_dec (dec d) true) as [Et | Ef].
      + exfalso. apply P_no. apply (proj1 (P_extensional d p_no (Hyes Et))). exact HPd.
      + apply Bool.not_true_is_false. exact Ef.
    - intro Hdf. apply (proj2 (P_extensional d p_yes (Hno Hdf))). exact P_yes.
  Qed.

  (** ★ RICE: a non-trivial semantic property is role-limit-drawn (undecidable), for any
      sufficiently programmable language — via the SAME engine as the halting boundary (Phase 1). *)
  Theorem rice_role_limit :
    (forall dec, RiceDiagonal dec) -> RoleLimitDrawn P.
  Proof.
    intro Hprog. apply diagonal_defeats_decider.
    intro dec. apply rice_diagonal_exists. apply Hprog.
  Qed.

  (** Spelled out: no decider correctly recognises P. *)
  Corollary rice_no_semantic_decider :
    (forall dec, RiceDiagonal dec) ->
    ~ exists dec : Prog -> bool, forall p, dec p = true <-> P p.
  Proof. intro Hprog. exact (rice_role_limit Hprog). Qed.

End Rice.

(** One diagonal, three theorems: cantor_no_surjection (set), no_halting_decider (program halting),
    rice_role_limit (program semantics) — all rest on diagonal_defeats_decider / negb_no_fixpoint.
    Rice generalises halting: "halts on all inputs" / "computes the zero function" are non-trivial
    semantic properties, hence role-limits. *)

Print Assumptions rice_role_limit.
