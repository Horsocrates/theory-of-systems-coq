(** * KnowledgeProbabilityEpistemic.v — ВЕРОЯТНОСТЬ как ЭПИСТЕМИЧЕСКАЯ РОЛЬ
      (степень уверенности свидетеля), де-реификация, пул-индифферентность,
      скрытый критерий -> кажущаяся случайность.  Companion to KnowledgeProbability.v.

    Formalizes the EPISTEMIC re-reading of probability worked out in the «Вероятность» разбор
    (Книги/Вероятность/, Р-1…Р-9) — exactly the layer the structural KnowledgeProbability.v LACKS.
    KnowledgeProbability.v locates probability STRUCTURALLY (unclampedness of the boundary);
    here probability is RE-LOCATED EPISTEMICALLY: it is the степень уверенности of a WITNESS under
    limited access — a ROLE (relation witness<->outcome), not an ELEMENT (a property of the event).

    WHAT IS PROVED (structural skeleton of the epistemic reading; 0 axioms):
      §1  Probability is WITNESS-RELATIVE: the SAME actual outcome carries different confidence-
          spread for witnesses with different access (probability_witness_relative); full access =
          certainty (full_access_certainty); partial access = positive spread (partial_access_uncertain).
      §2  DE-REIFICATION (the P4 diagnosis, machine-checked): probability is NOT a unary property of
          the event — there is NO function f : outcome -> spread (probability_not_unary).  «У события
          ЕСТЬ 70%» is ill-formed: probability is a Role (binary witness x situation), not an Element.
      §3  POOL / INDIFFERENCE: a selector by the role-relevant property is INDIFFERENT to a role-free
          property (selection_indifferent_to_col); the outcome on the role-free property is a fact
          about the POOL, not the system (col_outcome_is_pool_fact).
      §4  HIDDEN CRITERION: a fully DETERMINISTIC selection (by a hidden criterion) is OPAQUE to a
          witness without access — the outcome is NOT a function of the witness's observables
          (hidden_crit_opacity): same observable state, different outcome.  Apparent randomness =
          a function of the HIDDENNESS of the determinant, not ontology.

    ============================== E/R/R разбор ==============================
    Elements: свидетель (его доступ = admissible set adm_w); исход; элементы пула с роль-релевантным
              (erel) и роль-свободным (ecol) свойством; скрытый критерий (ecrit).
    Roles:    вероятность = РОЛЬ «степень уверенности» (spread свидетеля); селектор = argmax по
              роль-релевантному; наблюдаемое = проекция, доступная свидетелю.
    Rules:    (1) вероятность относительна доступу свидетеля; полный доступ -> достоверность;
              (2) вероятность НЕ унарное свойство события (де-реификация);
              (3) селектор индифферентен к роль-свободному свойству; число — о пуле, не о системе;
              (4) детерминированный отбор по скрытому критерию не есть функция наблюдаемых -> опаковость.
    P4-диагностика: «объективная вероятность единичного события/системы» = РЕИФИКАЦИЯ (Роль-свидетеля,
              застывшая в Элемент-события/системы); снимается §2 (нет унарного f) и §3 (число о пуле).
              Кажущаяся случайность §4 = скрытость детерминанта, не онтологическая случайность.

    ЧЕСТНАЯ СТЕНА: формализуется СТРУКТУРА эпистемического чтения (относительность доступу,
    не-унарность, индифферентность, скрытая-переменная-опаковость) — НЕ ценность и НЕ онтология
    случайности.  Числовая ФОРМА распределения, |psi|^2, физика — вне (как и в KnowledgeProbability.v).

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

(* ===================================================================== *)
(*  §1 — Probability is WITNESS-RELATIVE (a Role, indexed by access)       *)
(* ===================================================================== *)

(** A witness's confidence-spread = the residual uncertainty of the witness, = how many outcomes
    the witness still cannot rule out (their admissible set), beyond the first.  This is the same
    SHAPE as KnowledgeProbability.unclampedness — but indexed by the WITNESS's access, not by the
    boundary.  That re-indexing IS the epistemic re-location. *)
Definition spread {O : Type} (adm_w : list O) : nat := length adm_w - 1.

(** ★ Full access = certainty: a witness who has narrowed to ONE outcome has spread 0. *)
Theorem full_access_certainty : forall (O : Type) (o : O), spread [o] = 0.
Proof. intros O o. unfold spread. simpl. reflexivity. Qed.

(** ★ Partial access = uncertainty: a witness who cannot narrow below two outcomes has positive
    spread — this is where probability (степень уверенности) lives. *)
Theorem partial_access_uncertain : forall (O : Type) (adm_w : list O),
  2 <= length adm_w -> 0 < spread adm_w.
Proof. intros O adm_w H. unfold spread. lia. Qed.

(** ★★ PROBABILITY IS WITNESS-RELATIVE: the SAME actual outcome (here [true]) carries DIFFERENT
    confidence-spread for two witnesses with different access — full access (spread 0) vs partial
    access (spread 1).  Probability is therefore NOT a property OF the outcome; it is a relation
    witness<->outcome.  (The core of the epistemic reading: степень уверенности of a witness.) *)
Theorem probability_witness_relative :
  exists (O : Type) (o : O) (adm1 adm2 : list O),
    In o adm1 /\ In o adm2 /\ spread adm1 <> spread adm2.
Proof.
  exists bool, true, [true], [true; false].
  split; [ simpl; left; reflexivity | ].
  split; [ simpl; left; reflexivity | ].
  unfold spread; simpl; lia.
Qed.

(* ===================================================================== *)
(*  §2 — DE-REIFICATION: probability is NOT a unary property of the event  *)
(* ===================================================================== *)

(** ★★★ THE REIFICATION DIAGNOSIS, machine-checked.  There is NO function f : outcome -> spread that
    gives "the probability of outcome o" — because the same outcome carries different spread under
    different access (§1).  Hence «у события ЕСТЬ 70%-шанс» is ill-formed: it reifies a ROLE
    (relation, binary in witness x situation) into an ELEMENT (a unary property of the event).
    De-reified: probability is a Role, not an Element. *)
Theorem probability_not_unary :
  ~ exists (f : bool -> nat),
      forall (o : bool) (adm : list bool), In o adm -> spread adm = f o.
Proof.
  intros [f H].
  assert (H1 : spread [true] = f true) by (apply H; simpl; left; reflexivity).
  assert (H2 : spread [true; false] = f true) by (apply H; simpl; left; reflexivity).
  unfold spread in H1, H2; simpl in H1, H2. lia.
Qed.

(* ===================================================================== *)
(*  §3 — POOL / INDIFFERENCE: число — о ПУЛЕ, не о системе                 *)
(* ===================================================================== *)

(** An element carries a role-RELEVANT property (erel : nat, e.g. "шарность") and a role-FREE
    property (ecol3 : bool, e.g. цвет).  A selector picks by erel ALONE. *)
Definition Elt := (nat * bool)%type.
Definition erel  (e : Elt) : nat  := fst e.
Definition ecol3 (e : Elt) : bool := snd e.

(** The selection (which of two competes wins) is decided by the role-relevant property only. *)
Definition wins_first (a b : Elt) : bool := negb (Nat.ltb (erel a) (erel b)).

(** ★ The selector is INDIFFERENT to the role-free property: outcomes with the same role-relevant
    values select identically regardless of colour.  (System indifference, Р-6.) *)
Theorem selection_indifferent_to_col :
  forall (a b a' b' : Elt),
    erel a = erel a' -> erel b = erel b' ->
    wins_first a b = wins_first a' b'.
Proof.
  intros a b a' b' H1 H2. unfold wins_first. rewrite H1, H2. reflexivity.
Qed.

(** ★★ The colour OUTCOME is a fact about the POOL, not the system: two pools with the SAME
    role-relevant values (hence the SAME selection) but different colourings yield DIFFERENT winning
    colours.  So «вероятность синего» is a property of the candidate pool, not of the (colour-
    indifferent) system.  (Second layer of reification de-reified.) *)
Theorem col_outcome_is_pool_fact :
  exists (a b a' b' : Elt),
    erel a = erel a' /\ erel b = erel b' /\
    wins_first a b = wins_first a' b' /\
    ecol3 (if wins_first a b then a else b) <> ecol3 (if wins_first a' b' then a' else b').
Proof.
  exists (1, true), (0, false), (1, false), (0, true).
  repeat split; try reflexivity; discriminate.
Qed.

(* ===================================================================== *)
(*  §4 — HIDDEN CRITERION: детерминизм, опаковый для свидетеля             *)
(* ===================================================================== *)

(** An element carries an OBSERVABLE property (ecol : bool, what the witness sees) and a HIDDEN
    criterion (ecrit : nat, e.g. "шарность" — the witness has no channel to it). *)
Definition E2 := (bool * nat)%type.
Definition ecol  (e : E2) : bool := fst e.
Definition ecrit (e : E2) : nat  := snd e.

(** The system selects DETERMINISTICALLY by the hidden criterion (higher ecrit wins). *)
Definition winner  (a b : E2) : E2   := if Nat.ltb (ecrit a) (ecrit b) then b else a.
Definition outcome (a b : E2) : bool := ecol (winner a b).

(** ★★★ HIDDEN-CRITERION OPACITY: the selection is a function of the hidden criterion (fully
    deterministic), but NOT a function of the witness's OBSERVABLES — two pools with the SAME
    observable colours but different hidden criteria give DIFFERENT outcomes.  To a witness without
    a channel to the criterion the result is unpredictable: APPARENT randomness from a DETERMINISTIC
    system.  «Случайность» = функция СКРЫТОСТИ детерминанта, не онтология. *)
Theorem hidden_crit_opacity :
  exists (a b a' b' : E2),
    ecol a = ecol a' /\ ecol b = ecol b' /\   (* same observable colours present *)
    outcome a b <> outcome a' b'.             (* yet different outcome (hidden criterion) *)
Proof.
  exists (true, 1), (false, 0), (true, 0), (false, 1).
  repeat split; try reflexivity; discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The epistemic reading of probability, structurally: it is witness-relative (§1), NOT a unary
    property of the event (§2, reification blocked), indifferent to role-free properties whose number
    is a pool-fact (§3), and apparently-random only by the hiddenness of a deterministic criterion
    (§4).  Probability = степень уверенности (a Role under limited access), never a property of the
    event or the system. *)
Theorem probability_epistemic_capstone :
  (exists (O : Type) (o : O) (adm1 adm2 : list O),
     In o adm1 /\ In o adm2 /\ spread adm1 <> spread adm2)
  /\ (~ exists (f : bool -> nat),
        forall (o : bool) (adm : list bool), In o adm -> spread adm = f o)
  /\ (forall (a b a' b' : Elt),
        erel a = erel a' -> erel b = erel b' -> wins_first a b = wins_first a' b')
  /\ (exists (a b a' b' : E2),
        ecol a = ecol a' /\ ecol b = ecol b' /\ outcome a b <> outcome a' b').
Proof.
  split; [ exact probability_witness_relative | ].
  split; [ exact probability_not_unary | ].
  split; [ exact selection_indifferent_to_col | exact hidden_crit_opacity ].
Qed.

Print Assumptions probability_epistemic_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Probability RE-LOCATED epistemically: a Role (степень уверенности of a    *)
(*  witness under limited access), not an Element.  Witness-relative          *)
(*  (probability_witness_relative; full_access_certainty;                     *)
(*  partial_access_uncertain).  NOT a unary property of the event —           *)
(*  reification blocked (probability_not_unary).  Selector indifferent to a   *)
(*  role-free property; its number is a POOL fact (selection_indifferent_     *)
(*  to_col; col_outcome_is_pool_fact).  Deterministic selection by a hidden   *)
(*  criterion is opaque to the witness (hidden_crit_opacity) — apparent       *)
(*  randomness = hiddenness, not ontology.  Companion to KnowledgeProbability *)
(*  (which locates probability structurally); this is the epistemic layer.    *)
(* ========================================================================= *)
