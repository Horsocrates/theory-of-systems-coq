(** * RoleLimitLadder.v — НАПРАВЛЕНИЕ N2 (role-limit depth, по запросу автора 2026-06-07): the role-limit
      side of the finitization boundary is NOT FLAT -- it is a LADDER of omniscience principles, graded by
      the QUANTIFIER DEPTH of the boundary question; and the grading is a CONSTRUCTIVE phenomenon (it
      collapses classically).

   The finitization boundary so far has been binary: Element (decidable / finite / choice-free) vs
   role-limit (continuum / non-constructive).  N1++ (DynamicBoundaryLPO) showed the DYNAMIC boundary's
   "край" is EXACTLY LPO.  But LPO is one rung among several.  This file places the role-limit side on a
   LADDER and pins concrete ToS boundary-objects to rungs.

   THE LADDER (ascending omniscience), all proved here 0-axiom as Prop-implications:
       LLPO   (tie-break: "which of two events fails")
         <-  WLPO   (decide a Pi^0_1 truth value, no witness)
         <-  LPO    (decide a Sigma^0_1 statement WITH witness)        <- the N1++ rung
         <-  LPO_omega ("infinitely- vs finitely-many Sigma^0_1 events fire")   <- the CASCADE rung
   Proved: LPO_omega -> LPO -> WLPO -> LLPO, and LPO -> MP (Markov, a side rung).

   ★ THE GRADING IS CONSTRUCTIVE (the honest P4 point).  We ALSO prove  LEM -> LPO  and
   LEM -> LPO_omega.  So CLASSICALLY every rung is just a theorem (all principles hold, all collapse to
   "True"): the ladder is FLAT.  The depth is visible ONLY through the constructive / P4 lens.  This is
   what "the P4 angle is finer than the classical one" means HERE -- not a new theorem, but a structure
   classical logic cannot see, made machine-explicit.

   THE BOUNDARY-OBJECT -> RUNG MAP (the genuine placement):
       static algebraic boundary (Delta1 / DecidableBoundary)         -> rung 0  (Element, DECIDABLE);
       single dynamic eventual-constancy (N1++: MCT_nat <-> LPO)       -> rung LPO;
       cascade "infinitely many flows fire" (boundary-of-boundaries)   -> rung LPO_omega (this file).
   The ascent LPO_omega -> LPO is PROVED here: the cascade boundary demands strictly more omniscience
   than a single one.

   HONEST SCOPE (this is the file to be most honest about).  Fully machine-closed, 0 axioms (LEM is a
   Prop HYPOTHESIS, never asserted).  NOVELTY IS MODEST:
     -- the ascending implications LPO->WLPO->LLPO, LPO->MP are STANDARD constructive reverse mathematics
        (Bishop, Ishihara, ...) -- re-checked here for the ladder, NOT new;
     -- the STRICTNESS (the implications do NOT reverse: LPO_omega ↛ LPO, LPO ↛ WLPO, WLPO ↛ LLPO) is
        NOT proved -- it needs realizability / Kripke / topological MODELS (Kleene, Kreisel-Lacombe-
        Shoenfield) which are NOT formalized here.  CITED and STOPPED.  (Asserting strictness needs a
        model; importing `classic` would FLATTEN the ladder.)
     -- "P4 finer than classical" reduces to the KNOWN meta-fact "classically flat, constructively
        graded" -- machine-checked via LEM->..., NOT discovered.
   GENUINE-mine here is only: (a) the cascade principle LPO_omega + LPO_omega->LPO as MY program's rung 2;
   (b) the boundary-object -> rung MAP.  This file is PLACEMENT / synthesis, a rung BELOW H1 / N1++ in
   originality.  It does NOT overlap the user's P4_Eliminates_{AC,ATR,Infinity,Pi11} (those calibrate the
   CLASSICAL Big-Five / subsystems of Z_2; this is CONSTRUCTIVE reverse math -- a different hierarchy).

   Elements: a boolean sequence g; a pair (a,b) of sequences; a flow-of-flows a : nat->nat->bool; the
             predicate `fires`; finite prefix search.
   Roles:    each rung = "how much completed infinity the question demands"; LEM = the oracle that
             collapses the rungs; the question's quantifier depth = the rung index.
   Rules:    LPO_omega->LPO->WLPO->LLPO, LPO->MP (constructive ascent); LEM->LPO, LEM->LPO_omega
             (classical collapse); strictness = needs a model (cited).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: role-limit-сторона границы — её ГЛУБИНА: лестница всеведения LLPO<WLPO<LPO<LPO_omega.
     Rules (L5): восходящие импликации (конструктивны, доказаны); LEM->LPO, LEM->LPO_omega (классич.
                 схлопывание); строгость = модель (цитата, стоп).
     Roles (L4): ступень = «сколько завершённой бесконечности требует вопрос»; LEM = схлопывающий оракул;
                 квантовая глубина вопроса = номер ступени.
     Elements  : булева g; пара (a,b); поток-потоков a; предикат fires; конечный поиск.
     ОБРАЗУЮЩИЕ: N1++ (MCT<->LPO = ступень LPO); constructive RM (Bishop/Ishihara, цитата); LEM; Delta1.
     ВЛОЖЕННЫЕ : статич. граница (ступень 0); одиночный поток (ступень LPO, N1++); каскад «бесконечно много
                 срабатываний» = граница-границ (ступень LPO_omega, здесь).
   ДИАГНОСТИКА (P4): ⚠ ЧЕСТНО — novelty МОДЕСТНАЯ. Импликации = стандартная CRM (НЕ новое); строгость НЕ
   доказана (модель, цитата, стоп). Genuine-mine: (a) каскад LPO_omega + LPO_omega->LPO как ступень-2 моей
   программы; (b) карта объект->ступень. «P4 тоньше классики» = известный мета-факт (классически плоско,
   конструктивно градуировано), машинно проверяю LEM->…, не открываю. НЕ пересекается с P4_Eliminates_*
   (классич. Big-Five/Z_2 — другая иерархия). Это placement/синтез, ступень ниже H1/N1++.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  The principles, all as Props (NONE asserted as an axiom)               *)
(* ===================================================================== *)

(** LEM: full excluded middle (the CLASSICAL oracle). Hypothesis only, never asserted. *)
Definition LEM : Prop := forall P : Prop, P \/ ~ P.

(** LPO: decide a Sigma^0_1 statement WITH witness. (= the LPO of N1++ DynamicBoundaryLPO.v.) *)
Definition LPO : Prop :=
  forall g : nat -> bool, (exists n, g n = true) \/ (forall n, g n = false).

(** WLPO: decide a Pi^0_1 truth value, no witness. *)
Definition WLPO : Prop :=
  forall g : nat -> bool, (forall n, g n = false) \/ ~ (forall n, g n = false).

(** LLPO: tie-break -- if two events cannot both fire, one of them never fires. *)
Definition LLPO : Prop :=
  forall a b : nat -> bool,
    ~ ((exists n, a n = true) /\ (exists n, b n = true)) ->
    (forall n, a n = false) \/ (forall n, b n = false).

(** MP: Markov's principle (a side rung) -- a non-empty search terminates. *)
Definition MP : Prop :=
  forall g : nat -> bool, ~ (forall n, g n = false) -> exists n, g n = true.

(** fires a k = "the k-th boolean flow ever fires" (a Sigma^0_1 event). *)
Definition fires (a : nat -> nat -> bool) (k : nat) : Prop := exists m, a k m = true.

(** LPO_omega: the CASCADE rung -- decide "finitely many flows fire" vs "infinitely many do"
    (a Pi^0_2 question).  This is the boundary-of-boundaries. *)
Definition LPO_omega : Prop :=
  forall a : nat -> nat -> bool,
    (exists N, forall k, N <= k -> ~ fires a k)
    \/ (forall N, exists k, N <= k /\ fires a k).

(* ===================================================================== *)
(*  Ascending ladder (CONSTRUCTIVE): each rung implies the one below        *)
(* ===================================================================== *)

(** LPO -> MP (the Markov side rung). *)
Lemma lpo_mp : LPO -> MP.
Proof.
  intros lpo g Hnf. destruct (lpo g) as [H | H].
  - exact H.
  - exfalso. apply Hnf. exact H.
Qed.

(** LPO -> WLPO (witness-free decision is weaker). *)
Lemma lpo_wlpo : LPO -> WLPO.
Proof.
  intros lpo g. destruct (lpo g) as [H | H].
  - right. intro Hall. destruct H as [n Hn]. rewrite (Hall n) in Hn. discriminate.
  - left. exact H.
Qed.

(** WLPO -> LLPO (the tie-break needs only witness-free decisions). *)
Lemma wlpo_llpo : WLPO -> LLPO.
Proof.
  intros wlpo a b Hnand. destruct (wlpo a) as [Ha | Ha].
  - left. exact Ha.
  - right. intro n. destruct (b n) eqn:E; [ | reflexivity ].
    exfalso. apply Ha. intro m. destruct (a m) eqn:Ea; [ | reflexivity ].
    exfalso. apply Hnand. split; [ exists m; exact Ea | exists n; exact E ].
Qed.

(** LPO -> LLPO (corollary, completing the chain). *)
Lemma lpo_llpo : LPO -> LLPO.
Proof. intro lpo. apply wlpo_llpo. apply lpo_wlpo. exact lpo. Qed.

(* ===================================================================== *)
(*  The cascade rung is genuinely ABOVE LPO:  LPO_omega -> LPO             *)
(* ===================================================================== *)

(** Bounded prefix search is decidable (constructive). *)
Lemma finite_search : forall (g : nat -> bool) N,
  (exists k, k < N /\ g k = true) \/ (forall k, k < N -> g k = false).
Proof.
  intros g N. induction N.
  - right. intros k Hk. inversion Hk.
  - destruct IHN as [[k [Hk Hg]] | Hall].
    + left. exists k. split; [ lia | exact Hg ].
    + destruct (g N) eqn:E.
      * left. exists N. split; [ lia | exact E ].
      * right. intros k Hk. destruct (Nat.eq_dec k N) as [-> | Hne].
        -- exact E.
        -- apply Hall. lia.
Qed.

(** ★ The cascade boundary demands strictly more omniscience than a single one: LPO_omega -> LPO.
    (Encode g as a flow-of-flows constant in the inner index.) *)
Lemma lpo_omega_lpo : LPO_omega -> LPO.
Proof.
  intros lpoom g. destruct (lpoom (fun k _ => g k)) as [Hfin | Hinf].
  - destruct Hfin as [N HN]. destruct (finite_search g N) as [[k [Hk Hg]] | Hall].
    + left. exists k. exact Hg.
    + right. intro n. destruct (Nat.lt_ge_cases n N) as [Hlt | Hge].
      * apply Hall. exact Hlt.
      * specialize (HN n Hge). destruct (g n) eqn:E; [ | reflexivity ].
        exfalso. apply HN. exists 0. exact E.
  - left. destruct (Hinf 0) as [k [_ Hf]]. destruct Hf as [m Hm]. exists k. exact Hm.
Qed.

(* ===================================================================== *)
(*  ★ The grading is CONSTRUCTIVE: classically the ladder collapses         *)
(* ===================================================================== *)

(** LEM -> LPO: classically the bottom holds. *)
Lemma lem_lpo : LEM -> LPO.
Proof.
  intros lem g. destruct (lem (exists n, g n = true)) as [H | H].
  - left. exact H.
  - right. intro n. destruct (g n) eqn:E; [ | reflexivity ].
    exfalso. apply H. exists n. exact E.
Qed.

(** LEM -> LPO_omega: classically the TOP holds too -- so all rungs are classically flat. *)
Lemma lem_lpo_omega : LEM -> LPO_omega.
Proof.
  intros lem a. destruct (lem (exists N, forall k, N <= k -> ~ fires a k)) as [H | H].
  - left. exact H.
  - right. intro N. destruct (lem (exists k, N <= k /\ fires a k)) as [Hk | Hk].
    + exact Hk.
    + exfalso. apply H. exists N. intros k Hle Hf. apply Hk. exists k. split; [ exact Hle | exact Hf ].
Qed.

(* ===================================================================== *)
(*  Capstone: the role-limit ladder (ascent) and its classical collapse     *)
(* ===================================================================== *)

(** The role-limit side of the finitization boundary is a graded LADDER:
      (ascent, constructive)   LPO_omega -> LPO -> WLPO -> LLPO, and LPO -> MP;
      (classical collapse)     LEM -> LPO  and  LEM -> LPO_omega, so classically every rung holds
                               (the ladder is FLAT) -- the depth is a CONSTRUCTIVE / P4 phenomenon.
    Boundary-object -> rung: static (rung 0, Delta1, decidable), single flow (rung LPO, N1++:
    MCT_nat <-> LPO), cascade / boundary-of-boundaries (rung LPO_omega, here).  Ascent PROVED;
    strictness needs a model (cited, not crossed). *)
Theorem role_limit_ladder :
  (LPO_omega -> LPO) /\ (LPO -> WLPO) /\ (WLPO -> LLPO) /\ (LPO -> MP)
  /\ (LEM -> LPO) /\ (LEM -> LPO_omega).
Proof.
  split; [ exact lpo_omega_lpo |].
  split; [ exact lpo_wlpo |].
  split; [ exact wlpo_llpo |].
  split; [ exact lpo_mp |].
  split; [ exact lem_lpo | exact lem_lpo_omega ].
Qed.
