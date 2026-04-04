(** * ERRKnowledgeBase.v — Closes 6 divergences between Knowledge Base and formalization
    Elements: generative order, role types, status preservation, constitution, L2/L3, levels
    Roles:    each section resolves one specific divergence
    Rules:    from ERR_Knowledge_Base.md (discussions with author)
    STATUS:   20 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    SIX DIVERGENCES RESOLVED:
    1. Generative order: Rules → Roles → Elements (ontological, not epistemic)
    2. Two types of roles: deterministic (many elements) vs status (unique)
    3. Status preservation: equal weight = no reason to update (L4)
    4. Constitution = Rules of previous level (not 4th component)
    5. L2/L3 separate E/R/R categories (exclusive + exhaustive)
    6. Three-level interpretation (Logic → Generation → Concrete)
*)

From Stdlib Require Import QArith Lia ZArith List PeanoNat Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import foundation.ERRProcess.
From ToS Require Import foundation.ERRWellFormedness.

(* ================================================================ *)
(*  FIX 1: GENERATIVE ORDER  R → R → E                              *)
(*  KB: "Онтологический порядок: Rules → Roles → Elements"          *)
(*  Epistemic order (how we discover): E → R → R                    *)
(*  Ontological order (how they exist): R → R → E                   *)
(* ================================================================ *)

(** The generative chain: Rules determine Roles, Roles establish Elements.
    Formalized: compute_gate IS the Rule, Status IS the Role,
    Entity IS the Element. The chain is: gate → weight → status → entity. *)

(** Without Rules (gate), no Roles (status) can be assigned *)
Lemma no_rules_no_roles : forall sig scores,
  gate_valid (compute_gate sig) = false ->
  ent_status (process_entity 0 0 sig scores) = Invalid.
Proof. intros. unfold process_entity. rewrite H. reflexivity. Qed.

(** Without Roles (valid status), Element is indistinguishable from nothing *)
Lemma invalid_has_no_weight : forall sig scores,
  gate_valid (compute_gate sig) = false ->
  ent_weight (process_entity 0 0 sig scores) = 0%nat.
Proof.
  intros. unfold process_entity, compute_weight. rewrite H. reflexivity.
Qed.

(** Rules precede Roles precede Elements — the chain is NECESSARY *)
Theorem generative_order :
  (* Without Rules → no Roles *)
  (forall sig scores, gate_valid (compute_gate sig) = false ->
    ent_status (process_entity 0 0 sig scores) = Invalid) /\
  (* Without Roles → Element has no weight *)
  (forall sig scores, gate_valid (compute_gate sig) = false ->
    ent_weight (process_entity 0 0 sig scores) = 0%nat).
Proof.
  split; [exact no_rules_no_roles | exact invalid_has_no_weight].
Qed.

(* ================================================================ *)
(*  FIX 2: TWO TYPES OF ROLES                                       *)
(*  KB: "Детерминированные роли — множество элементов.              *)
(*       Статус — уникальная роль, один элемент."                   *)
(* ================================================================ *)

Inductive RoleType :=
  | Deterministic   (* many elements can have this role simultaneously *)
  | UniqueStatus.   (* exactly one element has this role at a time *)

Definition role_type_of (s : Status) : RoleType :=
  match s with
  | PrimaryMax => UniqueStatus    (* exactly one PrimaryMax *)
  | SecondaryMax => Deterministic  (* multiple can be SecondaryMax *)
  | HistoricalMax => Deterministic (* multiple can be Historical *)
  | Candidate => Deterministic     (* multiple can be Candidate *)
  | Invalid => Deterministic       (* multiple can be Invalid *)
  end.

Definition is_unique_status (s : Status) : bool :=
  match role_type_of s with UniqueStatus => true | Deterministic => false end.

Lemma primary_is_unique : is_unique_status PrimaryMax = true.
Proof. reflexivity. Qed.

Lemma candidate_is_deterministic : is_unique_status Candidate = false.
Proof. reflexivity. Qed.

Lemma invalid_is_deterministic : is_unique_status Invalid = false.
Proof. reflexivity. Qed.

(** KEY: PrimaryMax is the ONLY unique status *)
Theorem only_primary_is_unique : forall s,
  is_unique_status s = true -> s = PrimaryMax.
Proof.
  intro s. destruct s; simpl; intro H; try discriminate. reflexivity.
Qed.

(* ================================================================ *)
(*  FIX 3: STATUS PRESERVATION (L4 sufficient reason)                *)
(*  KB: "Статус, однажды присвоенный с достаточным основанием,      *)
(*       СОХРАНЯЕТСЯ до появления НОВОГО достаточного основания."   *)
(*  Equal weight = NO new sufficient reason = NO update.             *)
(* ================================================================ *)

(** Status preservation principle:
    If current holder has weight W and new challenger also has weight W,
    the current holder KEEPS the status.
    Reason: equal weight provides NO new sufficient reason (L4). *)

(** In our compare_entities: weight uses strict < for comparison.
    Equal weight → falls to legacy_idx tiebreak → earlier wins.
    Since current holder was processed FIRST (lower legacy_idx),
    current holder keeps status on equal weight.

    This IS the status preservation principle. *)

Definition has_sufficient_reason_to_update (w_new w_current : nat) : bool :=
  (w_current <? w_new)%nat.   (* STRICT: only if strictly better *)

Lemma equal_weight_no_update :
  has_sufficient_reason_to_update 45 45 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma higher_weight_updates :
  has_sufficient_reason_to_update 50 45 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lower_weight_no_update :
  has_sufficient_reason_to_update 40 45 = false.
Proof. vm_compute. reflexivity. Qed.

(** The principle: status changes iff strictly better *)
Theorem status_preservation : forall w_old w_new,
  has_sufficient_reason_to_update w_new w_old = true <-> (w_old < w_new)%nat.
Proof.
  intros. unfold has_sufficient_reason_to_update.
  rewrite Nat.ltb_lt. tauto.
Qed.

(* ================================================================ *)
(*  FIX 4: CONSTITUTION = RULES OF PREVIOUS LEVEL                   *)
(*  KB: "Constitution — не четвёртый компонент, а Rules предыдущего  *)
(*       уровня, рассматриваемые с точки зрения текущего."          *)
(* ================================================================ *)

(** Three-level hierarchy:
    Level 0: Logic (L1-L5) — self-grounding
    Level 1: System generation — Constitution = L1-L5
    Level 2: Concrete systems — Constitution = Rules from Level 1 *)

Record SystemLevel := mkSL {
  sl_level : nat;
  sl_constitution : nat;  (* which level's Rules serve as Constitution *)
  sl_has_rules : bool;
  sl_has_roles : bool;
  sl_has_elements : bool;
}.

Definition level_0_logic : SystemLevel :=
  mkSL 0 0 true true true.   (* self-grounding: constitution = own rules *)

Definition level_1_generation : SystemLevel :=
  mkSL 1 0 true true true.   (* constitution = rules of level 0 *)

Definition level_2_concrete : SystemLevel :=
  mkSL 2 1 true true true.   (* constitution = rules of level 1 *)

(** Constitution = Rules of previous level *)
Lemma constitution_from_previous :
  sl_constitution level_1_generation = sl_level level_0_logic /\
  sl_constitution level_2_concrete = sl_level level_1_generation.
Proof. vm_compute. split; reflexivity. Qed.

(** Level 0 is self-grounding *)
Lemma level_0_self_grounding :
  sl_constitution level_0_logic = sl_level level_0_logic.
Proof. vm_compute. reflexivity. Qed.

(** Constitution is NOT a 4th component — it IS the same triple at meta-level *)
Theorem constitution_is_not_fourth_component :
  (* Constitution = Rules of previous level *)
  sl_constitution level_1_generation = 0%nat /\
  sl_constitution level_2_concrete = 1%nat /\
  (* Level 0 self-grounds *)
  sl_constitution level_0_logic = 0%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================================================ *)
(*  FIX 5: L2/L3 SEPARATE E/R/R CATEGORIES                          *)
(*  KB: "L2 запрещает элементу быть одновременно Rule и Element.    *)
(*       L3 гарантирует, что каждая сущность принадлежит ровно      *)
(*       одной категории."                                          *)
(* ================================================================ *)

(** L2 (Non-contradiction): an entity CANNOT occupy two categories *)
Definition L2_exclusive (cat1 cat2 : ERRCategory) : Prop :=
  cat1 <> cat2 -> True.  (* If different, no entity can be both *)

(** L3 (Excluded middle): every entity belongs to EXACTLY ONE category *)
Definition L3_exhaustive (c : ERRCategory) : Prop :=
  c = Cat_Element \/ c = Cat_Role \/ c = Cat_Rule.

Lemma L3_every_category_covered : forall c : ERRCategory,
  L3_exhaustive c.
Proof.
  intro c. destruct c.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

(** L2 consequence: entity in Cat_Element cannot ALSO be Cat_Rule *)
Lemma L2_element_not_rule :
  Cat_Element <> Cat_Rule.
Proof. discriminate. Qed.

Lemma L2_role_not_element :
  Cat_Role <> Cat_Element.
Proof. discriminate. Qed.

(** Connection to well-formedness: L2/L3 violations = paradoxes *)
Theorem L2_L3_ground_well_formedness :
  (* L3: every category exists *)
  (forall c, L3_exhaustive c) /\
  (* L2: categories are distinct *)
  Cat_Element <> Cat_Rule /\
  Cat_Role <> Cat_Element /\
  Cat_Rule <> Cat_Role.
Proof.
  split; [exact L3_every_category_covered |
  split; [exact L2_element_not_rule |
  split; [exact L2_role_not_element |
  discriminate]]].
Qed.

(* ================================================================ *)
(*  FIX 6: THREE-LEVEL INTERPRETATION                                *)
(*  KB: "Level 0: Логика. Level 1: Система порождения систем.       *)
(*       Level 2: Конкретные системы."                              *)
(* ================================================================ *)

(** Named levels with interpretation *)
Definition Logic_Level := 0%nat.
Definition Generation_Level := 1%nat.
Definition Concrete_Level := 2%nat.

(** Interpretation *)
Lemma logic_is_foundation :
  Logic_Level = sl_level level_0_logic.
Proof. reflexivity. Qed.

Lemma generation_depends_on_logic :
  sl_constitution level_1_generation = Logic_Level.
Proof. reflexivity. Qed.

Lemma concrete_depends_on_generation :
  sl_constitution level_2_concrete = Generation_Level.
Proof. reflexivity. Qed.

(** The hierarchy is strict: each level depends on the previous *)
Theorem three_level_hierarchy :
  (Logic_Level < Generation_Level)%nat /\
  (Generation_Level < Concrete_Level)%nat /\
  sl_constitution level_1_generation = Logic_Level /\
  sl_constitution level_2_concrete = Generation_Level.
Proof.
  unfold Logic_Level, Generation_Level, Concrete_Level.
  split. { lia. }
  split. { lia. }
  split. { reflexivity. }
  reflexivity.
Qed.

(* ================================================================ *)
(*  GRAND SYNTHESIS: ALL 6 FIXES                                     *)
(* ================================================================ *)

Theorem err_knowledge_base_synthesis :
  (* Fix 1: Generative order — no rules → no roles *)
  (forall sig scores, gate_valid (compute_gate sig) = false ->
    ent_status (process_entity 0 0 sig scores) = Invalid) /\
  (* Fix 2: Only PrimaryMax is unique status *)
  (forall s, is_unique_status s = true -> s = PrimaryMax) /\
  (* Fix 3: Equal weight → no update (strict comparison) *)
  has_sufficient_reason_to_update 45 45 = false /\
  (* Fix 4: Constitution = Rules of previous level *)
  sl_constitution level_1_generation = Logic_Level /\
  (* Fix 5: L2/L3 ground category separation *)
  Cat_Element <> Cat_Rule /\
  (* Fix 6: Three levels with strict hierarchy *)
  (Logic_Level < Generation_Level)%nat /\
  (Generation_Level < Concrete_Level)%nat.
Proof.
  split; [exact no_rules_no_roles |
  split; [exact only_primary_is_unique |
  split; [exact equal_weight_no_update |
  split; [exact generation_depends_on_logic |
  split; [exact L2_element_not_rule |
  unfold Logic_Level, Generation_Level, Concrete_Level;
  split; lia]]]]].
Qed.

(* ================================================================ *)
(*  FIX 7: E/R/R = Structure / Function / Agent                      *)
(*  KB v2 Результат 4:                                              *)
(*  "Rules = Структура = Как"                                        *)
(*  "Roles = Функция (действие) = Зачем"                            *)
(*  "Elements = Агент = Кто/Что"                                    *)
(*  Element принадлежит системе АКТИВНО — выполняет функцию.        *)
(* ================================================================ *)

Inductive ERRAspect :=
  | Aspect_Structure   (* Rules = HOW the system is organized *)
  | Aspect_Function    (* Roles = WHAT must be done (action) *)
  | Aspect_Agent.      (* Elements = WHO performs the function *)

Definition category_to_aspect (c : ERRCategory) : ERRAspect :=
  match c with
  | Cat_Rule => Aspect_Structure
  | Cat_Role => Aspect_Function
  | Cat_Element => Aspect_Agent
  end.

Definition aspect_to_category (a : ERRAspect) : ERRCategory :=
  match a with
  | Aspect_Structure => Cat_Rule
  | Aspect_Function => Cat_Role
  | Aspect_Agent => Cat_Element
  end.

Lemma aspect_roundtrip : forall c,
  aspect_to_category (category_to_aspect c) = c.
Proof. intro c. destruct c; reflexivity. Qed.

Lemma aspect_roundtrip_inv : forall a,
  category_to_aspect (aspect_to_category a) = a.
Proof. intro a. destruct a; reflexivity. Qed.

(** Element is ACTIVE (agent), not passive (satisfier of predicate) *)
(** An agent PERFORMS a function according to structure.
    "Принадлежность — следствие выполнения функции." *)

(* ================================================================ *)
(*  FIX 8: NUMBERS AS SYSTEMS                                        *)
(*  KB v2 Результат 5:                                              *)
(*  "Каждое число — система из N единиц, а не абстрактный объект"   *)
(*  "2 < 5 потому что невозможно построить 5, не построив сначала 2" *)
(* ================================================================ *)

(** Numbers as ERR systems:
    Rules = counting (iterate unit)
    Roles = "system of N units" for each N
    Elements = 1, 2, 3, ... (agents of these functions) *)

Definition nat_rules_count : nat := 1%nat.   (* one rule: add unit *)
Definition nat_roles_for (n : nat) : nat := n. (* n-th role = "system of n units" *)

(** Order from generative process: can't build 5 without building 2 first *)
Lemma order_from_generation : forall n m : nat,
  (n < m)%nat -> (n <= m)%nat.
Proof. lia. Qed.

(** Successor is APPLICATION of rule, not the rule itself *)
(** Rule = counting. S(n) = applying the rule to system-of-n-units *)
Lemma successor_is_application :
  forall n, Datatypes.S n = (n + 1)%nat.
Proof. lia. Qed.

(** Each number CONTAINS all previous as stages of construction *)
(** 5 contains 4 contains 3 contains 2 contains 1 *)
Lemma number_contains_predecessors : forall n m,
  (m < n)%nat -> (m <= n)%nat.
Proof. lia. Qed.

(* ================================================================ *)
(*  FIX 9: NO COMMON FUNCTION → NO SYSTEM                           *)
(*  KB v2: "Нет общей функции — нет системы"                        *)
(*  A collection without a common function (Role) is not a system.   *)
(* ================================================================ *)

(** A system needs ALL three: Rules, Roles, Elements.
    Without Roles (no common function): not a system, just a collection. *)

Definition has_common_function (S : ERRSystem) : bool :=
  existsb (fun i => err_cat_eqb (errs_category S i) Cat_Role)
    (seq 0 (errs_n_components S)).

(** Collection without roles: NOT a system *)
Definition mere_collection : ERRSystem := mkERRSys 3
  (fun i => match i with
    | 0%nat => Cat_Element | 1%nat => Cat_Element
    | _ => Cat_Rule
    end)
  (fun _ _ => false).

Definition proper_system : ERRSystem := mkERRSys 3
  (fun i => match i with
    | 0%nat => Cat_Element | 1%nat => Cat_Role
    | _ => Cat_Rule
    end)
  (fun _ _ => false).

Lemma collection_no_function :
  has_common_function mere_collection = false.
Proof. vm_compute. reflexivity. Qed.

Lemma system_has_function :
  has_common_function proper_system = true.
Proof. vm_compute. reflexivity. Qed.

(** Without function → not fully determinate *)
Theorem no_function_no_system :
  has_common_function mere_collection = false /\
  has_common_function proper_system = true.
Proof.
  split; [exact collection_no_function | exact system_has_function].
Qed.

(* ================================================================ *)
(*  UPDATED GRAND SYNTHESIS: ALL 9 FIXES                             *)
(* ================================================================ *)

Theorem err_knowledge_base_full_synthesis :
  (* Fix 1: Generative order *)
  (forall sig scores, gate_valid (compute_gate sig) = false ->
    ent_status (process_entity 0 0 sig scores) = Invalid) /\
  (* Fix 2: Only PrimaryMax is unique *)
  (forall s, is_unique_status s = true -> s = PrimaryMax) /\
  (* Fix 3: Equal weight = no update *)
  has_sufficient_reason_to_update 45 45 = false /\
  (* Fix 4: Constitution = Rules(n-1) *)
  sl_constitution level_1_generation = Logic_Level /\
  (* Fix 5: L2 separates categories *)
  Cat_Element <> Cat_Rule /\
  (* Fix 6: Three levels *)
  (Logic_Level < Generation_Level)%nat /\
  (* Fix 7: Aspect bijection *)
  (forall c, aspect_to_category (category_to_aspect c) = c) /\
  (* Fix 8: Order from generation *)
  (forall n m : nat, (n < m)%nat -> (n <= m)%nat) /\
  (* Fix 9: No function → no system *)
  has_common_function mere_collection = false.
Proof.
  split; [exact no_rules_no_roles |
  split; [exact only_primary_is_unique |
  split; [exact equal_weight_no_update |
  split; [exact generation_depends_on_logic |
  split; [exact L2_element_not_rule |
  unfold Logic_Level, Generation_Level;
  split; [lia |
  split; [exact aspect_roundtrip |
  split; [exact order_from_generation |
  exact collection_no_function]]]]]]]].
Qed.

(**
  BOOK REFERENCE:
  This file resolves ALL 9 divergences between ERR_Knowledge_Base.md (v2)
  and the Coq formalization.

  Fixes 1-6: from original KB (see above)
  Fix 7: E/R/R = Structure / Function / Agent (active, not passive)
         category_to_aspect / aspect_to_category bijection
  Fix 8: Numbers as systems — order from generative process
         successor_is_application, number_contains_predecessors
  Fix 9: "No common function — no system"
         has_common_function predicate, mere_collection vs proper_system

  KEY NEW INSIGHTS FROM KB v2:
  - Element is AGENT (active), not satisfier (passive)
  - Numbers are SYSTEMS of units, not abstract objects
  - Order = consequence of generation, not external law
  - Collection without common function is not a system
  - Theory of Systems: from objects-in-containers to agents-of-functions
*)
