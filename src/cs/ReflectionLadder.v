(** * ReflectionLadder.v — the dichotomy and Lawvere are ONE ladder, at arbitrary B
      Layer 3 of the boundary thread: HaltingRoleLimit (engine) -> BoundaryDecidability
      (three faces, #97) -> BoundaryDichotomy (the watershed, #1858/H77) -> HERE (the
      watershed and Lawvere inter-derived, statuses generalized from bool to any B).

      THESIS (synthesis+framing, NOT a new theorem):
      Lawvere's fixed-point theorem and the H77 dichotomy decompose into ONE ladder of
      three rungs over an arbitrary status-carrier B with a twist f : B -> B:

        RUNG 1 (twist_hit_reflects)  : ONE hit of the f-twist of a classifier c by the
          enumeration φ yields a REFLECTION POINT — exists d, φ d d = f (c d).
          (Weaker hypothesis than full point-surjectivity: a single hit suffices.)
        RUNG 2 (reflection_at_diagonal_fixed_point) : reflection applied to the DIAGONAL
          classifier itself is a fixed point of f — φ d d = f (φ d d).  This IS the
          Lawvere engine, isolated as its own rung.
        RUNG 3 (twisted_diagonal_escapes) : a fixpoint-free twist NAMES the escapee —
          the f-twisted diagonal (fun x => f (φ x x)) is never in φ's range.
          Constructively sharper than "not surjective": the witness is exhibited.

      Assembled: lawvere_via_ladder recovers lawvere_fixed_point (#108); cantor_escape /
      nat_escape are the B=bool/negb and B=nat/S instances; and via the pointwise bridge
      reflection_point_bool, the Prop-level SelfReflective of BoundaryDichotomy is EXACTLY
      B-level negb-reflection of the decider's own bool status — so the H77 incompatibility
      re-derives as the B=bool, f=negb, c:=dec slice of the ladder
      (prop_incompatibility_via_ladder).

    Reuses (genuine unification, not restatement):
      - cs/HaltingRoleLimit.v     : negb_no_fixpoint (the seed).
      - cs/LawvereFixedPoint.v    : point_surjective (vocabulary; #108's theorem recovered).
      - cs/BoundaryDecidability.v : ElementDrawn (for the re-derivation).
      - cs/BoundaryDichotomy.v    : SelfReflective (the Prop-level shape being bridged).

    Elements: status-carriers B (bool with negb; nat with S); enumerations φ : A -> (A -> B);
              classifiers c : A -> B
    Roles:    hit = "named from within" (point_surjective = everything named); the
              reflection point d = the self-application role; the twist f = the obstruction
              role (its fixed points are where reflection is harmless); B = the generalized
              carrier of boundary statuses
    Rules:    rung 1 (one hit of the twist => reflection point); rung 2 (reflection at the
              diagonal => fixed point of f); rung 3 (fixpoint-free twist => NAMED escapee)

    ============ E/R/R разбор ============
      Rules (L5): правило подъёма — ОДНО попадание φ в f-твист классификатора рождает точку
                  отражения (слабее сюръективности); правило замыкания — отражение на самом
                  диагональном классификаторе даёт неподвижную точку f (механизм Ловера,
                  изолированный); правило побега — бесфиксточечный твист ИМЕНУЕТ беглеца
                  (f-твист диагонали вне образа φ).
      Roles (L4): hit — роль «названности изнутри» (point_surjective = «всё названо»);
                  точка отражения d — роль само-применения; твист f — роль обструкции
                  (неподвижные точки f = где отражение безвредно); B — обобщённый носитель
                  статусов границы (bool -> произвольный).
      Elements  : bool/negb (Кантор; мост к Prop-дихотомии H77), nat/S (нет перечисления
                  A->nat), конкретные перечислители φ и классификаторы c.
    ДИАГНОСТИКА (P4): лестница локализует, ГДЕ живёт невозможность — не в «мощности» и не в
      бесконечности B, а в ОДНОЙ точке: f-твист диагонали, именованный беглец (конструктивно:
      не «¬∀», а предъявленный классификатор вне образа).  Сюръективность падает на конкретном
      классификаторе.  Прежние результаты — срезы лестницы: Ловер (#108) = ступени 1+2;
      Кантор = bool/negb-инстанс ступени 3; H77-несовместимость = срез B=bool, f=negb,
      c:=dec через мост reflection_point_bool.  Невынужденность проверена: Leibniz-форма hit
      (φ a = c) вынуждена совместимостью с point_surjective (#108) — поточечная потребовала бы
      funext; ослабление сюръективности до одного hit вынуждено содержанием доказательства;
      твист через f, не f⁻¹ — f не обязан быть инъективным.  Честно: Ловер 1969 — классика,
      «беглец» — стандартное содержание канторовского доказательства; ново — лестничная
      декомпозиция (hit ⟹ отражение ⟹ фикспойнт/беглец), машинное взаимовыведение с
      Prop-дихотомией (мост) и инстансы bool/nat в одном каркасе.  НЕ новая теорема.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Bool Lia.
From ToS Require Import cs.HaltingRoleLimit.
From ToS Require Import cs.LawvereFixedPoint.
From ToS Require Import cs.BoundaryDecidability.
From ToS Require Import cs.BoundaryDichotomy.

(* ===================================================================== *)
(*  THE LADDER (arbitrary status-carrier B, arbitrary twist f)            *)
(* ===================================================================== *)

Section ReflectionLadder.

  Variables (A B : Type).

  (** φ NAMES the classifier c: c is drawn from WITHIN the domain. *)
  Definition hit (phi : A -> (A -> B)) (c : A -> B) : Prop :=
    exists a, phi a = c.

  (** The B-valued diagonal status of an enumeration. *)
  Definition diagB (phi : A -> (A -> B)) : A -> B := fun a => phi a a.

  (** RUNG 1 — ONE hit of the f-twist yields a reflection point: a self-application
      point where the true diagonal status is the twist of what c says.  Generalizes
      surjective_diagonal_self_reflective (BoundaryDichotomy) from bool/negb to
      arbitrary B/f, and weakens full surjectivity to a single hit. *)
  Lemma twist_hit_reflects :
    forall (phi : A -> (A -> B)) (f : B -> B) (c : A -> B),
      hit phi (fun x => f (c x)) ->
      exists d, phi d d = f (c d).
  Proof.
    intros phi f c [a Ha]. exists a.
    pose proof (f_equal (fun h : A -> B => h a) Ha) as E. simpl in E.
    exact E.
  Qed.

  (** RUNG 2 — reflection applied to the DIAGONAL classifier itself is a fixed point
      of the twist: this IS Lawvere's engine, isolated as its own rung. *)
  Lemma reflection_at_diagonal_fixed_point :
    forall (phi : A -> (A -> B)) (f : B -> B),
      hit phi (fun x => f (diagB phi x)) ->
      exists b, f b = b.
  Proof.
    intros phi f H.
    destruct (twist_hit_reflects phi f (diagB phi) H) as [d Hd].
    exists (phi d d). symmetry. exact Hd.
  Qed.

  (** Lawvere's fixed-point theorem (#108) RECOVERED through the ladder:
      surjectivity supplies the needed hit for every twist simultaneously. *)
  Theorem lawvere_via_ladder :
    forall (phi : A -> (A -> B)),
      point_surjective phi -> forall f : B -> B, exists b, f b = b.
  Proof.
    intros phi Hsurj f.
    apply (reflection_at_diagonal_fixed_point phi f).
    apply Hsurj.
  Qed.

  (** RUNG 3 — a fixpoint-free twist NAMES the escapee: the f-twisted diagonal is
      never in φ's range.  Constructively sharper than "not surjective". *)
  Theorem twisted_diagonal_escapes :
    forall (phi : A -> (A -> B)) (f : B -> B),
      (forall b, f b <> b) ->
      ~ hit phi (fun x => f (diagB phi x)).
  Proof.
    intros phi f Hff H.
    destruct (reflection_at_diagonal_fixed_point phi f H) as [b Hb].
    exact (Hff b Hb).
  Qed.

  (** No-surjection, through the named escapee (the ladder form of #108's corollary). *)
  Corollary no_surjection_via_escape :
    forall (phi : A -> (A -> B)) (f : B -> B),
      (forall b, f b <> b) -> ~ point_surjective phi.
  Proof.
    intros phi f Hff Hsurj.
    apply (twisted_diagonal_escapes phi f Hff). apply Hsurj.
  Qed.

End ReflectionLadder.

Arguments hit {A B} phi c.
Arguments diagB {A B} phi a.

(* ===================================================================== *)
(*  INSTANCES — the escapee, named                                        *)
(* ===================================================================== *)

(** B=bool, f=negb: CANTOR with the escapee exhibited — the negb-twisted diagonal. *)
Corollary cantor_escape :
  forall (Dom : Type) (phi : Dom -> (Dom -> bool)),
    ~ hit phi (fun x => negb (phi x x)).
Proof.
  intros Dom phi.
  apply (twisted_diagonal_escapes Dom bool phi negb).
  intros b H. apply (negb_no_fixpoint b). symmetry. exact H.
Qed.

(** B=nat, f=S: no φ names all nat-valued classifiers — the successor-twisted
    diagonal escapes (the ladder form of nat_fun_not_enumerable, #108). *)
Corollary nat_escape :
  forall (Dom : Type) (phi : Dom -> (Dom -> nat)),
    ~ hit phi (fun x => S (phi x x)).
Proof.
  intros Dom phi.
  apply (twisted_diagonal_escapes Dom nat phi S).
  intro n. lia.
Qed.

(* ===================================================================== *)
(*  BRIDGE — the Prop-level dichotomy (H77) is the B=bool, f=negb slice   *)
(* ===================================================================== *)

(** Pointwise bridge: given a correct decider bit b for P, the Prop-level reflection
    condition (P <-> c = false) IS the B-level negb-reflection equation b = negb c. *)
Lemma reflection_point_bool :
  forall (P : Prop) (b c : bool),
    (b = true <-> P) ->
    ((P <-> c = false) <-> b = negb c).
Proof.
  intros P b c HbP. destruct b, c; simpl; split; intro H.
  - (* b=true, c=true, -> : goal true = false *)
    apply (proj1 H). apply (proj1 HbP). reflexivity.
  - (* b=true, c=true, <- : H : true = false *)
    discriminate.
  - (* b=true, c=false, -> *)
    reflexivity.
  - (* b=true, c=false, <- : goal P <-> false = false *)
    split; intro; [reflexivity | apply (proj1 HbP); reflexivity].
  - (* b=false, c=true, -> *)
    reflexivity.
  - (* b=false, c=true, <- : goal P <-> true = false *)
    split; intro HP; [ | discriminate].
    apply (proj2 HbP) in HP. discriminate.
  - (* b=false, c=false, -> : goal false = true *)
    apply (proj2 HbP). apply (proj2 H). reflexivity.
  - (* b=false, c=false, <- : H : false = true *)
    discriminate.
Qed.

(** ★ The Prop-level SelfReflective (BoundaryDichotomy, H77) is EXACTLY B-level
    negb-reflection of the decider's own bool status. *)
Theorem self_reflective_is_negb_reflection :
  forall (Dom : Type) (Side : Dom -> Prop) (dec : Dom -> bool),
    (forall x, dec x = true <-> Side x) ->
    (SelfReflective Side <-> (forall c : Dom -> bool, exists d, dec d = negb (c d))).
Proof.
  intros Dom Side dec Hdec. split.
  - intros HSR c. destruct (HSR c) as [d Hd].
    exists d.
    exact (proj1 (reflection_point_bool (Side d) (dec d) (c d) (Hdec d)) Hd).
  - intros Hrefl c. destruct (Hrefl c) as [d Hd].
    exists d.
    exact (proj2 (reflection_point_bool (Side d) (dec d) (c d) (Hdec d)) Hd).
Qed.

(** ★ The H77 incompatibility RE-DERIVED as a ladder slice: a correct decider,
    negb-reflected at ITSELF (c := dec), yields dec d = negb (dec d) — the seed.
    Same statement as element_drawn_excludes_self_reflective, second proof THROUGH
    the general layer: the dichotomy is the B=bool, f=negb, c:=dec instance. *)
Theorem prop_incompatibility_via_ladder :
  forall (Dom : Type) (Side : Dom -> Prop),
    ElementDrawn Side -> SelfReflective Side -> False.
Proof.
  intros Dom Side [dec Hdec] HSR.
  destruct (proj1 (self_reflective_is_negb_reflection Dom Side dec Hdec) HSR dec)
    as [d Hd].
  exact (negb_no_fixpoint (dec d) Hd).
Qed.

(* ===================================================================== *)
(*  SYNTHESIS — one ladder, all the slices                                *)
(* ===================================================================== *)

(** ★ CAPSTONE.  Lawvere (#108), the named escapee, Cantor (bool/negb), and the
    H77 dichotomy are ONE structure: hit-of-twist ⟹ reflection ⟹ (at the diagonal)
    fixed point; fixpoint-free twist ⟹ named escapee ⟹ no surjection. *)
Theorem reflection_ladder :
  (* rungs 1+2 assembled: Lawvere's fixed-point theorem recovered *)
  (forall (A B : Type) (phi : A -> (A -> B)),
      point_surjective phi -> forall f : B -> B, exists b, f b = b)
  (* rung 3: the named escapee *)
  /\ (forall (A B : Type) (phi : A -> (A -> B)) (f : B -> B),
      (forall b, f b <> b) -> ~ hit phi (fun x => f (diagB phi x)))
  (* bool/negb slice: Cantor's escapee *)
  /\ (forall (Dom : Type) (phi : Dom -> (Dom -> bool)),
      ~ hit phi (fun x => negb (phi x x)))
  (* Prop slice: the H77 dichotomy *)
  /\ (forall (Dom : Type) (Side : Dom -> Prop),
      ElementDrawn Side -> SelfReflective Side -> False).
Proof.
  repeat split.
  - exact lawvere_via_ladder.
  - exact twisted_diagonal_escapes.
  - exact cantor_escape.
  - exact prop_incompatibility_via_ladder.
Qed.

Print Assumptions twisted_diagonal_escapes.
Print Assumptions self_reflective_is_negb_reflection.
Print Assumptions reflection_ladder.
