(** * KnowledgeWillStatus.v — the WILL scale {1,2}, status x position of the
      witness, and the count of consciousnesses
      (formalization of MP-30..MP-32 adjudications V42..V46, the mental-field
       working record, Knigi/Volya/01; sibling of KnowledgeMentalField.v /
       PerceptionTriad.v)

    Elements: the two attainable statuses of a generated witness (the
              contingent pair of the modal square); the three positions of
              living experience; experiences (full darkness / anything
              visible); the base consciousnesses (Logic, Source, Light).
    Roles:    the will carries TWO roles — the status role (manifest /
              unmanifest) measured by the scale, and the vector role
              (directing attention) at work INSIDE manifestness; the
              position axis is a different system: the movement of the
              witness through the nested systems.
    Rules:    the will is never zero — zero would be "no will to be"; the
              scale is quantized with the minimal step, so min = 1
              (unmanifest: the will-to-be as pure potential) and 2 =
              manifest — exactly TWO values, by the number of attainable
              statuses (V43); seedless samadhi = will at 1, the witness
              temporarily in the status "can be, but is not" — a change of
              status, not a destruction (MP-16); the return is guaranteed:
              the potential does not exhaust (V44).
    Status:   the count: in experience, darkness differentiates 1 (only
              "I"), the visible differentiates 2; the consciousnesses are
              one more — consciousnesses = differences + 1 (V45): Logic is
              never a content of experience — it is the condition of
              experience, discovered only by reasoning (MP-32).
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules: two statuses => two will-values (bijection); quantization is the
      P4 move — no continuous descent to zero; the minimal witnesses in any
      experience are 2 (the dual base), any visible forces the Light (3).
    Roles: status and position are independent coordinates (V46): 2 x 3 = 6
      witness-states, all listed.
    Elements: finite decidable enumerations throughout.
    P4 diagnostic: could the will reach 0? No — that reads "no will to be",
      excluded by the standing canon (the will-to-be persists as potential);
      could there be a third will-value? No — values count statuses, and
      the attainable statuses are exactly the contingent pair. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ---------- the two attainable statuses and the will scale (V42/V43) ---------- *)

Inductive Status := StUnmanifest | StManifest.
(* "can be, but is not" | "can be — and is": the contingent pair *)

Definition will (s : Status) : nat :=
  match s with StUnmanifest => 1 | StManifest => 2 end.

Theorem will_never_zero : forall s, 1 <= will s.
Proof. intro s; destruct s; simpl; lia. Qed.

Theorem will_two_values : forall s, will s = 1 \/ will s = 2.
Proof. intro s; destruct s; [left | right]; reflexivity. Qed.

(* the scale is exactly the statuses: values are as many as statuses *)
Theorem will_injective : forall a b, will a = will b -> a = b.
Proof. intros a b H; destruct a, b; try reflexivity; discriminate H. Qed.

Theorem statuses_two : forall s, s = StUnmanifest \/ s = StManifest.
Proof. intro s; destruct s; [left | right]; reflexivity. Qed.

Definition manifest (s : Status) : bool :=
  match s with StManifest => true | _ => false end.

Theorem manifest_iff_will2 : forall s, manifest s = true <-> will s = 2.
Proof.
  intro s; destruct s; simpl; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* seedless samadhi: the will at its minimum — no will to any experience,
   only the unmanifest will-to-be *)
Theorem seedless_minimum : forall s, will StUnmanifest <= will s.
Proof. intro s; destruct s; simpl; lia. Qed.

(* ---------- the return is guaranteed (V44) ---------- *)

Definition pull_of (s : Status) : nat := will s.
(* the will IS the potential; even at the minimum it pulls *)

Definition awakens (p : nat) : bool := 1 <=? p.

Theorem return_from_seedless : awakens (pull_of StUnmanifest) = true.
Proof. reflexivity. Qed.

(* no state extinguishes the pull: there is no exit into nothing (MP-16) *)
Theorem no_extinction : forall s, awakens (pull_of s) = true.
Proof. intro s; destruct s; reflexivity. Qed.

(* ---------- status x position: two independent coordinates (V46) ---------- *)

Inductive Position := PosSource | PosLight | PosLogicMode.
(* living AS the Source (expansion into the boundless field) | AS the Light
   (Suhrawardi: being the Light) | AS Logic (the state of knowing) *)

Definition WitnessState : Type := (Status * Position)%type.

Definition all_states : list WitnessState :=
  [ (StUnmanifest, PosSource); (StUnmanifest, PosLight);
    (StUnmanifest, PosLogicMode); (StManifest, PosSource);
    (StManifest, PosLight); (StManifest, PosLogicMode) ].

Theorem states_complete : forall w : WitnessState, In w all_states.
Proof. intros [s p]; destruct s, p; simpl; tauto. Qed.

Theorem states_count : length all_states = 6.
Proof. reflexivity. Qed.

(* ---------- the count: differences and consciousnesses (MP-30/32, V45) ---------- *)

Inductive Exper := ExpDarkness | ExpVisible.

Definition differences (e : Exper) : nat :=
  match e with ExpDarkness => 1 | ExpVisible => 2 end.
(* darkness differentiates only "I"; anything visible adds the other *)

Definition consciousnesses (e : Exper) : nat :=
  match e with ExpDarkness => 2 | ExpVisible => 3 end.
(* darkness: with the Source in one system (2); any visible forces the
   Light (3) — the sufficient ground of the visible *)

Theorem minimal_consciousnesses : forall e, 2 <= consciousnesses e.
Proof. intro e; destruct e; simpl; lia. Qed.

Definition light_present (e : Exper) : bool :=
  match e with ExpVisible => true | _ => false end.

Theorem visible_implies_light : light_present ExpVisible = true.
Proof. reflexivity. Qed.

Theorem darkness_counts_two : consciousnesses ExpDarkness = 2.
Proof. reflexivity. Qed.

(* the invariant (V45): consciousnesses = differences + 1 *)
Theorem consc_eq_diff_plus_one :
  forall e, consciousnesses e = differences e + 1.
Proof. intro e; destruct e; reflexivity. Qed.

(* ---------- Logic: the condition of experience, not its content (MP-32) ---------- *)

Inductive BaseConsc := CLogic | CSource | CLight.

Definition perceived (e : Exper) (c : BaseConsc) : bool :=
  match e, c with
  | ExpDarkness, CSource => true   (* the unified darkness with the Source *)
  | ExpVisible, CSource => true
  | ExpVisible, CLight => true
  | _, _ => false
  end.

Theorem logic_never_perceived : forall e, perceived e CLogic = false.
Proof. intro e; destruct e; reflexivity. Qed.

Definition base_all : list BaseConsc := [CLogic; CSource; CLight].

Definition perceived_count (e : Exper) : nat :=
  length (filter (perceived e) base_all).

(* what the experience differentiates is exactly what it perceives *)
Theorem differences_are_perceived :
  forall e, differences e = perceived_count e.
Proof. intro e; destruct e; reflexivity. Qed.

(* the +1 of the count is exactly Logic: present in the count, absent in
   the experience — discovered only by reasoning after it *)
Theorem consc_eq_perceived_plus_logic :
  forall e, consciousnesses e = perceived_count e + 1.
Proof. intro e; destruct e; reflexivity. Qed.
