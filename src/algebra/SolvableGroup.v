(** * SolvableGroup.v — the Abel–Ruffini engine: perfect ⇒ not solvable
    Elements: an abstract group, its subgroups, commutators
    Roles:    solvability as the role-limit "derived series reaches {e}"
    Rules:    derived subgroup minimal containing all commutators;
              a perfect non-trivial group can never reach {e}
    STATUS:   18 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The group-theoretic half of Abel–Ruffini, formalized abstractly with NO
    axioms (no classic, no funext — everything constructive over an abstract
    GroupStr with Leibniz equality). The core:

      Solvable G  :=  the derived series  G ⊵ [G,G] ⊵ [[G,G],[G,G]] ⊵ …
                      reaches the trivial subgroup {e}.

      Perfect G   :=  G is its own derived subgroup ([G,G] = G).

      THEOREM (perfect_nontrivial_not_solvable):
        a perfect group with a non-identity element is NOT solvable.

    Positive side (radical-step groups are abelian, hence solvable):
      abelian_solvable, and a concrete instance boolGroup_solvable (Z/2).

    HONEST SCOPE / THE WALL.  The quintic is unsolvable because its Galois
    group is S₅, whose commutator subgroup A₅ is a non-abelian SIMPLE group,
    hence PERFECT.  Simplicity of A₅ is heavy 60-element combinatorics; here it
    is supplied as the explicit premise `Perfect Quintic` (NOT a global axiom —
    the file stays at 0 axioms).  Given that premise, the engine below
    discharges "not solvable" with full rigor.  The remaining frontier — A₅'s
    simplicity proved in-engine, the algebraic closure of Q (a completed
    object), and the full radical-tower⇔solvable-group equivalence — stays a
    role-limit, characterized in the prose of Part XI rather than faked.
*)

From Stdlib Require Import Bool.

Section GroupTheory.

(* ===================== abstract group ===================== *)
Record GroupStr : Type := {
  gT  :> Type;
  gop : gT -> gT -> gT;
  gid : gT;
  ginv : gT -> gT;
  gassoc : forall a b c, gop a (gop b c) = gop (gop a b) c;
  gidl : forall a, gop gid a = a;
  gidr : forall a, gop a gid = a;
  ginvl : forall a, gop (ginv a) a = gid;
  ginvr : forall a, gop a (ginv a) = gid
}.

Context (G : GroupStr).

Local Notation "x ** y" := (gop G x y) (at level 40, left associativity).

(* ===================== group lemmas ===================== *)

Lemma inv_id : ginv G (gid G) = gid G.
Proof. rewrite <- (gidl G (ginv G (gid G))). apply ginvr. Qed.

Lemma inv_unique : forall a b, a ** b = gid G -> b = ginv G a.
Proof.
  intros a b H.
  rewrite <- (gidl G b).
  rewrite <- (ginvl G a).
  rewrite <- (gassoc G).
  rewrite H. rewrite (gidr G). reflexivity.
Qed.

Lemma inv_op : forall x y, ginv G (x ** y) = (ginv G y) ** (ginv G x).
Proof.
  intros x y. symmetry. apply inv_unique.
  rewrite <- (gassoc G x y (gop G (ginv G y) (ginv G x))).
  rewrite (gassoc G y (ginv G y) (ginv G x)).
  rewrite (ginvr G y).
  rewrite (gidl G (ginv G x)).
  exact (ginvr G x).
Qed.

(* the commutator [a,b] = a b a⁻¹ b⁻¹ *)
Definition comm (a b : gT G) : gT G := (a ** b) ** ((ginv G a) ** (ginv G b)).

Lemma comm_eq_id : forall a b, a ** b = b ** a -> comm a b = gid G.
Proof.
  intros a b Hab. unfold comm.
  rewrite <- (inv_op b a).
  rewrite Hab.
  exact (ginvr G (b ** a)).
Qed.

(* ===================== subgroups ===================== *)
Record SubGrp : Type := {
  mem : gT G -> Prop;
  sub_id : mem (gid G);
  sub_op : forall a b, mem a -> mem b -> mem (a ** b);
  sub_inv : forall a, mem a -> mem (ginv G a)
}.

Definition fullS : SubGrp :=
  {| mem := fun _ => True;
     sub_id := I;
     sub_op := fun a b _ _ => I;
     sub_inv := fun a _ => I |}.

Definition trivialS : SubGrp.
Proof.
  refine {| mem := fun x => x = gid G |}.
  - reflexivity.
  - intros a b Ha Hb. rewrite Ha, Hb. apply gidl.
  - intros a Ha. rewrite Ha. apply inv_id.
Defined.

Definition mem_equiv (H K : SubGrp) := forall x, mem H x <-> mem K x.

Definition contains_comms (H K : SubGrp) :=
  forall a b, mem H a -> mem H b -> mem K (comm a b).

(* D is THE derived subgroup of H: minimal subgroup containing all [a,b] *)
Definition IsDerived (H D : SubGrp) :=
  (forall x, mem D x -> mem H x)
  /\ contains_comms H D
  /\ (forall K, contains_comms H K -> forall x, mem D x -> mem K x).

Definition AbelianS (H : SubGrp) :=
  forall a b, mem H a -> mem H b -> a ** b = b ** a.

(* an abelian subgroup's derived subgroup is trivial *)
Lemma abelian_IsDerived_trivial : forall H, AbelianS H -> IsDerived H trivialS.
Proof.
  intros H Hab. split; [|split].
  - intros x Hx. cbn in Hx. rewrite Hx. apply (sub_id H).
  - intros a b Ha Hb. change (comm a b = gid G).
    apply comm_eq_id. apply (Hab a b Ha Hb).
  - intros K Hcomms x Hx. cbn in Hx. rewrite Hx. apply (sub_id K).
Qed.

(* ===================== solvability via the derived series ===== *)
Inductive SolvableFrom : SubGrp -> Prop :=
| solv_triv : forall H, (forall x, mem H x -> x = gid G) -> SolvableFrom H
| solv_step : forall H D, IsDerived H D -> SolvableFrom D -> SolvableFrom H.

Definition Solvable := SolvableFrom fullS.

Lemma trivialS_solvable : SolvableFrom trivialS.
Proof. apply solv_triv. intros x Hx. cbn in Hx. exact Hx. Qed.

Lemma abelian_solvable : forall H, AbelianS H -> SolvableFrom H.
Proof.
  intros H Hab. apply (solv_step H trivialS).
  - apply abelian_IsDerived_trivial; assumption.
  - apply solv_triv. intros x Hx. cbn in Hx. exact Hx.
Qed.

(* ===================== uniqueness and transport ===================== *)

Lemma derived_unique : forall H D D',
  IsDerived H D -> IsDerived H D' -> mem_equiv D D'.
Proof.
  intros H D D' (HD1 & HD2 & HD3) (HD'1 & HD'2 & HD'3).
  intro x. split; intro Hx.
  - apply (HD3 D' HD'2 x Hx).
  - apply (HD'3 D HD2 x Hx).
Qed.

Lemma IsDerived_transport_l : forall H H' D,
  mem_equiv H H' -> IsDerived H D -> IsDerived H' D.
Proof.
  intros H H' D Heq (HD1 & HD2 & HD3). split; [|split].
  - intros x Hx. apply (proj1 (Heq x)). apply HD1. exact Hx.
  - intros a b Ha Hb. apply HD2.
    + apply (proj2 (Heq a)); exact Ha.
    + apply (proj2 (Heq b)); exact Hb.
  - intros K HK x Hx. apply (HD3 K).
    + intros a b Ha Hb. apply HK.
      * apply (proj1 (Heq a)); exact Ha.
      * apply (proj1 (Heq b)); exact Hb.
    + exact Hx.
Qed.

Lemma IsDerived_transport_r : forall H D D',
  mem_equiv D D' -> IsDerived H D -> IsDerived H D'.
Proof.
  intros H D D' Heq (HD1 & HD2 & HD3). split; [|split].
  - intros x Hx. apply HD1. apply (proj2 (Heq x)); exact Hx.
  - intros a b Ha Hb. apply (proj1 (Heq (comm a b))). apply HD2; assumption.
  - intros K HK x Hx. apply (HD3 K HK). apply (proj2 (Heq x)); exact Hx.
Qed.

Lemma SolvableFrom_transport : forall H H',
  mem_equiv H H' -> SolvableFrom H -> SolvableFrom H'.
Proof.
  intros H H' Heq Hsolv. generalize dependent H'.
  induction Hsolv as [H0 Htriv | H0 D HD Hs IH]; intros H' Heq.
  - apply solv_triv. intros x Hx. apply Htriv. apply (proj2 (Heq x)); exact Hx.
  - apply (solv_step H' D).
    + apply (IsDerived_transport_l H0 H' D Heq HD).
    + exact Hs.
Qed.

(* ===================== the engine: perfect ⇒ not solvable ===== *)

Lemma perfect_solvable_trivial : forall H,
  SolvableFrom H -> IsDerived H H -> forall x, mem H x -> x = gid G.
Proof.
  intros H Hsolv. induction Hsolv as [H0 Htriv | H0 D HD Hs IH].
  - intros _ x Hx. apply Htriv; exact Hx.
  - intros Hperf x Hx.
    assert (Heq : mem_equiv H0 D) by (apply (derived_unique H0 H0 D Hperf HD)).
    assert (HDD : IsDerived D D).
    { apply (IsDerived_transport_l H0 D D Heq).
      apply (IsDerived_transport_r H0 H0 D Heq Hperf). }
    apply IH; [exact HDD|].
    apply (proj1 (Heq x)); exact Hx.
Qed.

Theorem perfect_nontrivial_not_solvable : forall H,
  IsDerived H H -> (exists x, mem H x /\ x <> gid G) -> ~ SolvableFrom H.
Proof.
  intros H Hperf [x [Hx Hne]] Hsolv.
  apply Hne. apply (perfect_solvable_trivial H Hsolv Hperf x Hx).
Qed.

(* ===================== perfect + non-abelian ⇒ not solvable ==== *)

Definition Perfect := IsDerived fullS fullS.
Definition NonAbelianFull := exists a b, (a ** b) <> (b ** a).

(* a non-abelian group has a non-identity element (decidability supplied
   as a hypothesis, NOT a global axiom — keeps the file at 0 axioms) *)
Lemma nonabelian_has_nontrivial :
  (forall a b : gT G, a = b \/ a <> b) ->
  NonAbelianFull -> exists x, mem fullS x /\ x <> gid G.
Proof.
  intros Hdec [a [b Hab]].
  destruct (Hdec a (gid G)) as [Ha|Ha].
  - destruct (Hdec b (gid G)) as [Hb|Hb].
    + subst a. subst b. exfalso. apply Hab. reflexivity.
    + exists b. split. exact I. exact Hb.
  - exists a. split. exact I. exact Ha.
Qed.

Theorem perfect_nonabelian_not_solvable :
  (forall a b : gT G, a = b \/ a <> b) ->
  Perfect -> NonAbelianFull -> ~ Solvable.
Proof.
  intros Hdec Hperf Hna.
  apply (perfect_nontrivial_not_solvable fullS Hperf).
  apply (nonabelian_has_nontrivial Hdec Hna).
Qed.

End GroupTheory.

(* ===================== Abel–Ruffini, instantiated ===================== *)
(* The Galois group of the general quintic realizes the A5 pattern: it has a
   perfect non-abelian section.  Perfectness is the heavy input (A5 simple);
   GIVEN it, the quintic's group is not solvable — hence, by the Galois
   solvability criterion, the general quintic is unsolvable by radicals. *)
Theorem quintic_galois_group_not_solvable :
  forall (Quintic : GroupStr),
    (forall a b : gT Quintic, a = b \/ a <> b) ->
    Perfect Quintic -> NonAbelianFull Quintic ->
    ~ Solvable Quintic.
Proof.
  intros Quintic Hdec Hp Hna.
  exact (perfect_nonabelian_not_solvable Quintic Hdec Hp Hna).
Qed.

(* ===================== concrete positive instance: Z/2 ===================== *)
(* The cyclic radical-step groups are abelian, hence solvable.  Z/2 = (bool,xor). *)
Definition boolGroup : GroupStr.
Proof.
  refine {| gT := bool; gop := xorb; gid := false; ginv := fun b => b |}.
  - intros a b c; destruct a, b, c; reflexivity.
  - intros a; destruct a; reflexivity.
  - intros a; destruct a; reflexivity.
  - intros a; destruct a; reflexivity.
  - intros a; destruct a; reflexivity.
Defined.

Lemma boolGroup_abelian : AbelianS boolGroup (fullS boolGroup).
Proof. intros a b _ _. cbn. destruct a, b; reflexivity. Qed.

Theorem boolGroup_solvable : Solvable boolGroup.
Proof. unfold Solvable. apply abelian_solvable. exact boolGroup_abelian. Qed.
