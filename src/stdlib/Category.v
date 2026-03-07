(** * Category.v — Categories as ToS Meta-Systems

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: objects (types), morphisms (structure-preserving maps)
    Roles:    identity -> Neutral, composition -> Combinator
    Rules:    associativity + identity laws (constitution = category axioms)
    Status:   iso | mono | epi | general

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* ================================================================= *)
(*  Category: objects, morphisms with identity, composition,          *)
(*  and associativity + unit laws. Uses custom equality on morphisms. *)
(* ================================================================= *)

Record Category := mkCategory {
  cat_obj : Type;
  cat_mor : cat_obj -> cat_obj -> Type;
  cat_mor_eq : forall a b, cat_mor a b -> cat_mor a b -> Prop;
  cat_id : forall a, cat_mor a a;
  cat_comp : forall a b c, cat_mor b c -> cat_mor a b -> cat_mor a c;
  (* Equality is equivalence *)
  cat_mor_eq_refl : forall a b (f : cat_mor a b), cat_mor_eq a b f f;
  cat_mor_eq_sym : forall a b (f g : cat_mor a b),
    cat_mor_eq a b f g -> cat_mor_eq a b g f;
  cat_mor_eq_trans : forall a b (f g h : cat_mor a b),
    cat_mor_eq a b f g -> cat_mor_eq a b g h -> cat_mor_eq a b f h;
  (* Composition respects equality *)
  cat_comp_compat : forall a b c (f f' : cat_mor b c) (g g' : cat_mor a b),
    cat_mor_eq b c f f' -> cat_mor_eq a b g g' ->
    cat_mor_eq a c (cat_comp a b c f g) (cat_comp a b c f' g');
  (* Category laws *)
  cat_assoc : forall a b c d (f : cat_mor a b) (g : cat_mor b c) (h : cat_mor c d),
    cat_mor_eq a d (cat_comp a c d h (cat_comp a b c g f))
                    (cat_comp a b d (cat_comp b c d h g) f);
  cat_id_l : forall a b (f : cat_mor a b),
    cat_mor_eq a b (cat_comp a b b (cat_id b) f) f;
  cat_id_r : forall a b (f : cat_mor a b),
    cat_mor_eq a b (cat_comp a a b f (cat_id a)) f;
}.

(* ================================================================= *)
(*         PART I: TYPE CATEGORY INSTANCE (1 Qed)                    *)
(* ================================================================= *)

(** The category of types and functions *)
Definition TypeCat : Category := mkCategory
  Type
  (fun A B => A -> B)
  (fun A B f g => forall x, f x = g x)
  (fun A (x : A) => x)
  (fun A B C (g : B -> C) (f : A -> B) (x : A) => g (f x))
  (* eq_refl *)
  (fun A B f x => eq_refl)
  (* eq_sym *)
  (fun A B f g H x => eq_sym (H x))
  (* eq_trans *)
  (fun A B f g h Hfg Hgh x => eq_trans (Hfg x) (Hgh x))
  (* comp_compat *)
  (fun A B C f f' g g' Hf Hg x =>
    eq_trans (f_equal f (Hg x)) (Hf (g' x)))
  (* assoc *)
  (fun A B C D f g h x => eq_refl)
  (* id_l *)
  (fun A B f x => eq_refl)
  (* id_r *)
  (fun A B f x => eq_refl).

Lemma TypeCat_valid : forall a b (f : cat_mor TypeCat a b),
  cat_mor_eq TypeCat a b (cat_comp TypeCat a b b (cat_id TypeCat b) f) f.
Proof.
  intros a b f. simpl. intro x. reflexivity.
Qed.

(* ================================================================= *)
(*         PART II: MORPHISM PROPERTIES (Definitions)                *)
(* ================================================================= *)

(** A morphism is an isomorphism if it has a two-sided inverse *)
Definition is_iso (C : Category) (a b : cat_obj C) (f : cat_mor C a b) : Prop :=
  exists g : cat_mor C b a,
    cat_mor_eq C a a (cat_comp C a b a g f) (cat_id C a) /\
    cat_mor_eq C b b (cat_comp C b a b f g) (cat_id C b).

(** A morphism is mono (left-cancellable) *)
Definition is_mono (C : Category) (a b : cat_obj C) (f : cat_mor C a b) : Prop :=
  forall z (g1 g2 : cat_mor C z a),
    cat_mor_eq C z b (cat_comp C z a b f g1) (cat_comp C z a b f g2) ->
    cat_mor_eq C z a g1 g2.

(** A morphism is epi (right-cancellable) *)
Definition is_epi (C : Category) (a b : cat_obj C) (f : cat_mor C a b) : Prop :=
  forall z (g1 g2 : cat_mor C b z),
    cat_mor_eq C a z (cat_comp C a b z g1 f) (cat_comp C a b z g2 f) ->
    cat_mor_eq C b z g1 g2.

(** An object is initial: unique morphism from it to any object *)
Definition is_initial (C : Category) (a : cat_obj C) : Prop :=
  forall b, exists f : cat_mor C a b,
    forall g : cat_mor C a b, cat_mor_eq C a b f g.

(** An object is terminal: unique morphism to it from any object *)
Definition is_terminal (C : Category) (a : cat_obj C) : Prop :=
  forall b, exists f : cat_mor C b a,
    forall g : cat_mor C b a, cat_mor_eq C b a f g.

(* ================================================================= *)
(*         PART III: ISOMORPHISM PROPERTIES (5 Qed)                  *)
(* ================================================================= *)

(** Identity is an isomorphism *)
Lemma iso_refl : forall (C : Category) (a : cat_obj C),
  is_iso C a a (cat_id C a).
Proof.
  intros C a.
  exists (cat_id C a).
  split.
  - apply cat_id_l.
  - apply cat_id_l.
Qed.

(** Isomorphism is symmetric: if f : a -> b is iso, then g : b -> a is iso *)
Lemma iso_sym : forall (C : Category) (a b : cat_obj C) (f : cat_mor C a b),
  is_iso C a b f ->
  exists g : cat_mor C b a, is_iso C b a g.
Proof.
  intros C a b f [g [Hgf Hfg]].
  exists g. exists f.
  split; assumption.
Qed.

(** Composition of isomorphisms is an isomorphism *)
Lemma iso_trans : forall (C : Category) (a b c : cat_obj C)
  (f : cat_mor C a b) (g : cat_mor C b c),
  is_iso C a b f -> is_iso C b c g ->
  is_iso C a c (cat_comp C a b c g f).
Proof.
  intros C a b c f g [f_inv [Hfinv_l Hfinv_r]] [g_inv [Hginv_l Hginv_r]].
  exists (cat_comp C c b a f_inv g_inv).
  split.
  - (* Goal: comp(comp(f_inv, g_inv), comp(g, f)) = id_a *)
    (* cat_assoc C a c b a (comp(g,f)) g_inv f_inv gives:
       comp(f_inv, comp(g_inv, comp(g,f))) = comp(comp(f_inv,g_inv), comp(g,f)) *)
    (* So sym(assoc) gives us the other direction *)
    pose proof (cat_assoc C a c b a (cat_comp C a b c g f) g_inv f_inv) as Hassoc1.
    (* Hassoc1: comp(f_inv, comp(g_inv, comp(g,f))) = comp(comp(f_inv,g_inv), comp(g,f)) *)
    apply (cat_mor_eq_trans C a a _ _ _ (cat_mor_eq_sym C a a _ _ Hassoc1)).
    (* Now goal: comp(f_inv, comp(g_inv, comp(g,f))) = id_a *)
    (* inner assoc: cat_assoc C a b c b f g g_inv:
       comp(g_inv, comp(g, f)) = comp(comp(g_inv, g), f) *)
    pose proof (cat_assoc C a b c b f g g_inv) as Hassoc2.
    (* Hassoc2: comp(g_inv, comp(g, f)) = comp(comp(g_inv, g), f) *)
    apply (cat_mor_eq_trans C a a _
      (cat_comp C a b a f_inv (cat_comp C a b b (cat_comp C b c b g_inv g) f))).
    + apply cat_comp_compat.
      * apply cat_mor_eq_refl.
      * exact Hassoc2.
    + (* Now: f_inv . ((g_inv . g) . f) = id_a *)
      apply (cat_mor_eq_trans C a a _
        (cat_comp C a b a f_inv (cat_comp C a b b (cat_id C b) f))).
      * apply cat_comp_compat.
        -- apply cat_mor_eq_refl.
        -- apply cat_comp_compat.
           ++ exact Hginv_l.
           ++ apply cat_mor_eq_refl.
      * apply (cat_mor_eq_trans C a a _ (cat_comp C a b a f_inv f)).
        -- apply cat_comp_compat.
           ++ apply cat_mor_eq_refl.
           ++ apply cat_id_l.
        -- exact Hfinv_l.
  - (* Goal: comp(comp(g, f), comp(f_inv, g_inv)) = id_c *)
    pose proof (cat_assoc C c a b c (cat_comp C c b a f_inv g_inv) f g) as Hassoc1.
    apply (cat_mor_eq_trans C c c _ _ _ (cat_mor_eq_sym C c c _ _ Hassoc1)).
    (* Now: comp(g, comp(f, comp(f_inv, g_inv))) = id_c *)
    pose proof (cat_assoc C c b a b g_inv f_inv f) as Hassoc2.
    apply (cat_mor_eq_trans C c c _
      (cat_comp C c b c g (cat_comp C c b b (cat_comp C b a b f f_inv) g_inv))).
    + apply cat_comp_compat.
      * apply cat_mor_eq_refl.
      * exact Hassoc2.
    + apply (cat_mor_eq_trans C c c _
        (cat_comp C c b c g (cat_comp C c b b (cat_id C b) g_inv))).
      * apply cat_comp_compat.
        -- apply cat_mor_eq_refl.
        -- apply cat_comp_compat.
           ++ exact Hfinv_r.
           ++ apply cat_mor_eq_refl.
      * apply (cat_mor_eq_trans C c c _ (cat_comp C c b c g g_inv)).
        -- apply cat_comp_compat.
           ++ apply cat_mor_eq_refl.
           ++ apply cat_id_l.
        -- exact Hginv_r.
Qed.

(** The inverse of an iso is unique up to cat_mor_eq *)
Lemma iso_inv_unique : forall (C : Category) (a b : cat_obj C)
  (f : cat_mor C a b) (g1 g2 : cat_mor C b a),
  cat_mor_eq C a a (cat_comp C a b a g1 f) (cat_id C a) ->
  cat_mor_eq C b b (cat_comp C b a b f g1) (cat_id C b) ->
  cat_mor_eq C a a (cat_comp C a b a g2 f) (cat_id C a) ->
  cat_mor_eq C b b (cat_comp C b a b f g2) (cat_id C b) ->
  cat_mor_eq C b a g1 g2.
Proof.
  intros C a b f g1 g2 Hg1f Hfg1 Hg2f Hfg2.
  (* g1 = g1 . id = g1 . (f . g2) = (g1 . f) . g2 = id . g2 = g2 *)
  apply (cat_mor_eq_trans C b a g1 (cat_comp C b b a g1 (cat_id C b))).
  - apply cat_mor_eq_sym. apply cat_id_r.
  - apply (cat_mor_eq_trans C b a _
      (cat_comp C b b a g1 (cat_comp C b a b f g2))).
    + apply cat_comp_compat.
      * apply cat_mor_eq_refl.
      * apply cat_mor_eq_sym. exact Hfg2.
    + apply (cat_mor_eq_trans C b a _
        (cat_comp C b a a (cat_comp C a b a g1 f) g2)).
      * apply (cat_assoc C b a b a g2 f g1).
      * apply (cat_mor_eq_trans C b a _ (cat_comp C b a a (cat_id C a) g2)).
        -- apply cat_comp_compat.
           ++ exact Hg1f.
           ++ apply cat_mor_eq_refl.
        -- apply cat_id_l.
Qed.

(** If e is both left and right identity, then e = cat_id *)
Lemma cat_id_unique : forall (C : Category) (a : cat_obj C)
  (e : cat_mor C a a),
  (forall b (f : cat_mor C a b), cat_mor_eq C a b (cat_comp C a a b f e) f) ->
  (forall b (f : cat_mor C b a), cat_mor_eq C b a (cat_comp C b a a e f) f) ->
  cat_mor_eq C a a e (cat_id C a).
Proof.
  intros C a e Hright Hleft.
  (* e = id . e    by id_l *)
  (* id . e = id   by Hright (take f := id) *)
  apply (cat_mor_eq_trans C a a e (cat_comp C a a a (cat_id C a) e)).
  - apply cat_mor_eq_sym. apply cat_id_l.
  - apply Hright.
Qed.

(* ================================================================= *)
(*         PART IV: MONO AND EPI PROPERTIES (4 Qed)                  *)
(* ================================================================= *)

(** Composition of monos is mono *)
Lemma comp_mono : forall (C : Category) (a b c : cat_obj C)
  (f : cat_mor C a b) (g : cat_mor C b c),
  is_mono C a b f -> is_mono C b c g ->
  is_mono C a c (cat_comp C a b c g f).
Proof.
  intros C a b c f g Hf Hg.
  unfold is_mono. intros z h1 h2 Heq.
  (* Heq: (g.f).h1 = (g.f).h2 *)
  (* Need: h1 = h2. Use Hf after Hg. *)
  (* First show g.(f.h1) = g.(f.h2) via assoc + Heq + assoc *)
  apply Hf. apply Hg.
  (* Goal: comp(g, comp(f, h1)) = comp(g, comp(f, h2)) *)
  (* assoc gives: comp(g, comp(f, h1)) = comp(comp(g,f), h1)  [cat_assoc C z a b c h1 f g] *)
  apply (cat_mor_eq_trans C z c _
    (cat_comp C z a c (cat_comp C a b c g f) h1)).
  - apply (cat_assoc C z a b c h1 f g).
  - apply (cat_mor_eq_trans C z c _ (cat_comp C z a c (cat_comp C a b c g f) h2)).
    + exact Heq.
    + apply cat_mor_eq_sym. apply (cat_assoc C z a b c h2 f g).
Qed.

(** Composition of epis is epi *)
Lemma comp_epi : forall (C : Category) (a b c : cat_obj C)
  (f : cat_mor C a b) (g : cat_mor C b c),
  is_epi C a b f -> is_epi C b c g ->
  is_epi C a c (cat_comp C a b c g f).
Proof.
  intros C a b c f g Hf Hg.
  unfold is_epi. intros z h1 h2 Heq.
  (* Heq: h1.(g.f) = h2.(g.f) *)
  (* Need: h1 = h2. Use Hg after Hf. *)
  apply Hg. apply Hf.
  (* Goal: comp(h1, comp(g, f)) ... but wait, need comp(comp(h1,g), f) = comp(comp(h2,g), f) *)
  (* cat_assoc C a b c z f g h1: comp(h1, comp(g,f)) = comp(comp(h1,g), f) *)
  apply (cat_mor_eq_trans C a z _
    (cat_comp C a c z h1 (cat_comp C a b c g f))).
  - apply cat_mor_eq_sym. apply (cat_assoc C a b c z f g h1).
  - apply (cat_mor_eq_trans C a z _ (cat_comp C a c z h2 (cat_comp C a b c g f))).
    + exact Heq.
    + apply (cat_assoc C a b c z f g h2).
Qed.

(** Every isomorphism is mono *)
Lemma iso_is_mono : forall (C : Category) (a b : cat_obj C) (f : cat_mor C a b),
  is_iso C a b f -> is_mono C a b f.
Proof.
  intros C a b f [g [Hgf Hfg]].
  unfold is_mono. intros z h1 h2 Heq.
  (* f . h1 = f . h2 *)
  (* g . (f . h1) = g . (f . h2) *)
  (* (g . f) . h1 = (g . f) . h2 *)
  (* id . h1 = id . h2 *)
  (* h1 = h2 *)
  apply (cat_mor_eq_trans C z a h1 (cat_comp C z a a (cat_id C a) h1)).
  - apply cat_mor_eq_sym. apply cat_id_l.
  - apply (cat_mor_eq_trans C z a _
      (cat_comp C z a a (cat_comp C a b a g f) h1)).
    + apply cat_comp_compat.
      * apply cat_mor_eq_sym. exact Hgf.
      * apply cat_mor_eq_refl.
    + apply (cat_mor_eq_trans C z a _
        (cat_comp C z b a g (cat_comp C z a b f h1))).
      * apply cat_mor_eq_sym. apply (cat_assoc C z a b a h1 f g).
      * apply (cat_mor_eq_trans C z a _
          (cat_comp C z b a g (cat_comp C z a b f h2))).
        -- apply cat_comp_compat.
           ++ apply cat_mor_eq_refl.
           ++ exact Heq.
        -- apply (cat_mor_eq_trans C z a _
             (cat_comp C z a a (cat_comp C a b a g f) h2)).
           ++ apply (cat_assoc C z a b a h2 f g).
           ++ apply (cat_mor_eq_trans C z a _ (cat_comp C z a a (cat_id C a) h2)).
              ** apply cat_comp_compat.
                 --- exact Hgf.
                 --- apply cat_mor_eq_refl.
              ** apply cat_id_l.
Qed.

(** Every isomorphism is epi *)
Lemma iso_is_epi : forall (C : Category) (a b : cat_obj C) (f : cat_mor C a b),
  is_iso C a b f -> is_epi C a b f.
Proof.
  intros C a b f [g [Hgf Hfg]].
  unfold is_epi. intros z h1 h2 Heq.
  (* h1 . f = h2 . f *)
  (* (h1 . f) . g = (h2 . f) . g *)
  (* h1 . (f . g) = h2 . (f . g) *)
  (* h1 . id = h2 . id *)
  (* h1 = h2 *)
  apply (cat_mor_eq_trans C b z h1 (cat_comp C b b z h1 (cat_id C b))).
  - apply cat_mor_eq_sym. apply cat_id_r.
  - apply (cat_mor_eq_trans C b z _
      (cat_comp C b b z h1 (cat_comp C b a b f g))).
    + apply cat_comp_compat.
      * apply cat_mor_eq_refl.
      * apply cat_mor_eq_sym. exact Hfg.
    + apply (cat_mor_eq_trans C b z _
        (cat_comp C b a z (cat_comp C a b z h1 f) g)).
      * apply (cat_assoc C b a b z g f h1).
      * apply (cat_mor_eq_trans C b z _
          (cat_comp C b a z (cat_comp C a b z h2 f) g)).
        -- apply cat_comp_compat.
           ++ exact Heq.
           ++ apply cat_mor_eq_refl.
        -- apply (cat_mor_eq_trans C b z _
             (cat_comp C b b z h2 (cat_comp C b a b f g))).
           ++ apply cat_mor_eq_sym. apply (cat_assoc C b a b z g f h2).
           ++ apply (cat_mor_eq_trans C b z _ (cat_comp C b b z h2 (cat_id C b))).
              ** apply cat_comp_compat.
                 --- apply cat_mor_eq_refl.
                 --- exact Hfg.
              ** apply cat_id_r.
Qed.

(* ================================================================= *)
(*         PART V: UNIVERSAL PROPERTIES (2 Qed)                      *)
(* ================================================================= *)

(** Initial objects are unique up to isomorphism *)
Lemma initial_unique_up_to_iso : forall (C : Category)
  (a b : cat_obj C),
  is_initial C a -> is_initial C b ->
  exists f : cat_mor C a b, is_iso C a b f.
Proof.
  intros C a b Ha Hb.
  destruct (Ha b) as [fab Hab_uniq].
  destruct (Hb a) as [fba Hba_uniq].
  exists fab.
  exists fba.
  split.
  - (* fba . fab = id_a *)
    (* Both fba . fab and id_a are morphisms a -> a *)
    (* By initiality of a, there's a unique morphism a -> a *)
    destruct (Ha a) as [ida Hida_uniq].
    apply (cat_mor_eq_trans C a a _ ida).
    + apply cat_mor_eq_sym. apply Hida_uniq.
    + apply Hida_uniq.
  - (* fab . fba = id_b *)
    destruct (Hb b) as [idb Hidb_uniq].
    apply (cat_mor_eq_trans C b b _ idb).
    + apply cat_mor_eq_sym. apply Hidb_uniq.
    + apply Hidb_uniq.
Qed.

(** Terminal objects are unique up to isomorphism *)
Lemma terminal_unique_up_to_iso : forall (C : Category)
  (a b : cat_obj C),
  is_terminal C a -> is_terminal C b ->
  exists f : cat_mor C a b, is_iso C a b f.
Proof.
  intros C a b Ha Hb.
  destruct (Hb a) as [fab Hab_uniq].
  destruct (Ha b) as [fba Hba_uniq].
  exists fab.
  exists fba.
  split.
  - destruct (Ha a) as [ida Hida_uniq].
    apply (cat_mor_eq_trans C a a _ ida).
    + apply cat_mor_eq_sym. apply Hida_uniq.
    + apply Hida_uniq.
  - destruct (Hb b) as [idb Hidb_uniq].
    apply (cat_mor_eq_trans C b b _ idb).
    + apply cat_mor_eq_sym. apply Hidb_uniq.
    + apply Hidb_uniq.
Qed.

(* ================================================================= *)
(*         PART VI: OPPOSITE CATEGORY (2 Qed)                        *)
(* ================================================================= *)

(** The opposite (dual) category reverses all morphisms *)
Definition opposite_cat (C : Category) : Category := mkCategory
  (cat_obj C)
  (fun a b => cat_mor C b a)
  (fun a b => cat_mor_eq C b a)
  (fun a => cat_id C a)
  (fun a b c (g : cat_mor C c b) (f : cat_mor C b a) =>
    cat_comp C c b a f g)
  (* eq_refl *)
  (fun a b => cat_mor_eq_refl C b a)
  (* eq_sym *)
  (fun a b => cat_mor_eq_sym C b a)
  (* eq_trans *)
  (fun a b => cat_mor_eq_trans C b a)
  (* comp_compat: need to reverse argument order *)
  (fun a b c f f' g g' Hf Hg =>
    cat_comp_compat C c b a g g' f f' Hg Hf)
  (* assoc: original says comp(h, comp(g,f)) = comp(comp(h,g), f) *)
  (* opposite reverses, so we need sym of original assoc *)
  (fun a b c d (f : cat_mor C b a) (g : cat_mor C c b) (h : cat_mor C d c) =>
    cat_mor_eq_sym C d a _ _ (cat_assoc C d c b a h g f))
  (* id_l in opposite = id_r in original *)
  (fun a b (f : cat_mor C b a) => cat_id_r C b a f)
  (* id_r in opposite = id_l in original *)
  (fun a b (f : cat_mor C b a) => cat_id_l C b a f).

(** Opposite of opposite is the original category (objects match) *)
Lemma opposite_obj_involutive : forall (C : Category),
  cat_obj (opposite_cat (opposite_cat C)) = cat_obj C.
Proof.
  intros C. reflexivity.
Qed.

(** Iso in C implies iso in C^op *)
Lemma iso_in_opposite : forall (C : Category) (a b : cat_obj C)
  (f : cat_mor C a b),
  is_iso C a b f ->
  is_iso (opposite_cat C) b a f.
Proof.
  intros C a b f [g [Hgf Hfg]].
  simpl. exists g. split; assumption.
Qed.

(* ================================================================= *)
(*         PART VII: ADDITIONAL STRUCTURAL LEMMAS (6 Qed)            *)
(* ================================================================= *)

(** Composition respects equality (standalone — mirrors the record field) *)
Lemma comp_compat : forall (C : Category) (a b c : cat_obj C)
  (f f' : cat_mor C b c) (g g' : cat_mor C a b),
  cat_mor_eq C b c f f' -> cat_mor_eq C a b g g' ->
  cat_mor_eq C a c (cat_comp C a b c f g) (cat_comp C a b c f' g').
Proof.
  intros. apply cat_comp_compat; assumption.
Qed.

(** Mono cancel left — direct unfolding of definition *)
Lemma mono_cancel_left : forall (C : Category) (a b : cat_obj C)
  (f : cat_mor C a b),
  is_mono C a b f ->
  forall z (g h : cat_mor C z a),
    cat_mor_eq C z b (cat_comp C z a b f g) (cat_comp C z a b f h) ->
    cat_mor_eq C z a g h.
Proof.
  intros C a b f Hmono z g h Heq.
  apply Hmono. exact Heq.
Qed.

(** Identity in TypeCat is an isomorphism *)
Lemma TypeCat_id_is_iso : forall (A : Type),
  is_iso TypeCat A A (cat_id TypeCat A).
Proof.
  intros A. apply iso_refl.
Qed.

(** Composition in TypeCat is an isomorphism if both components are *)
Lemma TypeCat_comp_iso : forall (A B C : Type)
  (f : A -> B) (g : B -> C),
  is_iso TypeCat A B f -> is_iso TypeCat B C g ->
  is_iso TypeCat A C (cat_comp TypeCat A B C g f).
Proof.
  intros A B Ct f g Hf Hg.
  apply iso_trans; assumption.
Qed.

(** Mono in opposite is epi in original *)
Lemma mono_op_is_epi : forall (C : Category) (a b : cat_obj C)
  (f : cat_mor C a b),
  is_mono (opposite_cat C) b a f -> is_epi C a b f.
Proof.
  intros C a b f Hmono.
  unfold is_epi. intros z g1 g2 Heq.
  unfold is_mono in Hmono. simpl in Hmono.
  apply Hmono. exact Heq.
Qed.

(** Epi in opposite is mono in original *)
Lemma epi_op_is_mono : forall (C : Category) (a b : cat_obj C)
  (f : cat_mor C a b),
  is_epi (opposite_cat C) b a f -> is_mono C a b f.
Proof.
  intros C a b f Hepi.
  unfold is_mono. intros z g1 g2 Heq.
  unfold is_epi in Hepi. simpl in Hepi.
  apply Hepi. exact Heq.
Qed.

(* ================================================================= *)
(*  Summary: 20 Qed, 0 Admitted                                      *)
(*    1 TypeCat: TypeCat_valid                                        *)
(*    5 iso: iso_refl, iso_sym, iso_trans, iso_inv_unique,            *)
(*           cat_id_unique                                            *)
(*    4 mono/epi: comp_mono, comp_epi, iso_is_mono, iso_is_epi       *)
(*    2 universal: initial_unique_up_to_iso, terminal_unique_up_to_iso*)
(*    2 opposite: opposite_obj_involutive, iso_in_opposite            *)
(*    6 structural: comp_compat, mono_cancel_left, TypeCat_id_is_iso, *)
(*      TypeCat_comp_iso, mono_op_is_epi, epi_op_is_mono             *)
(* ================================================================= *)
