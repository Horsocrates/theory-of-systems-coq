(** * RightAdjointPreservesLimits.v — RAPL (terminal case) as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: an adjunction F -| G, a terminal object
    Roles:    G (right adjoint) -> limit-preserver
    Rules:    the transpose round-trip phi.psi = id forces uniqueness (constitution)
    Status:   "right adjoints preserve limits", proved for the terminal object

    Builds on: stdlib/Category.v, stdlib/Functor.v, stdlib/Adjunction.v.

    Honest hypothesis.  The stdlib `Adjunction` record carries the unit and
    counit and the triangle identities, but NOT the naturality of the unit.
    Naturality is genuinely needed for the transpose to be a bijection, so we
    add it as an explicit predicate `unit_natural`.  This is an honest exposure
    of a record deficiency, not a hidden axiom: `unit_natural` is itself
    satisfiable (id_adjunction_unit_natural) and provable for any concrete
    adjunction whose unit is a natural transformation.

    Result.  G (the right adjoint) sends a terminal object of D to a terminal
    object of C — the terminal-object instance of "right adjoints preserve
    limits".  Core lemma: the transpose round-trip G(eps_d . F h) . eta_c = h.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import stdlib.Adjunction.

(* ================================================================= *)
(*  Naturality of the unit (the missing record field, made explicit) *)
(* ================================================================= *)

(** eta is a natural transformation id_C => G.F : for g : c -> c',
    eta_{c'} . g = (G F)(g) . eta_c. *)
Definition unit_natural {C D : Category} (A : Adjunction C D) : Prop :=
  forall c c' (g : cat_mor C c c'),
    cat_mor_eq C c (fobj (adj_right A) (fobj (adj_left A) c'))
      (cat_comp C c c' (fobj (adj_right A) (fobj (adj_left A) c'))
        (adj_unit A c') g)
      (cat_comp C c (fobj (adj_right A) (fobj (adj_left A) c))
        (fobj (adj_right A) (fobj (adj_left A) c'))
        (fmor (adj_right A) (fmor (adj_left A) g)) (adj_unit A c)).

(** The identity adjunction has a natural unit (so the hypothesis is real) *)
Lemma id_adjunction_unit_natural : forall (C : Category),
  unit_natural (id_adjunction C).
Proof.
  intro C. unfold unit_natural. intros c c' g. simpl.
  apply (cat_mor_eq_trans C c c'
    (cat_comp C c c' c' (cat_id C c') g) g
    (cat_comp C c c c' g (cat_id C c))).
  - apply cat_id_l.
  - apply cat_mor_eq_sym. apply cat_id_r.
Qed.

(* ================================================================= *)
(*  The transpose round-trip:  G(eps_d . F h) . eta_c = h            *)
(* ================================================================= *)

Lemma right_adjoint_transpose_roundtrip :
  forall (C D : Category) (A : Adjunction C D),
    unit_natural A -> triangle_right A ->
    forall c d (h : cat_mor C c (fobj (adj_right A) d)),
    cat_mor_eq C c (fobj (adj_right A) d)
      (cat_comp C c (fobj (adj_right A) (fobj (adj_left A) c)) (fobj (adj_right A) d)
        (fmor (adj_right A)
          (cat_comp D (fobj (adj_left A) c) (fobj (adj_left A) (fobj (adj_right A) d)) d
            (adj_counit A d) (fmor (adj_left A) h)))
        (adj_unit A c))
      h.
Proof.
  intros C D A Hnat Htri c d h.
  unfold unit_natural in Hnat.
  pose proof (Htri d) as HTd. cbv zeta in HTd.
  set (Fc := fobj (adj_left A) c).
  set (Gd := fobj (adj_right A) d).
  set (GFc := fobj (adj_right A) Fc).
  set (FGd := fobj (adj_left A) Gd).
  set (GFGd := fobj (adj_right A) FGd).
  set (ec := adj_unit A c).
  set (eGd := adj_unit A Gd).
  set (epd := adj_counit A d).
  set (Fh := fmor (adj_left A) h).
  set (Gepd := fmor (adj_right A) epd).
  set (GFh := fmor (adj_right A) Fh).
  (* G(eps_d . F h) . eta_c  ==  G eps_d . G F h . eta_c  (functoriality) *)
  apply (cat_mor_eq_trans C c Gd
    (cat_comp C c GFc Gd (fmor (adj_right A) (cat_comp D Fc FGd d epd Fh)) ec)
    (cat_comp C c GFc Gd (cat_comp C GFc GFGd Gd Gepd GFh) ec)
    h).
  { apply cat_comp_compat; [ apply (fmor_comp (adj_right A) Fh epd) | apply cat_mor_eq_refl ]. }
  (* (G eps_d . G F h) . eta_c  ==  G eps_d . (G F h . eta_c)  (sym assoc) *)
  apply (cat_mor_eq_trans C c Gd
    (cat_comp C c GFc Gd (cat_comp C GFc GFGd Gd Gepd GFh) ec)
    (cat_comp C c GFGd Gd Gepd (cat_comp C c GFc GFGd GFh ec))
    h).
  { apply cat_mor_eq_sym. apply (cat_assoc C c GFc GFGd Gd ec GFh Gepd). }
  (* G F h . eta_c  ==  eta_{Gd} . h   (naturality of eta) *)
  apply (cat_mor_eq_trans C c Gd
    (cat_comp C c GFGd Gd Gepd (cat_comp C c GFc GFGd GFh ec))
    (cat_comp C c GFGd Gd Gepd (cat_comp C c Gd GFGd eGd h))
    h).
  { apply cat_comp_compat;
      [ apply cat_mor_eq_refl | apply cat_mor_eq_sym; apply (Hnat c Gd h) ]. }
  (* G eps_d . (eta_{Gd} . h)  ==  (G eps_d . eta_{Gd}) . h   (assoc) *)
  apply (cat_mor_eq_trans C c Gd
    (cat_comp C c GFGd Gd Gepd (cat_comp C c Gd GFGd eGd h))
    (cat_comp C c Gd Gd (cat_comp C Gd GFGd Gd Gepd eGd) h)
    h).
  { apply (cat_assoc C c Gd GFGd Gd h eGd Gepd). }
  (* (G eps_d . eta_{Gd}) . h  ==  id_{Gd} . h   (triangle_right) *)
  apply (cat_mor_eq_trans C c Gd
    (cat_comp C c Gd Gd (cat_comp C Gd GFGd Gd Gepd eGd) h)
    (cat_comp C c Gd Gd (cat_id C Gd) h)
    h).
  { apply cat_comp_compat; [ apply HTd | apply cat_mor_eq_refl ]. }
  (* id_{Gd} . h  ==  h *)
  apply (cat_id_l C c Gd h).
Qed.

(* ================================================================= *)
(*  Right adjoints preserve the terminal object                      *)
(* ================================================================= *)

Theorem right_adjoint_preserves_terminal :
  forall (C D : Category) (A : Adjunction C D),
    unit_natural A -> triangle_right A ->
    forall t, is_terminal D t -> is_terminal C (fobj (adj_right A) t).
Proof.
  intros C D A Hnat Htri t Ht c.
  (* the unique morphism F c -> t *)
  destruct (Ht (fobj (adj_left A) c)) as [tc Htc].
  (* the canonical morphism c -> G t *)
  exists (cat_comp C c (fobj (adj_right A) (fobj (adj_left A) c)) (fobj (adj_right A) t)
            (fmor (adj_right A) tc) (adj_unit A c)).
  intro h.
  (* f = G(tc).eta_c == G(eps_t . F h).eta_c  (since tc is the unique F c -> t) *)
  apply (cat_mor_eq_trans C c (fobj (adj_right A) t)
    (cat_comp C c (fobj (adj_right A) (fobj (adj_left A) c)) (fobj (adj_right A) t)
       (fmor (adj_right A) tc) (adj_unit A c))
    (cat_comp C c (fobj (adj_right A) (fobj (adj_left A) c)) (fobj (adj_right A) t)
       (fmor (adj_right A)
         (cat_comp D (fobj (adj_left A) c) (fobj (adj_left A) (fobj (adj_right A) t)) t
           (adj_counit A t) (fmor (adj_left A) h)))
       (adj_unit A c))
    h).
  - apply cat_comp_compat.
    + apply (fmor_compat (adj_right A)).
      apply (Htc (cat_comp D (fobj (adj_left A) c) (fobj (adj_left A) (fobj (adj_right A) t)) t
                    (adj_counit A t) (fmor (adj_left A) h))).
    + apply cat_mor_eq_refl.
  - (* round-trip: == h *)
    apply (right_adjoint_transpose_roundtrip C D A Hnat Htri c t h).
Qed.

(* ================================================================= *)
(*  Summary: 3 Qed, 0 Admitted, 0 axioms                            *)
(*    id_adjunction_unit_natural (hypothesis is satisfiable)          *)
(*    right_adjoint_transpose_roundtrip (the bijection round-trip)    *)
(*    right_adjoint_preserves_terminal (RAPL, terminal case)          *)
(* ================================================================= *)
