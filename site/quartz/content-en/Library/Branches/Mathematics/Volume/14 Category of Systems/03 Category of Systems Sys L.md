---
title: "Chapter 3. The Category of Systems Sys(L)"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/14 Категория систем/03 Категория систем Sys(L).md"
sourceBlob: ef627f0837aecba5e18005ac15a4ba62bf967857
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 14.1 gave the category as a metasystem; Chapter 14.2 gave functors, natural transformations, and the Yoneda embedding, whose outcome was the thesis “an object is determined by its roles” (the categorical form of P3). This chapter closes the circle: we build the *category of systems themselves* $\Sys(L)$—the one for whose sake all of ToS was undertaken—and show that in it P3 receives its *original*, most concrete form:

> **isomorphism is strictly weaker than Leibniz equality**—there exist systems isomorphic in $\Sys(L)$
> but not equal as Rocq objects (`P3_strictly_stronger_than_iso`).

The Yoneda embedding of 14.2 (the local layer) is an abstract shadow of this fact. Here the fact is *machine-proved* on a concrete category of systems. All the anchors of the chapter are in the main branch (`origin/main`): they can be cited with confidence.

## A System Is an Object, a Morphism Is the Preservation of a Criterion

A return to Chapter I.4. A *system* at level $L$ carries its elements (`ElemOf` $S$) and a criterion (a role-rule constituting what belongs to the system). A *morphism* $f:S_1\to S_2$ is a map of elements $\texttt{ElemOf} S_1\to\texttt{ElemOf} S_2$ that *preserves the criterion*: it carries “being an element of $S_1$” into “being an element of $S_2$.”

In the machine formalization this is a record with composition and a setoid equality of morphisms.[^1] Composition is associative and the identity is neutral—exactly the conditions for systems and their morphisms to form a category (the next section). The roles of morphisms are introduced as well: the *embedding* (`is_embedding`, injective on elements), the *surjection* (`is_surjection`), and the *isomorphism* (`is_isomorphism`, an invertible pair in both directions).

## The Category $\Sys(L)$

The assembled category is `SystemCat` $L$: the objects are systems of level $L$, the morphisms are `SystemMorphism`, composition is `compose_morphism`, and the equality of morphisms is a setoid equality.[^2]

It is machine-checked that the categorical notions coincide with the systemic ones: an isomorphism in `SystemCat` is equivalent to a system isomorphism (`SystemCat_iso_iff_isomorphism`); an embedding implies being a monomorphism, and a surjection implies being an epimorphism (`embedding_implies_SystemCat_mono`, `surjection_implies_SystemCat_epi`). That is, the categorical language of 14.1 does *describe* systems: the “mono/epi/iso” of the network of arrows are the “embedding/surjection/isomorphism” of systems.

## Initial and Terminal Objects: The Hierarchy from Below

In $\Sys(L)$ there are initial and terminal objects: the *empty system* `empty_system` (a unique arrow from it into any system) and the *unit system* `unit_system` (a unique arrow into it).[^3]

**A P4 subtlety: they cannot be placed at the bottom.**  The construction of `empty_system` and `unit_system` requires a *witness* $w\ll L$—a level *below* $L$. At the level $L1$ there is no such witness (`no_system_at_L1_with_witness`), and `SystemCat` $L1$ is degenerate (`SystemCat_L1_vacuous`); the initial and terminal objects appear only at levels of the form $LS L$ (`SystemCat_LS_has_initial_and_terminal`). This is an honest P4 lesson: “the empty” and “the unit” are *roles in the hierarchy*, not primary objects at the bottom—they themselves rest on a level beneath them. (A parallel with Part X: the empty set is not an object free of presuppositions.)

## The Elements Functor: Forgetting Down to the Carrier

The categorical reading of E/R/R gives the *forgetful functor* “system ${}\mapsto{}$ its elements”:

$$
\texttt{ElementsFunctor}\ L\ :\ \Sys(L)\ \longrightarrow\ \mathbf{TypeCat},
$$

which assigns to an object the type of its elements, and to a morphism its action on elements. It is *faithful* (`ElementsFunctor_faithful`: a morphism is determined by its action on elements) and *preserves isomorphisms* (`ElementsFunctor_preserves_iso`).
[^4]

From the E/R/R standpoint, “elements” are the *image of the forgetful functor*; “roles” are the structure of morphisms; “rules” are the laws of the category and (below) the P3 separation. An isomorphism of systems gives a bijection of their elements (`iso_gives_element_bijection`)—but, as we will now see, it does *not* give the Leibniz equality of the systems.

## The Core of P3: Isomorphism $\neq$ Leibniz Equality

This is the center of the chapter and one of the summits of Part XIV. The relation “equality / isomorphism” has been decomposed by machine into two asymmetric halves:

- **Leibniz equality implies isomorphism:** equal systems are isomorphic (`P3_eq_implies_iso`)—the trivial side.
- **Isomorphism does *not* imply Leibniz equality:** there exist systems isomorphic in `SystemCat` but not equal as Rocq objects (`P3_strictly_stronger_than_iso`, `iso_not_implies_P3`).

Together this is `P3_separation_categorical`: *isomorphism is strictly weaker than Leibniz equality*. Isomorphism preserves everything visible “from outside”—the predicate-criterion (`iso_implies_predicate_equiv`), the bijection of elements, well-formedness—but *not* every internal marking: for example, the position bound is *not* invariant under isomorphism (`position_bound_not_iso_invariant`).
[^5]

**Why this is P3.**  P3 (Intensional Identity) asserted that *intensional* identity is finer than extensional coincidence. Here this becomes an exact categorical theorem: “to behave in the same way with respect to all arrows” (isomorphism) is *strictly weaker* than “to be the same object” (Leibniz equality). The link with 14.2 is direct: the Yoneda embedding (the local layer of 14.2) says that an object is determined by its roles *up to isomorphism*—and P3 adds that this precision is *not* identity. The categorical structure works invariantly with isomorphism; Leibniz equality remains a *meta-level* relation of Rocq objects and is not a categorical invariant—this is an *honest* boundary, not a defect.

## E/R/R Analysis: The Category of Systems as E/R/R, Categorically

**Rules (L5).**  The laws of the category $\Sys(L)$ (associativity/units) + the criterion-preservation of morphisms + the **P3 separation** (isomorphism $\neq$ Leibniz equality). The universal roles `empty_system`/`unit_system` require a level beneath themselves (the P4 hierarchy).

**Roles (L4).**  The system is an object; the morphism is a criterion-preserving transfer; embedding/surjection/isomorphism are roles of morphisms; `ElementsFunctor` is a role-forgetting (down to the carrier); isomorphism is the role “indistinguishable by roles,” not “identical.”

**Elements (L1${}+{}$P4).**  Concrete data: `ElemOf` $S$, the components of morphisms, the bijections of elements under isomorphism. *Not* an element *of categorical observability*: the Leibniz equality of systems—as a Prop it exists, but it is not recoverable from the network of morphisms (it is finer than isomorphism); this is exactly what P3 fixes.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the laws of $\Sys(L)$ + criterion-preservation + the P3 separation | the constitution of the category of systems | Rule (L5) |
| system ${}={}$ object; morphism ${}={}$ transfer; iso${}={}$“indistinguishable by roles” | the status of systems and maps | Role (L4) |
| `ElemOf` $S$; components of morphisms; bijections under iso | computable bearers | Element (L1${}+{}$P4) |

**What the analysis removes.**  The question “when are two systems one and the same?” often mixes two concepts. ToS distinguishes them by machine: isomorphism (sameness of roles) and Leibniz equality (identity of the object) are different relations, and the first is strictly weaker. The category of systems sees the first and does not see the second; this is the constitution of P3, not a gap.

## What the Chapter Has Prepared

The category of systems $\Sys(L)$ has been built (`SystemCat`, 29 Qed) with morphisms as criterion-preserving transfers (`SystemMorphism`, 17 Qed); the categorical iso/mono/epi have coincided with the systemic ones; the initial and terminal objects exist (at levels $LS L$, not at the bottom—P4); the forgetful `ElementsFunctor` is faithful and preserves isomorphisms. The core is the machine theorem `P3_strictly_stronger_than_iso`: *isomorphism is strictly weaker than Leibniz equality*. Everything is in `origin/main`, 0 axioms.

Next comes Chapter 14.4: functors *between levels* (`embed`/`forget`) and their adjunction—the crown of Part XIV, where the principle of complementarity turns out to be the categorical adjunction $\texttt{embed}\dashv\texttt{forget}$ (`embed` is the left adjoint, `forget` the right one).

---

[^1]: `src/SystemMorphism.v` (17 Qed, 0 Admitted; in `origin/main`; isomorphism is defined constructively, without the Axiom of Choice—the file declares 0 axioms): `ElemOf`, `Record SystemMorphism` (`mkSystemMorphism`), `id_morphism`, `compose_morphism`, `morphism_eq` (+ refl./sym./trans.), `compose_assoc`, `compose_id_left`/`_right`; `is_embedding`, `is_surjection`, `is_isomorphism` (+ `iso_symmetric`, `iso_pair_predicate_equiv`).
[^2]: `src/SystemCategory.v` (29 Qed, 0 axioms; in `origin/main`): `SystemCat` $L$ as a `Category`; `SystemCat_valid`, `SystemCat_comp_is_compose`, `SystemCat_id_is_id`; `SystemCat_iso_iff_isomorphism`, `embedding_implies_SystemCat_mono`, `surjection_implies_SystemCat_epi`, `SystemCat_iso_compose`.
[^3]: `SystemCategory.v`: `empty_system`, `empty_is_initial`; `unit_system`, `unit_is_terminal`; `SystemCat_initial_unique`, `SystemCat_terminal_unique`; `SystemCat_LS_has_initial_and_terminal`.
[^4]: `src/ERR_Categorical.v` (24 Qed, 0 axioms; in `origin/main`): `ElementsFunctor`, `ElementsFunctor_obj`/`_mor`, `ElementsFunctor_faithful`, `ElementsFunctor_preserves_iso`; `iso_gives_element_bijection`.
[^5]: `ERR_Categorical.v`: `P3_eq_implies_iso`, `iso_implies_predicate_equiv`, `P3_strictly_stronger_than_iso`, `iso_not_implies_P3`, `P3_separation_categorical`, `position_bound_not_iso_invariant`, `well_formed_iso_invariant`, `err_decomposition`.

---

Part: [[14 Category of Systems|Part XIV. The Category of Systems]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/14 Category of Systems/02 Functors Natural Transformations Yoneda Lemma|Chapter 2. Functors, Natural Transformations, the Yoneda Lemma]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/04 Functors Between Levels and Adjunction|Chapter 4. Functors between Levels and Adjunction]] →
