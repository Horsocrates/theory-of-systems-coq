---
title: "Chapter 1. Categories as Metasystems"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/14 Категория систем/01 Категории как метасистемы.md"
sourceBlob: 93a66e8ff02a43ce4dc9b50ba587e18ad83acd86
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The volume has passed through the special fields of mathematics: analysis (III–IX), set theory without choice (X), algebra and Galois theory (XI), geometry (XII), number theory and the zeta function (XIII). Part XIV is a *metatheoretical turn*: we do not add “one more topic” but unfold the *language* in which all the preceding parts turn out to be particular cases. This language is *category theory*.

In the ToS ontology the shift acquires a character of its own. A category is an **E/R/R structure of higher order**: a structure whose objects are systems themselves and whose arrows are the links between them. Therefore we fix at once the main honest frame, to which we will return in the finale of the part:

> **The categorical language is a language, not the subject matter of ToS.** ToS does not reduce to category theory;
> category theory serves as a *metalanguage* for describing the links of ToS.

This chapter takes the first step: it gives the formal concept of a category (a return to Chapter I.4 on E/R/R), the basic *universal constructions* (terminal/initial object, product, coproduct), a survey of the standard categories, and—what is essential for ToS—it shows their *constructive* nature (a type, not a “set,” without the Axiom of Choice; a bridge to Part X). At the end we build the first concrete category—the *category of setoids* `SetoidCat`, which will become the working stage of Chapters 14.2 and 14.6.

## The Category as an E/R/R Structure of Higher Order

A return to Chapter I.4. A system there is a structure of *elements* with *roles* and *rules*. A category $\mathcal{C}$ is the same triad raised one level higher:

- **Elements:** objects (the type `cat_obj`) and arrows/morphisms (the type `cat_mor` $a b$);
- **Roles:** the identity arrow `cat_id` $a$ (*the neutral*) and composition `cat_comp` $f g$ (*the combinator*);
- **Rules:** associativity $f\circ(g\circ h)=(f\circ g)\circ h$ and the unit laws $\mathrm{id}\circ f=f$, $f\circ\mathrm{id}=f$.

In Rocq this is a full-fledged record.[^1]

$$
\texttt{Record Category} := \{\ \texttt{cat\_obj} : \mathrm{Type};\ \
  \texttt{cat\_mor} : \texttt{cat\_obj}\to\texttt{cat\_obj}\to\mathrm{Type};\ …\ \}.
$$

**A subtlety that will later become a principle.**  The field `cat_mor_eq` sets its *own* equality of morphisms—a *setoid* equality rather than the Leibniz one (with explicit reflexivity, symmetry, transitivity, and compatibility with composition). This is not a technical detail: P3 is already built in here—the distinction between “equal” and “isomorphic/equivalent,” which will become central in Chapter 14.3 (`P3_strictly_stronger_than_iso`).

**The iteration of E/R/R.**  Applying E/R/R to structures, we obtain a new level—the category (a structure of structures). Applying E/R/R to categories, we obtain a 2-category (categories of categories), and so on. Part XIV lives on the first rung of this ladder; its honest boundary (the *full* “category of all categories” cannot be assembled as one object—small/bounded functor categories are possible, and the wall is precisely “all,” at the level of universes) will be discussed in 14.7.

## Universal Constructions: An Object Is Determined by Its Role

The categorical shift consists in this: an object is given *by its role in the network of arrows, not by its internal arrangement*—up to isomorphism. The basic constructions:

- **Terminal object** $\mathbf{1}$: from every object there is *exactly one* arrow into it ($\forall X,\ \exists! f:X\to\mathbf{1}$).
- **Initial object** $\mathbf{0}$: from it there is exactly one arrow into each object.
- **Product** $A\times B$: an object with projections $\pi_A,\pi_B$ through which any pair $f:C\to A$, $g:C\to B$ factors uniquely.
- **Coproduct** $A+B$: dually, with injections.

It is machine-checked that these roles are *determined uniquely up to isomorphism*: the initial and terminal objects are unique (`initial_unique_up_to_iso`, `terminal_unique_up_to_iso`); isomorphism is an equivalence relation (`iso_refl`/`iso_sym`/`iso_trans`); every isomorphism is monic and epic (`iso_is_mono`, `iso_is_epi`); a composition of monos/epis is again a mono/epi.[^2]

From the standpoint of ToS a universal property is a *rule* (L5) that constitutes an object through its role. The question is “how does $A\times B$ behave with respect to all the others,” rather than “what is $A\times B$ inside.” This is exactly the move that makes the categorical language a metalanguage: it speaks of links, not of substance.

*The boundary of the chapter.* The basic record of `Category.v` gives the *definitions* of the initial and terminal objects and the iso/mono/epi properties (with uniqueness up to isomorphism); the *products and coproducts* themselves (like exponentials with a subobject classifier) are introduced here as a standard categorical *scheme* and will be machine-built concretely for `SetoidCat` in 14.6.

## The Standard Categories

One record `Category` covers all of ordinary mathematics:

| **Category** | **Objects** | **Morphisms** |
|---|---|---|
| $\mathbf{Set}$ | sets/types | functions |
| $\mathbf{Grp}$ | groups | homomorphisms |
| $\mathbf{Ring}$/$\mathbf{Field}$ | rings/fields | homomorphisms |
| $\mathbf{Vec}_k$ | vector spaces | linear maps |
| $\mathbf{Top}$ | topological spaces | continuous maps |
| $\mathbf{Man}$ | smooth manifolds | smooth maps |
| $\mathbf{Cat}$ | categories | functors (Chapter 14.2) |

In the ToS formalization each such category is a concrete record of type `Category`. The basic example is already built: `TypeCat`, the category of types and functions (the equality of morphisms is pointwise; `TypeCat_valid`, `TypeCat_id_is_iso`, `TypeCat_comp_iso`). The manifolds, groups, and fields of Parts XI–XII live in their own categories; Part XIV gives the language that unites them.

## The Constructive Nature: A Type, Not a “Set”

Classical category theory often speaks of a “set of objects,” which is problematic in the ToS ontology (Part X: set theory without choice; P4: there is no completed infinity). ToS categories work on *types*:

$$
\texttt{cat\_obj} : \mathrm{Type}, \quad \texttt{cat\_mor}\ a\ b : \mathrm{Type}.
$$

In the *basic categorical layer of this chapter* no axiom of choice is used; the equality of morphisms is a constructive setoid relation (`cat_mor_eq`), not the Leibniz one. `Category.v` is closed without axioms (20 machine-checked lemmas, 0 axioms). The *process* categories further on (14.6) have their own axiom price (they inherit `classic` through the Cauchy layer); this will enter the map of boundaries in 14.7.

The link with Part X is direct: there a “set” was read as a *mode* (a forgetful functor from structure) rather than a primary object. The category inherits this honesty: its carrier is a type (a rule of construction), not a completed set-object.

## The First New Working Category of the Part: `SetoidCat`

So that the metalanguage does not remain a declaration, in the *locally built* layer `src/category/` we build a concrete, nontrivial category—the *category of setoids* (the first new working category of the part after the basic `TypeCat`). A *setoid* is a type with an equivalence relation given on it; a *morphism of setoids* is a function that *respects* the relation; the equality of morphisms is *pointwise* (by the relation of the target). All the laws of the category are derived *componentwise* from the reflexivity/symmetry/transitivity of the target relation.[^3]

Why `SetoidCat` in particular? Because the natural equality of hom-sets is a *setoid* equality (the equality of morphisms `cat_mor_eq`), not the Leibniz one. `TypeCat` uses pointwise *Leibniz* equality of *values* ($f\sim g := \forall x,\ f x=g x$); to receive the hom-functor $\mathrm{Hom}(x,-)$ of an arbitrary category functorially, one needs a codomain in which the equalities of the hom-types themselves are *setoid* relations. `SetoidCat` serves as exactly that: it is what will make the Yoneda lemma possible in Chapter 14.2, and in Chapter 14.6 it will turn out to be a constructive predicate topos layer (finite limits and colimits, cartesian closedness, a predicate subobject classifier).

## E/R/R Analysis: The Category as a Structure of Structures

**Rules (L5).**  The constitution of a category is *associativity* and the *unit laws* (plus the compatibility of composition with the equality of morphisms). Universal properties (terminal/initial/product) are rule-definitions of objects *through their role*, not through their arrangement.

**Roles (L4).**  “Identity” is the role-neutral; “composition” is the role-combinator; “terminal/initial/product” are roles in the network of arrows; “isomorphism/mono/epi” are roles of morphisms (invertibility, left/right cancellability).

**Elements (L1${}+{}$P4).**  Concrete typed data: the objects `cat_obj`,
the morphisms `cat_mor` $a b$—*types*, not sets; the equality of morphisms `cat_mor_eq` is a setoid equality. *Not* an element: “the set of all objects” as a *completed Element*.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| associativity + unit laws; universal properties | the constitution of the category and its objects | Rule (L5) |
| identity ${}={}$ neutral; composition ${}={}$ combinator; terminal/prod. ${}={}$ roles | the status of arrows and objects | Role (L4) |
| `cat_obj`, `cat_mor` $a b$ (types), `cat_mor_eq` | typed bearers | Element (L1${}+{}$P4) |

**What the analysis removes.**  A category is often perceived as “one more abstraction on top of sets.” ToS reads it as an *iteration* of its own arrangement: E/R/R applied to structures gives a category, a structure of structures. “The set of all objects” as a *completed Element* is then a category mistake (the carrier is a type-rule, not a completed set-object; P4, Part X). And the equality of morphisms, taken as a setoid equality, already carries the seed of P3.

## What the Chapter Has Prepared

The category has been established as a *metasystem*—an E/R/R structure of higher order—constructively (on types, without the Axiom of Choice in this basic layer), with the concepts of initial/terminal object and the properties of isomorphism/mono/epi machine-checked in `Category.v` (20 Qed, 0 axioms); products and coproducts are built concretely for `SetoidCat` in 14.6. The first new working category of the part has been built—`SetoidCat`, whose setoid equality of morphisms makes it the right stage for hom-functors.

Next comes Chapter 14.2: functors (structure-preserving maps of categories), natural transformations, and—machine-checked, without axioms—the **Yoneda lemma** and the **fully faithful
Yoneda embedding**. This will give an exact form to the thesis already built into the setoid equality of this chapter: *an object is determined by its roles*—the categorical form of P3.

---

[^1]: `src/stdlib/Category.v` (20 Qed, 0 axioms; in `origin/main`): `Record Category` with the fields `cat_obj`, `cat_mor`, `cat_mor_eq` (the equality of morphisms), `cat_id`, `cat_comp` and the axioms `cat_assoc`, `cat_id_l`, `cat_id_r`, `cat_comp_compat`; plus `TypeCat`, `is_iso`/`is_mono`/`is_epi`, `is_initial`/`is_terminal`, `opposite_cat`.
[^2]: The same 20 Qed of the file `Category.v`: `iso_refl`, `iso_sym`, `iso_trans`, `iso_inv_unique`, `cat_id_unique`, `comp_mono`, `comp_epi`, `iso_is_mono`, `iso_is_epi`, `initial_unique_up_to_iso`, `terminal_unique_up_to_iso`, `iso_in_opposite`, and others. All 0 axioms.
[^3]: `src/category/SetoidCategory.v` (3 Qed, 0 axioms): `Setoid` (a carrier + `st_eq`/`st_refl`/`st_sym`/ `st_trans`), `SetoidMor` (a map + `sm_resp`), `SetoidCat` as a `Category` (`SetoidCat_mor_eq_iff`, `SetoidCat_comp_map`, `SetoidCat_id_map`); `discrete_setoid` as an example. *A caveat on reproducibility:* the layer `src/category/` (13 files, 49 Qed, 0 axioms, `Print Assumptions`${}={}$“Closed under the global context”, commit `90ebd74`) has been built and checked *locally*; synchronization with the main branch is an item of the checklist (plan v2).

---

Part: [[14 Category of Systems|Part XIV. The Category of Systems]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/07 Riemann Hypothesis Three Forms and Map of Boundaries|Chapter 7. The Riemann Hypothesis: Three Forms and the Map of Boundaries—Part XIII]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/02 Functors Natural Transformations Yoneda Lemma|Chapter 2. Functors, Natural Transformations, the Yoneda Lemma]] →
