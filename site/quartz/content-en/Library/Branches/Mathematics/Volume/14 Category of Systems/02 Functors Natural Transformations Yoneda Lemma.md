---
title: "Chapter 2. Functors, Natural Transformations, the Yoneda Lemma"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/14 Категория систем/02 Функторы, естественные преобразования, лемма Йонеды.md"
sourceBlob: aa9339cda4851ed12c9e59b24636afcdecfde824
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 14.1 established the category as a metasystem. This chapter rises to the next storey: *functors*, structure-preserving maps between categories (morphisms of categories); *natural transformations*, morphisms between functors; and, as the culmination, the **Yoneda lemma** and
the **full faithfulness of the Yoneda embedding**.

This is the strongest new chapter of Part XIV: the Yoneda lemma and the fully faithful embedding are here *machine-proved results without axioms*, not a “classical reading.” Their substantive outcome is the exact form of the thesis already built into the setoid equality of 14.1:

> **An object is completely determined by its roles**—by the system of morphisms out of it and into it.

This is the categorical form of P3 (a bridge to 14.3). The basic `Functor.v` is closed without axioms; the new results of the layer `src/category/` are declared 0-axiom by the *local* build—until synchronization with the main branch, this is an item of the reproducibility checklist.

## The Functor as a Structural Correspondence

A functor $F:\mathcal{C}\to\mathcal{D}$ is a pair of maps, on objects $F_{\mathrm{obj}}$ and on arrows $F_{\mathrm{mor}}:\Hom_{\mathcal{C}}(a,b)\to\Hom_{\mathcal{D}}(Fa,Fb)$, that preserves structure: $F(\mathrm{id})=\mathrm{id}$ and $F(g\circ f)=F(g)\circ F(f)$.

In Rocq this is a record with three laws.[^1] Besides the preservation of identity and composition, the field `fmor_compat` requires respect for the *setoid* equality of morphisms (`cat_mor_eq`, from 14.1): the functor transfers arrows *up to* their equality rather than “bare arrows.”

**Co- and contravariance.**  A covariant functor preserves the direction of arrows; a contravariant one reverses it—formally this is a functor $\mathcal{C}^{\mathrm{op}}\to\mathcal{D}$ (via `opposite_cat` from 14.1). This subtlety will become essential for the Yoneda embedding (§14.2.7).

**The E/R/R reading.**  A functor is a *role-transfer*: it carries the elements, roles, and rules of the category $\mathcal{C}$ into $\mathcal{D}$, preserving the constitution (identity ${}\to{}$ identity, composition ${}\to{}$ composition). It is machine-checked that a functor preserves isomorphisms (`fmor_preserves_iso`): the role “invertibility” is transferred. The identity functor and the composition of functors (`id_functor`, `compose_functor`) are associative on objects (`compose_functor_assoc`).

**The process reading (a bridge to 14.6).**  ToS also has a process side of functoriality: the derived functors $R^nF$ as a process of approximations with a decreasing correction.[^2]

## Natural Transformations and the Functor Category $[\mathcal{C},\mathcal{D}]$

A natural transformation $\eta:F\Rightarrow G$ (between functors $F,G:\mathcal{C}\to\mathcal{D}$) is a family of arrows $\eta_a:Fa\to Ga$ consistent with the action on morphisms: for any $f:a\to b$ the square *commutes*, $\eta_b\circ F(f)=G(f)\circ\eta_a$. This is a rule of coherence (L5): the family of components acts “in the same way” throughout the category.

Machine-checked: `Record NatTrans` (`nt_comp`, `nt_natural`); the identity transformation `id_nat_trans` and the *vertical composition* `vert_comp_nat_trans` (the same `Functor.v`).

**The functor category has been built.**  The functors $\mathcal{C}\to\mathcal{D}$ themselves form a category $[\mathcal{C},\mathcal{D}]$: the objects are functors, the morphisms are natural transformations, composition is vertical, and the equality of morphisms is *componentwise*. This category has been *machine-built*, and all its laws are derived *componentwise* from the laws of $\mathcal{D}$.[^3]

## The Natural Isomorphism: The Inverse Is *Natural*

A natural isomorphism is precisely an isomorphism in the functor category $[\mathcal{C},\mathcal{D}]$. Therefore reflexivity, symmetry, and transitivity come *for free* from the general properties of isomorphism (§14.1); each component of a natural isomorphism is an isomorphism (and hence a mono and an epi).[^4]

The substantive theorem of the chapter is `natural_inverse_is_natural`:

> **If a natural transformation is pointwise invertible, then the inverse components
> are *automatically* natural.**

That is, “the inverse of a natural isomorphism is natural” is proved, not postulated. From the standpoint of L5/P4 this matters: the naturalness of the inverse is a *forced* rule that follows from the naturalness of the direct transformation and the invertibility of the components (a diagram chase, 0 axioms), not an additional assumption. The rule constitutes the object (the inverse isomorphism) and leaves it no room to be “unnatural.”

## The Representable Functor and the Yoneda Lemma

**The representable functor.**  Fix an object $x$. The functor $\Hom(x,-):\mathcal{C}\to\SetoidCat$ sends an object $a$ to the *hom-setoid* (the carrier $\Hom_{\mathcal{C}}(x,a)=\texttt{cat\_mor} x a$, with the setoid equality `cat_mor_eq`), and a morphism $f$ to *postcomposition* $g\mapsto f\circ g$. The functor laws follow from the compatibility of composition, the left unit, and the associativity of $\mathcal{C}$. Here the choice of $\mathbf{Setoid}$ in 14.1 pays off: it is precisely the setoid equality of hom-sets that makes $\Hom(x,-)$ a *functor*.[^5]

**The Yoneda lemma.**  For any functor $F:\mathcal{C}\to\SetoidCat$ and object $x$, the natural transformations $\Hom(x,-)\Rightarrow F$ are in *bijection* with the elements of $F(x)$:

$$
\Nat\bigl(\Hom(x,-), F\bigr)\ \cong\ F(x).
$$

The bijection is machine-proved in both directions:

- $Y:\alpha\mapsto \alpha_x(\mathrm{id}_x)$ (evaluate the family at the identity)—`yoneda_to`;
- $Y^{-1}:u\mapsto\bigl(a\mapsto(g\mapsto F(g)(u))\bigr)$—`yoneda_from`;
- $Y\circ Y^{-1}=\mathrm{id}$ (via $F(\mathrm{id})=\mathrm{id}$)—`yoneda_to_from`; $Y^{-1}\circ Y=\mathrm{id}$ (via the naturality of $\alpha$)—`yoneda_from_to`; uniqueness—`yoneda_unique`.

**What the lemma says (E/R/R / P4).**  A natural family is *completely determined by one seed*—the value $\alpha_x(\mathrm{id}_x)\in F(x)$; the naturality square is the *rule of reconstruction* $g\mapsto F(g)(u)$ of the whole family from this seed. Therefore “$\Nat(\Hom(x,-),F)$” is a *finite rule* of reconstruction, not a completed set of all transformations (a cardinality). This clears up the usual puzzle of “how one value knows the whole natural family”: naturality *is* the law, and the element is the seed.

## The Yoneda Embedding: An Object Is Determined by Its Roles

A morphism $h:y\to x$ induces a natural transformation $\Hom(x,-)\Rightarrow\Hom(y,-)$ by precomposition ($g\mapsto g\circ h$). It is machine-proved that this assignment is *full and faithful*:

$$
\texttt{cat\_mor} y x\ =\ \Hom(y,x)\ \cong\ \Nat\bigl(\Hom(x,-), \Hom(y,-)\bigr),
$$

that is, *faithfulness* (distinct morphisms give distinct transformations) and *fullness* (every transformation comes from a morphism) are a direct consequence of the Yoneda lemma with $F:=\Hom(y,-)$. On the left stands precisely $\Hom(y,x)$: this is the *contravariance* of the embedding—the object $x$ goes to $\Hom(x,-)$, and the arrow $h:y\to x$ gives the transformation $\Hom(x,-)\Rightarrow\Hom(y,-)$ (in the code, `yoneda_faithful`, `yoneda_full` over `cat_mor` $y x$).[^6] This is the exact form of the central thesis:

> **an object is completely determined by its system of morphisms**—the categorical form of P3 (the identity
> of an object is through its roles, not through an “internal substance”).

**An honest wall (important).**  Fullness and faithfulness are proved *in substance*—as a bijection between a hom-set and the set of natural transformations. But assembling the Yoneda embedding into a *single Functor object* $\mathcal{C}^{\mathrm{op}}\to[\mathcal{C},\SetoidCat]$ *does not go through*: the record `Category` is universe-monomorphic, and $[\mathcal{C},\SetoidCat]$ is strictly higher in universe than $\mathcal{C}$ (the objects of $\mathbf{Setoid}$ have already raised the level), while the packaging requires the reverse inequality. This is the classical “*the presheaf category is large*”—a P4 boundary of *size*, not a gap in the proof: the content of the embedding (fullness+faithfulness) does not depend on this large object. Therefore we *do not claim* that “the embedding has been built as a functor”; the size wall is carried over to the map of boundaries in 14.7.

## E/R/R Analysis: Functor, Naturality, Representation

**Rules (L5).**  The preservation of identity and composition (the constitution of a functor); the naturality square (the coherence of a family); the Yoneda bijection (the rule of reconstructing a family from a seed and the rule “object ${}\leftrightarrow{}$ its representable functor”).

**Roles (L4).**  The functor is a role-transfer (of the structure of $\mathcal{C}$ into $\mathcal{D}$); the natural transformation is a role-family (a coherent set of components); $\Hom(x,-)$ is the role “probing from $x$”; $\alpha_x(\mathrm{id}_x)$ is the role-seed; the Yoneda embedding is the role “to represent an object by its morphisms.”

**Elements (L1${}+{}$P4).**  Concrete data: the components $\eta_a$, the morphisms $g:x\to a$, the elements $u\in F(x)$. *Not* an element *in the sense of a completed cardinality*: “the set of all natural transformations” (in the working layer this is the hom-setoid of the category $[\mathcal{C},\SetoidCat]$ / a rule of reconstruction, not a cardinal totality); and the single large Functor object $[\mathcal{C},\SetoidCat]$ *as an object over* $\mathcal{C}$ (the size wall).

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| preservation of id/composition; naturality square; Yoneda bijection | the constitution of transfer, coherence, and representation | Rule (L5) |
| functor ${}={}$ transfer; nat. trans. ${}={}$ family; $\Hom(x,-)={}$ probe; $\alpha_x(\mathrm{id}_x)={}$ seed | the status of transfers and families | Role (L4) |
| $\eta_a$, $g:x\to a$, $u\in F(x)$ | computable bearers | Element (L1${}+{}$P4) |

**What the analysis removes.**  The Yoneda lemma often sounds mystical (“an object knows everything about itself through its arrows”). ToS reads it as a *rule*: naturality forces the reconstruction of a family from one seed, and the embedding makes “object ${}={}$ its roles” an exact bijection. There is no riddle—there is a law (L5) and its seed (L1). And the honest universe wall shows where the categorical language *itself* meets P4: the completed “category of all presheaves” cannot be assembled as an object.

## What the Chapter Has Prepared

We have established functors (role-transfer; they preserve isomorphisms), natural transformations, and the *machine-built* functor category $[\mathcal{C},\mathcal{D}]$; we have proved that the inverse of a natural isomorphism is natural; and, as the culmination, the **Yoneda lemma** and the **fully faithful
Yoneda embedding** (by the local build, 0 axioms, `Print Assumptions`${}={}$“Closed under the global
context”; after synchronization with `main` the status is fixed). The substantive outcome: *an object is determined by its roles*—the categorical form of P3; the honest wall: the completed presheaf category cannot be assembled as an object (size, P4).

Next comes Chapter 14.3: the *category of systems* $\mathrm{Sys}(L)$, where the same thesis receives its original, pre-ontological form—`P3_strictly_stronger_than_iso`: isomorphic systems need not be Leibniz-equal. The Yoneda embedding of this chapter is an abstract shadow of the same P3.

---

[^1]: `src/stdlib/Functor.v` (18 Qed, 0 axioms; in `origin/main`): `Record Functor` (`fobj`, `fmor`, `fmor_compat`, `fmor_id`, `fmor_comp`); `id_functor`, `compose_functor`, `compose_functor_assoc`; the examples `ListFunctor`, `OptionFunctor`, `const_functor`; `fmor_preserves_iso` (a functor preserves isomorphisms).
[^2]: `src/stdlib/ D1_DerivedFunctor.v` (20 Qed; in `origin/main`): $R^nF$ as levels of a process, a cascade of corrections $1/2^n$.
[^3]: `src/category/ FunctorCategory.v` (4 Qed, 0 axioms): `nt_eq` (componentwise equality), `FunctorCat` $\mathcal{C} \mathcal{D}$ as a `Category`; the bridge `FunctorCat_iso_componentwise` (an isomorphism in $[\mathcal{C},\mathcal{D}]$ = a pointwise isomorphism). *A caveat on reproducibility (as in 14.1):* the layer `src/category/` (13 files, 49 Qed, 0 axioms, `Print Assumptions`${}={}$“Closed under the global context”, commit `90ebd74`) has been built and checked *locally*; synchronization with the main branch is an item of the checklist.
[^4]: `src/category/NaturalIsomorphism.v` (7 Qed, 0 axioms, the same local layer): `NaturalIso` as `is_iso` in `FunctorCat`; `nat_iso_id`/`nat_iso_sym`/ `nat_iso_trans`; `nat_iso_components` (a pointwise isomorphism); the components are mono/epi.
[^5]: `src/category/YonedaLemma.v` (3 Qed, 0 axioms, the local layer): `hom_setoid`, `representable` ($\Hom(x,-):\mathcal{C}\to\SetoidCat$); `yoneda_to`, `yoneda_from`; `yoneda_to_from`, `yoneda_from_to`, `yoneda_unique`.
[^6]: `src/category/YonedaEmbedding.v` (3 Qed, 0 axioms, the local layer): `yoneda_embed_mor` (precomposition), `yoneda_faithful`, `yoneda_full`.

---

Part: [[14 Category of Systems|Part XIV. The Category of Systems]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/14 Category of Systems/01 Categories as Metasystems|Chapter 1. Categories as Metasystems]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/03 Category of Systems Sys L|Chapter 3. The Category of Systems Sys(L)]] →
