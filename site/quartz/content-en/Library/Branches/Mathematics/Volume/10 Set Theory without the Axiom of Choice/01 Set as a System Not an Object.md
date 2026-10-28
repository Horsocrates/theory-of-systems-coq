---
title: "Chapter 1. Set as a System, Not an Object"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/01 Множество как Система, а не объект.md"
sourceBlob: 2aef9d5e77c7facf78673a2d478dd47958577b48
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part X

Parts II–IX built mathematics from the bottom up: number, the rationals, the reals as processes, analysis, series, ordinary differential equations, and partial differential equations. Each time, a completed continuum object turned out to be a *role-limit* of a process rather than an initial building block. Part X returns to the very foundation—*what a set, membership, cardinality, choice, and infinity are*—and does so in the same optics.

Classical set theory takes the *set* as the primary *object*: a completed collection, an element of the universe $V$. To manage these objects without falling into paradoxes, it is compelled to add strong axioms: Infinity (large objects exist), Power Set (from an object one can form the collection of its subsets), Choice (from an arbitrary family of objects one can choose one from each), and Foundation (pathological objects are excluded). ToS makes the reverse move:

- a “set” is a *System*—the bearer of the role “a collection bounded by a criterion, at level $L$”—and *not* a self-standing Element-object;
- “membership” ($\in$) is a *role* (occupying a position at the level below), not a substantial relation between things;
- the strong axioms are either *structurally unnecessary* (the paradoxes are blocked by the rule of levels P1) or *replaced by rules* (choice by the positional resolution of L5; infinity by the process scheme of P4).

Hence the central thesis of Part X. *Within the P4 ontology of ToS*, the strong axioms of ZFC read as a *category mistake*—a symptom of level confusion: a role of comparison, a rule of choice, or a process of generation is taken for a completed Element-object. This is *not* an external metatheorem about the untenability of ZFC: within its own ontology ZFC is a different foundational regime. ToS takes issue precisely with the *reification of completed totalities*, not with the formal system as such.

### What This Part Claims—and What It Does Not

A short formula worth getting used to from the first page: ToS does *not* “prove ZFC without the Axiom of Choice.” ToS *changes the category*: a set becomes a system, membership a role, choice a rule, infinity a process. Therefore the *admissible core* of the strong axioms turns into a procedure and a theorem, while their *completed-object form* is ruled out by the principle P4.

The present chapter is the foundation of Part X. It introduces set-as-a-System and membership-as-a-role, formulates the rule of levels P1, which makes the theory paradox-free *by construction*, and shows that Russell, Cantor, and Burali-Forti are three guises of one category mistake. The following chapters develop this: countability and uncountability as rules about processes (10.2), comparing cardinalities without choice (10.3), the dual fate of the Axiom of Choice—exclusion and reinterpretation (10.4), ordinals as processes and the tower of strong axioms (10.5), and synthesis and the map of boundaries (10.6).

*Part X is a role-return to the foundations: not a new topic after analysis, but a revision of what “set,” “membership,” and “infinity” have been all along. A set is a role-System; a strong axiom is a reified rule.*

## Set as a System; Membership as a Role

In ToS the bearer that the classical theory calls a “set” is a *System*: a criterion over some lower level, labeled with a level $L$. The system does not hang in a void as a ready thing—it *plays the role* of a collection. Accordingly, “membership” $x\in S$ is `element_at`: $x$ occupying a position within $S$, where $x$ lives at a level strictly below the level of $S$. Membership is *relational and positional*, not substantial: to be an element is to perform a role in a system, not to possess a special property of “elementhood.”[^1]

Here the generating order of ToS is at work: *Rules* $\to$ *Roles* $\to$ *Elements*. First a *rule* (the order of levels and the criterion) sets what *can* be a collection at all; then the *role* is defined (being a member of this collection); and only then does it become clear which *elements* are actually present at each finite stage. A set does not precede its rules as an object—it is constituted by them as a role.

*A set is a role-System (a criterion over a lower level); membership is the role `element_at` (a position at the level below). The order of constitution: the rule of levels $\to$ the role of membership $\to$ the actual elements.*

## The Rule of Levels and Paradox-Freedom by Construction

The order of levels is given by a strict relation $l_1 \ll l_2$ (“$l_1$ is more fundamental than $l_2$”). It is *irreflexive*: no level is below itself. In ToS this is not a postulate but a *theorem*: $l \ll l$ entails a strict decrease of the natural-number depth of the level, which is impossible.[^2] Hence the principle P1: *no self-membership*.

P1 does the work that in ZFC is partly carried by the Axiom of Foundation (Regularity): the exclusion of self-membership and of cyclic totalization across levels. The forms are *functionally kindred* but do not literally coincide: ZFC *adds* Foundation as a separate axiom to rule out $\in$-cycles; ToS makes them *structurally impossible*—the exclusion is a consequence of the definition of a level, not a superfluous postulate.

The condition of *well-formedness* of a system is exactly this: the criterion domain lies strictly below the system itself (P2). Russell’s famous “set of all sets that do not contain themselves” fails precisely this condition—its criterion would have to range over its own level. Therefore it is not ruled out *ad hoc*; it simply *does not form* as a well-formed system.[^3]

*The order of levels is a role-rule constituting the theory; its irreflexivity is the condition of well-formedness that makes the system paradox-free by construction. Where ZFC excludes by an axiom, ToS does not form by structure.*

## Paradoxes as Category Mistakes

The three classical paradoxes—Russell’s, Cantor’s, and Burali-Forti’s—are, from the standpoint of ToS, *one* move: the reification of a *role/rule-totality* (“the set of all …,” “the level of all …”) as a completed Element-object.

**Russell.** $R=\{x \mid x\notin x\}$ is impredicative: it is defined through quantification over a totality that includes it. Under P1 (hierarchy) and P4 (Finite Actuality) it does not form: there is no completed totality of “all sets,” and self-membership is impossible.[^4]

**Burali-Forti.** “The set of all ordinals” leads to an ordinal greater than all ordinals. In ToS the corresponding device—“the level of all levels”—is impossible *structurally*: for any candidate for the top $M$, its *successor* $\mathrm{LS} M$ no longer lies below-or-equal to $M$. The top escapes by one step—and so for every candidate.[^5]

**Cantor’s paradox of the universal set.** “The set of all sets” (and its diagonal companion) is blocked in ToS by the same rule: the system “of all systems of level $L_2$” would require a criterion over level $L_2$, while the criterion must be strictly below.[^6]

The diagnosis is one: the phrase “$X$ of all $X$” names a *rule* (an order of generation), not an Element-object. The paradox arises at exactly the moment when this rule is demanded *as a completed thing*. To remove the paradox is to return the phrase to its true category: a role/rule, not an element.

*The paradox is a role-diagnostic: it points to the reification of a rule-totality as an Element. P1 removes level self-reference, and P4 rules out completed totality as an Element; together they return all three (Russell, Burali-Forti, Cantor) to a category mistake—not by a separate exclusion for each, but by a change of category.*

## E/R/R Analysis

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the order of levels $\ll$ (P1, irreflexive); criterion${}+{}$P2 (domain strictly below)—they do the work of Separation; the hierarchy as a constitutive rule |
| *Roles* (L4) | set ${}={}$ System; $\in{}={}$`element_at` (position); “being a collection,” “being a member” |
| *Elements* (L1${}+{}$P4) | at each stage, finite data; a completed infinite collection is a role-limit, not an Element |

**Well-formedness.** A system is well-formed $\Longleftrightarrow$ its criterion domain is strictly below (P2); the irreflexivity of $\ll$ guarantees the absence of $\in$-cycles *by construction*.

**What it yields.** Foundation $\to$ a theorem (`level_lt_irrefl`); the work of Separation is done by
criterion${}+{}$P2; paradoxes $\to$ structurally impossible. The strong axioms lose their work as soon as one stops reifying a collection as an Element.

**Diagnosis.** The root error is “the set as a completed object”; every strong axiom and every paradox is a particular manifestation of it.

**Honest boundaries.** The principle L4 (witness extraction from a single $\exists$) is not the Axiom of Choice as a completed graph, but its strength is choice-like: choice over any family follows from it ([[Formalization]]); this is clarified in 10.4. The power set *as an object* is not built here (only the type of bool-predicates, 10.3). ToS does not prove the metatheoretical independence of AC (forcing, models): what is at issue is an *object-level* bypass of choice.

*A set is a role-System; membership is a role; the hierarchy is a rule; completed infinity is a role-limit. A strong axiom and a paradox are two forms of one error: the reification of a role/rule as an Element.*

## Summary and Transition

The chapter has laid the foundation of Part X: a set is a System, membership is a role, and the rule of levels P1 makes the theory paradox-free without separate axioms of exclusion. Russell, Burali-Forti, and Cantor turned out to be three guises of one category mistake—the demand for a rule-totality as a completed object.

Further on, Part X unfolds this optics on concrete theorems. Chapter 10.2: countability is constructive (ℚ is enumerable without axioms), and uncountability is a *rule* about processes, not the size of a completed set. Chapter 10.3: comparing cardinalities without choice—Schröder–Bernstein and Cantor’s general theorem. Chapter 10.4: the Axiom of Choice in its dual fate—the *exclusion* of its completed-object form and the *reinterpretation* of its admissible core as a rule of L5. Chapter 10.5: ordinals as processes and the tower of strong axioms (ATR$_0$, $\Pi^1_1$). Chapter 10.6: synthesis and an honest map of boundaries.

*A set is a role-System, not an Element-object; membership is a role, the hierarchy a rule, paradox-freedom a consequence of structure. Such is the frame in which Part X rereads cardinality, choice, and infinity: not as things, but as rules and roles over finitely actual processes.*

---

[^1]: The basic definitions—`Level`, `System`, `element_at`, the criterion—are in `TheoryOfSystems_Core_ERR.v`. The level of a system is strictly above the level of its criterion domain (principle P2).
[^2]: `level_lt_irrefl` and `P1_no_self_membership` (`TheoryOfSystems_Core_ERR.v`): $\forall l,\ \lnot(l \ll l)$, proved via `level_depth` (strictly decreasing under $\ll$). Constructively, without axioms.
[^3]: `russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`): the Russell collection cannot be built at any level. See also `P4ProhibitsImpredicative.v`: the impredicative definition $R=\{x \mid x\notin x\}$ requires a completed totality of “all sets,” which P4 does not admit.
[^4]: `P4ProhibitsImpredicative.v`: $R$ requires a completed totality; P1${}+{}$P4 exclude it.
[^5]: `no_universal_level` (`TransfiniteInductionLevel.v`, this work): $\lnot \exists \text{Top},\ \forall L,\ L \ll \text{Top} \lor L = \text{Top}$. Proved via the successor $\mathrm{LS}$; constructively, 0 axioms. The same file gives well-founded induction on the hierarchy of levels.
[^6]: `cantor_paradox_blocked_v1` (`TheoryOfSystems_Core_ERR.v`).

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/05 Navier Stokes and Synthesis|Chapter 5. Navier–Stokes and Synthesis—Part IX]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/02 Countability Is Constructive Uncountability Is a Rule About Processes|Chapter 2. Countability Is Constructive; Uncountability Is a Rule about Processes]] →
