---
title: "Chapter 6. Synthesis and the Map of Boundaries"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/06 Синтез и карта границ.md"
sourceBlob: 36a7835de748abe1dc81fa76e7675872d98ce7eb
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

This is the finale of Part XI. Five chapters have traveled the path: the field as a role-extension (11.1); the algebraic number as a role-limit tamed by a minimal polynomial (11.2); constructibility as reachability by tier $2$ and the Greek impossibilities as theorems about the tier (11.3); finite multiplicatively stable structures (11.4); and, at the center, the concrete Galois correspondence with the engine of the unsolvability of the quintic (11.5).

This chapter does three things. First, it assembles a *unified picture* of Galois-in-ToS. Second, it presents a rethinking to which the work itself led: *the algebraic closure of $ℚ$ is not a wall but a process*. Third, it gives an *honest map of boundaries*—and its main result is unexpected: Part XI contains *not a single new P4 exclusion*. The boundary here is arranged differently than in Part X.

*The finale of Part XI: a unified picture (the tier governs everything), a rethinking (the closure of $ℚ$ is a process), and a map of boundaries without new P4 exclusions.*

## Galois-in-ToS: A Unified Picture

The recurring protagonist of the whole part is the *algebraic tier* (the degree). It governs everything encountered:

- the *field* is a role-extension given by the tier of surds (11.1);
- the *number* is a role-limit of a process tamed by a minimal polynomial whose degree is the tier (11.2);
- *constructibility* is reachability by tier $2$; the Greek impossibilities are the demand for tier $3$, structurally outside the quadratic tower (11.3);
- *finite structures* are finite multiplicative order: roots of unity, norm forms $1,2,4,8$, the fields $\FF_p$ (11.4);
- the *Galois group* is the role-symmetry of the roots (the concrete $V_4$ table for $ℚ[\sqrt2,\sqrt3]$: automorphisms, fixed subfields, reversal of inclusion); unsolvability is a perfect core (11.5).

One and the same tier determines what is *reachable* (the quadratic tower), what is *ruled out* (the cubic tier for the compass, the fivefold axis for a lattice), what is *symmetric* (the Galois group of the roots), and what is *stable* (finite norms). Hence the unified formula of the part. *Within the P4 ontology of ToS*, Galois theory is realized not as a general abstract functorial framework $L/K\mapsto\Aut(L/K)$ but as a *concrete degree-tier, norm-form, and correspondence shadow over $ℚ$*—with a genuine correspondence (for $ℚ[\sqrt2,\sqrt3]$) and a genuine engine of unsolvability. And all of this on finite coordinates; by
`Print Assumptions`, the key files introduce no new logical axioms (some statements of the previous chapters are a mathematical reading on top of this formal core).

*The algebraic tier is the recurring protagonist of Part XI: it governs the reachable, the ruled-out, the symmetric, and the stable. Galois-in-ToS is a concrete tier-norm-correspondence shadow over $ℚ$, finitely actual and requiring no axioms.*

## The Algebraic Closure of $ℚ$ as a Process

The most unexpected rethinking of the part concerns the *algebraic closure* $\overline{ℚ}$. The classical theory takes it as a completed object—a single field containing the roots of all polynomials (for an arbitrary field, via Zorn’s lemma). It is tempting to enter it into the “wall”: here, one might say, is a completed infinite totality that P4 does not let in. But this is a *mistake*: $\overline{ℚ}$ is *not a wall but a process*.

Let us analyze it by the layers of ToS. *Every* individual algebraic element, *when given by a minimal polynomial and a root selector* (an isolating interval or an index), has a finite description—it *terminates* in finite data, and is therefore in this sense *more P4-actual* than a general real, which needs a nonterminating Cauchy process. The *totality*, by contrast, is not a completed Element but an *$ℕ$-indexed ascending tower* of finite extensions

$$
ℚ \subset ℚ[\sqrt2] \subset ℚ[\sqrt2,\sqrt3] \subset ℚ[\sqrt2,\sqrt3,\sqrt5] \subset \cdots,
$$

which has *no maximal rung* and in which *every* element is localized at some finite rung.[^1] This is precisely the type of object the whole volume has dealt with: a process over finite stages, like `RealProcess`.

The moral repeats the device of Part X. The classical demand “build the closure as a ready thing” mixes two statements: the *Rule*—“the roots of any rational polynomial lie in *some* finite extension” (true, constructive, and precisely what mathematics actually uses)—and the completed *Element*—“there exists a *single* object with all the roots of all polynomials *at once*” (a Platonist surplus). ToS keeps the rule (the process) and discards the surplus. The formal file proves precisely the *tower ontology* of the process (no maximal rung, every element finitely localized), and *not* a full algorithm for factoring and adjoining all the roots; that for $ℚ$ *itself* the closure is constructive (without choice, factorization over $ℚ$ is algorithmic) is a classical / mathematical reading on top of this model.

*The algebraic closure of $ℚ$ is not a completed object but a process: an ascending tower of finite extensions without a maximal rung, every element finitely localized. The classical “closure-as-a-thing” is a surplus over a constructive rule; ToS holds the rule, as in Part X.*

## The Map of Boundaries of Part XI

Let us gather everything into an honest map. It has three layers.

| **Layer** | **Content** | **Price** |
|---|---|---|
| *Built (0 axioms)* | the whole cluster: extensions of $ℚ$ and degree-tier, the Greek impossibilities, the crystallographic restriction, norm forms, $\FF_p$, $S_3$ and the numerical layer of $S_5$; the concrete $V_4$ Galois table for $ℚ[\sqrt2,\sqrt3]$ (automorphisms, fixed subfields), the general Gauss’s lemma, the solvability engine (perfect nonabelian$ \Rightarrow$ not solvable); a concrete splitting field; **the closure of $ℚ$ as a process** | none |
| *Labor backlog (not an exclusion)* | the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an *arbitrary* $L/K$; the simplicity of $A_5$ *inside* the engine (finite combinatorics on 60 elements); the full Abel–Ruffini theorem; the Fundamental Theorem of Galois theory in general; the general tower law | role-limit / labor |
| *The prices of Part X* | the Axiom of Choice—for the closure of an *arbitrary* field (but not of $ℚ$!); the continuum—for embedding into the analytic $ℝ$/$ℂ$ | AC / continuum |

The main result of the map—and of the whole part. *In the formalized algebraic layer of Part XI there is not a single new P4 exclusion.* (The completed $\overline{ℚ}$ as a single object would still receive the P4 diagnosis of a completed totality—but this is exactly why the chapter reads it as a *process*, not as an Element.) In Part X the boundary contained *exclusions*: the Axiom of Choice in completed-object form is P4-incompatible. Here, by contrast, everything not done is of the kind “*labor* or *role-limit*”: large but in principle finitely constructive tasks (the simplicity of $A_5$ is a finite check; the closure of $ℚ$ is a constructive tower; the general Abel–Ruffini is finite for each polynomial). And the only genuine ineliminable *prices* nearby—the Axiom of Choice (for arbitrary fields) and the continuum (for embedding into $ℝ$/$ℂ$)—*have already been named and assessed in Part X*, and $ℚ$ itself does not pay them. Algebra over $ℚ$ turns out to be ontologically *almost free*.

*The map of boundaries has three layers: built (0 axioms, including the closure-as-process); labor backlog (the abstract functor, the simplicity of $A_5$, the full Abel–Ruffini); the prices of Part X (choice, the continuum, which $ℚ$ does not pay). There is no new P4 exclusion—unlike in Part X.*

## E/R/R Analysis of Part XI

Let us gather the whole part in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the minimal polynomial (the rule of algebraicity); the general Gauss’s lemma / rational root test (whether the process will close in $ℚ$); the criterion of constructibility (tier $2^k$) and the integrality of the trace; the multiplicativity of the norm ($1,2,4,8$); the Galois correspondence (subgroup ${}\leftrightarrow{}$ subfield); solvability (the derived series reaches $\{e\}$) |
| *Roles* (L4) | field ${}={}$ role-extension; degree ${}={}$ tier; number ${}={}$ role-limit; constructibility ${}={}$ the role of reachability by tier $2$; finite structures ${}={}$ roles of finite order; Galois group ${}={}$ the role-symmetry of the roots; closure ${}={}$ role-process (a tower) |
| *Elements* (L1${}+{}$P4) | everywhere finite data over $ℚ$: coordinates of extensions, lists of coefficients, approximations, permutations, elements of $\FF_p$, automorphisms as formulas, rungs of the tower; completed totalities (the functor $\Aut$, $\overline{ℚ}$-as-an-object) are *not* Elements |

**Well-formedness.** Each role is constituted by its rule, and at each stage only finite Elements are actual; completed objects are not instantiated but replaced by processes or concrete encodings. No component requires completed infinity as an Element.

**What it yields.** A coherent algebra over $ℚ$ on finite coordinates (the key files: 0 new axioms by `Print Assumptions`): tiers, impossibilities, norms, finite fields, the concrete $V_4$ Galois table, the engine of unsolvability (perfect nonabelian$ \Rightarrow$ not solvable), and the closure as a process.

**Diagnosis.** The root error of the whole classical frame is the reification of *completed algebraic totalities* (the abstract Galois functor, the splitting field, the closure-object) and the solving of problems through their properties. ToS returns the categories: rule, role, process—instead of a completed object.

**Honest boundaries.** Listed in the map (§11.6.4): the abstract functor for an arbitrary $L/K$, the simplicity of $A_5$ in the engine, the full Abel–Ruffini—labor/role-limits; choice and the continuum—the prices of Part X. There are no new P4 exclusions.

*The whole of Part XI: rules (tier, norms, correspondence, solvability) $\to$ roles (field, degree, number, symmetry, closure-process) $\to$ finite Elements over $ℚ$. Completed totalities are replaced by processes and encodings; 0 axioms.*

## Summary of Part XI

Part XI has read algebra, fields, and Galois theory in the same optics in which Part X read set theory: by changing the category and holding to the finitely actual. The field has become a role-extension, the degree a tier, the number a role-limit with the minimal polynomial as its rule. Constructibility has turned out to be reachability by tier $2$, and the Greek impossibilities theorems about the tier. Finite multiplicative structures (roots of unity, the norms $1,2,4,8$, $\FF_p$) have given a positive algebra of finite order. At the center are the concrete $V_4$ Galois table for $ℚ[\sqrt2,\sqrt3]$ (automorphisms, fixed subfields, reversal of inclusion) and the engine of group unsolvability (perfect nonabelian$ \Rightarrow$ not solvable; the application to the quintic—with explicit classical premises about $A_5/S_5$), which have raised the former numerical counts and the flag to real results.

Two conclusions are worth taking away. The first: *the algebraic closure of $ℚ$ is a process, not a wall*—one more completed object resolved into a rule plus finite Elements. The second, more general: *the boundary of the formalized layer of Part XI contains no P4 exclusions* (the completed $\overline{ℚ}$ as an object is not used—it is read as a process). Everything not done is labor or role-limit; the only genuine prices (choice, the continuum) have already been named in Part X, and $ℚ$ itself does not pay them. This agrees with the recurring thesis of the volume: *the finitization boundary is the boundary of constructivity*, not of exclusions—and over $ℚ$ this boundary lies especially far away.

*Galois-in-ToS is tiers of degree ${}+{}$ norm forms ${}+{}$ a concrete
correspondence ${}+{}$ an engine of unsolvability, finitely actual and with 0 new axioms in the key files. The closure of $ℚ$ is a process. The boundary is labor and role-limits, without new P4 exclusions in the formalized layer; algebra over $ℚ$ is ontologically almost free. With this, Part XI comes to a close.*

---

[^1]: `algebra/AlgebraicClosureProcess.v` (0 axioms): the abstract tower `AlgTower` (rungs, dimensions, embeddings with strict growth); `no_maximal_rung` (there is no maximal rung), `tower_unbounded` (the dimensions exceed any bound), `germ_finitely_sited` (every element of the colimit is localized at a finite rung), the capstone `closure_is_a_process`. The concrete instance `multiquadratic` is a multiquadratic tower of dimensions $2^n$; its rung 2 coincides in dimension with $[ℚ[\sqrt2,\sqrt3]:ℚ]=4$ from 11.5.

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/05 Galois Group Concrete Correspondence and Unsolvability of the Quintic|Chapter 5. Galois Group: Concrete Correspondence and Unsolvability of the Quintic]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/01 Geometry as Rational and Lattice Structure|Chapter 1. Geometry as a Rational and Lattice Structure—Part XII]] →
