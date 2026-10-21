---
title: "Chapter 7. Synthesis: One Diagonal, One Discriminant"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/07 Синтез одна диагональ, один дискриминант.md"
sourceBlob: 2cf0233c166af1dd22f6a64d67844055b29f528c
translated: 2026-10-20
status: draft
---

## One Boundary, Both Sides

The part has gone through six chapters but has described *one* thing: the finitization boundary made algorithmic. Let us take it in at one glance.

- [leftmargin=1.4em,itemsep=2pt]
- **Is it possible?** (15.1, 15.3) The central cut: the bounded is an Element, decidable; the unbounded *as a universal recognition problem* is a role-limit. The negative side is held by *one diagonal*: negation has no fixed point, so there is no total decider (of halting, semantics, enumeration, complexity).
- **How to finitize?** (15.2, 15.4, 15.5) The positive side is held by *one discriminant* (perfect square ${}\Rightarrow$ decidable); the reduction atlas reduces many engines to it, the Chomsky ladder grades memory, and fuel ${}+{}$ type safety fold the infinite reduction into a safe finite run.
- **How much does it cost?** (15.6) On the positive side there remains the *price*—a metric of the finitized process; $\mathrm{P}$ vs $\mathrm{NP}$ is posed, not solved.

Not six topics but **one boundary under three angles**: whether, how, and at what cost. And it has two *master structures*—the diagonal and the discriminant—while price is the measure of distance within its positive side.

## The Capstone: Computation = the Finitization Boundary

All of this is assembled into *one* theorem. Its three conjuncts are exactly the three sides of the picture:

1. [leftmargin=2.2em,itemsep=2pt]
2. [(1)] *Element*: bounded halting is **decidable on any machine** (on the arena of the P4-finite run);
3. [(2)] *one diagonal, four faces*: number (the discriminant) is Element-drawn; program / set / complexity are role-limit-drawn;
4. [(3)] *the root* is the fixed point (Lawvere’s theorem), the common engine of all the faces.

Note: *both* master structures are represented already *within conjunct (2)*: the diagonal through the role-limit faces, the discriminant through `ElementDrawn rational_split`; the full reduction atlas unfolds this discriminant face as a separate layer. That is, “diagonal $\oplus$ discriminant—one boundary” is literally *one conjunction*, not a metaphor.[^1]

This is the thesis of the part: *computation is the finitization boundary made algorithmic*—one arena carries both sides.

## The Map of Boundaries of the Part

Where exactly the honest tiers run—just as in the finales of the previous parts.

**0 axioms (dominant).**  The diagonal side (halting, Rice, Cantor over Boolean predicates, Kolmogorov ${}+{}$ the Lawvere root); Element decidability (bounded halting, regular languages, the discriminant atlas, choice without AC); type safety ${}+{}$ fuel; the complexity framework. Everything is machine-checked and 0-axiom.

**classic (L3)${}+{}$L4\ — only one face.**  *The uncountability of the completed continuum* (a separate, stronger layer; cf. Part IV). The contrast is the point: halting and Cantor-over-predicates do *not* require classic—the Element side is constructive.

**Zero domain axioms.**  As in Part XIV: not a single subject-matter axiom. The logical price appears only in the layer of the completed continuum (Part IV), not in the computational core of XV.

**Honest non-results and horizons.**  $\mathrm{P}$ vs $\mathrm{NP}$ is a posing, not a solution. Halting / Rice: we prove *un*decidability (and only for a self-applicable language, as a hypothesis, not for all systems). A closed decision procedure of *general degree* is a horizon, not a single procedure. Kolmogorov’s $K$ is model-relative (invariance under the machine is not claimed). Complexity theory is an applied metric and is not retold.

## E/R/R Analysis of the Whole Part

**Rules (L5).**  The boundary “terminates${}\Leftrightarrow{}$Element”; the diagonal (no fixed point ${}\Rightarrow$ no universal decider); the quadratic discriminant (perfect square ${}\Rightarrow$ decidable criterion); reduction ${}+{}$ fuel.

**Roles (L4).**  Element / role-limit are roles of computations (decidable / undecidable); the decider versus the diagonalizer; memory (control / stack / tape) is the role of a tier; the type is a role; price is a metric of the positive side.

{

**Elements (L1${}+{}$P4).**  Finite computations, fuel runs, DFA runs, concrete programs / matrices / certificates. *Not* an element (role-limit): a total halting oracle, a model-relative $K$-oracle, a completed infinite reduction, an unbounded search. *Not yet* an element of the current formalization (a horizon, not an ontological exclusion): a closed decision procedure of general degree.}

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the cut “terminates${}\Leftrightarrow{}$Element”; diagonal; discriminant; fuel | the constitution of computability | Rule (L5) |
| Element / role-limit; decider / diagonalizer; memory; type; price | roles and metrics | Role (L4) |
| finite computations; runs; programs; matrices; certificates | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Uncomputability / nontermination is a role-limit (a process), not a completed object; “we have solved halting” would be a level confusion. Finitization is the systemic answer: do not solve the role-limit (that cannot be done) but take an Element approximation with a process parameter. This is what binds all six chapters into one boundary.

## Bridges

**To Part XVI (the discrete, probability, information).**  The Kolmogorov face (15.3) is a bridge to Shannon: information as a structural quantity, $K$ its model-relative, uncomputable limit. The dyadic / trit representation and counting estimates will continue the finitization line in the informational arena.

**To Volume III (quantum computation).**  The same Element / role-limit cut applies to quantum processes: a finite circuit depth is an Element, the idealized limit is a role-limit.

**To Part IV (uncountability).**  The ring closes: the uncountability of the completed continuum is *the same* diagonal as halting and Cantor. This is *one diagonal pattern*, but on different formal tiers: the constructive Boolean diagonal in XV (0 axioms) and the classical layer of the completed continuum (L3${}+{}$L4) in IV.

**To Part XIV (the category).**  Computation is the finitization kernel of the categorical metalanguage: limits-as-processes (P4) and decidability at a finite stage are its algorithmic face.

## What the Part Has Established

Part XV has given computation a home in our system. The thesis: *computation is the finitization boundary made algorithmic*. Two master structures—**one diagonal** (undecidability as a fixed point) and **one discriminant** (decidability as a perfect square)—the positive face of fuel and type safety, price as a metric; everything is assembled into one capstone and is 0-axiom, except for the honestly set-apart uncountability of the continuum.

And the flagship of the part, worth taking away:

> **undecidability is one diagonal; decidability is one discriminant; and these are two sides of one
> finitization boundary.**

What is not proved is named honestly ($\mathrm{P}$ vs $\mathrm{NP}$, the general degree, the invariance of $K$). The part is closed; next comes Part XVI, where the same boundary arises in the discrete, the probabilistic, and the informational.

---

[^1]: Machine-checked, **0 axioms**: `src/cs/ComputationModel.computation_ is_ finitization_ boundary`, the conjunction of (1) `cm_bounded_decidable` (bounded halting is decidable on any `CompModel`); (2) `one_boundary_four_faces`; (3) `lawvere_ fixed_point`.

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/06 Complexity as the Price of Finitization|Chapter 6. Complexity as the Price of Finitization]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/01 Finitization Boundary at the Level of Functions|Chapter 1. The Finitization Boundary at the Level of Functions—Part XVI]] →
