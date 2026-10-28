---
title: "Chapter 7. The Uncertainty Principle in Information"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/07 Принцип неопределённости в информации.md"
sourceBlob: 0ff16144fa2c81aad114462b2d3ca8c7f0d3bffe
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The last step of the part is the limit of information itself. Information has its own *uncertainty principle*: resolution cannot be increased for free; every bit has a price. This principle is parallel to Fourier uncertainty (Part VII: time $\leftrightarrow$ frequency) and to quantum uncertainty (position $\leftrightarrow$ momentum), and through Landauer’s principle information joins with physics. The chapter closes the part and builds a bridge to von Neumann and quantum information—to physics.

*Information has a price: in the finite ladder of resolution the first (coarse) bit is the most expensive (the informational uncertainty principle), and the erasure of a bit has a physical price (Landauer). Distinction is not free.*

## The Informational Uncertainty Principle

In refining position, we pay with resolution: the more bits of position we demand, the smaller the residual uncertainty of the block, but the *price* of each next bit decreases—and in the basic finite ladder the first (coarse) bit is *the most expensive*[^1]. This is the informational form of the uncertainty relation: a *price curve* of resolution, finite and computable over ℚ, not an exclusion.

*The same structure as in Fourier uncertainty (Part VII) and in quantum uncertainty: two conjugate quantities cannot be brought to zero simultaneously. Here it is resolution against price, and everything is on the Element side.*

In this finite rational model the informational uncertainty principle is a classical 0-axiom statement: a computable ladder of prices of resolution—neither a quantum postulate nor a generally accepted theorem under this name. It *anticipates* the quantum one without needing it, and shows that conjugacy is a structural phenomenon rather than a specifically quantum one.

## Landauer’s Principle

Information joins with thermodynamics through Landauer’s principle: the erasure of one bit has an energy cost—in physical units it is proportional to $kT\ln 2$, while in the formal model the coefficient $k\ln 2$ is normalized, so that the proportionality structure $T\cdot b$ remains[^2]. This binds the part into one: Shannon entropy (Chapter 5), the growth of entropy under mixing (Chapter 4), and the erasure of information are one and the same balance of distinctions, now with a physical price. A bit is not an abstraction: to *forget* a distinction, one has to pay.

## Von Neumann and Quantum Information: The Bridge to Physics

Here the part goes beyond its 0-axiom domain—toward quantum information—and does so honestly, as a *bridge*, not as a ready formalization. In the ontological reading of ToS, quantum measurement is the *physical execution* of L3: a superposition (an indeterminate “or”) becomes a determinate outcome upon measurement—an act of distinction carried out over the world. The von Neumann entropy $S = -\operatorname{Tr}\rho\log\rho$ generalizes the Shannon entropy (which is its special case for a diagonal density matrix), and the qubit—the quantum bit—lives already on Tier-1 (the physical tier of realization; via the Born rule).

*The classical side—informational uncertainty and Landauer—has 0 axioms and is built here; the quantum side (von Neumann entropy, qubits) is Tier-1 and is left as a prose bridge to physics, honestly, without overpromising.*

The Heisenberg uncertainty cluster (220 machine statements in 18 files) formalizes the classical conjugacy of *resolution* in discrete ℚ-form (not the continuous relation $\Delta x \Delta p$); the von Neumann generalization and the quantum measures of information are the subject of physics, where the present part leads: Shannon $\to$ von Neumann $\to$ the quantum, through a single ontology of distinctions.

## The Synthesis of the Part: Information as the Number of Distinctions

The part gathers into one statement. *Information is the number of acts of distinction*, and each chapter measured it from its own side: combinatorics *counted* distinctions (Chapter 1), graphs gave them *structure* (Chapter 2), probability *distributed* them (Chapter 3), the Markov process *mixed* them (Chapter 4), Shannon entropy *measured* them and turned out to be the unique measure on the dyadic core (Chapter 5), Kolmogorov complexity *individualized* them (Chapter 6), and uncertainty named their *price* (Chapter 7).

*And everywhere one and the same cut—the finitization boundary: the finite / decidable / 0-axiom (Element) against the limit / uncomputable / continuum / quantum (role-limit). A distinction is finite and exact while it terminates; beyond the limit there is a process.*

Discrete mathematics, probability, and information form one of the best-supported and most thoroughly 0-axiom parts of the volume precisely because their bearers are finite by construction. And their only boundary is the same one the whole project carries: the passage to the completed infinite (limit laws, the uncomputable $K$, continuum measure, the quantum) is the role-limit side. Measurement—the execution of L3—is the very point where a distinction becomes determinate.

## E/R/R Analysis: Information as a System

Let us analyze information as the system of the part—in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *measure of distinctions*: additive, nonnegative, normalized (Shannon, unique on the dyadic core); adjoining it are the rule of conjugacy (two conjugate quantities cannot be zeroed at once) and the rule of price (Landauer: distinction/erasure has a physical cost).

**Roles (L4).** Entropy, mutual information, and complexity are role-measures; resolution and uncertainty are conjugate roles; measurement is the role of executing L3 (turning the indeterminate into the determinate). Shannon and von Neumann are the classical and quantum roles of one measure (the quantum one in a bridging reading not yet formalized here).

**Elements (L1 + P4).** The bearers are finite distributions, bits, ℚ-prices of resolution. Under P4 it is they that are actual; the von Neumann entropy on a continuum state space and the quantum measures are role-limit / Tier-1, a bridge to physics, not completed objects of this part.

**Well-formedness check.** Measure, conjugacy, and price are Rules; entropy/complexity/resolution/measurement are Roles; finite distributions and bits are Elements; there are no overlaps. There is no diagonal self-application here: the rule of the measure is not an object of the same distributional space.

**What the analysis yields.** It closes the flagship of the part: information is the number of acts of distinction, measurable by a unique measure, having a price (uncertainty, Landauer) and two faces (Shannon’s statistical one and Kolmogorov’s algorithmic one), and cut everywhere by one finitization boundary. Measurement as the execution of L3 is the bridge to the quantum and to physics.

The applied triad of the volume is complete. Information, as the number and as the measure of distinctions, is ready to become the language of physics—the path there leads through von Neumann and the quantum, and within the present volume the path leads to the final synthesis, where both sides of the finitization boundary will meet.

---

[^1]: `cost_per_bit_16`, `first_bit_most_expensive`, `cost_monotone_*`, `full_resolution_highest_total` (in `heisenberg/InformationUncertainty`): on the concrete chain $K{=}16$ the price of a bit along the ladder of blocks $8\to4\to2$ strictly decreases ($\tfrac12\to\tfrac14\to\tfrac16$), the coarsest bit is the most expensive of all, and all prices are positive. This is a *concrete computable ladder over ℚ*, not a general monotonicity theorem. Machine-checked, 0 axioms.
[^2]: `information/LandauerConnection`: what is machine-closed is the *proportionality structure* of the erasure cost—$\mathtt{landauer\_cost} T b=T\cdot b$ (the cost is $\propto T$, $\propto$ the number of bits, zero at $T=0$; `landauer_connection_synthesis`); the factor $k\ln 2$ is absorbed into natural units. A structural/symbolic law linking information and energy, a bridge to the second law (Chapter 4) and to thermodynamics, not a full thermodynamic model. Machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/06 Kolmogorov Complexity and Algorithmic Information|Chapter 6. Kolmogorov Complexity and Algorithmic Information]] · [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/01 Ascending Tower of Role Types|Chapter 1. The Ascending Tower of Role-Types—Part XVIII]] →
