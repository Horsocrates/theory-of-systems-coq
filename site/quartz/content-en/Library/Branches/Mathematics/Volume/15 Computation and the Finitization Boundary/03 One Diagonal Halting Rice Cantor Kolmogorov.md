---
title: "Chapter 3. One Diagonal: Halting, Rice, Cantor, Kolmogorov"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/03 Одна диагональ halting, Райс, Кантор, Колмогоров.md"
sourceBlob: 85a0d67090a104d52b3b7752483b67ba40fbfab1
translated: 2026-10-20
status: draft
---

## One Engine: The Fixed Point

The heart of the part is a claim that at first sight seems out of proportion to its consequences:

> **the key negative results of computation—halting, Rice, Cantor, Kolmogorov—are
> one fixed-point theorem dressed in different costumes.**

There is no universal halting decider; there is no decider of nontrivial semantic properties; the Boolean space of predicates is not enumerable; complexity is uncomputable. In textbooks these are four different proofs. In our system this is *one* engine, and its name is *Lawvere’s theorem*.

Its form is simple. If a map $\varphi\colon A \to (A\to B)$ is *point-surjective* (every function $A\to B$ is $\varphi(a)$ for some $a$), then *every* endomorphism $f\colon B\to B$ has a fixed point:

$$
\varphi\colon A \to (A\to B)\ \text{point-surjective}
  \quad\Longrightarrow\quad
  \forall  f\colon B\to B,\ \exists  b,\ f(b)=b .
$$

The contrapositive is the working tool: *if some $f$ has NO fixed point, there can be no point-surjection*. And the simplest endomorphism without a fixed point is Boolean negation:

$$
\forall  b\in\BB\colon\quad b \neq \negb b .
$$

This single fact is the seed of *every* diagonal below. Each time, the diagonal object is built so as to become a fixed point of negation—and there is none; the contradiction closes off the decider.[^1]

This is the **first master structure of the part**: *undecidability is one fixed-point theorem*. Below are its four faces; the mirror, *positive* master structure (one discriminant) awaits in 15.4.

## The Program: There Is No Universal Halting Decider

Suppose the contrary—there is a *total* decider $D(p,q)$ answering “yes / no” to the question “does the program $p$ halt on the input $q$?” Let us build a *diagonal* program $\Delta$: on the input $p$ it asks $D(p,p)$ and does the *opposite*—it halts exactly when $D$ says “will not halt”:

$$
\Delta(p)\ \text{halts}\quad\iff\quad D(p,p)=\mathrm{false}.
$$

Let us substitute $\Delta$ into itself. We obtain $\Delta(\Delta)\ \text{halts}\iff\Delta(\Delta)\ \text{does not
halt}$—exactly the sought fixed point of negation, which does not exist. Hence a total decider $D$ does not exist.[^2]

Let us compare with 15.1. There *bounded* halting was decidable (Element). What is ruled out here is a *total* decider “for all programs at once,” not a separate run. The diagonal rules out precisely the *reification* of a role-limit into an Element decider: not “we failed to compute,” but “there is no such Element object.”

## The Set: The Boolean Space Is Not Enumerable (Cantor)

The same construction over sets. No $g\colon A \to (A\to\BB)$ is surjective: the predicate

$$
d(a) := \negb \bigl(g(a)(a)\bigr)
  \quad\text{differs from every } g(a)\ \text{at the point } a,
$$

since $d(a)=\negb(g(a)(a))\neq g(a)(a)$. Hence $d$ is none of the $g(a)$—there is no enumeration of all predicates $A\to\BB$. This is again $b\neq\negb b$, now along the diagonal $a\mapsto g(a)(a)$.[^3]

**The most important distinction (an honest price).**  This diagonal—over the space of *Boolean predicates* $A\to\BB$—is fully **constructive**: neither the Law of Excluded Middle, nor choice, nor a single axiom. But the famous “uncountability of the *continuum*” (of the completed real line) is a *different and stronger* statement: it rests on the classical layer (L3, classic) together with L4 and lives separately. Our system does *not mix* them: the diagonal-over-predicates is 0-axiom, while the uncountability of the completed continuum pays the classical price.[^4]

## Semantics: There Is No Decider of Nontrivial Properties (Rice)

The third face concerns the *meaning* of a program, not its text. *Trivial* semantic properties (always true or always false) are decidable—this is the Element side. But any *nontrivial* semantic property (one that depends only on the computed function and is neither always true nor always false) has *no* decider: from a candidate decider a self-negating witness is built—a program whose property contradicts the verdict—and the same diagonal engine closes off the decider.[^5]

Rice is “halting in general form”: not only halting, but *any* nontrivial property of behavior cannot be finitized into a total decider. The boundary is the same: the trivial (degenerate) is an Element; the substantively semantic is a role-limit.

## Complexity: The Kolmogorov Face (Berry/Chaitin)

The fourth face is the *complexity* of an object (its shortest description). Like halting, it has two sides. The *Element side* is incompressibility *by counting*: for any budget $n$ there are *finitely* many short programs, so some object is not described within $n$—the pure pigeonhole, 0 axioms. The *role-limit side* is a total decider of the *criterion* of complexity (a model-relative $K$-oracle): when the model admits the self-negating Berry / Chaitin witness (“the least number not describable in fewer than $k$ symbols”—which has just described itself), that decider is ruled out by *the same* diagonal.[^6]

**The honest domain.**  Kolmogorov’s $K$ here is *model-relative*: full invariance of $K$ under the choice of machine is NOT claimed (that lies beyond the boundary of what is formalized). The statement is exact: for a fixed model of description, a total decider of the complexity criterion is a role-limit defeated by *the same* $ b\neq\negb b$ as halting and Cantor. Kolmogorov is the *fourth* face.

## One Diagonal, Four Faces (and Beyond)

Let us gather the faces into one. All four are particular cases of one engine (`diagonal_ defeats_ decider`), rooted in Lawvere’s theorem:

| **Face** | **Role-limit (ruled out by the diagonal)** | **Machine anchor** |
|---|---|---|
| program | a total halting decider | `no_halting_decider` |
| set | a surjection $A\to(A\to\BB)$ (Cantor) | `cantor_no_surjection` |
| semantics | a decider of a nontrivial property (Rice) | `rice_role_limit` |
| complexity | a decider of the complexity criterion (Berry / Chaitin) | `kolmogorov_ role_ limit_ drawn` |
| \multicolumn{3}{@{}p{0.93\textwidth}@{}}{*Element contrast (number):* the discriminant `rational_split` is *decidable* (`discriminant_element_drawn`)—a bridge to 15.4.} |

These faces are assembled into one machine result: number (Element), program, set, and complexity are *one* boundary, four faces, a single engine $b\neq\negb b$.[^7] The *decidable* face (number, the discriminant) deliberately stands in the same theorem—it is the very mirror that 15.4 unfolds.

**Faces beyond the four.**  “And beyond” means *the same diagonal scheme* extended to the classical *paradoxes*, not new faces in the capstone of this chapter (it gathers exactly four CS faces, `one_boundary_four_faces`): there is no universal set (Russell), there is no truth predicate (Tarski), the “liar” and “Grelling” are impossible. This is the same diagonal over Prop (the twin $(\neg P)\neq P$ instead of $b\neq\negb b$), with *its own* machine proofs in separate files.[^8] Thus the diagonal unites not only uncomputability but also the paradoxes of reasoning—a bridge to the taxonomy of paradoxes of the Architecture of Reasoning.

## E/R/R Analysis and What the Chapter Has Prepared

**Rules (L5).**  The diagonal is a *rule* that does not admit the reification of a role-limit into an Element decider; the atomic rule is $b\neq\negb b$ (and its Prop twin $(\neg P)\neq P$); Lawvere’s theorem *names* why this rule holds for all the faces at once.

**Roles (L4).**  The decider / oracle is a role-oracle; “halts,” “is complex,” “is true,” “is in the diagonal set” are role-limit predicates. Their Element twins (bounded halting, a trivial property, incompressibility-by-counting, the discriminant) are decidable—this is a different role.

{

**Elements (L1${}+{}$P4).**  Concrete programs, finite runs, Boolean negation itself, the counting argument of the pigeonhole. *Not* an element: a total halting oracle, a total $K$-decider, a truth predicate, a universal set—the diagonal rules out each of them.}

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| diagonal; $b\neq\negb b$; $(\neg P)\neq P$; Lawvere’s theorem | the exclusion of reifying a role-limit | Rule (L5) |
| decider-oracle; “halts / complex / true” as role-limit predicates | roles and limits | Role (L4) |
| programs; runs; `negb`; the pigeonhole count | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Each face is one and the same category mistake: an attempt to reify a role-limit (a process / limit) into a completed Element decider. Lawvere’s theorem is the *exact formulation* of the impossibility; the four faces are its costumes. The boundary does not “hinder computation”—it *names the scale*: what is captured by a decider, and what is a limit.

**What the chapter has prepared.**  The *first* master structure of the part has been presented: undecidability is one diagonal, its root is the fixed point (Lawvere), four faces (halting / Cantor / Rice / Kolmogorov) plus the paradoxes (Russell / Tarski). Everything is 0-axiom and machine-checked; the only *classical* price is the uncountability of the completed continuum, and it is set apart. Next comes the *mirror*: Chapter 15.4 will present the *positive* master structure—*one discriminant* of the reduction atlas, which draws the decidable (Element) side by one terminating criterion.

---

[^1]: `src/cs/LawvereFixedPoint.v` (**0 axioms**): `point_surjective`, `lawvere_fixed_point`; the theorem `cs_ diagonals_ are_lawvere` formally assembles the root—`lawvere_fixed_point`, `negb_no_fixpoint`, and the Cantor face; halting / Rice / Kolmogorov use the same $\negb$ engine via `diagonal_ defeats_ decider`. The seed is `HaltingRoleLimit.negb_no_fixpoint` ($b\neq\negb b$). The universal engine is `src/cs/BoundaryDecidability.diagonal_defeats_decider`: if against every decider there is a self-negating witness, the criterion is role-limit-drawn.
[^2]: `src/cs/HaltingRoleLimit.v` (**0 axioms**): `no_halting_decider` (there is no decider of self-application under self-programmability, `SelfProgrammable`), `no_total_halting_oracle`. The Element twin is `bounded_halting_decidable` from 15.1.
[^3]: `src/cs/HaltingRoleLimit.cantor_no_surjection` (**0 axioms**); as a particular case of Lawvere: `LawvereFixedPoint.cantor_via_lawvere`, `nat_fun_not_enumerable`.
[^4]: The uncountability of the completed continuum is `ProcessDiagonal.binary_processes_not_enumerable`, `ProcessContinuumHypothesis.process_continuum_hypothesis`: the layer L3 (classic)${}+{}$L4, separate and stronger (cf. Part IV). The contrast is honest: `cantor_no_surjection` and halting do NOT require classic—this is what “the Element side is constructive” means.
[^5]: `src/cs/RiceRoleLimit.v` (**0 axioms**): `trivial_property_element_drawn` (the trivial is an Element, decidable), `RiceDiagonal` and `rice_diagonal_exists` (the self-negating witness), `rice_role_limit`, `rice_no_semantic_decider`.
[^6]: `src/cs/KolmogorovRoleLimit.v` (**0 axioms**): `incompressible_exists` (Element / counting: for a budget $n$ there is an indescribable object), `kolmogorov_ role_ limit_ drawn` proves the role-limit character of the criterion `Complex` under the Berry / Chaitin diagonal (a particular case of `diagonal_ defeats_ decider`); this is *not* a theorem on the invariance of $K$ and not a universal machine in full generality.
[^7]: The formal capstone of the section is `src/cs/ KolmogorovRoleLimit. one_boundary_ four_faces`; it extends `BoundaryDecidability. one_boundary_ three_faces`; **0 axioms**.
[^8]: `src/cs/RussellViaLawvere.v` (`russell_ no_universal_set`, `liar`, `grelling`, `paradoxes_ one_diagonal`; the seed is `not_no_fixpoint`: $(\neg P)\neq P$); `src/cs/TarskiUndefinability.v` (`tarski_ no_truth_predicate`, `tarski_ from_lawvere`). **0 axioms**.

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/02 Finite Memory and the Chomsky Hierarchy|Chapter 2. Finite Memory and the Chomsky Ladder]] · [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/04 One Discriminant Reduction Atlas and the Decidable Side|Chapter 4. One Discriminant: The Reduction Atlas and the Decidable Side]] →
