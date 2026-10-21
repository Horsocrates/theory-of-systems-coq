---
title: "Chapter 1. The Ascending Tower of Role-Types"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/18 Процессная иерархия/01 Восходящая башня роль-типов.md"
sourceBlob: b0de0827cc72209ff0261c14d5bcb1af0c829576
translated: 2026-10-20
status: draft
---

## Where the Part Stands

One dividing line has run through the whole volume—the *finitization boundary*. On one side of it is the *Element*: a terminating process, its terminus, finitely actual and provable without axioms. On the other is the *role-limit*: a non-terminating process whose “value” is approached but not filled by an Element, and to speak of it as a ready object requires exactly the Law of Excluded Middle[^1]. In Part X this second side carried the “high” constructions of set theory—the completed $\mathcal{P}(ℕ)$, the tower of Borel ranks, the minimal bad sequence of Kruskal’s theorem—and, seen from the familiar classical packaging, it looked like a single blank *wall*: behind it, supposedly, lies completed actual infinity, without which the content cannot be reached.

The present part contests precisely this image. The thesis is simple and checkable:

*The role-limit side is neither a plane nor a wall but an **upward ascent**: a tower of role-types indexed by an ordinal-process, generative (without a top), each storey of which is reachable as a process, while a completed storey-object does not exist.*

This is a direct continuation of the line of the volume. A number turned out to be a process-position rather than a ready point (Part III); a real number, a Cauchy process rather than a completed object (Part IV); the algebraic closure $\overline{ℚ}$, a generative tower without a maximal storey rather than a fully built field (Part XI); a manifold, a process of gluing rather than a ready many-point set (Part XII). The present part adds to this series *the hierarchy itself*: the set-theoretic analogue of the same reframings.

*The flagship of the part: the hierarchy is a process.*

The chapter you are reading is the *core* of the part. It builds the tower itself and proves three of its features: the tower grows strictly, storey by storey; it has no top; and its height is an ordinal-process. The subsequent chapters grade the ascent by depth (Chapter 2), trace determinacy (Chapter 3) and well-quasi-ordering (Chapter 4) along it, and gather everything into a summary (Chapter 5).

## What the Chapter Establishes and What It Does Not

Honesty from the very start. The chapter does *not* build the completed cumulative hierarchy $V_\alpha$, the Borel or the projective tower *as a ready object*: such an object is exactly the ZFC packaging that Part X marked as an artifact rather than as reachable content[^2].

What the chapter proves exactly is the *structure of the ascent*: that the tower of role-types strictly ascends, is generative, and is indexed by an ordinal-process. Each of these statements is *machine-checked and requires not a single axiom*[^3]. The applications of the ascent to “high” theorems—and the exact localization of how far one can provably climb along it—are the subject of the following chapters, while full Borel determinacy and Kruskal’s theorem remain honest *horizon-ascents* rather than fully built objects.

So: the *ascent* is proved; the *completed object* is not built. The difference between them is the very content of the part.

## The Tower of Role-Types

Let us take the basic role of the volume—the role of a *predicate over a countable carrier*, a function $ℕ\to\{\text{yes},\text{no}\}$. This is the same role through which uncountability entered Part IV. Let us set it in tiers.

**The zeroth storey** is the countable carrier itself: the natural number series $ℕ$. (In the code of the foundation the tier is counted from zero—a technical convention of the instrument; for us $ℕ$ is the primary carrier, and one is primary[^4].)

**Storey $k+1$** is the space of predicates over storey $k$: functions $(\text{storey } k)\to\{\text{yes},\text{no}\}$. This is the same role $ℕ\to\{\cdots\}$ *raised by a tier*: instead of predicates about numbers, predicates about predicates, and so on. Each next storey is a space of *decision-processes* over the one below.

| **Storey** | **What it is** | **Role** |
|---|---|---|
| $0$ | the carrier $ℕ$ | basic elements |
| $1$ | predicates over $ℕ$ (the role $ℕ\to\{\text{yes},\text{no}\}$) | decision-processes about numbers |
| $2$ | predicates over storey $1$ | decisions about decisions |
| $\;\vdots$ | $\;\vdots$ | $\;\vdots$ |
| $k+1$ | predicates over storey $k$ | decisions over storey $k$ |

The tower is *cumulative and processual*: each storey is finitely constructible at its stage—its point (a predicate) is a process-thread that gives “yes/no” on request—and no storey is a completed set-object. This is essential: we build *tiers of roles*, not nested ready sets.

## The Diagonal on Every Storey: Strict Ascent

The tower does not merely stretch upward—it grows *strictly*: each next storey is richer than the previous one, and this is proved by a *diagonal* on every tier.

> *No map from storey $n$ to storey $n+1$ covers it entirely.*

The proof is the same Cantor diagonal, raised by a tier. Let $f$ assign to each point of storey $n$ a predicate of storey $n+1$. We build the predicate $g(x)=\neg \bigl(f(x)\bigr)(x)$—“the negation of what $f$ of $x$ says about $x$ itself.” Then $g$ coincides with no $f(x)$: they differ at the point $x$. Hence $f$ is not surjective, and storey $n+1$ is strictly *wider* than storey $n$[^5].

For $n=0$ this is exactly the familiar fact: *there is no enumerator* $ℕ\to(ℕ\to\{\cdots\})$, the very core of uncountability from Part IV. What is new here is that the same diagonal works *on every storey*, and therefore the tower grows without stopping: the ascent does not run out of breath at the first step.

## No Top: A Generative Structure

From the diagonal on every storey it follows at once that the tower *has no top storey*: above any storey $n$ there is a strictly larger one, not covered surjectively from below[^6].

This is the same feature as that of $\overline{ℚ}$ in Part XI (no maximal storey of roots) and of the manifold-process in Part XII (no completing chart): the structure is *generative*, not fully built. To ask “what is the top storey of the tower?” is to demand that a generative process be a completed object; there is no such storey, and the reason is not our weakness but the very arrangement of the ascent.

*The tower of role-types is generative in exactly the same way as $\overline{ℚ}$ and the manifold: above anything reached there is one more, and there is no top.*

## Height as an Ordinal-Process

What *indexes* the ascent? The storeys are numbered by the natural number series, but the *height* of the tower itself is not a number. The height is $\omega$, and $\omega$ in our foundation is given as the *limit of a process*: ordinals are processes, and $\omega$ is exactly “the limit of the process that numbers the storeys”[^7]. Thus the height of the tower *is itself an ordinal-process*, not a greatest value attained.

And this index *does not close*: the stream of heights is unbounded—beyond any bound there is a higher storey[^8]. By the dichotomy of the level analyzed in the foundation—*bounded means Element, unbounded means role-limit*—the closure of the tower lies on the role-limit side: it is reachable only as a process, and never as a completed storey-Element.

*The height of the tower is the ordinal-process $\omega$, not a number; its closure is a role-limit, not an object.* Here one sees what distinguishes “the hierarchy as a process” from the classical “hierarchy as an object”: the index of the ascent is itself processual.

## E/R/R Analysis: The Tower as a System

The tower of role-types is itself a *system* in the sense of ToS, and it should be analyzed by E/R/R. Epistemically we went from below—from the storeys to the rule of ascent; ontologically the structure is generated in the reverse, generating order: Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *rule of ascent*: the next storey is the space of predicates (a role-type) over the previous one, and the diagonal *forces* strict growth (no storey enumerates the next). Adjoining it is the rule of indexing: the height is taken as the *limit of a process* ($\omega$), not as a completed supremum. The rule stands one level above the storeys and generates them one after another.

**Roles (L4).** Each storey is a *role-type over the previous one*—a role assigned by the rule of ascent, not a pre-existing set. The height plays the role of an *ordinal-process*. The diagonal predicate plays the role of the *witness of the ascent*: it is what shows that the role of the next storey does not reduce to the roles of the lower one. The positions are grounded by structure: a “storey” is defined not by its nature but by its relation to the rule—by being the space of decisions over the one below.

**Elements (L1 + P4).** The bearers are finite stages: the points of the storeys, each of which is finitely constructible and is a process-thread (a predicate that answers “yes/no” on request). Actualization under P4 is *finite*: what is actual are the stages and storeys reached by a finite construction; the $\omega$-closure of the tower is *not* actualized as a storey-Element—it is a role-limit. This is what gives the whole tower its processual character.

**Well-formedness check.** Each component falls into exactly one category: the rule of ascent is a Rule, the storey and the height are Roles, the point-stages are Elements; none is assigned to two at once. Self-application, which P1 rules out, does not arise: the rule of ascent stands one level above the storeys and is not one of them—the tower does not contain itself as a storey.

{
**What the analysis yields.** First, it shows that the question “how large is the hierarchy?” is a confusion of categories: it demands that the process-ascent be a completed Element-object, whereas the hierarchy *is* a process. The correct question is a different one—*how far one can provably climb*; and it is answered rung by rung by the following chapters, not by one completed “all.” Second, the analysis explains why the ascent is constructive: the rule, the storeys, and the height are built without appeal to a completed object, and the demand for completed infinity—if it arises at all—concerns only the *completed* limit, not the ascent itself (Chapter 2 will show that this demand, too, is itself graded).}

{
Thus the line begun by number-as-process (Part III) and the principle P4 (Part IV), and continued by the tower $\overline{ℚ}$ (Part XI) and the manifold-process (Part XII), arrives at the hierarchy: *the role-limit side is an ascending ordinal-process, generative and uncompletable*. In the next chapter we will see that this ascent is also *graded by depth*—that the question on each storey requires a precisely determined measure of “completed infinity,” and that this gradation is visible only under P4.}

---

[^1]: The coincidence of the finitization boundary with the boundary of constructivity is the subject of the final synthesis of the volume (Part XX); here it is used as an established background.
[^2]: The volume’s registry of “former walls” sums up the verdict: of the classical “high” constructions, the only object that P4 genuinely rules out is completed actual infinity itself; the rest is either reached as an operation-role or built as a process. The summary is machine-checked (0 axioms).
[^3]: The core of the chapter is the file `ProcessHierarchyCore`; all its statements are checked completely, with an empty list of axioms used (`Print Assumptions`: “Closed under the global context”). This is the Element side: the construction and the diagonal, without L3 and without the finite witness.
[^4]: Numbering the storeys from zero and starting $ℕ$ at zero in Rocq is a convention of the instrument, not an ontological statement; in substance the zeroth storey is the carrier $ℕ$.
[^5]: The statement “there is no surjection from storey $n$ onto storey $n+1$” is the theorem `cantor_level`, machine-checked, 0 axioms. It generalizes the diagonal of uncountability (`cantor_bool_seq`) from one tier to *every* tier.
[^6]: The theorem `no_maximal_level`, machine-checked, 0 axioms.
[^7]: The height of the tower coincides with $\omega$, given as the limit of the process of indices (`tower_height_is_limit_process`); ordinals are formalized as processes—a limit ordinal is the limit of a sequence-process, not a completed number. Machine-checked, 0 axioms.
[^8]: `tower_height_unbounded`: the height, as a monotone stream, exceeds any bound given in advance. 0 axioms.

---

Part: [[18 Process Hierarchy|Part XVIII. The Process Hierarchy]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/07 Uncertainty Principle in Information|Chapter 7. The Uncertainty Principle in Information—Part XVII]] · [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/02 Depth Equals Rung of Omniscience|Chapter 2. Depth = Rung of Omniscience]] →
