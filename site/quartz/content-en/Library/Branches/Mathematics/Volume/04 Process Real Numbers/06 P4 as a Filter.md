---
title: "Chapter 6. P4 as a Filter"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/04 Процессные действительные числа/06 P4 как фильтр.md"
sourceBlob: 729ea926eae15f3460486b514cf198051fd8ebb5
translated: 2026-10-20
status: draft
---

## What the Chapter Needs a Filter For

### Five Recastings and a Step Back

Part IV has gone through five recastings. Infinity became a process
rather than a ready set (Chapter 4.1). The real number became a process
of rational approximations rather than a point-atom (Chapter 4.2). The
point became a class of equivalent processes rather than a primary
givenness (Chapter 4.3). Uncountability became the impossibility for a
regular enumeration to cover all classes rather than a property of a
completed set (Chapter 4.4). The continuum became a structural dichotomy
of closed collections rather than an uncountable set or a measure of
cardinality (Chapter 4.5).

Each time, one and the same movement: from a completed object to a
process, from a ready collection to a structure, from a measure of
magnitude to a type of structure. Part IV carried out this movement
through machine-checked junctures and honestly marked conceptual
transitions. But behind it another, less visible movement was going on
all the time—and now, in the last chapter of the part, it is worth
making it explicit.

In all the chapters of the volume—not only those of Part IV—a
*reservation about precision* accompanied the construction.
Proved—but proved in such-and-such a sense. Rests on such-and-such an
axiom. This formulation is a substantive interpretation, not a machine
theorem. This result is the author’s thesis, not a consequence of the
code. The volume kept a double record: what is built—and what the
*strength* of what is built is. The present chapter takes a step back
and names the discipline to which this second record was subject.

### Summary of Part IV

Before naming the discipline, let us survey the whole course of
Part IV—for it is precisely its material that the chapter will
classify.

The part began with an alarm: if $P4$ is accepted—if infinity is only a
property of a process and there are no completed infinite objects—will
not the classical analysis of the real number collapse together with
them? Five chapters answered this alarm, and the answer took shape as
follows. $P4$ does *not* destroy the basic structures of analysis; it
changes their *carrier*. Infinity ceases to be a ready set and becomes a
process, never completed but finite at every moment (Chapter 4.1). The
real number ceases to be a point and becomes a process of rational
approximations (Chapter 4.2). The point ceases to be primary and becomes
a class of equivalent processes (Chapter 4.3). Uncountability ceases to
be a property of a completed set and becomes the impossibility for a
process enumeration to cover all classes (Chapter 4.4). The continuum
ceases to be an uncountable set and becomes a structural dichotomy
(Chapter 4.5).

The classical result is not lost in this—it is *translated*: it
receives a process carrier and in the new form is proved by machine,
without completed infinities. Part IV did not preserve the whole of
classical analysis as a single whole—it did not set itself such a task;
it showed on key results *how* $P4$ rebuilds the basic structures on
process carriers, and that this rebuilding is possible, rigorous, and
checkable.

### $P4$ as a Filter: The Central Thesis

The discipline in question can be named in a single formula. Up to now
$P4$ has appeared as an ontological principle: infinity is a property of
a process. But it also has a second, methodological role.

*$P4$ is not a machine that turns every successful interpretation into a
proved result. $P4$ is a **filter**: it distinguishes the forced, the
natural, the chosen, the compatible, and the external. Therefore a
mature theory must not only build objects but also classify the
strength of the connection of each construction with the original
principles.*

This second role is the subject of the chapter. The filter adds no new
objects to the volume; it brings order into what has already been
built—separating what *follows* from the starting points from what is
merely *compatible* with them, what is *chosen* among possibilities,
what is *accepted* from outside, and what *remains open*. Without such a
filter, a theory rich in constructions imperceptibly slides into
overstatement: every successful model begins to sound like a proved
truth. The filter stops this sliding.

### The Plan of the Chapter

The chapter is arranged as follows. First, the two scales of strength by
which ToS assesses its results: the scale of *derivation strength*
(§ 6.2) and the scale of *IF-conditions* (§ 6.3). Then an analysis of
the filter itself as an E/R/R system (§ 6.4). Then the application of
the filter to the *mathematical* corpus of the volume (§ 6.5): what in it
is proved, what is accepted, what is chosen. Then the two sides of the
filter: what $P4$ *cuts off* (§ 6.6) and what it *keeps* (§ 6.7). Then
an honest catalog of what is *open* (§ 6.8). And finally, the summary of
Part IV and the place of the volume in the landscape of foundations
(§ 6.9).

## Derivation Strength: Five Grades

### What a Scale Is For

To say of a result “it is proved” is not enough—one must say *to what
extent* it is connected with the original starting points. One thing is
a statement that follows from $P1$–$P4$ by pure algebra, without a
single choice. Another is a statement true *under* some additional
assumption. A third is a statement merely *compatible* with the starting
points but not forced by them. These cases must not be conflated, and
ToS distinguishes them by a formal scale.

### Five Grades

The scale is introduced in the Rocq repository by the type
`DerivationStrength` with five values.[^1] Here they are, from the
strongest to the weakest:

| Grade | What it means |
|---|---|
| `FullyDerived` | follows from $P1$–$P4$ alone, without choices |
| `DerivedWithInput` | derived given an input parameter |
| `Constrained` | the starting points narrow it to a finite number of possibilities |
| `ConsistentWith` | compatible with the starting points but not forced by them |
| `ExternalInput` | postulated, not derived |

Precision is needed here about the *material* of the scale. In the file
itself this scale is applied first of all to the results of the *future
physical layer*—not to the mathematics of the present volume. The file
classifies physical results: some are marked `FullyDerived` (three of
them, by its count), others `DerivedWithInput` (two), `Constrained`
(two), `ConsistentWith` (one); in total, eight classified results (the
theorem `total_classified`). These results themselves are the subject of
physics; what matters here is *the scale itself*, which we will
take as an instrument, not their nature.

### A Documented Meta-Audit, Not a Scanner

The status of this file must be stated plainly, so that no false
impression arises. `ProcessAxiomAudit.v` is *not* an automatic
dependency crawler that itself scans the repository and labels each
theorem. It is a *documented* meta-audit: the strength labeling was
entered by the author on the basis of the results of the command
`Print Assumptions`, run separately for each theorem. The file *records*
the conclusion of this audit as a set of definitions and checkable
lemmas (for example, `fully_derived_strongest`), but by itself it
*scans* nothing.

The file carries the same reservation about the *axiom price*. Its
theorem `axiom_minimal` asserts in substance: the key results depend
only on `classic`—that is, on $L3$, the law of excluded middle—while the
law of sufficient reason `L4_witness` is localized and appears only in
individual files (the lemma `l4_witness_localized`). The axioms of
choice, infinity, univalence, and functional extensionality are not
used. This is a *documented* statement about the audit, based on
`Print Assumptions`, not a machine check of the whole repository by a
single command.

## IF-Conditions: Forced / Natural / Chosen

### The Second Scale

The scale of derivation strength answers the question “how closely is
the result connected with the starting points.” The second scale
refines the first from another side: it asks *what kind* of condition
stands *before* the result. This scale—the type `IFStrength`—is
introduced in a separate file[^2] and has three values: `Forced`
(follows from $P1$–$P4$ without choice), `Natural` (the simplest,
generic case, but not forced), and `Chosen` (a definite choice among
several possibilities).

### “Follows” versus “Is Compatible”

The distinction that the two scales draw together is the fundamental
distinction of a mature theory: between “$X$ *follows* from the starting
points” and “$X$ is *compatible* with the starting points.” The first
means: having accepted the starting points, one cannot reject $X$. The
second means only: $X$ can be accepted without falling into
contradiction with the starting points—but it can also be left
unaccepted. A theory that does not distinguish these two passes off
compatibility as derivability and thereby overstates its strength.

And here the file is honest in its *count*. Of the twelve derivations
analyzed in it, four turned out `Forced`, five `Natural`, three `Chosen`
(the lemmas `derivation_count_forced`, `derivation_count_natural`,
`derivation_count_chosen`). *Not everything is derived*—and this is said
plainly, with a number.

### “Not Everything Is Derived” as Honesty

The acknowledgment that only a third of the derivations are `Forced`,
and the rest `Natural` or `Chosen`, is the *maturity* of the theory, not
its weakness. A theory in which everything is `Forced` is either trivial
or dishonest: it either asserts nothing substantive or passes off its
choices as necessities. The strength of a theory lies in knowing exactly
and naming plainly what is forced, what is natural, and what is
chosen—not in declaring everything forced. The two scales of ToS serve
precisely this knowledge.

## E/R/R Analysis: The Derivation Filter as a System

### The Filter in Three Layers

Before applying the filter, let us analyze the filter itself by E/R/R
(Part I): the apparatus of strength assessment is itself a system, and
it is useful to see its arrangement. The headers of the supporting files
give the labeling directly: *elements—results and their
classifications; roles—meta-level significance, honest assessment;
rules—classify every result by strength*.[^3] We conduct the analysis in the ontological
order Rules $\to$ Roles $\to$ Elements.

*Rules.* The constitution of the filter system is two rules of
classification: the scale of derivation strength (`DerivationStrength`,
§ 6.2) and the scale of IF-conditions (`IFStrength`, § 6.3). Added to
them is the rule of honest accounting: the status of each result is
determined by an audit of its dependencies (`Print Assumptions`,
documented), not by wishes.

*Roles.* The roles are the *strength statuses* themselves:
`FullyDerived`, `DerivedWithInput`, `Constrained`, `ConsistentWith`,
`ExternalInput` on one scale; `Forced`, `Natural`, `Chosen` on the
other. Each result occupies a place in this grid of statuses, and this
place is its role in the system of knowledge: not “what is proved” but
“with what strength it is connected with the starting points.”

*Elements.* The elements are the results of the volume themselves
(theorems, constructions, interpretations), which the filter distributes
among the statuses. By $L1$ each result is identical to itself; by $P4$
their finite, existing list—what has already been built—is the material
of the classification.

### Well-Formedness and Diagnostics

*Well-formedness.* The labeling is unambiguous: the results are
elements, the strength statuses are roles, the two scales are rules.
The principle $P1$ (no self-membership) is observed: the filter
classifies *results*, not itself; the scale is not one of its own
results. And here the analysis turns into *diagnostics*—the very
diagnostics for which the filter is needed. To confuse the role
`ConsistentWith` with the role `FullyDerived`—to read “compatible” as
“derived”—is a confusion of categories: an element is ascribed someone
else’s, higher role. This is exactly the overstatement that the filter
catches. The maturity of a theory is measured by the *precision* of the
labeling, not by the number of `FullyDerived` results.

## The Filter on the Mathematics of the Volume

### An Author’s Retrospective, Not a Coq Table

In the meta-files themselves the scales are applied first of all to the
results of the future physical layer. In this chapter we use the same
scales as a *retrospective instrument* for the mathematical corpus of
the volume. This is the *author’s* classification of results already
proved, not a separate Coq table automatically labeling Parts II–IV.
The repository has no file that would list the mathematical theorems of
the volume with their strength statuses; the labeling below was derived
by the author from the chapters themselves and from their axiom price,
checkable by the command `Print Assumptions`.

### Two Independent Axes

The labeling is best carried out along *two* axes, for they are
connected but do not coincide. The first axis is the *axiom price*: how
many and which logical axioms stand behind the result (zero; one, $L3$;
two, $L3$ and $L4$). The second axis is the *type of inferential
strength*: whether the result is forced by the starting points or is a
choice of representation. A low axiom price is not the same as full
derivability: a result can be constructive (zero axioms) and at the same
time rest on a *choice* of model; and vice versa. A zero axiom price
speaks of the *purity* of the proof within the chosen formalization;
`FullyDerived` speaks of the *strength* of the connection of the result
with the starting points. These are different judgments.

### A Slice of the Mathematical Results

Let us apply both axes to the key results of Parts II–IV.

| Status | Mathematical results of the volume |
|---|---|
| 0 axioms, constructively | the countability of $ℚ^{+}$ via the Calkin–Wilf tree (Chapter III.3, `Countability_Q.v`); the irrationality of $\sqrt{2}$ constructively, without $L3$ (Chapter III.4, `Sqrt2Irrational.v`); the basic process constructions `RealProcess`/`is_Cauchy`/`process_equiv` (`ProcessCore.v`) |
| $L3$ (classic) | the uncountability of processes of the unit interval relative to regular enumerations (Chapter 4.4) |
| $L3 + L4$ | the Cantor–Bendixson dichotomy for closed collections of binary processes (Chapter 4.5; $L4$ in the countable union) |
| Choice of model or representation | the binary model $2^{ℕ}$ versus the Cauchy model (Chapter 4.5); the choice of a class representative, the registration of the unit (Chapter II.1), the encoding format |

This slice is honest in both directions. On the one hand, the core of
the volume stands *cheaply* and *firmly*: the countability of the
rationals and the irrationality of $\sqrt{2}$ cost not a single axiom
and are proved constructively; so is process arithmetic. On the other
hand, two central results of Part IV rest on logical
axioms—uncountability on $L3$, the dichotomy on $L3$ and $L4$—and this
must be named, not hidden. And finally, a number of forks are a
*choice*, not a derivation: which model of the continuum, which
representative of a class, from which number to count—here ToS chooses
deliberately, and this choice is the role `Chosen`, not `Forced`.

## What $P4$ Cuts Off

### Completed Infinity as the Primary Carrier

The main thing that $P4$ cuts off is *completed infinity* as the
original ontological carrier. It cuts off the *postulate* of a ready
infinite set as an actual object given all at once—not the axiom of
infinity as an entry in the Rocq language (the type `nat` and function
types are legitimate types of the language, § 4.1). Where the classics
take the completed number line, the completed set of all naturals, the
uncountable set of points—there $P4$ does not admit the original object
and requires a process. Part IV carried out this cutting off
retrospectively on five examples (§ 6.1): each time a completed object
was replaced by a process carrier.

### Impredicative Completed-Set Constructions—as Carriers

One must be more careful with impredicativity. It would be wrong to say
that $P4$ “cuts off impredicativity in general”: the logical level
Prop in Rocq itself carries impredicative features, and many files of
the volume work at this level (the perfect kernel of § 4.5 is a
Prop-valued witness). $P4$ does not rule out Prop as a logical level.
What $P4$ cuts off is the turning of impredicatively given collections
into *primary ontological objects* of analysis: defining a real number
or the continuum through a collection that quantifies over itself as a
ready object. The logical instrument Prop remains; only its ontological
translation into a completed carrier-object is ruled out.

### The External Axiom of Choice—but Not the Law of Witnessing

And separately—about the Axiom of Choice, for here it is easiest to say
too much. $P4$ does not use the external set-theoretic *Axiom of
Choice* as an ontological principle of building objects: in the process
ontology there is no act of simultaneous choice over a completed family
of sets. But it would be inexact to say “there is no choice at all.”
ToS has $L4$—the law of sufficient reason, `L4_witness` in the
formalization—and it performs work *resembling* choice, but at the
level of witnesses: from a proof of existence it extracts a concrete
witness. In Chapter 4.5 this law works directly—in the countable union
of enumerable families (`countable_union_enum`) it extracts for each
class its enumerator. Therefore the correct formula is not “there is no
choice” but this: *there is no external ZFC axiom of choice; there is a
local law of witnessing, $L4$, within ToS*—choice-like in technical
strength, but not set-theoretic in substance.

## What $P4$ Keeps

### A Retrospective Table of What Has Been Built

Cutting off is matched by preserving. And here it is important to
name directly *what has been built or justified over five chapters* on
process carriers, rather than repeat the discussion of Chapter 4.1 about
*why* $P4$ admits this or that. Let us gather this into a table of the
process forms built or justified in Chapters 4.1–4.5.

| Classical subject | What $P4$ keeps (process form) |
|---|---|
| infinity | a process of generation, never completed, finite at every moment |
| real number | a Cauchy process—`RealProcess`, a convergent sequence of rational approximations |
| point | a setoid class of equivalent representatives (by `process_equiv`) |
| uncountability | the impossibility for a regular traversal to cover all classes |
| continuum | the dichotomy of closed binary collections (enumerable or perfect) |

This is the answer to the original alarm of Part IV. Analysis is not
lost—it has received a process corpus: number, point, limit,
derivative, integral, uncountability, continuum—all this is in the
volume, but with a process carrier instead of a completed one. $P4$
keeps mathematics; it only changes *what* it is made *of*.

## What Remains Open

### A Working Map, Not a Repository File

The maturity of a theory is visible also in its naming plainly what has
*not been done*. Below is the working numbering of a backlog of
$F$-tasks. These are *not* names of Coq theorems and not a repository
file: this is a map of open formalization tasks, derived from the
previous chapters of the volume and compiled by the author. (The code of
the $P4$ program has its own catalog of what is open—the file
`ProcessOpenQuestions.v`, “what remains”; but its items are physical,
and its own honest final assessment is given for the physical layer.
Here, by contrast, the subject is the mathematical tasks of the present
volume.)

### Open Problems of the Mathematics of the Volume

The main open problems are these.

*The quotient type of points is not built* ($F$-10). The point rests on
the setoid reading—a class by `process_equiv`; a genuine quotient type,
in which equivalent processes are one term, does not exist in the
repository. Both the metric and the topology on classes stand on it.

*A full enumeration of $ℚ$* ($F$-17). The Calkin–Wilf tree enumerates
only the *positive* rationals; a full bijection $ℕ\leftrightarrowℚ$
with sign and zero is a standard extension not secured by a theorem.

*A bridge between the models* ($F$-19). The reals as Cauchy processes
(Chapters 4.2–4.4) and the continuum as $2^{ℕ}$ (Chapter 4.5) live in
*different* models; a full translation between them—$2^{ℕ}\leftrightarrow
[0,1]$—does not exist in the code: only the direct `bin_to_real` is formalized (Chapter 4.5).

*The derivation $L1\wedge L5\Rightarrow P4$* ($F$-18). The derivation of
the principle $P4$ itself from the laws is carried out in the volume *in
substance*, not by machine: in the code $P4$ stands as an independent
predicate, without a formal chain from the laws.

This catalog is a map of the way, not an admission of failure. Each
problem is named because it *can* be named exactly: it follows from what
has already been built and awaits formalization.

## Summary of Part IV and the Place of the Volume

### Where the Filter Goes Next

The filter, analyzed on the mathematics of the volume, does not end with
it. Its most substantive applications lie ahead, in the physical layer,
from which both scales are taken (§ 6.2–6.3). It is there that the
filter distinguishes what is *derived* from the principles, what is
*compatible* with them, what is *chosen* as a parameter, and what is
merely *postulated*. The examples of those files—the quantities and
relations of physics—lie beyond the volume; what matters
here is that the *discipline* of the filter has already been worked out
and tested on mathematics before being applied to more contentious
material.

### The Place of the Volume in the Landscape of Foundations

And the last point. The present volume is not yet another axiomatics competing
with set theory for the right to be the foundation. It is a *recasting
of the carrier*: the same mathematics—number, point, limit,
continuum—but on a process instead of a completed set, with an
explicitly labeled axiom price—first of all $L3$ and, locally,
$L4$—instead of an implicit set-theoretic background, and with an
honest labeling of the strength of each result. ToS does not argue with
standard mathematics about theorems; it offers a different *reading* of
what mathematics is made of—and the filter $P4$ is what keeps this
reading from overstatement.

*The summary of the chapter comes in three parts. First: what has been
done. $P4$ has been read not only as the ontological principle of
processes but also as a filter of the admissible strength of a
statement—one that distinguishes the forced, the natural, the chosen,
the compatible, and the external; this filter has been applied
retrospectively to the mathematics of the volume. Second: what it rests
on. The two scales—`DerivationStrength` and `IFStrength`—are introduced
in the code on physical material; here they are taken as an instrument,
and the labeling of the mathematics of the volume is the author’s own,
based on `Print Assumptions`, not a separate Coq table. The core of the
volume stands on zero axioms, the two results of Part IV on $L3$ and on
$L3+L4$; there is no external axiom of choice, but there is the
choice-like law of witnessing $L4$. Third: what remains open. The
quotient type of points, a full enumeration of $ℚ$, a bridge between
the models, a machine derivation of $P4$ from the laws—a working map,
not proved theorems. With this Part IV comes to an end: by showing how
$P4$ rebuilds analysis on process carriers—and by an honest labeling of
the strength of each step—rather than by preserving the whole of
analysis at once.*

---

[^1]: The type `DerivationStrength` and its applications are in the file `ProcessAxiomAudit.v` of the ToS Rocq repository (directory `src/process/`).
[^2]: `ProcessDerivedVsConsistent.v` of the ToS Rocq repository; the type `IFStrength`, the record `DerivationRecord`, the list `all_derivations`.
[^3]: The E/R/R labeling in the headers of `ProcessAxiomAudit.v` and `ProcessDerivedVsConsistent.v`.

---

Part: [[04 Process Real Numbers|Part IV. Process Real Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/05 Process Continuum|Chapter 5. The Process Continuum]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/01 Metric on Processes|Chapter 1. Metric on Processes—Part V]] →
