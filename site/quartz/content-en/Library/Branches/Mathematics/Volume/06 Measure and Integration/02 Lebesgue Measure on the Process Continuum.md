---
title: "Chapter 2. Lebesgue Measure on the Process Continuum"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/02 Мера Лебега на процессном континууме.md"
sourceBlob: 6070969cda2e6d27b4efd207a4f79ae5404db5ce
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From the Rule to the Continuum

Chapter 6.1 introduced measure as a *rule of assignment*: $\mu(A)=I(\chi_A)$, the integral of the indicator. On intervals this rule gives the exact measure $\mu([c,d])=d-c$ without any passage to the limit; nonnegativity, finite additivity, and monotonicity are its consequences, and countable additivity is the convergence of the process of partial sums. The present chapter extends this rule to the *process continuum* itself—to unions of intervals and to sets given by processes—and brings two reference sets to measure zero: the rational points of an interval and the Cantor set. At the end we analyze the most sensitive question of Part VI: *what is lost without the Axiom of Choice and why this is not a loss.*

### What the Chapter Proves and What It Leaves as a Program

Let us hold to the three levels of rigor introduced in [[Library/Branches/Mathematics/Volume/06 Measure and Integration/01 Measure as a Process of Assignment#Where the Chapter Stands|§ 1.1 “Where the Chapter Stands”]]. *Proved without axioms*: the measure of an interval and its invariance under translation and scaling; measure zero for the rational points of an interval and for the Cantor set, as the convergence of a covering process to zero. *Proved at an explicit price* (L3): countable additivity as the convergence of partial sums (Chapter 6.1). *Remains a program or a classical comparison*: outer measure and Carathéodory measurability (in our order they are neither built nor needed), measure on the whole process continuum as a completed object, and the impossibility of the Vitali set (this is not a theorem of the system but a diagnosis of the absence of a bearer).

*The spine of the exposition here deliberately diverges from the textbook: we do not build a $\sigma$-algebra and an outer measure but extend the rule $\mu=I(\chi)$ directly.*

The title of the chapter designates the *direction* of the extension: what is formally proved here is the measure of an interval, null covers, and the process rules of accumulation, not a completed measure on the totality of all subsets of the continuum.

### The E/R/R Framework of the Chapter

We set out the framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter extends the system of measure to the process continuum.

**Rules ($\leftrightarrow$ L5).** On top of $\mu=I(\chi)$ (Chapter 6.1): invariance under translation and scaling; the rule “countable $\Rightarrow$ zero”; accumulation for unions. The P4 layer admits no completed totalities—hence the Vitali set has no bearer.

**Roles ($\leftrightarrow$ L4).** “Measure zero” is the role-limit of a covering process; “measurable” is the role of a distinguishable set; “measure on the continuum” is the role-limit of the extension over $[-N,N]$; “the Vitali set” is a role without a bearer.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Measures of intervals $d-c$, cover lengths $(1/2)^n$, $(2/3)^n$, partial sums; the completed union and the whole line lie outside the elements.

## The Interval and Its Invariance

The point of support is the measure of an interval. It depends *only on the width*, not on the position: a translation of the interval along the continuum does not change the measure, and a dilation changes it proportionally. Both invariances are proved as exact identities over ℚ.[^1]

*The measure of an interval is not a marking of position but the width of a process of distinction: where the interval stands is indifferent to the measure.*

This already has content. Translation invariance is the very property that in classical theory serves as the *defining* one for Lebesgue measure (the unique translation-invariant measure on the line normalized by the unit interval). For us it is not postulated but *computed* from the fact that the integral of the indicator depends only on the width of the step. A degenerate interval—a single point—has measure zero: a rectangle of zero width. From this it is already visible that “measure zero” does not mean “empty”: measure and how populated a set is are different questions, and this fork will become the main one in § “Sets of Measure Zero: The Countable and the Cantor Set.”

## From Intervals to Unions

The next step is unions. For a *finite* collection of disjoint intervals the measure of the union is the sum of the measures; the base case of two adjacent intervals is proved, $\mu([a,b])+\mu([b,c])=\mu([a,c])$, and the general finite case is a natural repetition of this scheme.[^2]

For a *countable* collection the result of Chapter 6.1 works: the partial sums of measures $S_n=\sum_{k<n}\mu(A_k)$ increase monotonically when the terms are nonnegative, are bounded when the total mass is finite, and therefore form a convergent (Cauchy) process.[^3] The measure of a countable union is, in our reading, the *role-limit* of this process; the completed union $\bigsqcup_k A_k$ as a ready object is not built—it would remain an actual infinity, which P4 does not admit. The substantive part, the convergence of the accumulation of measure, is proved; it does not need the completed object.

## What Outer Measure Would Be—and Why It Is Not Here

At this point the textbook builds *outer measure*: it covers a set by countable collections of intervals and takes the infimum of the total lengths over all covers; then Carathéodory measurability selects the “good” sets by a condition on the splitting of any test set. This is a powerful apparatus—and in our order it is *not needed*.

The reason is simple: measurability for us is already defined differently—as distinguishability, that is, the approximability of the indicator by step functions—and measure as the integral of this indicator. Outer measure and Carathéodory are an alternative route to the same concept, not its foundation. Therefore in ToS they can be introduced as a *classical comparison*, but the spine of the exposition goes past them: *$\sigma$-algebras are not built, and the infimum over all covers is not taken as a completed object.* Here lies the relief that comes from renouncing the Axiom of Choice: a good half of the “fear without AC” concerned precisely the completed $\sigma$-algebra and the nonconstructive infimum, which simply do not arise here.[^4]

## Sets of Measure Zero: The Countable and the Cantor Set

Here the rule-measure shows its strength. A set has *measure zero* if it can be covered by intervals of arbitrarily small total length—more precisely, if the total length of the cover is a process converging to zero. In ToS this is the definition: not “the infimum equals zero” (a completed operation) but *the presence of a covering process converging to $0$*.

### The Rational Points of an Interval

The rational points of an interval, the set $ℚ\cap[c,d]$, are countable: they can be enumerated (Chapter 3.3, an explicit traversal). Then the $k$-th point is covered by an interval of geometrically decreasing length, and at stage $n$ the total length of the cover behaves like
$(1/2)^n$—a process converging to zero. Hence $ℚ\cap[c,d]$ has measure zero.[^5]

*A countable dense set can have measure zero: “densely arranged” and “large in measure” are different questions about the process.*

### The Cantor Set

This gap is seen even more sharply in the Cantor set. It is built by trisection: from an interval the middle third is removed, from each remainder again the middle third, and so on; at stage $n$ there remain $2^n$ intervals of length $3^{-n}$, of total length
$(2/3)^n$. This total length is a covering process converging to zero, so the Cantor set has measure zero.[^6] But the Cantor set, unlike the rational points, is *classically uncountable*: it has the cardinality of the continuum. In the present process line only its *measure zero* is proved; uncountability is taken as a classical and structural reading—through the binary branchings of the stages, in the spirit of the uncountability of processes (Chapter 4.4)—and no separate Rocq theorem on the cardinality of the Cantor set itself is used here.

**Uncountable—yet of measure zero.** This is not a paradox but a separation of two questions: *counting* asks how many distinguishable processes fit into a set, and *measure* asks what total width they occupy. The Cantor set is classically uncountable by the first question and *provably* null by the second. To mix them up is a category mistake, of the same nature as the other diagnoses of the volume.

The three sets build up the full picture: the rational points (countable, measure zero), the Cantor set (uncountable, measure zero), the whole interval (uncountable, measure $d-c$). *Cardinality and measure are independent*: neither determines the other; both are answers to different questions about the processes that populate the continuum.

## What Is Lost without the Axiom of Choice—and Why It Is Not a Loss

Classical measure theory knows sets to which measure *cannot* be assigned—the Vitali set—and paradoxical decompositions of the ball (Banach–Tarski) that double the volume. Both constructions rest on one and the same thing: on the *completed* collection of all subsets of the continuum and on the *external choice* of a representative from each equivalence class, that is, on the Axiom of Choice over a ready totality.

In our order neither of these exists as an ontological bearer. P4 does not actualize the completed collection of all subsets; the external choice of a representative from an uncountable family of classes is exactly the operation over completed infinity that ToS replaces with a constructive witness (L4: existence $\to$ presentation), and here there is nothing to present. Therefore the initial *conditions* of the constructions of Vitali and Banach–Tarski do not arise in this frame, and the constructions themselves are not objects of the present measure theory.

*This is not a separate metatheorem of impossibility but a diagnosis of the absence of the needed bearer: the paradoxical constructions are not ruled out by a special law—there is simply nothing for them to be assembled from.*

And this is not a loss. Everything substantive—the measure of intervals, invariance, measures zero, the convergence of accumulation, the convergence theorems (Chapter 6.4)—works without the Axiom of Choice. All that disappears is what was a postulate about a completed nonconstructive totality all along: exactly the layer that produced paradoxes, not theorems. Renouncing it does not impoverish measure theory; it purifies it.

## Measure on the Whole Process Continuum

There remains the question of measure on the *whole* continuum, not on a separate interval. Here ToS stays true to itself: “the whole line” is not a completed object, and therefore measure on it is not a function on a ready collection but a process. The measure of a set $A$ on the whole line is naturally read as the process of its measures on growing intervals $[-N,N]$: for each $N$ the quantity is finite and available, and “measure on the whole continuum” is the role-limit of this expanding process.

This remains a *program* in the same sense as the completed countable union: the finite approximations (the measure on $[-N,N]$) are provable, while the completed limit object is not actualized. In substance nothing is lost: any concrete question about measure concerns a bounded region and is decided at a finite stage $N$.

## E/R/R Analysis: Lebesgue Measure as a Rule on the Continuum

### Analysis in the Generating Order

The framework was set at the beginning of the chapter (§ “The E/R/R Framework of the Chapter”); here we unfold it with a table and a check of correctness. Let us analyze the extended system—Lebesgue measure on the process continuum—in terms of E/R/R, continuing the analysis of Chapter 6.1. The reservation about the level is the same as before: the “system of measure on the continuum” is a substantive interpretation of the construction, not an object literally declared in the code. We conduct the analysis in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules ($\leftrightarrow$ L5).** Besides the rule of assignment
$\mu=I(\chi)$ and its preservations (Chapter 6.1), on the continuum the following are added: invariance under translation and scaling (measure depends only on width); the rule “countable $\Rightarrow$ zero” (a set with a covering process converging to zero has measure zero); the rule of accumulation for unions (convergence of partial sums). The universal layer is the laws L1–L5 and P4, which admits no completed totalities; it is this layer, and not a special exclusion, that leaves Vitali and Banach–Tarski without bearers.

**Roles ($\leftrightarrow$ L4).** “Measure zero” is the role-limit of a covering process; “measurable on the continuum” is the role of a distinguishable set; “measure on the whole continuum” is the role-limit of the expanding process over $[-N,N]$. A *nonexistent* role is also essential: “the non-measurable Vitali set” finds no bearer—there is no element that would occupy it.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite
at every stage: measures of intervals $(d-c)$, cover lengths $(1/2)^n$ and $(2/3)^n$, partial sums, and measures on $[-N,N]$. Completed objects—an infinite union, the whole line, the collection of all subsets—do not belong to the elements.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| invariance; “countable $\Rightarrow$ zero”; accumulation of unions | HOW the rule-measure behaves on the continuum | Rules ($L5$) |
| measure zero; measurable; measure on $[-N,N]$; (the absent role of Vitali) | WHAT FOR the bearers are significant; which bearer is absent | Roles ($L4$) |
| $d-c$; $(1/2)^n$, $(2/3)^n$; partial sums | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### What the Analysis Yields

The capstone of the chapter is the diagnosis of “what is lost without AC.” Vitali and Banach–Tarski are *roles without a bearer*: the classical theory assigns them a place, but this place requires a bearer—the completed collection of all subsets and an external choice—and under P4 there is no such bearer. Hence their absence is not a gap in the theory: it is a direct structural consequence of the fact that the continuum in ToS is populated by *processes*, not by completed objects. The same diagnosis has guided the whole volume: to take a role (measure zero, measurability, uncountability) for an object is a confusion of categories; to populate the continuum with completed subsets instead of processes is the same confusion at the level of the whole of measure theory.

The positive part is exactly the one that is proved: the measure of an interval and its invariance, measure zero for the countable and the Cantor sets as convergent processes, and the accumulation of measure for unions. This is enough to pass on to functions: the next chapter introduces measurable functions and the Lebesgue integral as a process, relying on the same step foundation, and brings the notion of “almost everywhere” to classes that echo the point-class of Chapter 4.3.

---

[^1]: `measure_translation`: $\mu([a,a+w])=\mu([b,b+w])$ (the measure depends only on the width $w$); `measure_scale`: $\mu([0,k])=k$. Plus `measure_point_zero` (a degenerate interval has measure zero). All in `LebesgueMeasure.v`, 0 axioms.
[^2]: `measure_additive` in `LebesgueMeasure.v` (the case of two adjacent intervals); the process analogue is `q_measure_additive` in `ProcessMeasureTheory.v`.
[^3]: `sigma_additive_converges` (`ProcessSigmaAdditive.v`), price: L3. More in [[Library/Branches/Mathematics/Volume/06 Measure and Integration/01 Measure as a Process of Assignment#Countable Additivity as Convergence of a Process|§ 1.4 “Countable Additivity as Convergence of a Process”]] of Chapter 6.1.
[^4]: The infimum over *all* covers is a completed operation over an infinite collection; in the process reading it is replaced by a concrete covering process with an explicit decreasing estimate (see § “Sets of Measure Zero: The Countable and the Cantor Set”), not by taking an exact bound over a ready totality.
[^5]: Proved: the covering process $(1/2)^n$ converges to zero as a process, `rationals_cover_to_zero` (`ProcessRationalsNull.v`, 0 axioms). It is precisely countability (the enumeration from Chapter 3.3) that makes the total budget of the cover summable.
[^6]: Proved: the covering process $(2/3)^n$ converges to zero, `cantor_measure_zero` (`ProcessCantorMeasure.v`, 0 axioms).

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[01 Measure as a Process of Assignment|Chapter 1. Measure as a Process of Assignment]] · [[03 Measurable Functions and the Lebesgue Integral|Chapter 3. Measurable Functions and the Lebesgue Integral]] →
