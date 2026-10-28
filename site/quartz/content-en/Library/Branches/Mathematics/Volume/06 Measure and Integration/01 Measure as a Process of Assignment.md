---
title: "Chapter 1. Measure as a Process of Assignment"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/01 Мера как процесс приписывания.md"
sourceBlob: edb98d7d8c52ce5965b65179fdd7c3abe54ee4c2
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part VI

Part V carried one-dimensional analysis on processes through to the end: the metric, topology and compactness, continuity, the derivative as a process of refining the slope, the integral as a process of accumulation, and the fundamental theorem that linked them, and then the first law of multidimensional integration, Fubini’s theorem. Everywhere the same device is at work: what classical analysis takes as a *completed object* (a limit, an area, a measure), ToS takes as a *process*, one that can be carried to any required precision but is never declared ready.

Part VI applies this device to measure and Lebesgue integration—and applies it at the most sensitive place. It is precisely here that classical theory traditionally relies on the Axiom of Choice: on it stand the non-measurable Vitali sets, the Banach–Tarski paradox, and the existence of a “sufficient” dominating function in the convergence theorems. The question of Part VI is direct: *what remains of measure theory if there is no Axiom of Choice?* The answer, which we will unfold chapter by chapter, is that everything substantive remains, and all that disappears is what was never a construction to begin with, only a postulate about a completed nonconstructive totality.

### What This Chapter Claims—and What It Does Not

Honesty from the very start. The present chapter does *not* build a general $\sigma$-algebra of measurable sets and does *not* prove the theorem on extending a measure from an algebra to a $\sigma$-algebra: neither is present in our construction, and, as will become clear, neither is needed. What is proved here is different, more modest in appearance but firmer in its ground: the measure of an interval is the integral of its indicator; the nonnegativity, finite additivity, and monotonicity of measure are *consequences* of this construction rather than axioms imposed on measure; countable additivity is a statement about the *convergence of the process* of partial sums of measures, and in this reading it is proved.[^1]

The boundary runs exactly along the line of P4. The finite and process core is proved *without a single axiom*; the step at which a monotone bounded process is declared *convergent* relies on the Law of Excluded Middle (L3); and the *completed* countable union as a ready object is something ToS does not actualize at all. This is not a gap in the exposition but a position: *measure is a process of assignment, not a function on a completed set.* This sentence is what the chapter unfolds.

To keep these boundaries in view, we distinguish three levels of rigor. The *first* is the exact measure of intervals through the step integral: here everything is proved without axioms. The *second* is the process *readings* of measure and $\sigma$-additivity (measure as a sup-process, convergence of partial sums): exactly these process statements are proved, at an explicitly named price (L3). The *third* is general Lebesgue measure on all measurable sets as a completed formal object—a substantive interpretation and the direction of the next layer, not an already built theory. The chapter treats the first two levels as proved and the third as an honestly marked program.

### The E/R/R Framework of the Chapter

We set out the framework of the system in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis with a table and a check of correctness is in § “Analysis in the Generating Order.” The chapter introduces the system of measure.

**Rules ($\leftrightarrow$ L5).** Measure is the integral of the indicator,
$\mu(A)=I(\chi_A)$; nonnegativity, finite additivity, monotonicity, and countable additivity (a monotone bounded process converges).

**Roles ($\leftrightarrow$ L4).** “Measurable” is the role of a distinguishable set; “measure” is the role of the assigned value; the limit $\mu(\bigsqcup_k A_k)$ is the role-limit of the process of accumulation.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational measures
$\mu(A_k)$, step indicators, partial sums $S_n$; completed infinity lies outside the elements (P4).

## Measure from the Integral, Not from a $\sigma$-Algebra

### Reversing the Textbook Order

The textbook introduces measure first: a $\sigma$-algebra $\Sigma$ of “measurable sets” is given, on it a function $\mu\colon \Sigma \to [0,\infty]$, and only then, on top of the measure, is the integral built. This order presupposes $\Sigma$ to be *given in advance*—a completed collection of all the sets to which a measure has already been assigned. It is precisely into this presupposition that the Axiom of Choice is built: to speak of sets to which a measure *cannot* be assigned (Vitali), one must first have a completed totality of all subsets from which such a set is “chosen.”

ToS goes the opposite way, following the Bishop–Cheng line: *first the integral, then measure from it.*[^2] The integral has already been built in Part V as a process of accumulation over ℚ. The measure of a set $A$ is defined as the integral of its *indicator*, the characteristic function $\chi_A$, equal to one on $A$ and zero outside it:

$$
\mu(A) \;=\; I(\chi_A).
$$

*Measure is not a marking of a set given in advance but a rule: integrate the indicator. The domain on which the rule works is itself outlined by a process, not given as a ready $\sigma$-algebra.*

### The Interval: Measure without a Limit

For an interval $[c,d]$ the indicator $\chi_{[c,d]}$ already *is* a step function—a step of height $1$ on $[c,d]$. Its integral requires no passage to the limit: it is the area of a rectangle with sides $1$ and $d-c$. Therefore

$$
\mu([c,d]) \;=\; I(\chi_{[c,d]}) \;=\; 1\cdot(d-c) \;=\; d-c,
$$

and this equality is proved as an exact identity over ℚ, without axioms.[^3] The length $d-c$ is not postulated here as the “measure of the interval” but *computed* from the integral; the agreement with the naive length is a result, not a definition.

### The Measurable Is the Distinguishable

What does “the set $A$ is measurable” mean in this order? Not “belongs to a $\sigma$-algebra given in advance,” but this: *its indicator is approximated by step functions*, that is, the boundary of $A$ can be outlined with arbitrary precision by finite rational data. This is exactly the sense of “distinguishability” that runs through the whole present volume: the measurable is what a process of finite approximations is able to *separate* from its complement.[^4]

*Measurability is not membership in a completed collection but a role that a set plays with respect to the process of approximation: being separable by finite data.*

Let us state the formal status. In the code this thesis is so far implemented at the basic interval/step level: the characteristic step functions of intervals and the measure of an interval are built. The general predicate “a set $A$ is measurable if and only if its indicator is approximated by step functions” for an arbitrary set is a substantive *reading* and the direction of the next layer, not a theory already fully built in this file.[^5]

From this one sees at once why in this order there is no place for a non-measurable set as an “exception”: Vitali non-measurability is not a property of some concretely presented set but a statement about the completed collection of all subsets, which ToS simply does not have. We will return to this in Chapter 6.2; here it matters only that the question “what if $A$ is non-measurable?” does not precede measure in our order but falls away together with the renunciation of completed totality.

## Nonnegativity and Finite Additivity

### Nonnegativity as a Consequence, Not an Axiom

In Carathéodory’s axiomatics nonnegativity $\mu(A)\ge 0$ is postulated—it is the first axiom of measure. In our order there is nothing to postulate: the indicator $\chi_A$ is nonnegative, the integral of a nonnegative step function is nonnegative, and hence $\mu(A)=I(\chi_A)\ge 0$ *by construction*.[^6] The same holds for the other “axioms of measure”: at the interval/step level the corresponding properties of measure turn out to be *theorems* about the construction.

*Structural nonnegativity*: the properties of measure are not imposed on it from outside by a list of axioms but are traced in the very rule of assignment.

### Finite Additivity, Monotonicity, the Point

For two *adjacent* intervals $[a,b]$ and $[b,c]$ the indicator of the union is the sum of the indicators, and the integral is additive—therefore their total measure equals $\mu([a,c])$. This is the *base case* of finite additivity; general additivity for an arbitrary list of disjoint intervals would be a natural extension of the same scheme.[^7] Monotonicity is just as transparent: if $A\subseteq B$, then $\chi_A\le\chi_B$ pointwise, and the integral preserves order, hence $\mu(A)\le\mu(B)$. Finally, the measure of a point is zero: the degenerate interval $[a,a]$ gives a rectangle of zero width.

In parallel, the process line contains an *infrastructure* of measure as a process: processes of indicators, the rational interval measure $q_measure=d-c$, outer covers, and predicates for sets of measure zero.[^8] This is not a single factored object “Lebesgue measure” in general form but a set of bridges that allow measure to be *read* as a process of approximation to a number, in the spirit of P4.

## Countable Additivity as Convergence of a Process

### Where Infinity Hides

Countable ($\sigma$-) additivity is the heart of measure theory: for a countable family of pairwise disjoint sets $A_1,A_2,A_3,…$

$$
\mu\Big(\bigsqcup_{k} A_k\Big) \;=\; \sum_{k} \mu(A_k).
$$

Here there are two completed infinities at once: the *completed* countable union $\bigsqcup_k A_k$ on the left and the *completed* sum of the series on the right. The classical theory takes both as ready objects. ToS takes neither as ready—and precisely for this reason can say something exact about $\sigma$-additivity instead of postulating it.

### The Accumulation of Measure as a Monotone Bounded Process

Let us read the equality as a statement about a *process of accumulation*. The partial sum

$$
S_n \;=\; \sum_{k<n} \mu(A_k)
$$

is the measure of the union of the first $n$ pieces, a finite quantity available at every stage. Since every $\mu(A_k)\ge 0$, the sequence $S_n$ *increases monotonically*.[^9] If all the $A_k$ lie in one bounded interval $[c,d]$ (as happens in practice), then their disjoint pieces taken together cover no more than $[c,d]$, and therefore $S_n\le d-c$ for all $n$: the process is *bounded*.

And a monotone bounded process over ℚ *converges*: it forms a Cauchy sequence.[^10] Thus the *provable core* of $\sigma$-additivity in our reading is a theorem: the process of partial sums of measures converges.

**$\sigma$-additivity is not an equality of two completed
infinities but the convergence of the process of partial sums of measures.** The limit that the classical theory writes as $\mu(\bigsqcup_k A_k)$ is a *role*, the value to which the process converges; reading it as the measure of the countable union is a substantive role of the process, not a built object of a completed union.

### The Honest Price

There is exactly one price, and it is named. The step “a monotone bounded process converges” is classical: it relies on the Law of Excluded Middle (L3) in the same sense in which the theorem on the monotone convergence of processes rests on it (`monotone_bounded_Cauchy` in the process arithmetic).[^11] The *completed* union $\bigsqcup_k A_k$ as a self-standing object, however, is something ToS does not build: it would remain an actual infinity, which P4 does not admit. But for the content of the theory it is not needed: everything that $\sigma$-additivity says is expressed by the convergence of the process $S_n$, and the convergence is proved.

## The Domain-Explicit Dominating Function—the Method of Part VI

There is a place where the Axiom of Choice enters measure theory more quietly than in Vitali, and therefore more dangerously: the convergence theorems. Their formulations again and again begin with the words “let there exist an integrable dominating function $g$ such that $|f_n|\le g$…”—and in the classical exposition this $g$ is often obtained nonconstructively, “by existence.”

ToS turns silent existence into an *explicit parameter*. The dominating function $g$ is not “some existing function” but a *given* function, presented by a hypothesis; the theorem speaks of a pair $(f_n, g)$, where $g$ is *shown* rather than summoned into existence.[^12] This is a direct application of P4 in the form “existence $\to$ witness” (L4): where the classical theory chooses a dominating function from a completed collection, ToS requires it to be *built and presented*.

*The domain-explicit dominating function is the recurring method of Part VI: whenever the classical theory silently chooses a controlling object, ToS makes it an explicit parameter of the construction.*

This device is not a reservation for the sake of purity; it is what makes the convergence theorems constructive without the Axiom of Choice. In Chapter 6.4 it carries the whole dominated convergence theorem: with $g$ as a parameter, what remains is the purely constructive estimate $| I(f_n)-I(f) |\le I(|f_n-f|)$ and the squeezing of the residual—and then the convergence of the integrals follows *without a single axiom*.[^13]

## Lebesgue Measure versus Jordan Content

It is useful to see in what way the constructed measure is stronger than a naive “volume.” Jordan content measures a set by finite covers of intervals: one takes a finite collection of intervals covering the set from outside and a finite collection inscribed inside, and checks whether the two estimates meet. This is a *finitely* additive measure, and no more.

The difference between it and Lebesgue measure is exactly one step: from *finite* accumulation to *countable*, that is, to the convergent process of § “Countable Additivity as Convergence of a Process.” And this step has content. Consider the rational points of an interval, the set $ℚ\cap[c,d]$. By Jordan it is *non-measurable*: from inside, not a single interval of positive length fits into it (between any two rationals there is an irrational process whose point the rationals do not fill), and from outside it cannot be covered by finitely many intervals of total length less than the whole length $d-c$. The inner and outer estimates do not meet—the Jordan content is undefined.

Lebesgue measure, in the process reading, gives $ℚ\cap[c,d]$ *zero*. The reason is precisely countability: the rationals can be enumerated (Chapter 3.3), and then the $k$-th point can be covered by an interval whose length decreases geometrically, so that the total length of the cover is a process converging to zero.[^14]

*Lebesgue is stronger than Jordan exactly where finite accumulation gives way to a convergent process. “Lebesgue measure beyond Jordan” is “process beyond the finite.”*

And here the price and the gain of renouncing completed totality are visible at once. The countable set $ℚ\cap[c,d]$ is “uncountably small” in measure, although “dense” in arrangement: measure and cardinality answer different questions about the process, and to confuse them is a category mistake. This is the same diagnosis that guided Part IV.

## E/R/R Analysis: Measure as a Rule

### Setup

Let us analyze the constructed system—measure on the process continuum—in terms of E/R/R. We state the reservation about the level at once: the “system of measure” here is a substantive *interpretation* of the construction (the integral of the indicator plus the process of accumulation), not an object literally declared in the code as `System`. The analysis is an ontological comprehension of the structure of the chapter and a reading of the author’s E/R/R headers of the supporting files,[^15] not an attribution of new formal claims to the code.

Recall the distinction adopted in the volume: the abbreviation E/R/R sets the *epistemic* order (Elements $\to$ Roles $\to$ Rules, from the observable to the deep), while the generating (*ontological*) order is the reverse: Rules $\to$ Roles $\to$ Elements. Epistemically the chapter went from observable quantities (lengths, sums) to laws; we conduct the analysis in the generating order.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the rule of assignment itself: *measure is the integral of the indicator*, $\mu(A)=I(\chi_A)$. Above it are the rules that sustain this assignment: structural nonnegativity, finite additivity, monotonicity with respect to inclusion, and, at the process level, the rule that a monotone bounded process of partial sums converges (countable additivity). The universal layer of these rules is the laws L1–L5 (in particular L3, which pays for convergence); the concrete layer is precisely the formula $\mu=I(\chi)$ and the domain-explicit dominating function.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. “Being measurable” is a role of a set: its indicator is distinguishable by finite approximations. “The measure of a set” is the role of the value that the rule assigns. “The limit $\mu(\bigsqcup_k A_k)$” is a role-limit occupied by the process of accumulation $S_n$. None of these roles is a ready object: they are *functions* in the system, places that elements occupy in relation to the rule.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The roles select bearers. The bearers here are finite at every stage: the rational values of the measures
$\mu(A_k)$, characteristic step functions, partial sums $S_n$. Under P4 no element is a completed infinity—only finite approximations are actual; the “value” of the system (the limit) is not actualized as an element; what is actualized is the process toward it.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $\mu(A)=I(\chi_A)$; additivity; “monotone-bounded converges” | HOW the assignment of measure and its preservation are organized | Rules ($L5$) |
| measurability (distinguishability); measure of a set; limit of accumulation | WHAT FOR the bearers are significant: places in the system | Roles ($L4$) |
| $\mu(A_k)\inℚ$; step $\chi$; partial sums $S_n$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the rule $\mu=I(\chi)$ does *not* take as its element “the collection of all measurable sets.” A completed $\sigma$-algebra does not exist as a bearer: the domain of the rule is outlined by distinguishability, stage by stage, and is not given as a ready totality. It is precisely the absence of such self-reference (measure as an element of its own domain) that explains why the initial conditions of the classical constructions of Vitali and Banach–Tarski do not arise within this frame: the *completed* totality of all subsets and the external choice of representatives. Therefore these constructions are not objects of the present measure theory. This is not a separate metatheorem of impossibility but a diagnosis of the absence of the needed bearer.

What the analysis yields. It translates the central sentence of the chapter into the language of structure: *measure is a Rule* (a process of assignment), *measurability is a Role* (distinguishability), and the numerical measures and partial sums are *Elements* (finite at every stage). To take measure as a “function on a completed set” is to put the never-completed domain of the Rule in the place of a ready Element-totality—a confusion of categories of the same kind as “number as an object” instead of the role-quantity (Part II), “a point as an object” instead of a class (Chapter 4.3), and “uncountability as a property of a set” instead of a rule about processes (Chapter 4.4). The loss of the Axiom of Choice does not impoverish the theory here: it only removes what was a postulate about a completed totality all along, leaving everything constructive untouched.

The next chapter applies this rule to the process continuum itself: it builds Lebesgue measure on intervals and their unions, brings the countable and the Cantor sets to measure zero, and clarifies *what exactly* is lost without the Axiom of Choice and *why* this is not a loss.

---

[^1]: The supporting files are `LebesgueMeasure.v` (directory `src/analysis/` of the ToS Rocq repository, 20 proved statements, 0 `Admitted`, 0 axioms) and `ProcessSigmaAdditive.v` (directory `src/process/`, 5 statements). The lemma names cited in the notes below come from them.
[^2]: The header of `LebesgueMeasure.v`: “measure is derived from integral,” “we COMPUTE integrals, then DEFINE measure”—a reversal of the standard order “measure $\to$ integral.”
[^3]: In the code the measure of an interval is *defined* as the integral of the indicator, and a separate lemma reduces it to $d-c$ in a single tactic step, `ring`. The corresponding statements are `measure_interval` and `measure_interval_eq`.
[^4]: The header of `LebesgueMeasure.v`: “measurability $=$ distinguishability: a set is measurable when its characteristic function is approximable by step functions. No sigma-algebras, no AC, no completed infinities.”
[^5]: `LebesgueMeasure.v` builds `characteristic_step`, `measure_interval`, and their properties; the formula “measurability $=$ distinguishability” is present there as the author’s programmatic thesis, not as a proved general predicate of measurability.
[^6]: The statement `measure_nonneg` in `LebesgueMeasure.v` (0 axioms).
[^7]: The proved lemma `measure_additive` gives the case of two adjacent intervals: $\mu([a,b])+\mu([b,c])=\mu([a,c])$. Also `measure_monotone` and `measure_point_zero` (the measure of the degenerate interval $[a,a]$ equals zero). All: 0 axioms.
[^8]: In `ProcessMeasureTheory.v`: `measure_process` (the process of an indicator), `q_measure_additive`, `q_measure_monotone`, the predicate of distinguishability at stage $n$ `measurable_at`, as well as outer estimates and predicates for sets of measure zero.
[^9]: The partial sum of measures is `partial_measure`; its monotonicity is `partial_measure_monotone`, and `partial_measure_le` gives the monotonicity of measure with respect to inclusion: more pieces, no less measure.
[^10]: This is exactly what is proved: for nonnegative $\mu(A_k)$ and a common bound on the partial sums, the process $S_n$ is a Cauchy process—the statement `sigma_additive_converges` (`ProcessSigmaAdditive.v`), which relies on `monotone_bounded_Cauchy` from the process arithmetic.
[^11]: In Rocq this is the axiom `classic`; `Print Assumptions` for `sigma_additive_converges` shows it and only it—no new axioms. This is the same dependence as for the monotone convergence theorem (Chapter 6.4).
[^12]: In the code domination is the predicate `dominated`, which takes the dominating function $g$ as an explicit argument: $\forall k x,\ |f_k(x)|\le g(x)$. This is the “domain-explicit dominating function.”
[^13]: The reduction of dominated convergence is `process_dct` (`ProcessDCT.v`), 0 axioms: the engine and the “envelope” dominating function are proved constructively, and the only nonconstructive step (the convergence of the residuals to zero) is moved out into an explicit input hypothesis.
[^14]: This is proved as a process statement: the total length of the cover at stage $n$ behaves like $(1/2)^n$ and converges to zero—`rationals_cover_to_zero` (`ProcessRationalsNull.v`, 0 axioms). The same device gives measure zero for the Cantor set as well—`cantor_measure_zero` (`ProcessCantorMeasure.v`). The full formalization of this passage for both sets is unfolded in the next chapter.
[^15]: The headers give the labeling directly: `LebesgueMeasure.v`—Elements: characteristic step functions, measure as integral; Roles: measure of intervals, additivity, monotonicity; Rules: $\mu(A)=I(\chi_A)$, measure from integration, not from $\sigma$-algebras. `ProcessSigmaAdditive.v`—Rules: nonnegativity $\Rightarrow$ growth, finite mass $\Rightarrow$ boundedness $\Rightarrow$ Cauchy.

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[07 Fubini Theorem on Processes|Chapter 7. Fubini’s Theorem on Processes—Part V]] · [[02 Lebesgue Measure on the Process Continuum|Chapter 2. Lebesgue Measure on the Process Continuum]] →
