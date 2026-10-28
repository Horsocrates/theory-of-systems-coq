---
title: "Chapter 3. Probability as an Operational Theory"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/03 Вероятность как операциональная теория.md"
sourceBlob: b120153d27987c29909c8e4c79c4655a7fdb8e15
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Probability in the present volume is an *operational* theory: a function on a finite list of outcomes with values in ℚ. No Lebesgue measure, no $\sigma$-algebra, no axiom of choice—these constructions belong to the completed continuum, that is, to the role-limit side, and are *not needed* for discrete probability. “The set of outcomes” is a mode: in reality we work with a list of possible values, and probability distributes over it the acts of distinction that combinatorics (Chapter 1) learned to count.

*The flagship of the chapter: concentration (Markov, Chebyshev) is an **Element**—a finite, decidable estimate; the limit laws (the LLN) are a **role-limit**—convergence-as-process.*

Probabilities are structurally nonnegative ($P\ge 0$), and this is a property of the construction, not an axiom. The chapter leads from probability-without-measure through Bayes-as-algorithm to the machine diagnosis of cognitive fallacies and ends with the finitization boundary in its probabilistic form.

## Probability without Measure

A finite probability space is a list of outcomes with assigned rational weights whose sum equals one. An event is a decidable predicate on the list of outcomes (equivalent to a subset of outcomes in a representation without repetitions); the probability of an event is the sum of the weights of the outcomes that pass the predicate. There is no completed measure space here: there is a finite list and ℚ-arithmetic on it. Nonnegativity $P\ge 0$ is structural in the chosen model: the distribution contains only nonnegative rational weights (from a nonnegative subtype / with a proof of nonnegativity), and normalization is a condition on a finite sum. Everything is decidable by enumerating the list—the Element side.

A random variable, then, is a *morphism of lists*, not a mysterious “quantity with randomness”: a function that translates the list of outcomes into a list of values. This is operational divisibility: a random variable, its distribution, and its numerical characteristics (mean, variance) are different *role-levels* of one finite object, not different entities.

## Bayes as an Algorithm of Distinction

Bayes’ theorem in the operational reading is an *algorithm*: a rule that recomputes the distribution upon the arrival of a new act of distinction (evidence)[^1]. Evidence is a distinction that narrows the list of outcomes; Bayes is the rule for exactly how to redistribute the weights. There is no completed infinity here: the input is finite, the recomputation is finite.

## Fallacies as Structural Impossibility

The sharpest result of the chapter is the *machine diagnosis of cognitive fallacies*. And the diagnosis is stronger than “unlikely”: typical errors of judgment turn out to be *structurally impossible*—contradicting proved identities, not merely rare.

**The conjunction fallacy.** The famous “Linda problem” supposes that a conjunction of events can be more probable than one of them. But $P(A\wedge B)\le P(A)$ is a *theorem*; to assert the opposite is *absurd*, not “unlikely,” and this is proved as an absurdity[^2].

**The base-rate fallacy** confuses $P(H\mid E)$ with $P(E\mid H)$: in the nondegenerate case (nonzero $P(H)$, $P(E)$ and a nonzero joint probability $P(H\wedge E)$) the equality $P(H\mid E)=P(E\mid H)$ is legitimate only when $P(H)=P(E)$, which is detected[^3]. **The gambler’s fallacy** denies the independence of trials and is likewise caught as a contradiction[^4].

*A cognitive fallacy is a confusion of categories caught by *structure*: the error is structurally impossible, not rare. A distinction drawn incorrectly yields a P1-incompatible result—incompatible with the primary rule of the event—not an improbable one.*

This is a direct continuation of the ToS diagnosis of fallacies (Architecture of Reasoning): an incorrect judgment is a violation of the rules for structuring distinctions, and it is recognized by machine.

## Concentration versus Limit Laws

Where, then, does probability cross the finitization boundary? Exactly between *concentration* and *limit laws*.

Markov’s and Chebyshev’s inequalities are *finite* estimates: Markov’s for a nonnegative random variable, Chebyshev’s through the variance (always finite on a finite list); both give a rational bound on the probability of a deviation and are computed exactly on a finite distribution[^5]. This is an Element: a decidable estimate, a terminating count.

The weak law of large numbers is different: it asserts the *convergence in probability* of the mean to the expectation, that is, the limit of a *process* of refinement. This is the role-limit side—and our formalization draws the cut exactly along this line[^6].

*Concentration is an Element (a finite estimate); a limit law is a role-limit (convergence as a process). The same finitization boundary, now in probability.*

## E/R/R Analysis: Probability as a System

Let us analyze probability by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rules are the axioms of probability (nonnegativity, normalization, additivity of incompatible events) and Bayes’ update rule. Above them are the rules of concentration (Markov, Chebyshev). These rules structure the distribution of distinctions.

**Roles (L4).** A random variable (a morphism of lists), its distribution, and its characteristics (mean, variance) are three *role-levels* of one finite object. “The set of outcomes” is a mode of the list. Probability is a role-weight (a normalized weight function), structurally nonnegative.

**Elements (L1 + P4).** The bearers are finite lists of outcomes with rational weights. Under P4 it is they that are actual; a completed probability space on the continuum (Lebesgue measure, $\sigma$-algebra) and the limit of the LLN are role-limits, not completed objects.

**Well-formedness check.** The axioms and Bayes are Rules; variable/distribution/characteristics are Roles; finite weighted lists are Elements; there are no overlaps. There is no self-application: the rules stand above the distribution and are not its outcomes.

**What the analysis yields.** It explains why probability does not need Lebesgue measure: its bearers are finite, and the distribution is a ℚ-function on a list; and why a cognitive error is caught structurally: it violates the rules (Rules) rather than merely being improbable. The boundary enters only in the limit laws—the role-limit, the same one the volume carries.

The static distribution is built; in the next chapter it begins to *move*—we pass to random processes and Markov chains, where the structure of order itself yields the growth of entropy.

---

[^1]: `bayes_rule`: $P(H\mid E) P(E) = P(E\mid H) P(H)$ over ℚ, constructively; conditional probability is a separate cluster (`ConditionalProbability`). Machine-checked, 0 axioms (`Print Assumptions`).
[^2]: `conjunction_fallacy_detected`: $P(A\wedge B)\le P(A)$; `conjunction_fallacy_absurd`: the assumption $P(A\wedge B)>P(A)$ leads to a contradiction. Machine-checked, 0 axioms.
[^3]: `base_rate_fallacy_detected` and `bayes_asymmetry`: for $P(H),P(E),P(H\wedge E)\neq 0$, $P(H\mid E)=P(E\mid H)$ implies $P(H)=P(E)$; Bayes’ asymmetry as the contrapositive. Machine-checked, 0 axioms.
[^4]: `gamblers_fallacy_detected`/`gamblers_fallacy_absurd`: if the trials are given as independent, past outcomes do not change the probability of the next one; the contrary is absurd. 0 axioms.
[^5]: `markov` ($P(X\ge a)\le \mathbb{E}[X]/a$ for $X\ge 0$) and `chebyshev` (through the variance), over ℚ on a finite distribution (`dist` $=$ a list of value–weight pairs). Machine-checked, 0 axioms.
[^6]: `chebyshev_lln_boundary` formalizes the *cut*: the Chebyshev bound at fixed $n$ is an Element (decidable), while the statement about the limit $n\to\infty$ is a role-limit; `cheb_bound` is an explicit estimate decreasing in $n$. This is not a full formalization of the LLN as an analytic theorem. Machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/02 Graph Theory Connectivity Cycles Curvature|Chapter 2. Graph Theory: Connectivity, Cycles, Curvature]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/04 Random Processes and Markov Chains|Chapter 4. Random Processes and Markov Chains]] →
