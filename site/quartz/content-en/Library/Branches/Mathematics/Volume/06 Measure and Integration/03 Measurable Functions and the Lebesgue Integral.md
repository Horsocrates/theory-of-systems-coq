---
title: "Chapter 3. Measurable Functions and the Lebesgue Integral"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/03 Измеримые функции и интеграл Лебега.md"
sourceBlob: c900721cae2aa9360097868a301e2549244b8ca6
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From Sets to Functions

Chapters 6.1 and 6.2 built measure: the rule $\mu(A)=I(\chi_A)$, invariance, sets of measure zero. But the measure of an interval was already obtained as the integral of the indicator—so the integral is primary and measure is derived. The present chapter returns to the integral and extends it from indicators to arbitrary *integrable functions*, clarifying along the way what “a function is measurable” means, what “almost everywhere” means, and how the Lebesgue integral relates to the Riemann integral of Part V.

### Two Definitions of Measurability

The textbook defines a measurable function through the *preimage*: $f$ is measurable if the preimage $f^{-1}(U)$ of every open $U$ is measurable. This definition inherits all the presuppositions of textbook measure, above all a completed $\sigma$-algebra in which the preimages must lie.

ToS, as with measure, follows Bishop–Cheng and defines not a preimage-measurable but an *integrable* function: one that is a *limit of step functions* in the norm
$\|\cdot\|_1$. This is a direct continuation of “measurable $=$ distinguishable”: a function is integrable when it can be approximated with arbitrary precision by finite step data—just as a set is measurable when its indicator is distinguishable.

*An integrable function is not an object with measurable preimages but a process of step approximations converging in the integral norm.*

We will introduce preimage measurability in § “Preimage Measurability—a Classical Comparison” as a *classical comparison*; the spine of the exposition follows integrability. And again we hold to the three levels of rigor: *proved without axioms*—the step integral and its properties, the integral-process on bounded functions, the L¹ integral as a limit and its classes (equality almost everywhere); *remains a substantive reading or a classical comparison*—preimage measurability, the agreement of Lebesgue with Riemann beyond the step level, and the fully pointwise “almost everywhere.”

### The E/R/R Framework of the Chapter

We set out the framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter introduces the system of the Lebesgue integral.

**Rules ($\leftrightarrow$ L5).** The integral of a step function (the exact sum $\sum v_i w_i$) and its properties; the $L^1$ completion (an integrable function is a Cauchy sequence of step functions in $\|\cdot\|_1$); identification almost everywhere
($\|f-g\|_1\to0$).

**Roles ($\leftrightarrow$ L4).** “Integrable function” is the role of a process of step approximations (an $L^1$ class); “integral” is the role-limit of sums; “almost everywhere” is a role-mode that suppresses distinctions of zero norm; “measurability” is the role of distinguishability.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Step functions, their
exact integrals $\sum v_i w_i$, the terms of the approximating sequence; the completed limit function and a ready $L^1$ lie outside the elements.

## The Step Function and Its Integral

The brick of the whole construction is the step function: a finite list of steps, each with its own value on its own interval. Its integral is exact and requires no limit: it is a finite sum of areas $\sum_i v_i\cdot w_i$ (value times width), computed in rational arithmetic.[^1]

At this finite level the integral already has all the expected properties, and all of them are proved as exact identities: *additivity under concatenation* (the integral of a joined list of steps is the sum of the integrals of the parts), *homogeneity* (pulling out a constant factor), and *monotonicity* (if one step function is everywhere no greater than another, then its integral is no greater either).[^2] There are no axioms here and no passages to the limit—only finite rational arithmetic. This is the same motif as with the measure of an interval: at the step level the “properties of the integral” are theorems about the construction.

## The Lebesgue Integral as a Process of Accumulation

On a bounded function the integral is naturally read as a *process of accumulation*: at each stage $n$ there is a finite step sum, and the integral itself is the limit of these sums, a sequence of rational approximations, not a completed number. In the process layer of the code this integral-process *coincides* with the Riemann one—and coincides not by chance: the “Lebesgue process” there is simply *defined* as the Riemann process, so their equivalence is an identity by definition, not a separate substantive theorem.[^3]

*The true power of Lebesgue—to integrate functions inaccessible to the Riemann grid—lives not in another process of accumulation but in another notion of integrable function: in approximability by step functions in the norm $\|\cdot\|_1$.*

It is to this notion, an integrable function as an L¹ limit of step functions, that we now pass; it is the exact route of ToS. The agreement of Lebesgue with Riemann at the step level is proved exactly (the embedding `step_to_l1`); for a broader class of “good” functions it remains an expected next theorem, not a result on which this chapter rests.

## An Integrable Function as a Limit of Step Functions

Now the exact definition. An *integrable function* is a Cauchy sequence of step functions in the norm $\|\cdot\|_1$ (the integral of the absolute value): a sequence $f_n$ of step functions for which $\|f_n-f_m\|_1$ becomes arbitrarily small.[^4] Its integral is the limit of the integrals of the approximating step functions; it is defined as a process and is provably stable.[^5]

*The completion is built into the type itself: an L¹ object already is a Cauchy process of step functions, so the representatives of the completion are built directly—this is not a separately proved Riesz–Fischer theorem about a ready quotient space but a way of building the completion by construction.*

This is the same reformulation of completeness that ran through Part V: completeness is not the existence of a completed limit in a ready space but the *constructibility* of the limit-process. An integrable function does not “lie” in an L¹ given in advance; it *is* a process, and L¹ is the type of such processes, considered up to equality almost everywhere (§ “Almost Everywhere and Classes”).

## Preimage Measurability—a Classical Comparison

Let us return to the textbook definition. Measurability through the preimage—$f^{-1}(U)$ is measurable for every open $U$—is powerful and familiar, but in our order it is *not a foundation but an alternative route*. To speak of the preimages of all open sets one needs a completed $\sigma$-algebra, which ToS does not build (§ (see the corresponding chapter) of Chapter 6.2). Therefore preimage measurability is introduced as a classical comparison, while the spine follows integrability.

The connection between the two notions has content: for “good” functions they coincide, and preimage measurability is a convenient criterion where it applies. But what is *defining* in ToS is integrability, approximability by step functions, precisely because it is constructive and does not require a completed collection of preimages.[^6]

## Almost Everywhere and Classes

The last brick is the relation “almost everywhere.” Two integrable functions are naturally *identified* if they differ on a set of measure zero: the integral of their difference then does not feel the distinction. In the process reading this is expressed without any completed “measure zero as an object”: two L¹ functions are equivalent if the integral of the absolute value of their difference converges to zero, that is, $\|f-g\|_1\to 0$.[^7]

**“Almost everywhere” is a mode of identification, not a property of points.** A function in L¹ is not a separate pointwise object but a *class* of functions indistinguishable in the integral norm; distinctions on a set of measure zero are suppressed as inessential.

This is a direct echo of a recurring motif of the volume. A rational number was a *class* of fractions (Chapter 3.2, the relation of $ℚ$-equality); a point of the continuum, a *class* of convergent processes (Chapter 4.3); now an integrable function is a *class* of functions equal almost everywhere. Each time a class is a *mode* in which the system declares inessential those distinctions that do not affect its rule (equality of fractions, equivalence of processes, zero norm of a difference). This is motif M3: ignoring distinctions that are not significant for the system. As in Chapter 4.3, what is formally given are the *representatives* (the type of L¹ processes) and the equivalence *relation* ($\|f-g\|_1\to 0$), but a separate quotient type of L¹ classes is not built: the class remains a mode of reading, not a built object.

## E/R/R Analysis: The Integral as a Rule, the Function as a Role

### Analysis in the Generating Order

The framework was set at the beginning of the chapter (§ “The E/R/R Framework of the Chapter”); here we unfold it with a table and a check of correctness. Let us analyze the system of the Lebesgue integral in terms of E/R/R, continuing the analyses of Chapters 6.1–6.2. The reservation about the level is the same as before: the “system of the integral” is a substantive interpretation of the construction. We conduct the analysis in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules ($\leftrightarrow$ L5).** At the foundation is the integral of a step function (the exact sum $\sum v_i w_i$) and its properties (additivity, homogeneity, monotonicity). Above it are the rule of L¹ completion (an integrable function is a Cauchy sequence of step functions in $\|\cdot\|_1$), the rule of identification almost everywhere ($\|f-g\|_1\to 0$), and the agreement of the integral-process with the Riemann one (on bounded functions, by definition). The universal layer is L1–L5 and P4.

**Roles ($\leftrightarrow$ L4).** “Integrable function” is the role of a process of step approximations (an L¹ class), not a preimage object. “The integral of a function” is the role-limit of the process of step sums. “Almost everywhere” is a role-mode that suppresses distinctions of zero norm (M3). “Measurability” is the role of distinguishability, extended from sets to functions.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite at every stage: step functions, their exact integrals $\sum v_i w_i$, the terms of the approximating sequence. The completed limit function and the completed L¹ as a ready pleroma do not belong to the elements; only finite approximations are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| integral of a step function; L¹ completion; $\|f-g\|_1\to 0$ | HOW integration and identification are organized | Rules ($L5$) |
| integrable function (L¹ class); integral; “almost everywhere” | WHAT FOR the bearers are significant: role-processes | Roles ($L4$) |
| step functions; $\sum v_i w_i$; terms of the approximation | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### What the Analysis Yields

{
The analysis fixes two things. First: *an integrable function is a Role*—a process of step approximations, read up to equality almost everywhere—not a preimage object in a completed $\sigma$-algebra. To take it for a pointwise object with measurable preimages is to substitute a ready element for a role-process, the same confusion of categories as in the other chapters. Second: *“almost everywhere” is the mode M3*, the third embodiment of the class-as-role after the rational number (Chapter 3.2) and the point (Chapter 4.3); the system suppresses distinctions that do not affect its rule ($\|f-g\|_1=0$), just as it suppressed the distinctions of fractions ($ℚ$-equality) and of processes (equivalence).}

The proved part—the step integral and its properties, the Lebesgue integral as a process, the agreement with Riemann, the L¹ integral as a limit and its classes—gives a firm foundation for the next step. The next chapter raises the question of the *limit under the integral sign*: when the integral of the limit equals the limit of the integrals—the theorems of monotone and dominated convergence, where the domain-explicit dominating function (Chapter 6.1) carries the whole constructive load.

---

[^1]: The type of a step function and `step_integral` (the area of one step), `step_fun_integral` (the sum) in `StepIntegral.v` (directory `src/analysis/`, 20 proved statements, 0 `Admitted`, 0 axioms).
[^2]: `integral_app` (additivity under concatenation), `integral_scale` (homogeneity), `integral_monotone_step` (monotonicity) in `StepIntegral.v`; `step_integral_nonneg`.
[^3]: In `ProcessLebesgue.v` (directory `src/process/`) `lebesgue_process` is defined as `riemann_process`, and `lebesgue_riemann_equiv` proves their `process_equiv` as an identity. This is a process identification, not a separate construction of Lebesgue at the layer of values.
[^4]: The type `L1Process` and the norm `step_fun_norm` in `L1Space.v` (directory `src/analysis/`, 25 proved statements, 0 `Admitted`, 0 axioms).
[^5]: `l1_integral_approx`—the integral of an L¹ function as an approximating process; `step_to_l1`—the embedding of a step function into L¹; `l1_constant_integral`.
[^6]: The process predicate of the distinguishability of a function at stage $n$ is `measurable_at` in `ProcessMeasureTheory.v`; a separate type of “preimage-measurable function” is not built in the current corpus and is given as a classical comparison.
[^7]: `l1_equiv` in `L1Space.v`: $\forall\varepsilon>0\ \exists N\ \forall n\ge N:\ \|f_n-g_n\|_1<\varepsilon$. This is the L¹ sense of equality almost everywhere; the fully pointwise “they differ only on a set of measure zero” is a substantive reading on top of this core.

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[02 Lebesgue Measure on the Process Continuum|Chapter 2. Lebesgue Measure on the Process Continuum]] · [[04 Convergence Theorems Monotone and Dominated|Chapter 4. Convergence Theorems: Monotone and Dominated]] →
