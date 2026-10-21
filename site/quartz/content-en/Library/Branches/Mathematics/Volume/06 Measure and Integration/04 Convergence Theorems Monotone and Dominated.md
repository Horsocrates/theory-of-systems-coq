---
title: "Chapter 4. Convergence Theorems: Monotone and Dominated"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/04 Теоремы сходимости монотонная и мажорированная.md"
sourceBlob: b738437c8606fe58998737d21bee4e7291e9917b
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Limit under the Integral

Chapters 6.1–6.3 built measure and the Lebesgue integral as processes. The present chapter raises the question for whose sake the Lebesgue integral was created in the first place: *when may the limit be brought under the integral sign*—when is

$$
\int \lim_n f_n \;=\; \lim_n \int f_n.
$$

This is an *interchange of two limits*, and it is not automatic: the integral is itself a limit (a process of accumulation), and it can be swapped with the limit of the sequence $f_n$ only under conditions. Two classical conditions give two theorems—*monotone* convergence (Beppo Levi) and *dominated* convergence (Lebesgue); these are what the chapter analyzes, together with Fatou’s lemma, which supports both.

### Where Infinity Hides—and What Is Proved

The interchange of two limits is exactly the place where nonconstructivity hides in classical analysis: now a completed measure, now an “existing” dominating function obtained implicitly. ToS brings both into the light. We hold to the three levels of rigor. *Proved*: monotone convergence—an increasing bounded sequence of integrals converges (price: L3); the *reduction* of dominated convergence—its engine and the envelope dominating function are proved *without axioms*, and the convergence of the integrals follows from the convergence of the residuals; Fatou’s lemma at the process level. *Remains an honest boundary*: the step “pointwise convergence plus a dominating function implies the convergence of the residuals to zero” itself—the very Fatou step over a completed measure—is taken as an explicit input hypothesis rather than proved within the system.[^1]

### The E/R/R Framework of the Chapter

We set out the framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter introduces the system of convergence theorems.

**Rules ($\leftrightarrow$ L5).** The rule of interchange $\int\lim=\lim\int$ under conditions, split into: “monotone-bounded converges” (price L3); the engine (the difference of the integrals is no greater than the integral of the absolute value of the difference); the envelope (domination); the squeezing of the residual.

**Roles ($\leftrightarrow$ L4).** “The integral of the limit” is the role-limit of the process of integrals; the dominating function $g$ is the role-envelope (an explicit parameter); the residual
$\int|f_n-f|$ is the role-indicator of closeness.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The values $\int f_n$, the values of the dominating function $g$, the residuals $\int|f_n-f|$; the completed limit-function and the completed measure (full Fatou) lie outside the elements.

## Monotone Convergence (Beppo Levi)

Let the functions increase pointwise, $f_0\le f_1\le f_2\le…$, and be uniformly bounded. Then their integrals increase as well (the integral is monotone) and are bounded above—and an increasing bounded sequence *converges*. This is monotone convergence: $\int f_n$ increases to a limit, and this limit exists as a process.

The proof works in processes and relies on a single classical step—*a monotone bounded process is a Cauchy process*—which stands on the Law of Excluded Middle.[^2]

**The provable core of monotone convergence is a theorem: the process of integrals of an increasing
bounded sequence converges.** “The integral of the limit” $\int\lim_n f_n$ is the *role-limit* of this process; the completed limit function as an object is not needed.

The price, L3, is precisely the price of the lemma `monotone_bounded_Cauchy`: the passage from monotonicity and boundedness to the Cauchy behavior of the process (the same dependence as for countable additivity in Chapter 6.1). This is the *honest and only* price of monotone convergence; it requires no completed measure and no Axiom of Choice.

## The Domain-Explicit Dominating Function

Before passing to dominated convergence, let us return to the method announced in Chapter 6.1: *the dominating function is an explicit parameter, not an object existing by default.* The classical formulation begins with the words “let there exist an integrable $g$ such that $|f_n|\le g$…,” and in the classical proof this $g$ is often given as an existing upper envelope of a class of functions or as a consequence of a previous theorem, rather than presented as data. In ToS $g$ is a *given* function, presented by a hypothesis; domination is a relation that takes $g$ as an explicit argument.[^3]

*Where the classical theory silently chooses a controlling function from a completed collection, ToS requires it to be built and shown.*

It is precisely the explicitness of the dominating function that makes dominated convergence constructive without the Axiom of Choice: with $g$ in hand, what remains is the purely finite arithmetic of estimates, to which we now pass.

## Dominated Convergence as a Reduction

Lebesgue’s dominated convergence theorem states: if $f_n\to f$ pointwise and $|f_n|\le g$ with an integrable $g$, then $\int f_n\to\int f$. ToS decomposes it into three links, and the first two are proved *without axioms*.

*The engine* is the inequality

$$
\Big|\int f_n-\int f\Big| \;\le\; \int |f_n-f|.
$$

The difference of the integrals does not exceed the integral of the absolute value of the difference; this is linearity plus the triangle inequality for finite sums, proved exactly.[^4]

*The envelope*: domination drives the residual under the dominating function:

$$
|f_n-f|\le 2g \;\Longrightarrow\; \int|f_n-f|\le\int 2g.
$$

This is the monotonicity of the integral applied to the domain-explicit dominating function.[^5]

*The squeeze*: if the integral of the residual tends to zero, then by the engine also
$\big|\int f_n-\int f\big|\to 0$, that is, $\int f_n\to\int f$.[^6]

**The engine and the envelope are proved constructively, without a single axiom.** The convergence of the integrals of a dominated sequence *reduces* to one statement: the integral of the residual tends to zero.

And here is the honest boundary. The step “pointwise convergence $f_n\to f$ under a dominating function $g$ implies $\int|f_n-f|\to 0$” is the substantive core of Lebesgue’s theorem (classically it is proved through Fatou’s lemma over a completed measure). ToS takes *it* as an explicit input hypothesis rather than proving it within the system: it is precisely here that the completed measure would live, and precisely this measure is what we do not actualize (P4). What is proved is the *reduction*: the whole arithmetic machine of the interchange (engine and envelope) is assembled constructively, and exactly one infinitary step remains, honestly moved outside.

## Fatou’s Lemma at the Process Level

ToS keeps Fatou’s lemma—that the integral of the lower limit does not exceed the lower limit of the integrals—at the process level: for nonnegative functions the lower envelope of the sequence of integrals is nonnegative, and under domination it is bounded.[^7] This is the finite-process core of Fatou: at each stage $n$ the quantities are defined and satisfy the required inequalities.

The full Fatou lemma over a completed measure—the one through which the step “residuals $\to 0$” from § “Dominated Convergence as a Reduction” is classically proved—remains beyond the P4 boundary: it requires a formulated lower limit and a measure at the level of a completed ($L^1$/measure) space, a layer that is not actualized in the present chapter. The process core is proved; the completed object is not actualized. This is the same line of honesty as everywhere in Part VI.

## E/R/R Analysis: The Interchange of Limits as a Rule

### Analysis in the Generating Order

The framework was set at the beginning of the chapter (§ “The E/R/R Framework of the Chapter”); here we unfold it with a table and a check of correctness. Let us analyze the system of convergence theorems in terms of E/R/R, continuing the analyses of Chapters 6.1–6.3. The reservation about the level is the same as before. We conduct the analysis in the generating order
Rules $\to$ Roles $\to$ Elements.

**Rules ($\leftrightarrow$ L5).** At the foundation is the rule of interchange
$\int\lim=\lim\int$ under conditions. It is split into: “monotone-bounded converges” (monotone convergence, price L3); the *engine*—the difference of the integrals is no greater than the integral of the absolute value of the difference; the *envelope*—domination drives the residual under the dominating function; the *squeezing* of the residual (the formulas are in § “Dominated Convergence as a Reduction”). The universal layer is L1–L5 (in particular L3 for the monotone limit) and P4, which moves the Fatou step beyond the boundary.

**Roles ($\leftrightarrow$ L4).** “The integral of the limit”
$\int\lim_n f_n$ is the role-limit of the process of integrals. The dominating function $g$ is the role-*envelope* that enforces the interchange: an explicit parameter, not an object “by existence” (the methodology of presenting data). “The residual $\int|f_n-f|$” is the role-indicator of closeness, whose tending to zero is precisely the honest input hypothesis.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite at
every stage: the values of the integrals $\int f_n$, the values of the dominating function $g$, the residuals $\int|f_n-f|$. The completed limit-function and the completed measure through which the full Fatou goes do not belong to the elements.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| interchange $\int\lim=\lim\int$; engine; envelope; “monotone-bounded converges” | HOW the passage of the limit under the integral is organized | Rules ($L5$) |
| integral of the limit; envelope dominating function; residual | WHAT FOR the bearers are significant: roles of the interchange | Roles ($L4$) |
| $\int f_n$; values of $g$; $\int|f_n-f|$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### What the Analysis Yields

{
The analysis shows where infinity hides in the interchange of limits and how ToS deals with it. Monotone convergence honestly pays L3 for the single step “monotone-bounded converges.” Dominated convergence is *reduced*: its arithmetic machine (engine and envelope) is proved without axioms, and the only infinitary step—the tending of the residual to zero, classically going through the completed measure and Fatou—is moved out into an explicit hypothesis. The dominating function, moreover, does not “exist” but is *presented* (L4, P4). This is the way ToS makes convergence theorems constructive: not by hiding the infinitary step in a completed object but by naming it and placing it on the boundary.}

The proved part—monotone convergence, the engine and envelope of dominated convergence, the process core of Fatou—gives a working apparatus for passing to the limit under the integral. The next chapter assembles *spaces* from the integral—$L^1$ and $L^2$—where this apparatus of convergence finds its natural place, and completeness, as before, turns out to be the constructibility of the limit-process.

---

[^1]: The supporting files are `ProcessMCT.v`, `ProcessDCT.v`, `ProcessFatou.v` (directory `src/process/` of the ToS Rocq repository). The lemma names are in the notes below.
[^2]: The statement `process_mct`: for a pointwise increasing and uniformly bounded sequence of integrable functions, the sequence of their integrals is a Cauchy process—`is_Cauchy`. It relies on `riemann_sum_monotone` (pointwise $f\le g$ implies $\int f\le\int g$) and `monotone_bounded_Cauchy`. The price is `classic` (L3); there are no new axioms. In the code the statement is proved for a self-contained rational integral-sum $\int f = w\sum_i f(x_i)$; the transfer to the $L^1$ integral layer is a substantive reading of the same scheme (it uses only the monotonicity and boundedness of the integral process), not a separate theorem of this chapter.
[^3]: The predicate `dominated` in `ProcessFatou.v`: $\forall k x,\ |f_k(x)|\le g(x)$, where $g$ is a parameter. This is a direct P4 reading (a methodology of presenting data, not an axiom used by the file): existence $\to$ presentation.
[^4]: `dct_diff_bound` in `ProcessDCT.v` (0 axioms): it relies on the additivity of sums and the componentwise triangle inequality `q_sum_abs_le`.
[^5]: `dct_dom_bound` in `ProcessDCT.v` (0 axioms).
[^6]: `process_dct` in `ProcessDCT.v` (0 axioms): from the convergence of the residuals $\int|f_n-f|\to 0$ follows the convergence of the integrals. The package `process_dct_dominated` combines the envelope and the squeeze.
[^7]: `process_fatou_nonneg` and `process_fatou_bounded` in `ProcessFatou.v` (0 axioms); `dominated_integral_bound` is an estimate of the difference of integrals through the dominating function.

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[03 Measurable Functions and the Lebesgue Integral|Chapter 3. Measurable Functions and the Lebesgue Integral]] · [[05 L1 and L2 Spaces as Processes Completeness as Constructibility|Chapter 5. L^1 and L^2: Spaces as Processes, Completeness as Constructibility]] →
