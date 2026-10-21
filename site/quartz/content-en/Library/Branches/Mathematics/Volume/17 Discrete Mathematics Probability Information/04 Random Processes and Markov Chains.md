---
title: "Chapter 4. Random Processes and Markov Chains"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/04 Случайные процессы и марковские цепи.md"
sourceBlob: 9ee7128bfe29ba6991c4441873e4d778a992acd4
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The distribution (Chapter 3) begins to move. A Markov chain is the simplest moving process: the distribution is updated by applying a *stochastic matrix*, and no memory is needed—the next step depends only on the current state. Over ℚ on a finite space this is again an Element: the matrix is finite, multiplication is exact, the composition of steps is decidable.

*The summit of the chapter: **a model second law from L5**—in the class of doubly stochastic (mixing) steps, entropy grows by the structure of order alone, without a separate Past Hypothesis inside the model.*

The chapter leads from the Markov step and the Chapman–Kolmogorov identity through double stochasticity and majorization to this summit, and closes with concrete random walks.

## The Markov Chain and Chapman–Kolmogorov

A Markov chain is a stochastic matrix over ℚ: the rows sum to one, the transition is memoryless. The composition of steps obeys the Chapman–Kolmogorov identity: the matrix for $m+n$ steps is the product of the matrices for $m$ and for $n$ steps[^1]. This rule is the associativity of motion: the process can be split and reassembled, and the result is the same.

A beautiful special case: a matrix with the golden ratio generates the *addition of Fibonacci numbers* through the composition of transitions—the combinatorics of Chapter 1 and motion meet here[^2]. All of this is exact ℚ-arithmetic on $2\times 2$ matrices: Element.

## Double Stochasticity and Majorization

A special class is the *doubly stochastic* matrices (both the rows and the columns sum to one). Let us write a distribution as a row $p$ and a step as $p\mapsto pT$. Then the initial distribution *majorizes* the mixed one, $p\succ pT$: the step *smooths*, and the uniform distribution is the *minimal* element under majorization (all distributions majorize it)[^3]. Majorization is a *structural order* on distributions (L5): “how smoothed a distribution is.” A doubly stochastic step never makes a distribution “sharper.”

## The Second Law from L5{L5} without the Past Hypothesis

Hence the summit of the chapter and one of the machine summits of the whole volume.

{
On representative distributions the chosen rational measure of mixedness $S_2$ (quadratic, a Padé form; Shannon entropy proper is in Chapter 5) *does not decrease* under doubly stochastic mixing: $S_2(p) \le S_2(T p)$—and this is checked *without any Past Hypothesis*, without a postulate of a special low-entropy beginning[^4].}

*In the class of doubly stochastic (mixing) steps, the arrow of time comes from the **structure of order** (majorization, L5) rather than from a special initial condition: the model second law is a consequence of the rule of mixing, not a postulate about the past.*

This is a strong ToS claim—and it is important to outline it honestly. In the usual formulation, the growth of entropy requires the “past hypothesis” (the universe began in an especially low-entropy state). Here the growth follows from structure alone: a doubly stochastic step smooths ($p\succ pT$), and $S_2$ is Schur-concave—hence, on the checked cases, it grows toward the equilibrium maximum. An important caveat: this is *not* a full physical replacement for the Past Hypothesis (the macroscopic arrow of time and the low-entropy beginning of the Universe are a separate question), but a **model** second law for the class of mixing / coarse-graining dynamics; within its frame, the direction of time turns out to be a role of structure, not a given. Full generality (all distributions) rests on classical Schur concavity.

## Random Walks

The concrete processes are random walks. The walks on a *finite discrete line* (a segment) and on a circle are formalized as Markov chains on a finite carrier; in concrete discrete geometry the walk is linked to *approximations* of $\pi$[^5]. At every finite stage the walk is an Element; its *limiting* (stationary) distribution and the mixing time in general form are the role-limit side, which the process only approaches.

## E/R/R Analysis: The Markov Process as a System

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rules are the Markov property (a memoryless transition by a stochastic matrix) and the Chapman–Kolmogorov composition; above them is the structural order of majorization, from which the monotonicity of entropy follows. It is precisely the L5 order that gives the arrow of time.

**Roles (L4).** The chain, the current distribution, and its entropy are role-levels of one moving object (M2). Double stochasticity is the role of the “mixing” step; the uniform equilibrium is the role of the attractor-maximum of entropy.

**Elements (L1 + P4).** The bearers are finite stochastic matrices over ℚ and finite distributions. Under P4 the finite steps are actual; the stationary distribution and the limit of mixing in general are a role-limit, not a completed object.

{
**Well-formedness check.** The Markov property, Chapman–Kolmogorov, and majorization are Rules; chain/distribution/entropy/equilibrium are Roles; finite ℚ-matrices are Elements; there are no overlaps. There is no self-application: the rule of transition stands above the states.}

**What the analysis yields.** It shows that the motion of a distribution is an Element at every step, and its irreversibility (the growth of entropy) is a consequence of the L5 order, not of a special beginning; and that the only boundary is the limit of mixing (stationarity), the role-limit side. The arrow of time here is a structural role, not a postulate.

Motion and its irreversibility are built; in the next chapter the measure of irreversibility receives a name and a form—we pass to Shannon entropy as a quantitative measure of acts of distinction.

---

[^1]: `chapman_kolmogorov_synthesis` (in `ChapmanKolmogorov`) with `ck_sum`—the composition of transitions; checked on concrete matrices. Machine-checked, 0 axioms.
[^2]: `ck_golden_*` and `fibonacci_addition_*`: the transitions of the golden matrix realize the Fibonacci addition identities. Machine-checked, 0 axioms.
[^3]: Double stochasticity and Schur majorization are the clusters `foundations/DoublyStochastic` and `foundations/MajorizationSchur`; checked on representative distributions (`apply_T` on concrete $p$): the step brings the distribution closer to the uniform one ($pT$ is less sharp than $p$). General majorization is a classical fact due to Schur. Machine-checked, 0 axioms.
[^4]: `no_past_hypothesis_1..3`: $S_2(p)\le S_2(\mathtt{apply_T} p)$ for the two-state doubly stoch. step `apply_T` on concrete $p$ (e.g., $3/4$, $9/10$); `iterated_entropy_*`: the growth is preserved under iteration; `equilibrium_is_max_*`: the (uniform) equilibrium is the maximum of $S_2$. General monotonicity is the classical Schur concavity of entropy. Machine-checked, 0 axioms.
[^5]: Random walks on a finite line and on a circle (`RandomWalkLine`/`RandomWalkCycle`) and the link to approximations of $\pi$ (`PiRandomWalk`); finite Markov chains, exact ℚ-arithmetic. Machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/03 Probability as an Operational Theory|Chapter 3. Probability as an Operational Theory]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/05 Shannon Entropy|Chapter 5. Shannon Entropy]] →
