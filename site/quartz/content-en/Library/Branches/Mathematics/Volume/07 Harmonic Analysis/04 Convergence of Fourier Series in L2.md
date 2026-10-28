---
title: "Chapter 4. Convergence of Fourier Series in L²"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/07 Гармонический анализ/04 Сходимость рядов Фурье в L2.md"
sourceBlob: 1ec1f403d4dce9a259e0762ba1c05b81ea2dd1ec
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### Return to the Rational Core

Chapter 7.3 drew the boundary: trigonometric and complex Fourier go beyond ℚ through the choice of the group and the field of values of its characters. The present chapter returns to this side of the boundary—to what in the theory of Fourier series is *provable*, finite, and rational: to *convergence in L<sup>2</sup>*.

And here ToS makes its usual move. The classical theory says: “the Fourier series of a function $f$ converges to it in L<sup>2</sup>”—and takes the series as a completed infinite sum, and convergence as an attained limit. ToS takes the Fourier series as a *process* of partial sums, and convergence as the *monotone decrease of the error* of this process. The provable core is this: for each truncation $K$ the partial sum is the best approximation, its squared error equals the discarded tail energy, and this error decreases as $K$ grows. The completed infinite series and its L<sup>2</sup> limit remain an honest P4 boundary.

### What Is Proved—and What Is the Boundary

The following is proved over ℚ (for a finite orthonormal system on $N$ coordinates), and all of it without axioms.[^1] The squared truncation error equals the full energy minus the captured energy, $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$; this error is nonnegative (Bessel) and *decreases monotonically* as $K$ grows; the partial sum $P_K$ is the best $K$-term approximation; and the error vanishes if and only if Parseval’s identity holds, that is, the system fully recovers $f$.

What the chapter does *not* claim. The *completed* infinite Fourier series
$\sum_{k=1}^{\infty}c_k e_k$ as a ready object and its L<sup>2</sup> limit
$\lim_K P_K=f$ for an infinite system are a role-limit: ToS does not build it otherwise than through a separate Cauchy process in $K$ and the completeness of the system, and completeness in the limit is itself a limit statement. Both *pointwise* convergence (Dirichlet’s theorem) and the Gibbs phenomenon lie outside the L<sup>2</sup> core altogether: these are questions about behavior at points, not about energy, and they drag in the transcendental machinery of Chapter 7.3.

Let us distinguish the levels of rigor. The *first* is the finite theory of truncations (error = tail, monotonicity, best approximation, the completeness criterion): proved over ℚ, 0 axioms. The *second* is the process reading: the Fourier series as a process $K\mapsto P_K$ with a decreasing error, L<sup>2</sup> completeness by construction (the Riesz–Fischer of Part VI). The *third* is the completed series, its limit, pointwise convergence, and Gibbs: role-limits and a different (pointwise) layer. We treat the first as proved, the second as a process, and the third as a marked boundary.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.”

**Rules ($\leftrightarrow$ L5).** The partial sum $P_K=\sum_{k<K}c_k
e_k$ with $c_k=\inner{e_k}{f}$; the error identity $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$; the monotone decrease of the error in $K$; $P_K$ is the best approximation; zero error
$\Leftrightarrow$ Parseval (completeness).

**Roles ($\leftrightarrow$ L4).** $P_K$ is the role-approximation; the tail energy $\norm{f-P_K}^2$ is the role-defect; “convergence” is the role-decrease of the error; the completed series and the L<sup>2</sup> limit are a role-limit; pointwise convergence and Gibbs are roles of a different (pointwise) layer.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational
coefficients $c_k$, partial sums $P_K$, finite sums $\sum_{k<K}$, $K\le N$; the completed infinite series lies outside the elements (P4).

## Convergence as a Process of Truncations

### The Fourier Series as a Process, Not as a Sum

Take an orthonormal system $\{e_k\}$ and a function $f$. Its Fourier coefficients
$c_k=\inner{e_k}{f}$ and partial sums

$$
P_K \;=\; \sum_{k<K} c_k e_k
$$

were introduced in Chapter 7.1. The classical Fourier series is the “sum of all” $\sum_{k=1}^{\infty}
c_k e_k$, an object that exists only as a completed infinity. ToS reads it differently: there is a *process* $K\mapsto P_K$, at each stage a finite rational sum that can be carried to any required precision; the “Fourier series” is the name of this process, not of its completion.

*A Fourier series is not an infinite sum-object but a process of partial sums $P_K$. Each $P_K$ is finite and rational; “convergence” is a property of the process, not an attained state of a completed sum.*

### An Energy Budget, Not a Guarantee of the Limit

What guarantees that the process of truncations behaves in a controlled way? Bessel’s inequality (Chapter 7.1) gives an *energy budget*:

$$
\sum_{k<K} c_k^2 \;\le\; \norm{f}^2 .
$$

The captured energy cannot exceed the full energy, its partial sums have a common upper bound, and the error $\norm{f-P_K}^2$ does not increase.

But this is *not yet* full L<sup>2</sup> convergence to $f$ itself. For convergence to the function it is necessary that the *tail energy tend to zero*, that is, that completeness (Parseval) hold in the limit sense. At a finite truncation to $N$ coordinates this is checked by a finite criterion (§ “Parseval as a Criterion of Convergence to Zero”): with a complete set of directions the error vanishes. For an infinite system a separate Cauchy process in $K$ and a proof that the tail vanishes are required, and this is already a limit statement, not a consequence of Bessel alone.

Here the Riesz–Fischer of Part VI helps: *if* such a Cauchy process of partial sums has been built, its limit is read as an L<sup>2</sup> process (the space of L<sup>2</sup> processes is Cauchy-complete by construction).[^2] But the Cauchy convergence of the Fourier series to $f$ itself does *not* follow from Bessel alone: it requires the completeness of the system. Riesz–Fischer guarantees the *bearer* of the limit, not that the limit is precisely $f$.

## The Truncation Error Equals the Tail Energy

### The Energy Split and Its Consequences

The heart of the provable core is the Pythagorean identity of Chapter 7.1, read as the energy balance of a truncation:

$$
\underbrace{\norm{f-P_K}^2}_{\text{error}}
  \;=\;
  \underbrace{\norm{f}^2}_{\text{full}}
  \;-\;
  \underbrace{\sum_{k<K} c_k^2}_{\text{captured}} .
$$

The squared truncation error equals *exactly* the discarded tail energy, the energy that the first $K$ coefficients did not grasp.[^3] Hence three consequences, and each is proved:

*Nonnegativity.* The error $\norm{f-P_K}^2\ge0$; hence $\sum_{k<K}c_k^2\le
\norm{f}^2$ (Bessel’s inequality): the captured energy never exceeds the full energy.[^4]

*Monotone decrease.* As $K$ grows the captured energy does not decrease, hence the error *does not increase*: $K\le K'\Rightarrow\norm{f-P_{K'}}^2\le\norm{f-P_K}^2$. This is convergence at the finite level: each new coefficient decreases (does not increase) the residual.[^5]

*The provable core of L<sup>2</sup> convergence is control of the tail energy: it is nonnegative, does not increase when coefficients are added, and vanishes exactly at Parseval. Each step is an exact rational identity; no completed limit is required for these statements.*

## Best Approximation and the Completeness Criterion

### The Partial Sum Is Optimal

The decrease of the error would be of little value if the partial sums were not the *best* approximations. But they are: among all $K$-term linear combinations of the system
$\{e_k\}$, the Fourier partial sum $P_K$ minimizes the L<sup>2</sup> error, and this minimum is unique (Chapter 7.1). Therefore the process of truncation does not merely decrease—it decreases *optimally*: at each $K$ one cannot approximate $f$ through $K$ directions better than $P_K$ does.[^6]

### Parseval as a Criterion of Convergence to Zero

When does the error reach zero? If and only if Parseval’s identity $\sum_{k<K}c_k^2=\norm{f}^2$ holds, that is, when the system *fully* recovers $f$. This is the finite completeness criterion of Chapter 7.1, read as a criterion of convergence: zero tail energy is equivalent to exact recovery.[^7] If the system is complete at the given truncation $N$, the error vanishes for sufficiently large $K$; for the standard complete $N$-directional set it does so exactly at $K=N$: the process of truncation ends with *exact* recovery in a finite number of steps.

*The convergence of a Fourier series to the function is the decrease of the error to zero, and zero error is Parseval, is completeness. For a complete finite system the goal is reached exactly in a finite number of steps; the infinite case is the limit of this process, a boundary.*

## The Boundary: The Completed Series, Pointwise Convergence, Gibbs

Let us outline the boundary exactly, so that the provable core is not passed off as something larger. Three things remain on the other side.

*The completed series and its L<sup>2</sup> limit.* The infinite sum
$\sum_{k=1}^{\infty}c_k e_k$ as a ready object and the equality $\lim_K P_K=f$ for an infinite system are a role-limit. One can approach them as a process (the error decreases, the space is complete by construction), but ToS does not actualize the *completed* limit: building it requires a separate Cauchy process in $K$ and the completeness of the system in the limit, and this is already a limit statement, not a finite identity.

*Pointwise convergence (Dirichlet).* Whether the Fourier series converges to $f$ *at each point* is a question of a different layer. Dirichlet’s theorem on pointwise convergence (to the half-sum of the one-sided limits at a point of discontinuity) speaks of values, not of energy; it lives in the transcendental trigonometry of Chapter 7.3 and does not enter the L<sup>2</sup> core. Convergence in energy and convergence at a point are different statements; to confuse them is a category mistake.

*The Gibbs phenomenon.* The well-known “overshoot” of partial sums near a discontinuity, which does not disappear as $K$ grows, is also a pointwise-uniform phenomenon, not an L<sup>2</sup> effect: in energy it is negligible (the tail energy decreases), but in the maximum norm it is not. It only emphasizes that L<sup>2</sup> convergence and pointwise convergence are not the same.

*L<sup>2</sup> convergence has a provable finite core: the error-energy decreases optimally to zero-at-completeness. The completed series is a role-limit; pointwise convergence and Gibbs are questions of a different, pointwise layer, outside energy and beyond the boundary of 7.3.*

## E/R/R Analysis: Convergence as the Decrease of a Defect

### Setup

Let us analyze the constructed system—L<sup>2</sup> convergence as a process of truncations—in terms of E/R/R. A reservation about the level: the “system of convergence” here is a substantive *interpretation* of the process $K\mapsto P_K$ and its finite theorems, not an object declared in the code as `System`. The analysis is a comprehension of the structure of the chapter and a reading of the headers of the supporting files,[^8] not an attribution of new claims to the code.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the rule of truncation: the partial sum $P_K=\sum_{k<K}c_k e_k$. Above it are the rules that sustain convergence: the error identity $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$, the monotone decrease of the error in $K$, the optimality of $P_K$ (best approximation), and the zero criterion (error $=0
\Leftrightarrow$ Parseval). The universal layer is L1–L5; the concrete one is the formula for the coefficients and the energy split.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. $P_K$ is the role-approximation (the best on $K$ directions). The tail energy
$\norm{f-P_K}^2$ is the role-defect of completeness. “Convergence” is the role-decrease of this defect. The completed series and the L<sup>2</sup> limit are a role-limit; pointwise convergence and Gibbs are roles of a different, pointwise layer, outside energy.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite and
rational: the coefficients $c_k\inℚ$, the partial sums $P_K$, the finite sums
$\sum_{k<K}$, the indices $K\le N$. Under P4 the completed infinite series is not an element: only finite truncations are actual; the limit is not actualized as a sum; what is actualized is the process toward it.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $P_K=\sum c_k e_k$; error $=\norm{f}^2-\sum c_k^2$; monotonicity; $P_K$ optimal; zero $\Leftrightarrow$ Parseval | HOW the process of truncations and its convergence are organized | Rules ($L5$) |
| $P_K$ as approximation; tail as defect; convergence as decrease; series/limit as limit; Dirichlet/Gibbs | WHAT FOR the bearers are significant; what is a different layer | Roles ($L4$) |
| $c_k\inℚ$; $P_K$; finite sums $\sum_{k<K}$; $K\le N$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component is in one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the system does not take as its element the completed infinite series. “Convergence” is not an attained state of a completed sum but the *role*-decrease of the defect, a property of the process of truncations; and the limit itself is a role-limit toward which the process moves without being actualized as a sum.

What the analysis yields. It translates the convergence of Fourier series into the language of structure: *the partial sum is a Role* (the best approximation), *convergence is a Rule-decrease* of the defect, and the coefficients and truncations are *Elements* (finite, rational). To take “the Fourier series converges to $f$” for an equality of two completed objects is to put a role-limit in the place of an Element, the same confusion of categories that guided Parts II and IV. And to confuse L<sup>2</sup> convergence with pointwise convergence (Dirichlet, Gibbs) is to mix the layer of energy with the layer of values: different roles, different bearers.

The next chapter applies this core: compression as truncation by significant coefficients with an error equal to the discarded energy; the fast Walsh transform as a process-algorithm equal to the matrix transform; and convolution—after which Part VII closes with a bridge to spectral methods and physics.

---

[^1]: The supporting files are `ProcessFourierSeriesL2.v` (6 statements, 0 axioms) and `ProcessBestApproximation.v` (9 statements, 0 axioms), both in the directory `src/process/`, on top of the L<sup>2</sup> apparatus of Part VI (`ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v`, `ProcessL2RieszFischer.v`). The names are in the notes below.
[^2]: The process reading of Riesz–Fischer is `l2_riesz_fischer` in `ProcessL2RieszFischer.v` (Part VI): the L<sup>2</sup> space of processes is Cauchy-complete by construction; this is a *bridge* to the bearer of the limit; see § “The Boundary: The Completed Series, Pointwise Convergence, Gibbs.”
[^3]: `fourier_error_eq` in `ProcessFourierSeriesL2.v`: $\norm{f-P_K}^2=\norm{f}^2-\texttt{captured}(c,K)$, where `captured`$(c,K)=\sum_{k<K}c_k^2$. A direct consequence of `resid_norm` (Part VI). 0 axioms.
[^4]: `fourier_error_nonneg`; equivalent to `bessel_general` (Chapter 7.1).
[^5]: `fourier_error_monotone`; it relies on the monotonicity of the captured energy (`captured_mono`, Chapter 7.5). 0 axioms.
[^6]: `fourier_partial_best` in `ProcessFourierSeriesL2.v` (the same as `best_approx_ge` from `ProcessBestApproximation.v`): $\norm{f-P_K}^2\le\norm{f-\sum_{k<K}a_k e_k}^2$ for any weights $a_k$; the uniqueness of the minimum is `best_approx_unique`. 0 axioms.
[^7]: `fourier_error_zero_iff`: $\norm{f-P_K}^2=0 \Leftrightarrow \sum_{k<K}c_k^2=\norm{f}^2$; it relies on the completeness criterion `parseval_iff_complete` (Chapter 7.1). 0 axioms.
[^8]: The headers: `ProcessFourierSeriesL2.v`—Rules: error $=\norm{f}^2-$ captured, monotone, zero $\Leftrightarrow$ Parseval; Roles: $P_K$ is an approximation, the tail is the completeness defect; $N\to\infty$ is marked as the P4 boundary. `ProcessBestApproximation.v`—Rules: $P_K$ is the unique minimum of the residual.

---

Part: [[07 Harmonic Analysis|Part VII. Harmonic Analysis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[03 Trigonometry and Complex Dft Where the Boundary Lies|Chapter 3. Trigonometry and the Complex DFT: Where the Boundary Lies]] · [[05 Compression Fast Transform Convolution|Chapter 5. Compression, Fast Transform, Convolution]] →
