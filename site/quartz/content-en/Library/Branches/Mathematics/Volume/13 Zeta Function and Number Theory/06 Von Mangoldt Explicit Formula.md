---
title: "Chapter 6. Von Mangoldt’s Explicit Formula"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/06 Явная формула фон Мангольдта.md"
sourceBlob: 4bd7410cf58a8e0d1c2810137e46216386dedef7
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 13.5 gave the zeros of zeta; Chapter 13.1, the primes. This chapter joins them by the explicit formula—the mathematical heart of analytic number theory, which says: *the distribution of primes is linear growth minus the oscillations set by the zeros of zeta*. The bridge is the von Mangoldt function.

**The von Mangoldt function.**  Classically

$$
\Lambda(n) = \begin{cases} \log p, & n=p^{k}\ (p\text{ prime},\ k\ge 1),\\ 0, & \text{otherwise.}\end{cases}
$$

For example, $\Lambda(2)=\log 2$, $\Lambda(4)=\log 2$ (since $4=2^2$), $\Lambda(6)=0$, $\Lambda(9)=\log 3$. This function “concentrates” the primes: it is nonzero exactly on prime powers.

**What is machine-checked.**  The logarithm is not directly available over $ℚ$, so our arithmetic base formalizes a *multiplicative* version—$\Lambda_{\exp}(n)$, equal to $p$ for $n=p^{k}$ and to $1$ otherwise (this is $e^{\Lambda(n)}$, but without recourse to the actual exponential). The main thing is the identity

$$
\prod_{d\mid n}\Lambda_{\exp}(d) = n,
$$

which is exactly the multiplicative (exponentiated) form of the classical $\sum_{d\mid n}\Lambda(d)=\log n$.[^1]

## The Summatory Function $\psi(x)$

The summatory von Mangoldt function is

$$
\psi(x) = \sum_{n\le x}\Lambda(n) = \sum_{p^{k}\le x}\log p.
$$

*The link to the PNT.* The prime number theorem is equivalent to $\psi(x)\sim x$ as $x\to\infty$—the “logarithmic count of primes” is asymptotically equal to $x$. This is the form of the PNT convenient for analysis.

In the repository the rational side of counting primes is machine-checked: the prime counter $\texttt{prime\_count} N=| \text{sieve up to }N |$ and the Chebyshev sum $\texttt{chebyshev\_theta} N=
\sum_{p\le N}\log_{\text{approx}}(p)$.[^2]
$\psi(x)\sim x$ itself (and with it the PNT) is *not proved* in this volume—we have rational counters and a link to the zeros at our disposal, and we leave the full asymptotics classical.

## The Logarithmic Derivative of Zeta

The link between zeta and $\Lambda$ is given by the logarithmic derivative:

$$
-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n\ge 1}\frac{\Lambda(n)}{n^{s}}\quad(\Re s>1).
$$

This is a Dirichlet series with coefficients $\Lambda(n)$—a direct link between zeta and the von Mangoldt function. It is derived by taking the logarithm of the Euler product (Chapter 13.3):

$$
\log\zeta(s) = -\sum_{p}\log(1-p^{-s}) = \sum_{p}\sum_{m\ge 1}\frac{p^{-ms}}{m},
$$

and differentiating.

In ToS the *rational* side of taking the logarithm of the Euler product is machine-checked: the finite partial sums of the series $\sum_{m\ge 1}\frac{x^{m}}{m}$ (which classically represents $\log\frac{1}{1-x}$) and of the sums $\sum_p\sum_m p^{-ms}/m$, with positivity and monotonicity.[^3]

## Von Mangoldt’s Explicit Formula

The classical analytic formula reads:

$$
\psi(x) = x - \sum_{\rho}\frac{x^{\rho}}{\rho} - \log(2\pi) - \tfrac12\log\bigl(1-x^{-2}\bigr),
$$

where the sum runs over all nontrivial zeros $\rho$ of zeta (with the symmetrization $\rho\to\bar\rho$). The formula is striking: it says directly

$$
\text{“distribution of primes”} = \text{“linear growth } x\text{”} - \text{“oscillations from the zeros of zeta”}.
$$

The main term $x$ gives $\psi(x)\sim x$ (the PNT); each zero $\rho$ contributes an oscillatory term $-x^{\rho}/\rho$.

In ToS a *truncated, computable* form of the explicit formula is formalized: at each level $K$ the sum of the contributions of the zeros is finite, rational, and computable.[^4] This is the operational essence: we read the explicit formula as a *process* of approximation—a finite sum of the contributions of the zeros up to level $K$, not as a completed summation over all $\rho$.

## The Geometric Interpretation: The Zeros Govern the Deviations

The zeros of zeta “govern” the deviations of the distribution of primes from the average. If the Riemann Hypothesis is true (all zeros on $\Re s=1/2$):

- the oscillatory terms have $|x^{\rho}|=x^{1/2}$;
- their sum is of order $x^{1/2}\log x$ (after symmetrization);
- hence $\psi(x)=x+O\bigl(x^{1/2}\log x\bigr)$—the optimal bound for the error term in the PNT.

If, however, RH fails (there is a zero with $\Re\sigma>1/2$), the corresponding term has $|x^{\rho}|=x^{\sigma}>
x^{1/2}$, and the bound for the error term worsens. In other words,

> **The Riemann Hypothesis ${}={}$ the optimal asymptotics of the prime numbers.**

This is a classical reading (we do not prove it): the link between the position of the zeros and the precision of the PNT. Operationally what matters is that the *mechanism* is transparent—the closer the zeros are to the critical line, the smaller the oscillations; the explicit formula makes “zeros ${}\leftrightarrow{}$ primes” an explicit dependence, not a mystery.

## What Is Proved: An Honest Summary by Tiers

Let us gather the status of the formalization of Part XIII by *tiers of strength* (this is a foretaste of the map of boundaries of 13.7):

- **Proved, 0 axioms** (rational/algebraic/counting cores): the definitions of the partial sums of zeta and the rational telescoping estimates; the finite Euler layer; the log expansion (`LogZeta`); the algebraic trig inequality $2(1+x)^2\ge 0$ over $ℚ$; the rational core of the zero-free region; the crude estimate of the zero count; the prime counters and the Chebyshev sum (`PrimeSumBounds`); the exponentiated von Mangoldt function and the identity $\prod_{d\mid n}\Lambda_{\exp}(d)=n$ (a new layer, local).
- **With `classic` (L3):** the Cauchy formulation of the zeta/Euler process; the truncated explicit formula (`ExplicitFormula`); the syntheses of the zero-free region and of phases 1/2.
- **A lemma:** the symmetry of the formal predicate of a zero under reflection (`functional_equation_structure`); the analytic equation belongs to the classical reading.
- **A classical reading (not formalized as completed):** the full complex zeta and analytic continuation; the full Euler and logarithmic complex layer; the de la Vallée Poussin region; the actual $N(T)$ and the Riemann–von Mangoldt formula; the full explicit formula; the PNT; the Riemann Hypothesis itself.

The `src/zeta/` corpus is an impressive volume of formalization of analytic number theory (exact counts per the current build accounting); but honesty matters more than volume: we strictly separate the proved core and the classical reading.

## E/R/R Analysis: The $\Lambda$-Selector and the Formula-Link

**Rules (L5).**  The constituting rules are the *selection of prime powers* (the function $\Lambda$ is nonzero only on $p^k$; machine-checked is its exponentiated form with the identity $\prod_{d\mid n}\Lambda_{\exp}(d)=n$) and the *link zeros ${}\leftrightarrow{}$ primes* (the explicit formula: $\psi(x)=x-\sum_\rho x^\rho/\rho$). Taking the logarithm of the Euler product is the rule of transition from the primes to the Dirichlet series with $\Lambda$.

**Roles (L4).**  “$\Lambda$” is a *role-selector* (it isolates the prime-power skeleton of a number); “$\psi(x)$” is a *role-counter* (the logarithmic weight of the primes up to $x$); “the contribution of a zero $x^{\rho}/\rho$” is a *role-oscillation*; “the explicit formula” is a *role-link* between the zeros and the primes.

**Elements (L1${}+{}$P4).**  Concrete data: the values $\Lambda_{\exp}(n)$, the products $\prod_{d\mid n}\Lambda_{\exp}(d)$, the rational $\texttt{chebyshev\_theta} N$, the truncated $\texttt{explicit\_formula\_level} (K,x)$. *Not* elements: the completed sum over all zeros, the full analytic $\psi(x)$, the series $-\zeta'/\zeta$ as a complex object.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the selection of $p^k$ ($\Lambda_{\exp}$, $\prod_{d\mid n}\Lambda_{\exp}(d)=n$); the link of the explicit formula | the constitution of the link zeros ${}\leftrightarrow{}$ primes | Rule (L5) |
| $\Lambda={}$ selector; $\psi={}$ counter; $x^{\rho}/\rho={}$ oscillation; formula ${}={}$ link | the status of objects in the link | Role (L4) |
| $\Lambda_{\exp}(n)$; `chebyshev_theta`; `explicit_formula_level` | the bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes.**  The explicit formula often sounds like a mysterious link: “how do the zeros know about the primes?” ToS reads it as a *rule-link* whose rational core (the selection of prime powers, the truncated contributions) is machine-checkable, while the full analytic form honestly remains a classical reading. The function $\Lambda$, moreover, is not a magical coefficient but a selector of the prime-power skeleton, growing directly out of the factorization of Chapter 13.1.

## What the Chapter Has Prepared

The von Mangoldt function has been read as a *selector* of prime powers (machine-checked is its exponentiated form with the identity $\prod_{d\mid n}\Lambda_{\exp}(d)=n$, a direct bridge to the factorization of 13.1); the explicit formula, as a *rule-link* of the zeros and the primes, whose rational truncated core is formalized, while the full analysis is left classical. The status of the whole part has been gathered by tiers.

Next comes Chapter 13.7: three equivalent forms of the Riemann Hypothesis, their machine-checked equivalence, and the map of boundaries of the part, which finally separates the proved core, the classical reading, the continuum price, and the openness of RH.

---

[^1]: The new layer `src/numbertheory/VonMangoldt.v`: `Lambda_exp` ($=p$ for $n=p^k$, otherwise $1$), `mangoldt_prod`, `psi_exp`, and `mangoldt_identity_upto_20`—the identity $\prod_{d\mid n}\Lambda_{\exp}(d)=n$ for all $n\le 20$ (0 axioms, by `Print Assumptions`). This connects the arithmetic base of Chapter 13.1 (divisors, factorization) with the analytic formula below. *A reservation about reproducibility:* the layer `src/numbertheory/` has not yet entered the main branch—it is built and checked locally (it is included in `_CoqProject`); the classical *additive* $\Lambda$ with $\log p$ is, meanwhile, the standard mathematical reading, while what is machine-checked is its exponentiated form.
[^2]: `src/zeta/PrimeSumBounds.v` (0 axioms beyond the inherited ones): $\texttt{prime\_count} N=|\texttt{sieve} N|$ (for example, `prime_count 3`${}=2$, `prime_count 6`${}=3$), $\texttt{prime\_recip} N=\sum_{p\le N}1/p$, and $\texttt{chebyshev\_theta} N=\sum_{p\le N}\texttt{log\_approx}(p)$—which corresponds to $\theta(x)=\sum_{p\le x}\log p$ (over the *primes*), *not* to the full $\psi(x)=\sum_{p^k\le x}\log p$ (over prime *powers*). These are rational/integer sums; the asymptotics $\psi(x)\sim x$ (that is, the PNT) is a classical result not proved here.
[^3]: `src/zeta/LogZeta.v` (its header says “AXIOMS: none,” 0 axioms): `log_series_term`, `log_series_partial`, `prime_power_sum`, `log_zeta_approx`—rational partial sums of the series that classically represents $\log(1/(1-x))$, with nonnegativity and monotonicity (there is no actual `log` function in the file). The passage to the *complex* formula $-\zeta'(s)/\zeta(s)=\sum_n\Lambda(n)/n^s$ requires differentiation, the complex logarithm, and the additive $\Lambda$—this is the classical analytic layer, not formalized here.
[^4]: `src/zeta/ExplicitFormula.v` (its header: “AXIOMS: classic, inherited from ZetaProcess”): `zero_contribution`$(\beta,x)$ is the rational contribution $x^{\beta}$, `explicit_formula_level`$(K,x)$ is the truncation of the explicit formula at level $K$ (computable: `explicit_formula_computable`), `pole_correction`, `explicit_formula_step`. This is a *truncated process* variant, inheriting `classic`; the full classical explicit formula $\psi(x)=x-\sum_\rho x^\rho/\rho-\dots$ is an analytic reading on top of it.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/05 Zeta Zeros and the Zero Free Region|Chapter 5. The Zeros of Zeta and the Zero-Free Region]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/07 Riemann Hypothesis Three Forms and Map of Boundaries|Chapter 7. The Riemann Hypothesis: Three Forms and the Map of Boundaries]] →
