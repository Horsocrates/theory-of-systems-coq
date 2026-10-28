---
title: "Chapter 2. Shadow, Derivative, Integral: Calculus as One Operation st"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/19 Нестандартный анализ над процессами/02 Тень, производная, интеграл исчисление как одна операция st.md"
sourceBlob: feaf3cdb0eb623519d2a934d85bfbcf65b55e3ad
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

In the previous chapter the infinitesimal became the process $\delta=1/(n+1)$. Now comes the opposite operation: the *shadow*, the standard part $\st$, which returns from a process to a standard value. The whole of differential and integral calculus rests on it.

*The flagship of the chapter: the derivative and the integral are ONE operation, the shadow of an infinitesimal expression. $f'(x)=\st\big((f(x+\delta)-f(x))/\delta\big)$, $\int_0^1 f=\st\big(\sum_k f(k\delta) \delta\big)$. The increment $\delta$ is nonzero at every step—division and summation are legitimate; “$o=0$” is not a substitution of zero but the taking of the shadow at the end. This is how Berkeley’s paradox of the “ghosts of departed quantities” is laid open by machine.*

The shadow is a *partial* function: total and single-valued on convergent processes (the Element side), but undefined on bounded divergent ones (a role-limit—a choice of subsequence is needed). We begin with it.

## The Shadow: The Standard Part as a Partial Function

The standard part $\st(x)$ is the standard value to which the process $x$ is infinitely close. Where it exists, it is **unique**: two limits of one convergent process coincide—this is the L5 determinism of the shadow (mathematically, the ordinary uniqueness of the limit)[^1]. This is the Element side.

But the shadow is **partial**. The canonical witness is the oscillator $\mathrm{alt}(n)=(-1)^n$: $1,-1,1,-1,…$ It is *bounded* but *not Cauchy* and **has no shadow**[^2]. To assign it a shadow, one must CHOOSE which subsequence is the limit: “the evens are large”—shadow $+1$; “the odds are large”—shadow $-1$. Two incompatible values[^3]—there is no canon: the shadow is completed only by an external choice of tail (the even or the odd subsequence), and an ultrafilter is the global version of such a choice (a role-limit, Chapter 4).

*And here is the machine bridge to Chapter 1: $\mathrm{alt}=E-O$, the difference of the same indicators of the evens and the odds whose PRODUCT was a zero divisor[^4]. One undecided Evens/Odds split shows itself twice: additively, as an oscillator without a shadow; multiplicatively, as a zero divisor. The same boundary, two algebraic forms.*

## The Derivative through the Infinitesimal: Berkeley’s Paradox Laid Open

The derivative is the shadow of the difference quotient. Take $f(x)=x^2$. The increment $\delta$ is nonzero at every step, so division is legitimate (no $0/0$), and pointwise

$$
\frac{f(x+\delta)-f(x)}{\delta}=2x+\delta
$$

*exactly*—an identity of field algebra on the Element side[^5]. The remainder is exactly $\delta$; the shadow removes it, and $f'(x)=2x$ **exactly**[^6].

This is where Berkeley’s paradox is laid open. The classical charge against fluxions is that they divide by $o$ as by a nonzero quantity, THEN set $o=0$—a phantom of vanished quantities (Berkeley’s *ghosts of departed quantities*). There is no contradiction: $\delta$ is a process, at every step $\delta_n>0$ (we divide legitimately), and nowhere does it “become” zero; “$o=0$” is a separate operation, the taking of the *shadow* (the limit of the process). The ghost is $\delta_n$: nonzero at each step, vanishing only in the shadow.

The same device carries the cube through as well: from the identity $(f(x+\delta)-f(x))/\delta = 3x^2+3x\delta+\delta^2$ the remainder $3x\delta+\delta^2$ is bounded by $(3|x|+1) \delta$ and vanishes in the shadow, so that $f'(x^3)=3x^2$ **exactly**[^7]. And the finitization boundary: the limits $2x$ and $3x^2$ are *rational* for rational $x$, and the processes $2x+\delta_n$ and $3x^2+3x\delta_n+\delta_n^2$ converge INSIDE the Element side—on the checked powers ($1,x,x^2,x^3$) the boundary is not crossed. The general polynomial theorem is the next step; for nonpolynomial functions additional limit estimates arise (the general $x^n$ and transcendental $f$ are the horizon).

## The Integral Is the Shadow of a Hyperfinite Sum

The integral is the same shadow operation, only over a sum. The left Riemann sum for $f(x)=x$ with $n$ subintervals (step $1/n$—the same infinitesimal grid $\delta$ as the increment of the derivative; points $k/n$) is $\sum_{k<n}(k/n)(1/n)$. This is a *process of finite sums* (hyperfinite in the process reading), not a substituted formula; its closed form is expressed through Gauss’s sum $\sum_{k<n}k=n(n-1)/2$, proved over $ℕ$[^8]. Explicitly, the sum equals $\tfrac12-\tfrac{1}{2n}$ (the finite sum itself), and its *shadow* (the limit of the process) equals $\int_0^1 x=\tfrac12$ **exactly**[^9]: the grid $\delta$ is nowhere zero (we summed legitimately), $\tfrac12$ is reached only in the shadow, and the remainder $\tfrac{1}{2n}$ vanishes.

*Here is the heart of nonstandard analysis: $\int=\st\!\big(\sum f(k\delta) \delta\big)$ and $f'=\st\!\big(\Delta f/\delta\big)$—BOTH halves of the calculus are one operation $\st$ over processes with an infinitesimal $\delta$. And again the Element: the limits $\tfrac12$ and $\tfrac13$ are rational—integrating the checked powers does not cross the boundary.*

By the same device $\int_0^1 x^2=\tfrac13$ is also closed by machine (through $6\sum k^2=n(n-1)(2n-1)$: the sum is $\tfrac13-\tfrac1{2n}+\tfrac1{6n^2}$, the shadow $=\tfrac13$)[^10]. The general $\int_0^1 x^n=\tfrac1{n+1}$ (Faulhaber/Bernoulli sums) and the integral of an arbitrary smooth function remain the horizon—the arena of the Riemann theory of the integral.

## E/R/R Analysis: Calculus as a Shadow

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the shadow $\st$: single-valued where it exists (L5 determinism); $\delta\neq 0$ at every step makes division and summation legitimate; the difference quotient and the Riemann sum are *exact* identities (the derivative plus remainder $\cdot\delta$; the closed form through Gauss’s sum), and the shadow removes the remainder. One operation $\st$ generates both halves of analysis.

**Roles (L4).** $\delta$ has the role of the increment and the grid (infinitesimal, nonzero); the difference quotient, the role of the slope of the secant; the Riemann sum, the role of the approximation of area; $\st$, the role of the shadow; the derivative and the integral are the tangent and the area as shadows.

**Elements (L1 + P4).** The bearers are processes $ℕ\toℚ$: $\delta_n=1/(n+1)$, the difference quotients $2x+\delta_n$, the partial sums $\tfrac12-\tfrac{1}{2n}$. They are finitely actual at every stage; the shadow is not a term of the process but its limit.

**Well-formedness check.** The rule is the shadow and the exact identities; the roles are the increment, the slope, the area, the shadow; the elements are rational processes; there are no overlaps. The oscillator $\mathrm{alt}$ is an element as a system: the values $\pm 1$ alternate, the role is the oscillator, while the value of the shadow is *not determined internally* $\Rightarrow$ the system is incomplete $\Rightarrow$ an external choice is needed (a role-limit).

**What the analysis yields.** It reduces the calculus to one shadow operation over the infinitesimal and names where it remains on the Element side (polynomials: the limits $2x$ and $\tfrac12$ are rational) and where the role-limit begins (the shadow of a bounded divergent process requires a choice of subsequence). And it connects the additive form of the gap (an oscillator without a shadow) with the multiplicative one (the zero divisor of Chapter 1): one Evens/Odds split.

From this split the next chapter extracts the common root: one undecided distinction generates *three* algebraic forms—a zero divisor, an oscillator without a shadow, and non-invertibility. The ring of germs is not a field, and there is exactly one reason for this.

---

[^1]: `shadow_unique`: `converges` $x L_1$ and `converges` $x L_2$ imply $L_1=L_2$; convergence is taken two-sidedly ($-\varepsilon<x_n-L<\varepsilon$), purely linearly. Constants converge to themselves and have a shadow (`const_has_shadow`). In `StandardPart`. Machine-checked, 0 axioms.
[^2]: `alt_bounded`, `alt_not_cauchy`, `no_shadow_for_alt`: $\mathrm{alt}$ is bounded ($|\cdot|\le 1$), but neighboring terms differ by $2$, and a supposed shadow $L$ would have to lie near $+1$ and near $-1$ at once—a contradiction. In `StandardPart`. Machine-checked, 0 axioms.
[^3]: `alt_shadow_mod_evens` (shadow $=1$) and `alt_shadow_mod_odds` (shadow $=-1$). In `StandardPart`. Machine-checked, 0 axioms.
[^4]: `alt_decomp`: $\mathrm{alt}_n=E_n-O_n$. In `StandardPart`. Machine-checked, 0 axioms.
[^5]: `dq_sq`: $\mathrm{diffquot} f_{\mathrm{sq}} x n = 2x+\delta_n$, given $\delta_n\neq 0$ (`delta_nonzero`). In `DerivativeViaInfinitesimal`. Machine-checked, 0 axioms.
[^6]: `deriv_sq` (the flagship): `converges`$(\mathrm{diffquot} f_{\mathrm{sq}} x) (2x)$; plus $f'(x)=1$ (`deriv_id`) and $f'(c)=0$ (`deriv_const`). The summary theorem `derivative_summary`. Machine-checked, 15 Qed, 0 axioms.
[^7]: `dq_cube` (the exact identity) and `deriv_cube`: $f'(x^3)=3x^2$ through the shadow, the remainder estimated through $Q_{\mathrm{abs}}$. In `DerivativeViaInfinitesimal`. Machine-checked, 0 axioms.
[^8]: `rsumlin_closed` (the termwise sum in closed form, not a substituted formula) and `sumk_closed_Q` ($2\sum k=n(n-1)$). In `HyperfiniteSum`. Machine-checked, 0 axioms.
[^9]: `integral_x_closed` ($=\tfrac12-\tfrac12\cdot\tfrac1n$) and `integral_x_converges` ($\int_0^1 x=\tfrac12$). The summary theorem `hyperfinite_sum_summary`. Machine-checked, 16 Qed, 0 axioms.
[^10]: `rsumquad_closed`, `sumk2_closed_Q`, `integral_xsq_converges` (in `HyperfiniteSum`). Machine-checked, 0 axioms.

---

Part: [[19 Nonstandard Analysis over Processes|Part XIX. Nonstandard Analysis over Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/01 Infinitesimal as Process|Chapter 1. The Infinitesimal as a Process]] · [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/03 A Ring Not a Field One Gap Three Forms|Chapter 3. A Ring, Not a Field: One Gap, Three Forms]] →
