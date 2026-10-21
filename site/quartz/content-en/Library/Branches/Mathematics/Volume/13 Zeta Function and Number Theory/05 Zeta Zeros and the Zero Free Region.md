---
title: "Chapter 5. The Zeros of Zeta and the Zero-Free Region"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/05 Нули дзеты и свободная от нулей зона.md"
sourceBlob: 51cda6c8ceec6ab70dd64f8148db47d1de4fb7da
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 13.4 showed that the nontrivial zeros of zeta live in the critical strip $0<\Re s<1$ and are symmetric about the line $\Re s=1/2$. This chapter introduces the main technical tool of analytic number theory—the *zero-free region*—and its machine-checkable core. And here it is especially important to keep the cut: the repository proves *rational and algebraic* pieces (identities, estimates, counting processes—all with 0 axioms), while the full *complex-analytic* theorems (the de la Vallée Poussin region, the Riemann–von Mangoldt asymptotics) remain a classical reading.

**A zero as a process.**  In ToS a zero of zeta is not a point of a completed set but a *process*: a complex Cauchy sequence $\rho\colonℕ\to\mathbb{TC}$ whose value converges to zero. Nontriviality and position are fixed by predicates over such a process.[^1] The known small zeros—$\rho_1\approx\tfrac12+14{,}13 i$, $\rho_2\approx\tfrac12+21{,}02 i,…$—are *numerical* data (huge initial ranges have been checked, all on the critical line); they enter the repository as a landmark, not as machine-constructed objects.

## The Zero-Free Region

A *zero-free region* is a region guaranteed to contain no zeros. The classical region of de la Vallée Poussin (1899):

$$
\Re s \;>\; 1 - \frac{c}{\log|\Im s|}
$$

for some $c>0$: the zeros recede from the line $\Re s=1$ at the rate $O(1/\log|t|)$.

What is *machine-checked* is the *rational* core of the mechanism “the pole repels the zeros from $\Re s=1$”: the Mertens combination and the lower estimate through the pole, with explicit rational bounds.[^2]

## The Trigonometric Inequality: The Algebraic Core

The main tool in the proof of the classical zero-free region is the inequality

$$
3 + 4\cos\theta + \cos 2\theta \;\ge\; 0\quad\text{for all }\theta.
$$

It is proved *algebraically*, without any analysis: substituting $\cos 2\theta=2\cos^2\theta-1$,

$$
3 + 4\cos\theta + 2\cos^2\theta - 1 \;=\; 2 + 4\cos\theta + 2\cos^2\theta \;=\; 2(1+\cos\theta)^2 \;\ge\; 0.
$$

In ToS this is precisely the machine-checked core—and in the most honest form: the inequality is proved as an *algebraic identity over $ℚ$* for *any* rational $x$ playing the role of a “cosine proxy,” not as a statement about the real $\cos\theta$.[^3]

**How this locks out the zeros.**  For $s=\sigma+it$ the inequality (through the Dirichlet series for the logarithm of zeta) implies

$$
3\log|\zeta(\sigma)| + 4\log|\zeta(\sigma+it)| + \log|\zeta(\sigma+2it)| \;\ge\; 0.
$$

Were $\zeta(\sigma+it)=0$, the middle term would go off to $-\infty$; but the first term $3\log|\zeta(\sigma)|$, as $\sigma\to 1$, grows because of the pole more slowly than the middle term falls—and in a suitable region this gives a contradiction. This *assembly* (the combination of the inequality, the pole, and the estimates) is formalized at the rational level in the synthesis.[^4]

## The Zero-Counting Function $N(T)$

How many zeros lie in a horizontal strip of height $T$? The classical Riemann–von Mangoldt formula:

$$
N(T) \;=\; \frac{T}{2\pi}\log\frac{T}{2\pi e} + O(\log T),
$$

that is, the number of zeros grows roughly like $(T\log T)/(2\pi)$.

In ToS the counting of zeros is a *role-counter*: for each finite $T$ it is a concrete rational bound, not a property of a completed “set of all zeros.” Machine-checked is a *crude* rational control estimate $K\cdot(T+1)$—nonnegative, positive at a nonzero level, and monotone.[^5] This allows one to work with the zeros *algorithmically*: even if “the set of all zeros” is not a completed object, the control estimate gives a concrete number for each $T$.

## Properties of the Region and Progress toward the Riemann Hypothesis

The zero-free region is a ladder toward the Riemann Hypothesis:

- the classical region (de la Vallée Poussin): $\Re s>1-c/\log|t|$—proved classically;
- the Korobov–Vinogradov region (1958): wider than the classical one—proved classically;
- the hypothetical region under RH: $\Re s>1/2$—equivalent to the Riemann Hypothesis.

Progress in widening the zero-free region is progress in the direction of RH; this is an active field. In ToS the rational core is machine-checked (the trig inequality, the pole estimate, the counting process), while the regions themselves in their full complex form are a classical reading on top of this core. In addition, a *process framework* is set up for the zeros of the truncated $\zeta_N$: perturbations, a crude counter, the geometry of the reflection, and the fixed critical line; the formulation about *migration* toward $\Re s=1/2$ is a mathematical/process reading, not a theorem about all the zeros of $\zeta_N$.[^6]

## E/R/R Analysis: Zero-Process, Region-Rule, Counter-Role

**Rules (L5).**  The constituting rules are the *inequality* (the algebraic identity $2(1+x)^2\ge 0$ over $ℚ$, which locks the zeros out of the neighborhood of $\Re s=1$) and the *pole estimate*: the growing gap between $k=1$ (divergence) and $k\ge 2$ (`pole_large`, `gap_unbounded`)—a rational surrogate of the analytic idea that the pole repels the zeros from $\Re s=1$. Together they give the rational core of the rule of the zero-free region.

**Roles (L4).**  “A zero” is a *role-process* (a Cauchy sequence converging to zero); “the zero-free region” is a *role-region* (where the rule admits no zeros); “$N(T)$” is a *role-counter* (a concrete number at each finite level); “the migration of the zeros of $\zeta_N$” is a *role-squeeze* toward the critical line.

**Elements (L1${}+{}$P4).**  Concrete data: the rational values
`mertens_f`$(x)$ and `double_angle_form`$(x)$, the rational pole estimates `pole_lower_bound`, the rational counting estimates `zero_count_bound`$(K,T)$. *Not* elements: the completed set of all zeros, the full complex zero-free region, the asymptotics of $N(T)$ as a ready equality.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the algebraic inequality $2(1+x)^2\ge 0$; the pole estimate | the exclusion of zeros near $\Re s=1$ | Rule (L5) |
| zero ${}={}$ process; zone ${}={}$ region; $N(T)$ ${}={}$ counter; migration ${}={}$ squeeze | the status of special points and of their distribution | Role (L4) |
| rational `mertens_f`, `pole_lower_bound`, `zero_count_bound` | the bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes.**  The “trigonometric” inequality that locks out the zeros turns out to be *not* an analytic fact but an *algebraic identity over $ℚ$*—maximally transparent and machine-checkable. The counting of zeros is not a property of a completed infinity but a rational estimate at each finite level. ToS singles out precisely the finite rational core of the theory of zeros, honestly leaving the full complex analysis as a classical reading.

## What the Chapter Has Prepared

{
The zeros have been read as processes; the zero-free region as a rule. The rational core is sorted by status: `TrigInequality.v` (the algebraic $2(1+x)^2\ge 0$ over $ℚ$), `ZeroFreeRegion.v` (the pole estimate, the model width $c/(1+|t|)$), and `ZeroCountingProcess.v` (the crude counting estimate $K(T+1)$) are *0 axioms*; the synthesis `RH_Phase1_Synthesis.v` and the layer `PartialSumZeros.v` inherit `classic`. The full complex region of de la Vallée Poussin $1-c/\log|t|$ and the Riemann–von Mangoldt asymptotics are honestly left classical.}

Next:

- Chapter 13.6—the logarithmic derivative of zeta and von Mangoldt’s explicit formula, which links the zeros with the distribution of primes (where the von Mangoldt layer of our arithmetic base meshes with the analysis);
- Chapter 13.7—three equivalent forms of the Riemann Hypothesis (the “process” form directly uses the zero-process of this chapter) and the map of boundaries of the part, which gathers the continuum price, the axiom tier, and the openness of RH.

---

[^1]: `src/zeta/ZetaZeros.v`: `CauchyComplex`${}={}ℕ\to{}$`TComplex`, the predicates `in_critical_strip`, `is_nontrivial_zero`, `on_critical_line`; a zero is a Cauchy process converging to the zero value (`nontrivial_zero_cauchy`).
[^2]: `src/zeta/ZeroFreeRegion.v` (its header says “AXIOMS: none,” 0 axioms): `pole_lower_bound`, `pole_lower_bound_nonneg`, `pole_lower_bound_monotone`, and `pole_large`—a lower estimate of the “pole” contribution, expressing the repulsion of the zeros from $\Re s=1$ at the rational/process level; also `mertens_combination`, `gap_unbounded`, `integer_zero_free`, and the *model* width $`dvp_width`=c/(1+|t|)$ with $`dvp_boundary`=1-`dvp_width`\to 1$. *Important:* $c/(1+|t|)$ is a rational surrogate, *not* the classical width $c/\log|t|$. The full *complex* region of de la Vallée Poussin $\Re s>1-c/\log|t|$ is a classical result; the file formalizes its rational, estimating side.
[^3]: `src/zeta/TrigInequality.v` (its header: 0 axioms; and directly: “Over Q: we prove this for ALL rational $x$, not just $\cos\theta$”). Here `mertens_f`$(x)=2(1+x)^2$ (the Mertens combination after the substitution $\cos 2\theta\to{}$`double_angle_form`$(x)=2x^2-1$), and `mertens_f_nonneg`: $`mertens_f`(x)\ge 0$ for all rational $x$; and `mertens_f_positive`: $`mertens_f`(x)>0$ for $x\ne -1$ (with a zero only at $x=-1$, `mertens_f_zero_iff`); `trig_inequality_algebraic`, `trig_inequality_double_angle`. The trigonometric reading ($x=\cos\theta$) is the classical interpretation of a rational algebraic lemma.
[^4]: `src/zeta/RH_Phase1_Synthesis.v`: the assembly of the zero-free region from the trig inequality, the pole estimate (`pole_large`), and the Mertens “squeeze”—at the rational/process level (it inherits `classic`). The full analytic form with the complex logarithm of zeta is classical.
[^5]: `src/zeta/ZeroCountingProcess.v` (its header says “AXIOMS: none,” 0 axioms): $`zero_count_bound` K T := K\cdot(T+1)$ is a *crude linear* estimate (with `zero_count_bound_nonneg`, `_pos`, `_mono_K`), *not* the Riemann–von Mangoldt formula. The full asymptotics $N(T)\sim(T\log T)/(2\pi)$ is a classical result. The file also introduces the process formulation `rh_zero_variance` and proves basic consequences (`rh_implies_no_deviation`)—this is *not* a proof of RH and not a full equivalence for the analytic zeros.
[^6]: `src/zeta/PartialSumZeros.v`: the gap at $k=2$, interval estimates, a crude count, the decay of the perturbation, the fixed critical line, `zero_squeeze`, the reflection distance; it inherits `classic`. This is a process framework, not a proof of the migration of all the zeros of $\zeta_N$ to the line.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/04 Functional Equation|Chapter 4. The Functional Equation]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/06 Von Mangoldt Explicit Formula|Chapter 6. Von Mangoldt’s Explicit Formula]] →
