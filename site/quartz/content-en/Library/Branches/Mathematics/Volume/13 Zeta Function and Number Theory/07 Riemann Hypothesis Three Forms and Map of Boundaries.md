---
title: "Chapter 7. The Riemann Hypothesis: Three Forms and the Map of Boundaries"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/07 Гипотеза Римана три формы и карта границ.md"
sourceBlob: b6f034c3be24aced1720929f3c5189ce448875b5
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Part XIII has traveled the path of analytic number theory from beginning to end. Chapter 13.1 gave the *primes* as finite, computable, constructive material: the uniqueness of factorization, the infinitude of primes, arithmetic functions. Chapters 13.2–13.3 built *zeta as a process* and the Euler product—the bridge “analysis ${}\leftrightarrow{}$ primes.” Chapter 13.4 gave the *functional equation* and the symmetry $s\leftrightarrow 1-s$; Chapter 13.5, the *zeros* in the critical strip; Chapter 13.6, the *explicit formula*, which linked the zeros and the primes.

What remains is the summit—**the Riemann Hypothesis**: all nontrivial zeros of zeta lie on the critical line $\Re s = 1/2$. This chapter does not solve RH (no one has solved it). It does what, in the spirit of ToS, is more honest and more useful: it *formalizes the formulation itself*—three equivalent forms of the hypothesis with machine-checked equivalence; it reads RH as a statement about a *fixed point* and connects it with the recurring fixed-point primitive of the whole volume; it formalizes the *obstacle*—why the method of the “squeeze” in principle does not reach the line; and, finally, it draws the **map of boundaries** of the whole of Part XIII, separating the proved core from the classical reading, the continuum price, and the openness of RH proper.

## The Three Forms of the Hypothesis and Their Equivalence

In our foundation a zero of zeta is not a point of a completed plane but a *process* (a Cauchy process $\rho:ℕ\toℂ$ over $ℚ$, in the spirit of “$ℝ={}$ process” of Part III). Over this representation the Riemann Hypothesis is written in three ways.

- **The zero form.** Every nontrivial zero lies on the critical line: 
$$
\texttt{RH\_zeros}:\quad \forall\rho,\ \text{nontrivial}(\rho)\Rightarrow \text{on\_line}(\rho).
$$

- **The process form.** The real part of every nontrivial zero converges to $1/2$: 
$$
\texttt{RH\_process}:\quad \forall\rho,\ \forall\varepsilon>0,\ \exists N,\ \forall n\ge N:\ |\Re\rho_n - \tfrac12| < \varepsilon.
$$

- **The fixed-point form.** The real part converges to its own reflection $1-\Re\rho$: 
$$
\texttt{RH\_fixed}:\quad \forall\rho,\ \forall\varepsilon>0,\ \exists N,\ \forall n\ge N:\ |\Re\rho_n - (1-\Re\rho_n)| < \varepsilon.
$$

These three forms are *machine-equivalent*. The zero form and the process form coincide by definition; the passage to the fixed-point form is a simple rescaling: $\Re - (1-\Re) = 2(\Re - \tfrac12)$, so that $| \cdot |<\varepsilon$ in one form is equivalent to $| \cdot |<\varepsilon$ in the other up to a factor of $2$.[^1]

$$
\boxed{\ \texttt{RH\_all\_equivalent}:\quad
  \texttt{RH\_zeros}\ \Longleftrightarrow\ \texttt{RH\_process}
  \ \wedge\ (\texttt{RH\_process}\Longleftrightarrow\texttt{RH\_fixed}).\ }
$$

Let us stress: what is machine-proved is the *equivalence of the formulations*, not the hypothesis itself. But this too has content—three different languages (the geometry of zeros, the convergence of a process, the fixed point of a symmetry) turn out to be one statement, and this is *proved without a single axiom*.

## RH as a Fixed Point: The Recurring Primitive of the Volume

The third form is no accident. The critical line $\Re s = 1/2$ is exactly the *fixed point* of the reflection $\sigma\mapsto 1-\sigma$:

$$
\sigma = 1-\sigma \iff \sigma = \tfrac12,
$$

and this is machine-checked (`re_fixed_point_half`). The complex reflection $s\mapsto 1-\bar s$ of the functional equation fixes exactly the line $\Re s = 1/2$ (`reflect_fixed_iff`). Hence RH is the statement “*all zeros lie on the fixed set of the constituting symmetry*,” and the form `RH_fixed` says literally: each zero is a fixed point of the reflection of the real part.

**The fixed-point primitive across the whole volume.**  The fixed point is one of the recurring structural primitives of the whole Theory of Systems. It has already been at work: the *Banach contraction* (`is_contraction`, `iterate_is_cauchy` in `FixedPoint.v`)—the engine of the convergence of reasoning and of iterations; *L5 resolution* (`l5_resolve_gen`)—the constituting “fixed choice” that removes indeterminacy; the *Cauchy completion* (Part III)—a point as a process whose tail is “fixed” up to $\varepsilon$; the *fixed field* of a Galois subgroup (Part XI). RH takes its place in this row: the critical line is the fixed set of the reflection.

**An honest reservation (and why RH is hard).**  But here the primitive behaves differently, and this is *proved*. In the cases of Banach and L5 the fixed point is an *attractor*: iteration converges to it because the map is a *contraction*. The reflection $s\mapsto 1-\bar s$, by contrast, is an *isometry*: it preserves distance (`reflect_isometry`), and therefore is *not* a contraction (`reflect_not_contraction_euclidean`); moreover, *no* metric in which the reflection is an isometry makes it contracting (`reflect_not_contractive_isometric`).[^2] The conclusion is honest and deep: the symmetry *fixes* the critical line as a fixed *set* but gives *no dynamics* that draws the zeros onto it. The very fixed-point device that solves other problems of the volume *provably does not work* here—and this is one of the reasons why RH resists.[^3]

## What Is Proved toward RH: The Squeeze and the Wall

The `src/zeta/` corpus formalizes not RH itself but the *scaffolding* around it—and, more importantly, the *boundary* of how far this scaffolding reaches.

**The squeeze.**  Two “walls” of zero-free regions squeeze the zeros toward the line: the left one (near $\Re=1$, from the Mertens identity and the pole) and the right one (near $\Re=0$, by the functional equation). Both are formalized (`left_wall`, `right_wall`, `squeeze`).

**The wall (the limit of the method).**  But the honest outcome of the squeeze is *negative* in the right sense. The current width of the zero-free region has the form $c/(1+|t|)$ and tends to $0$; therefore the boundary of the region reaches only $\Re\to 1$, and the gap to $1/2$ tends to $1/2$, *not* to $0$ (`rh_gap_approaches_half`, `gap_current_limit`). ToS formalizes this as a “wall”: for any constant $c$ the width $\to 0$ (`the_wall`, `wall_holds`), and a “breaker” (a width bounded away from zero) is *incompatible* with it—and this is machine-proved (`wall_vs_breaker`).[^4]

**Conditional RH.**  What is proved *positively* is a conditional statement: *if* all zeros are on the line, *then* the Li coefficients are nonnegative (`conditional_rh`); and every finite check at level $K$ passes (`p4_each_check_passes`). This is not RH—it is “everything agrees with RH at every computable step.”[^5]

**Openness—formalized.**  RH itself remains *open*, and in our system this is not a silence but a formal object: `rh_requires_gap_to_zero` is the predicate “the gap tends to $0$,” which is true exactly when RH is true and which has not been proved; and `wall_vs_breaker` proves that the current method of the squeeze *cannot* close it. What we have formalized is not a solution but the precise *form of not-knowing*.

## A Bridge to Physics: The Spectral Hypothesis

The most promising approach to RH is the *spectral* one, and it leads straight into physics. The Hilbert–Pólya conjecture: the nontrivial zeros are the eigenvalues of some *self-adjoint* operator; self-adjointness implies that the spectrum is real, and hence that the zeros lie on the critical line. Montgomery (1973) discovered that the pair correlation of the zeros coincides with the correlation of the eigenvalues of random Hermitian matrices (the GUE ensemble); Odlyzko’s numerical experiments confirmed this with striking precision for zeros of enormous index. Berry and Keating linked the zeros with the quantization of classical dynamics.

These are classical and hypothetical connections; in this volume they are *not formalized* and are given as motivation. But the direction coincides with ours: self-adjointness gives a *real* spectrum, which after the right renormalization should correspond to the zeros lying on the critical line—that is, the language of the fixed point and of self-adjointness is a bridge from arithmetic to physics. The spectral side is the subject of physics; here we only note that the form `RH_fixed` (zero ${}={}$ the fixed point of the reflection) and spectral reality are two dialects of one thought.

## The Map of Boundaries of Part XIII

Let us gather the status of the whole part by *tiers of strength*—this is the final honest summary for which §13.6.6 and every chapter have prepared.

- **Proved, 0 axioms** (at the level of separate rational, algebraic, and constructive lemmas). *Elementary number theory* (the layer `src/numbertheory/`, 9 files, 138 `Qed`, built and checked locally—to be synchronized with the main branch upon publication): the uniqueness of factorization, the infinitude of primes ($N!+1$), the functions $\varphi/\tau/\sigma/\mu$, the commutativity of Dirichlet convolution, Fermat’s little theorem, Euler’s theorem, the Chinese remainder theorem, the multiplicativity of $\varphi$. *The formulation of RH:* the equivalence of the three forms (`RH_all_equivalent`; the file `RH_Statement.v`, header “AXIOMS: none”—pure ℚ-algebra). *Rational cores of the analysis:* finite Euler products are nonzero, the trig inequality $2(1+x)^2\ge0$, the prime counters and the Chebyshev sum, the rationality of the Li coefficients, the log series, the crude estimate of the zero count, the exponentiated von Mangoldt function.
- **With `classic` (L3)—inherited through the Cauchy/zeta layer:** zeta as a Cauchy process; the Euler extension; the zeros of partial sums; the truncated explicit formula; the structure of the zeros; the geometry of the fixed point ($1/2$ as the fixed point of the reflection, `re_fixed_point_half`); the metric analysis of the reflection—an isometry, not a contraction (`reflect_isometry`, `reflect_not_contraction_euclidean`; `ContractionZeros.v`, header “classic (inherited)”); the squeeze and the limit of the method—the wall against the breaker (`squeeze`, `wall_vs_breaker`; the syntheses `rh_phase1_complete`, `rh_phase2_complete`, headers “1 axiom (classic)”); conditional RH (`conditional_rh`).
- **A lemma** (an axiom until June 2026): `functional_equation_structure` (`FunctionalEquation.v`): “if $\rho$ is a nontrivial zero, then its reflection $1-\rho$ is a nontrivial zero too,” where “nontrivial zero” is a formal predicate (a Cauchy process in the critical strip; it contains no condition that zeta vanishes). The analytic functional equation is a classical reading.
- **The continuum price (role-limit; not formalized as completed):** the full complex zeta and analytic continuation; the zeros of the completed zeta as objects; the existence of the process-limit; the actual $N(T)$ and the Riemann–von Mangoldt formula; the full explicit formula; the PNT; the spectral side (Hilbert–Pólya).
- **Open:** **the Riemann Hypothesis itself**—formalized exactly as `rh_requires_gap_to_zero` (the gap ${}\to0$); the wall (`the_wall`${}+{}$`wall_vs_breaker`) proves that the current method does not close it.

This ladder is the main result of Part XIII. We have not solved RH; we have built a rigorous framework around it and *precisely outlined* where the proved ends, where the classical reading begins, where the continuum price lies, and where the genuinely open is. The honesty of a boundary matters more than its extent.

*A remark on the precision of the tier.* Separate lemmas within `classic`-tier files (for example, `reflect_isometry`, `re_fixed_point_half`, `wall_vs_breaker`) are algebraically rational and do not use `classic` in the term itself; we assign them to the `classic` tier *conservatively*—by the status of the carrier file, without singling them out by a separate `Print Assumptions`. This is a deliberate *understatement* of strength, not an overstatement.

## E/R/R Analysis: The Riemann Hypothesis as a System

**Rules (L5).**  The constituting rule is the *reflection symmetry* $s\mapsto 1-\bar s$, whose fixed set *is* the critical line (`re_fixed_point_half`, `reflect_fixed_iff`), together with the *link zeros ${}\leftrightarrow{}$ primes* (the explicit formula, 13.6). RH is the rule “the zeros lie on the fixed line of the constituting symmetry.”

**Roles (L4).**  RH itself is a *role-statement* (an object of type Prop). The three forms (zeros / process / fixed point) are *role-equivalent* representations of one constraint (`RH_all_equivalent`). “A zero” is a role; “the critical line” is a role-target (the fixed set of the reflection but, as proved in §13.7.3, *not* an attractor of its dynamics); “the reflection” is a role-symmetry; “the gap” is a role-measure of the distance to the target.

**Elements (L1${}+{}$P4).**  Concrete computable data: the zeros of the partial sum $\zeta_N$, the nonnegative $\lambda_n^{(K)}$, the finite estimates of the squeeze at a given $|t|$, the passing of each conditional check—`conditional_rh`, `p4_each_check_passes`—*under the premise* that a finite list of zeros already lies on the line (this is the conditional tier, not a check of the actual zeros of $\zeta$). *Not* elements in the sense of a finite computable check: the completed set of the zeros of zeta, the process-limit, the truth-value of RH as a completed statement about all analytic zeros (the formula `RH_zeros` : Prop exists as an object of the language, but there is no proof of it).

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the reflection $s\mapsto 1-\bar s$ (line ${}={}$ fixed set); the link zeros ${}\leftrightarrow{}$ primes | the constitution “zeros on the fixed line” | Rule (L5) |
| RH ${}={}$ Prop-statement; three forms ${}={}$ one constraint; zero/line/reflection ${}={}$ roles | the status of the objects of the hypothesis | Role (L4) |
| zeros of $\zeta_N$; $\lambda_n^{(K)}\!\ge\!0$; finite estimates of the squeeze; conditional checks | computable bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes.**  RH is often presented as an isolated riddle about the zeros of a remote function. ToS reads it structurally: the rule is a symmetry whose line of fixed points is pinned down; the role is one constraint in three equivalent forms; the elements are finite computable checks, each of which passes *under the condition “zeros on the line”* (the conditional tier, not a check of the actual zeros of $\zeta$). The openness of RH is not a “hole” but a precisely localized gap between the *role* (the fixed line exists) and the *dynamics* (there is no contraction that draws the zeros onto it), and this gap is formalized.

## What Part XIII Has Prepared

Part XIII has gone from the *primes* (finite, constructive, 0-axiom material) through *zeta as a process* to *the Riemann Hypothesis as an open fixed point*. We have machine-built the elementary foundation of number theory; read zeta not as a completed object but as a process; formalized the formulation of RH in three equivalent forms and proved their equivalence without axioms; shown that the critical line is the fixed point of the reflection, and *proved* why the recurring fixed-point device does not draw the zeros in here; formalized the obstacle (the wall) and the precise form of not-knowing; and drawn the map of boundaries of the whole part.

The main result is honest: **we have not solved the Riemann Hypothesis, and we say so directly**—but we have formalized its framework, its equivalent forms, and the provable limit of the current method. The spectral side (Hilbert–Pólya, GUE) leads into *physics*, where the language of self-adjointness and the fixed point receives a physical body. With this, “Mathematics” as a process closes its conversation about numbers and passes to the next topic of the volume—carrying the same discipline: to build the proved core, to name the classical reading and the continuum price honestly, and not to pass off the open as solved.

---

[^1]: `src/zeta/RH_Statement.v` (8 `Qed`; its header says “AXIOMS: none”—pure ℚ-algebra over the definitions): `RH_zeros`, `RH_process`, `RH_fixed`; `RH_zeros_iff_process` (by definition), `RH_process_implies_fixed` and `RH_fixed_implies_process` (rescaling by $2$, through `Qabs_Qmult`); the result is `RH_all_equivalent`. Consequences: `RH_deviation_bound`, `critical_strip_width` (without RH the zeros are in any case in the strip $|\Re-\tfrac12|<\tfrac12$).
[^2]: `src/zeta/ContractionZeros.v` (its header says “AXIOMS: classic (inherited)”): `reflect_isometry` (the reflection preserves the $L^1$ distance), `reflect_not_contraction_euclidean` (hence not a contraction: on the pair $(0,0),(1,0)$ the distance does not decrease), `reflect_not_contractive_isometric` (an impossibility: no metric in which the reflection is an isometry makes it a contraction), `re_fixed_point_half` ($\sigma=1-\sigma\Leftrightarrow\sigma=\tfrac12$), `critical_line_minimizes_reflect_dist` (on the line the distance to the reflection is zero). It imports `FixedPoint.v`—the very Banach contraction whose inapplicability is proved here.
[^3]: The three regimes of the fixed point are brought together in one *0-axiom* taxonomy: `foundation/FixedPointTaxonomy.v` (8 Qed, 0 axioms, Stdlib-only)—*contraction* $r<1$ (`half_lipschitz`: factor $1/2$, a unique attracting point); *isometry* $r=1$ (`reflect_isometry` ${}+{}$ `reflect_not_contraction`: there is a fixed set, but it is *not* an attractor—the regime of RH); and the *absence* of a point altogether (`negb_no_fixpoint`); the capstone `fixed_point_taxonomy`. Here it is an abstract, self-contained analogue of the classic-tier `ContractionZeros.v` above. An observation/classification, not a new theorem; machine-checked.
[^4]: `src/zeta/RH_Phase1_Synthesis.v` (13 `Qed`, its header says “1 axiom (classic)”) and `RH_Phase2_Synthesis.v` (22 `Qed`, “1 axiom (classic)”): `left_wall`, `right_wall`, `squeeze`; the gap `rh_gap` and `rh_gap_approaches_half` (the gap $\to\tfrac12$, not to $0$); `the_wall`/`wall_holds`/`wall_vs_breaker` (the wall is incompatible with the breaker); the honest gap `rh_requires_gap_to_zero`—exactly what RH requires and what the method does not give. These syntheses inherit `classic` through the Cauchy formulation of zeta (`zeta_process_cauchy`).
[^5]: `src/zeta/RH_FinalAssessment.v` (16 `Qed`): rational cores with 0 axioms (`conditional_rh_proved`: on-line${}\Rightarrow{}$Li${}\ge0$; `proved_weil_li_equiv`: Weil-PSD ${}={}$ Li-nonnegativity; `proved_unbiased`: the mean of the migration ${}={}1/2$; variance bounds). The summaries that go through the convergence of zeta (`proved_zeta_converges`, `rh_grand_summary`, `tos_rh_verified`) inherit `classic`. Also defined is `the_honest_gap`—exactly what RH asserts and what is *not* proved.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/06 Von Mangoldt Explicit Formula|Chapter 6. Von Mangoldt’s Explicit Formula]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/01 Categories as Metasystems|Chapter 1. Categories as Metasystems—Part XIV]] →
