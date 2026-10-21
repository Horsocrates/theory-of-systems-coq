---
title: "Chapter 4. The Functional Equation"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/04 Функциональное уравнение.md"
sourceBlob: 74de0c3112fd35636a0914c487712ce1009f9f2e
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 13.3 drove all the “interesting” zeros of zeta into the critical strip $0<\Re s<1$. This chapter explains *why* the strip is symmetric and why its axis is the line $\Re s=1/2$. The source is Riemann’s *functional equation*, which links the values of zeta at $s$ and at $1-s$:

$$
\zeta(s) \;=\; 2^{s} \pi^{s-1} \sin\!\Bigl(\frac{\pi s}{2}\Bigr) \Gamma(1-s) \zeta(1-s),
$$

or, in symmetric form with the *full* zeta $\xi(s)=\tfrac12 s(s-1) \pi^{-s/2}\Gamma(s/2) \zeta(s)$,

$$
\xi(s) \;=\; \xi(1-s).
$$

We use the notation $\xi(s)$ as a *role-designation* of the symmetric continued process, and *not* as a constructed completed analytic object (its full construction is the continuum boundary of the part, 13.7). And this symmetry itself is a property of the already *continued* zeta: in the region of convergence ($\Re s>1$, Chapter 13.2) and on the Euler layer (Chapter 13.3) it is not yet visible—it appears only after analytic continuation.

**Status (important, so we state it at once).** In our formal layer the functional equation *itself* is *accepted as one mathematical axiom*, not derived: this is the honest *axiom tier* of Part XIII (its place in the map of boundaries is 13.7). In other words, this chapter does *not prove* the analytic functional equation $\xi(s)=\xi(1-s)$ (for that one needs the $\Gamma$ factor, complex analysis, and continuation)—it formalizes its *reflection structure*. What is machine-checked is what *follows structurally* from this symmetry: the *reflection* $s\mapsto 1-s$, its fixed points (the line $\Re s=1/2$), and the structure of the quadruple of zeros; and separately, the equivalence of the three forms of the Riemann Hypothesis (Chapter 13.7). The *truth-value* of the Riemann Hypothesis itself remains open.[^1]

## The Reflection $s\mapsto 1-s$ and the Critical Line

What is *proved* in the repository is the geometry of the reflection itself. The transformation

$$
\text{reflect}\colon s \longmapsto 1-s
$$

is the reflection of the complex plane in the line $\Re s=1/2$. Its basic properties are machine-checked: it is involutive (applying it twice returns the original point), it acts on the coordinates as $\Re(\text{reflect} s)=1-\Re s$, $\Im(\text{reflect} s)=-\Im s$, and—the key point—*the fixed points of the reflection are exactly the line $\Re s=1/2$*.[^2]

> **The critical line.** $\Re s=1/2$ is the line of fixed points of the reflection $s\mapsto 1-s$.

Here the separation of levels is visible: the *reflection* is checkable geometry (the rational condition $\Re s=1/2$, simple and machine-confirmed); the *functional equation* is an accepted rule linking the values of zeta across this reflection. The first is a role-axis (see 13.4.7); the second is the axiom tier.

## The Trivial Zeros

From the functional equation (as an accepted rule) there classically follow the *trivial* zeros of zeta at the negative even integers:

$$
\zeta(-2)=\zeta(-4)=\zeta(-6)=…=0.
$$

The reason is simple: on the right-hand side of the equation the factor $\sin(\pi s/2)$ vanishes at $s=-2,-4,-6,…$ These zeros are called *trivial* because they follow *immediately* from the equation.

*Honestly:* the trivial zeros here are a *classical landmark*, not a separate machine-checked object: they live on the same *axiom tier* as the equation itself (we do not derive them from more primary facts but read them off the accepted symmetry). What matters is the qualitative distribution of the zeros that takes shape from here:

- $\Re s>1$: no zeros (the Euler product, Chapter 13.3; the finite side is machine-checked);
- $\Re s<0$: only the trivial zeros (the functional equation, the axiom tier);
- the strip $0<\Re s<1$: all the *nontrivial* zeros, symmetric about $\Re s=1/2$.

## The Riemann Hypothesis: A Preliminary Formulation

A natural question arises: where exactly in the strip do the nontrivial zeros lie?

> **The Riemann Hypothesis (1859).** All nontrivial zeros of zeta lie on the critical line
> $\Re s=1/2$.

This is a statement of *symmetry*: if $\rho=\tfrac12+i\gamma$ is a zero, then by the functional equation and complex conjugation $1-\rho$ and $\bar\rho$ are zeros too; on the critical line this quadruple degenerates (see 13.4.5). In our layer the Riemann Hypothesis is formalized in *three equivalent forms*, and the equivalence is machine-checked—this is a self-standing result that makes no claim to prove the hypothesis itself.[^3] The full analysis of the three forms and their role is in Chapter 13.7; here what matters is only the *setting* and its symmetric nature.

## The Structure of the Quadruple of Zeros

From the functional equation together with complex conjugation one obtains: if $\rho=\sigma+i\gamma$ is a nontrivial zero, then so are

$$
\bar\rho=\sigma-i\gamma,\quad 1-\rho=(1-\sigma)-i\gamma,\quad 1-\bar\rho=(1-\sigma)+i\gamma.
$$

This *quadruple* forms a rectangle in the complex plane, symmetric about the line $\Re s=1/2$ and about the real axis. For $\sigma=1/2$ (the scenario of the Riemann Hypothesis) the rectangle degenerates into a segment on the critical line—$\rho$ and $1-\rho$ merge (up to conjugation).[^4]

In the ToS reading the quadruple is the *orbit* of a zero under the symmetry group “reflection ${}+{}$ conjugation.” The critical line is the set of points where the orbit is minimal (a segment instead of a rectangle). The Riemann Hypothesis says: *all* nontrivial zeros lie where the orbit is degenerate.

## The Geometric Meaning

The functional equation is a model of a deep mathematical symmetry that replaces a variable by its “complement” ($s\leftrightarrow 1-s$) and thereby links distant regions. Analogies in other fields are numerous: Poincaré duality in topology (the link between $H_k$ and $H_{n-k}$), Serre duality in algebraic geometry, CPT symmetry and mirror symmetry in physics. Everywhere the symmetry replaces a quantity by its complement and thereby extracts deep structural information.

In the case of zeta the symmetry $s\leftrightarrow 1-s$ links the convergent regime ($\Re s>1$, the Euler product) with the regime beyond the region of convergence ($\Re s<0$, the trivial zeros) through the critical strip. These analogies are cultural context, not formal statements; we give them to show *what kind* of object the functional equation is, and why it is taken as the structural axis of the theory.

## E/R/R Analysis: Symmetry as an Accepted Rule

**Rules (L5).**  Here there are two rules of different status. The first is the *reflection* $s\mapsto 1-s$: a machine-checked involution with the fixed axis $\Re s=1/2$. The second is the *functional equation*: the rule of the symmetry of the *values* of zeta across this reflection, *accepted as an axiom* (`functional_equation_structure`), not derived. Part XIII honestly keeps these levels apart.

**Roles (L4).**  “The critical line $\Re s=1/2$” is a *role-axis* (the set of fixed points of the reflection). “The trivial zeros” are a *role-consequence* of the accepted symmetry. “A nontrivial zero” is a *role in the strip*; “an RH zero” is a *role-fixed-point* (on the axis; more fully, 13.7). “The quadruple of zeros” is a *role-orbit* under the group “reflection ${}+{}$ conjugation.”

**Elements (L1${}+{}$P4).**  Concrete data: the map `reflect` on `TComplex`, the rational condition $\Re s=1/2$, the four reflected/conjugated points of the orbit. *Not* elements: the completed zeta on the whole plane, the equation itself as a derived fact (it is an accepted axiom), the completed set of all zeros.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the reflection $s\mapsto 1-s$ (machine-checked); the functional equation (an accepted axiom) | the symmetry of the plane and the symmetry of the values of zeta | Rule (L5) |
| critical line ${}={}$ axis; trivial zeros ${}={}$ consequence; quadruple ${}={}$ orbit | the status of special points with respect to the symmetry | Role (L4) |
| `reflect` on `TComplex`; the condition $\Re s=\tfrac12$; the four points of the orbit | the bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes.**  The critical line ceases to be a “mysterious place”: it is the *axis of fixed points* of an explicit symmetry, and the condition $\Re s=1/2$ is rational and machine-checkable. At the same time the analysis honestly records the *price*: the functional equation itself we *accept* (the axiom tier) rather than derive—and this, along with the continuum price and the openness of RH, will go into the map of boundaries of the part (13.7).

## What the Chapter Has Prepared

The functional equation has been read as an *accepted* rule of the symmetry $s\leftrightarrow 1-s$; from it the critical line $\Re s=1/2$ emerges as the *axis of fixed points* of the reflection—and it is precisely this reflection (involutivity, the fixed axis) that is machine-checked, whereas the equation itself rests on the axiom tier. The trivial zeros, the quadruple of zeros, and the preliminary formulation of the Riemann Hypothesis are organized around this symmetry.

Next:

- Chapter 13.5—the nontrivial zeros, the zero-free region, and the zero count $N(T)$;
- Chapter 13.6—the logarithmic derivative and von Mangoldt’s explicit formula (the link between the zeros and the distribution of primes);
- Chapter 13.7—three equivalent forms of the Riemann Hypothesis (where the “fixed point” form directly uses the reflection of this chapter) and the map of boundaries of the part, which brings together the continuum price, the axiom tier (this equation), and the openness of RH.

---

[^1]: `src/zeta/FunctionalEquation.v` (its header says directly: “the functional equation is taken as ONE domain axiom `functional_equation_structure` in this branch” (our translation); “AXIOMS: classic (from classify_zeros), 1 mathematical axiom”). Machine-checked are `reflect`, `reflect_involutive`, `reflect_re/im`, `reflect_fixed_iff`, and `RH_iff_reflect_equiv`; the equation itself is an accepted axiom, not a theorem.
[^2]: `FunctionalEquation.v`: `reflect` on `TComplex`, `reflect_involutive` ($\text{reflect}\circ\text{reflect}=\mathrm{id}$), `reflect_re`, `reflect_im`, and `reflect_fixed_iff` ($\Re s=\tfrac12 \Leftrightarrow s$ is a fixed point of the reflection). These are simple rational facts (proved by `ring`/`lra`), and they do *not* depend on the axiom of the functional equation—only on the definition of the reflection.
[^3]: `src/zeta/RH_Statement.v`: `RH_zeros` (all nontrivial zeros on $\Re s=1/2$), `RH_process` (the process form), `RH_fixed` (the fixed-point form), and `RH_all_equivalent`—their machine-checked equivalence. In detail, Chapter 13.7. That the Riemann Hypothesis is true is not proved.
[^4]: The structure of the quadruple is encoded by `FunctionalEquation.v` (through `reflect` and conjugation: $\rho$, $\bar\rho$, $\text{reflect} \rho$, $\text{reflect} \bar\rho$) and `src/zeta/ZeroStructure.v` (`conj_zero`, `zero_structure`). Note the status: `ZeroStructure.v` inherits `classic` and `L4_witness` (through `ProcessContinuumHypothesis`); the side that depends on the equation itself is the axiom tier.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/03 Euler Product and the Link to Primes|Chapter 3. The Euler Product and the Link to the Primes]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/05 Zeta Zeros and the Zero Free Region|Chapter 5. The Zeros of Zeta and the Zero-Free Region]] →
