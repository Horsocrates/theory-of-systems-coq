---
title: "Chapter 5. L¹ and L²: Spaces as Processes, Completeness as Constructibility"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/05 L^1 и L^2 пространства как процессы, полнота как конструируемость.md"
sourceBlob: e664bdd7a763c53e6f126c0d298ee38f2005f10e
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From the Integral to Spaces

Chapters 6.1–6.4 built measure, the Lebesgue integral, and the apparatus for passing to the limit under the integral. The present chapter takes the next step: it assembles *function spaces* from the integral—$L^1$ and $L^2$. $L^1$ is the completion of step functions in the integral norm $\|f\|_1=\int|f|$; it was already built in Chapter 6.3 as a process. $L^2$ is the space of functions with finite $\int|f|^2$, equipped with an *inner product* $\langle f,g\rangle=\int fg$, and therefore with geometry: lengths, angles, orthogonality. This geometry is the new material of the chapter: it turns analysis into geometry, and it is $L^2$, a Hilbert space, that will become the stage for operators and quantum mechanics (Chapter 6.6, then physics).

### Where Infinity Hides—and What Is Proved

The main question about any such space is *completeness*: does every sequence that “converges in itself” (Cauchy) have a limit *inside* the space? The classical answer for $L^2$, the Riesz–Fischer theorem, says yes; but the classical proof drags in a completed measure, the choice of a subsequence almost everywhere, and the limit function as a ready object. This is where nonconstructivity hides.

ToS rereads completeness the same way as everywhere in Part VI: *completeness is the constructibility of the limit-process*, not existence obtained by Zorn or the Axiom of Choice. We hold to the three levels of rigor. *Proved without axioms* (on a finite support of $N$ points, at every stage): the Cauchy–Schwarz inequality (through the sum-of-squares identity), the square-root-free squared estimate for the $L^2$ distance, best approximation and the general Bessel inequality, Parseval’s identity as a *finite criterion of the completeness of an expansion*, and Riesz–Fischer *by construction*: the limit of a Cauchy sequence is built coordinatewise. *Remains an honest boundary* (P4): the completed infinite-dimensional $\ell^2/L^2$—where the norm is a sum over *all* coordinates ($N\to\infty$)—and a completed orthobasis; these are role-limits, not actualizable objects. We hold this boundary explicitly in every section.[^1]

### The E/R/R Framework of the Chapter

Before building, let us set out the framework of the system in the generating order
Rules $\to$ Roles $\to$ Elements; the full analysis with a table and a check of correctness is in § “E/R/R Analysis: The L^2 Space as a System.” The chapter introduces a system: the space $L^2$.

**Rules ($\leftrightarrow$ L5).** The geometry of the inner product (Cauchy–Schwarz, best approximation, Bessel, Parseval) and completeness as the constructibility of the limit-process. These rules organize everything else.

**Roles ($\leftrightarrow$ L4).** The inner product is a pairing (geometry); the norm is a magnitude (energy); the coordinate $\langle e_k,f\rangle$ is a projection; the limit $f_\infty$ is a role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational
values $f_i$ and finite sums at every stage; the completed $\ell^2$ lies outside the elements (the P4 boundary).

The subsequent sections fill in the framework: § “The Inner Product and the Cauchy–Schwarz Inequality”—the pairing and Cauchy–Schwarz; § “Best Approximation: Projection, Pythagoras, Bessel”—projection and Bessel; § “Parseval: A Finite Criterion of Completeness”—Parseval; § “Riesz–Fischer: Completeness by Construction”—completeness as a limit.

## $L^1$: The Result of Chapter 6.3 and Its Place in the Hierarchy

The present chapter does not build the space $L^1$ anew: it was built in Chapter 6.3. Let us recall the result: *an integrable function is a limit of step functions in the integral norm* $\|f\|_1=\int|f|$, that is, a Cauchy sequence of step functions. The space $L^1$ itself is the type of such Cauchy processes, up to the relation “to coincide in the mean” ($\|f-g\|_1\to0$, the process reading of “almost everywhere”). The completeness of $L^1$ is then not a separate theorem but a *property of the construction*: $L^1$ *is* the space of Cauchy processes of step functions, and its limit elements are constructible by definition.[^2]

Where, then, is the place of $L^2$ relative to $L^1$? On a finite sample of $N$ points both measure the same function, and the proved Cauchy–Schwarz inequality (§ “The Inner Product and the Cauchy–Schwarz Inequality”) links them at once: taking the constant one as the second argument, we get

$$
\Big(\textstyle\sum_{i<N}|f_i|\Big)^2 \;\le\; \Big(\textstyle\sum_{i<N}|f_i|^2\Big)\cdot N,
  \quad\text{that is,}\quad \|f\|_1^2 \;\le\; N \|f\|_2^2 .
$$

$L^2$ control implies $L^1$ control (on $N$ points): closeness in the mean square gives closeness in the mean.[^3]

*$L^1$ is the background built in 6.3; $L^2$ is the new geometry. Their connection on a finite sample is one application of Cauchy–Schwarz.* The full inclusions $L^2\subset L^1$ on a completed measure are statements about ready spaces, and they lie on the same P4 boundary as the completed $L^2$ itself.

## The Inner Product and the Cauchy–Schwarz Inequality

The inner product of two functions (on a finite support or on a sample of $N$ points) is $\langle f,g\rangle=\sum_{i<N} f_i g_i$, and the norm is $\|f\|^2=\langle f,f\rangle$. This is a finite sum at every stage: the bearer is rational values, and the sum is actually finite (P4).

The cornerstone inequality of $L^2$ geometry is *Cauchy–Schwarz*:

$$
\langle f,g\rangle^2 \;\le\; \|f\|^2 \|g\|^2 .
$$

It says that “the cosine of an angle is no greater than one,” and it is proved *exactly, without axioms*, through Lagrange’s identity, which expresses the gap as a sum of squares:

$$
\|f\|^2\|g\|^2-\langle f,g\rangle^2
  \;=\;\tfrac12\sum_{i,j}(f_i g_j-f_j g_i)^2 \;\ge\;0 .
$$

The right-hand side is nonnegative as a sum of squares of rational quantities: neither completeness nor a passage to the limit is needed here.[^4]

### Polarization: The Norm Remembers the Product

The inner product is symmetric, $\langle f,g\rangle=\langle g,f\rangle$, and from it, by *polarization*, the whole bilinear structure is recovered: the product is expressed through norms alone,

$$
\langle f,g\rangle \;=\; \tfrac12\bigl(\|f+g\|^2-\|f\|^2-\|g\|^2\bigr).
$$

This identity is pure finite algebra, and it shows that the geometry of $L^2$ is entirely encoded in a single norm.[^5]

**Cauchy–Schwarz is a purely finite-arithmetic fact.** The geometry of $L^2$ (angles, projections, orthogonality) stands not on a completed space but on the nonnegativity of a sum of squares, at every finite stage.

## The Squared $L^2$ Distance and the Square-Root-Free Estimate

The inner product sets the square of the distance $d^2(f,g)=\|f-g\|^2$. The classical *metric* $d=\sqrt{d^2}$ would require extracting a square root—and a root in ToS is not a number but a *process* (ℝ as `RealProcess`, $ℕ\toℚ$): we are not entitled to actualize it as a ready object. Therefore we work with the *square* of the distance, the part of it that lives in ℚ, and prove the square-root-free squared estimate

$$
d^2(f,h)\;\le\;2 d^2(f,g)+2 d^2(g,h),
$$

whose gap is the sum of squares $\sum_i\bigl(f_i-2g_i+h_i\bigr)^2\ge0$, proved exactly and without axioms.[^6]

*An important reservation.* What is proved is *not* the classical triangle inequality
$d(f,h)\le d(f,g)+d(g,h)$ but its square-root-free squared substitute, sufficient for *energy control* (estimates through the square of the norm). The full metric is obtained by extracting the root, that is, by passing to the real / process-real layer; in the ℚ-part that we keep, there is no root. This is the same discipline as in Chapters 6.1–6.4: compute in the rational, without turning the root into a ready number.

## Best Approximation: Projection, Pythagoras, Bessel

An *orthonormal* (ON) system is a family $\{e_k\}$ with $\langle e_i,e_j\rangle=1$ for $i=j$ and $0$ otherwise. The *projection* of a function $f$ onto the first $K$ directions is the sum $P_K f=\sum_{k<K}c_k e_k$ with coefficients $c_k=\langle e_k,f\rangle$; the *remainder* is $r_K=f-P_K f$. The core of the theory is the *identity for the norm of the remainder*:

$$
\|r_K\|^2 \;=\; \|f\|^2-\sum_{k<K}c_k^2 .
$$

It is proved by induction on $K$ and relies on the *linearity of the inner product over a finite expansion* $\langle h,\sum_{k<K}c_k e_k\rangle=\sum_{k<K}c_k\langle h,e_k\rangle$—and this is an interchange of a double finite sum, a discrete analogue of Fubini’s theorem from Chapter 5.7 (the end of Part V)—plus orthogonality.[^7]

For a single unit direction the identity takes the form of the *Pythagorean theorem*:

$$
\|f\|^2 \;=\; \langle e,f\rangle^2 + \|f-\langle e,f\rangle e\|^2,
$$

that is, the energy splits into the share along $e$ and the energy of the remainder, and the remainder is orthogonal to $e$. Geometrically: the projection splits off the orthogonal component, and the coefficient $c=\langle
e,f\rangle$ is exactly the share that lies along the direction.[^8]

From the nonnegativity $\|r_K\|^2\ge0$ follows at once the *general Bessel inequality*:

$$
\sum_{k<K}c_k^2 \;\le\; \|f\|^2 \quad(\text{for any ON system and any }K).
$$

The energy collected over $K$ directions does not exceed the full energy $\|f\|^2$: projection does not create energy; it only redistributes it.[^9]

## Parseval: A Finite Criterion of Completeness

*Equality* in Bessel, *Parseval’s identity*, holds exactly when the remainder vanishes:

$$
\sum_{k<K}c_k^2=\|f\|^2 \quad\Longleftrightarrow\quad \|r_K\|^2=0
  \quad\Longleftrightarrow\quad \text{the expansion exactly recovers }f .
$$

The last equivalence holds because over ℚ a finite sum of squares equals zero if and only if each term is zero.[^10]

*What “completeness” means here.* Strictly: for a fixed truncation to $N$ coordinates, the first $K$ directions *recover every coordinate* $m<N$. This is a finite criterion of the completeness *of a given expansion at a given truncation*, not a statement about a completed infinite orthonormal basis. Parseval holds exactly for those systems that exhaust the vector at this $N$; an infinite basis ($K,N\to\infty$) and the unconditional equality for a completed ONB are a role-limit (P4).

## Riesz–Fischer: Completeness by Construction

Completeness is the heart of the Riesz–Fischer theorem: every $L^2$-Cauchy sequence $\{f_n\}$ has a limit in $L^2$. Classically the limit is a ready function obtained by choosing a subsequence and taking a limit almost everywhere. ToS *builds* it, and moreover without any choice.

The engine of the construction is the inequality *“one coordinate is no greater than the norm”*: for each
$i<N$ we have $(a_i)^2\le\|a\|^2$ (one term is no greater than a sum of nonnegative terms). Hence, if $\{f_n\}$ is Cauchy in the $L^2$ norm, then *each coordinate* $\bigl(f_n(i)\bigr)_n$ is a Cauchy sequence in ℚ. And a Cauchy sequence in ℚ is exactly the definition of a real number as a process (`RealProcess`, $ℕ\toℚ$). Therefore the limit *is built coordinatewise*: coordinate $i$ is a process real

$$
f_\infty(i)\;:=\;\bigl(n\mapsto f_n(i)\bigr).
$$

No choice at all: the limit is the sequence itself, reread as a vector of process reals. Then the convergence “$\|f_n-f_\infty\|_2\to0$” *unfolds into the Cauchy condition itself*: the stage-$s$ rational approximation of the limit $f_\infty$ is exactly $f_s$.[^11]

**The completeness of $L^2$ is not the existence of a limit but its constructibility.** The limit is not “chosen” from a completed space (Zorn, AC) but *built* as a process from the sequence itself.

*An honest boundary (the most important reservation of the chapter).* The proved theorem works at a *fixed finite truncation* $N$: the square of the norm is a finite sum over $N$ coordinates, and from $L^2$-Cauchy in this finite norm a coordinatewise limit-process is built—this is the constructive *core* of Riesz–Fischer. The full infinite-dimensional Riesz–Fischer theorem for a completed $\ell^2/L^2$, where the norm contains a sum over *all* coordinates ($N\to\infty$), and the limit as a *separate completed* real object remain a role-limit / the P4 boundary. We build the core; the completed infinite-dimensional space we mark.

## E/R/R Analysis: The $L^2$ Space as a System

### Analysis in the Generating Order

The framework of the system was set at the beginning (§ “The E/R/R Framework of the Chapter”); here we unfold it with a table and a check of correctness (well-formedness). The reservation about the level is the same as before: the “space” here is a substantive interpretation of the process carrier, not an object literally typed as `System`. We conduct the analysis in the generating order
Rules $\to$ Roles $\to$ Elements.

**Rules ($\leftrightarrow$ L5).** The geometry of the inner product: Cauchy–Schwarz, polarization, the square-root-free squared estimate of the distance, best approximation (Pythagoras), the general Bessel inequality, the finite Parseval criterion. And the rule of completeness: *completeness is the constructibility of the limit-process* (Riesz–Fischer by construction, at a fixed $N$). The universal layer is L1–L5 and P4, which moves the completed ONB and the infinite-dimensional $\ell^2$ beyond the boundary.

**Roles ($\leftrightarrow$ L4).** The inner product
$\langle f,g\rangle$ is the role-pairing that carries geometry. The norm $\|f\|$ is the role-magnitude (energy). The coefficient $c_k=\langle e_k,f\rangle$ is the role-coordinate (projection onto a direction). The limit $f_\infty$ is a role-limit: the tail of the sequence, reread as a vector of process reals. Completeness is a role-property of the system: the constructibility of the limit, not its choice.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite at
every stage: the rational values $f_i$, the finite sums $\sum_{i<N}$ and $\sum_{k<K}$, the coefficients $c_k$. The completed $\ell^2$, a completed orthobasis, the limit as a ready real number, and the sum over all coordinates ($N\to\infty$) do not belong to the elements.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| Cauchy–Schwarz; square-root-free estimate; Pythagoras / Bessel; Parseval criterion; completeness as constructibility | HOW the geometry and completeness of $L^2$ are organized | Rules ($L5$) |
| inner product; norm; coordinate $c_k$; limit $f_\infty$ | WHAT FOR the bearers are significant: roles of geometry and of the limit | Roles ($L4$) |
| values $f_i$; sums $\sum_{i<N},\sum_{k<K}$; coefficients $c_k$ (finite, at a given $N$) | WHAT exists at each stage (P4) | Elements ($L1$, P4) |

The analysis is well-formed: each component falls into exactly one category, and none refers to itself (P1). The inner product and the norm are roles over value-elements, not elements themselves; completeness is a rule, not an object; the completed $\ell^2$ lies outside the elements.

### What the Analysis Yields

The analysis shows that $L^2$ in ToS is not a completed Hilbert space but a *process geometry* at a fixed finite $N$: the rules (Cauchy–Schwarz, the square-root-free distance, best approximation, Bessel, Parseval) are proved at finite stages without axioms, and completeness is read as the constructibility of the limit—it is built coordinatewise, not chosen. Infinity—the completed basis, the infinite-dimensional
$\ell^2$, the sum over all coordinates—is honestly moved to the P4 boundary and marked as a role-limit. This is the same line of honesty as in Chapters 6.1–6.4: the infinitary step is not hidden in a ready object but named and placed on the boundary.

Having obtained a space with an inner product, a squared distance, best approximation, orthonormal expansions, and completeness by construction, we are ready for its *operators*. The next chapter introduces self-adjoint operators on $L^2$, their spectrum, and the orthogonality of eigendirections—and carries the line through to the canonical commutator, the harmonic oscillator, and Schrödinger evolution, through which the $L^2$ apparatus becomes a bridge to quantum mechanics.

---

[^1]: The supporting files in the directory `src/process/` of the ToS Rocq repository: `ProcessL2CauchySchwarz.v`, `ProcessL2Triangle.v`, `ProcessL2Bessel.v`, `ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v`, `ProcessL2RieszFischer.v`; the links between them are in `ProcessL2HilbertSynthesis.v`. According to the headers of these files and the synthesis file of the cluster, 0 axioms; for a full audit, the key theorems carry `Print Assumptions`. The theorem names are in the notes below.
[^2]: The file `L1Space.v` (directory `analysis/`, 25 Qed by its header): `L1Process` (representatives), `step_fun_norm`, `l1_integral_approx`, `l1_equiv` ($\|f-g\|_1\to0$), `step_to_l1`. Discussed in Chapter 6.3.
[^3]: A direct consequence of `q_sum_cauchy_schwarz` in `ProcessL2CauchySchwarz.v` (0 axioms) with $g\equiv1$. Written in squared form: the factor $\sqrt N$ would arise only after extracting the root, that is, after passing to the process-ℝ.
[^4]: `q_sum_cauchy_schwarz` and `l2_cauchy_schwarz` in `ProcessL2CauchySchwarz.v` (0 axioms); the supporting facts are the nonnegativity of a square, `q_sq_nonneg`, and Lagrange’s identity, `sos_identity`.
[^5]: The symmetry `l2_inner_sym` and the expansion of the squared norm `l2_inner_expand` in `ProcessL2CauchySchwarz.v` (0 axioms); polarization is their direct consequence.
[^6]: `l2_dist_sq_triangle` in `ProcessL2Triangle.v` (0 axioms); the squared distance `l2_dist_sq`, its symmetry and nonnegativity; the gap is handled through `q_sq_nonneg` applied to a composite square.
[^7]: Linearity over an expansion is `inner_proj_swap` in `ProcessL2BesselGeneral.v` (through the interchange of sums `q_sum_swap`); the orthogonality of the projection is `proj_ortho`; the remainder identity for one direction is `seq_inner_residual_identity` in `ProcessL2Bessel.v`. All: 0 axioms.
[^8]: `pythagoras_one` and `bessel_one` in `ProcessL2Bessel.v` (0 axioms).
[^9]: `bessel_general` in `ProcessL2BesselGeneral.v` (0 axioms): from the remainder identity `resid_norm` and the nonnegativity of a sum of squares.
[^10]: `parseval_iff_complete` in `ProcessL2Parseval.v` (0 axioms): `energy_split` $\sum c_k^2+\|r_K\|^2=\|f\|^2$, `parseval_iff_resid_zero`, and the lemma `q_sum_sq_zero` (a sum of squares is zero $\Rightarrow$ each term is zero, through the integral-domain property of multiplication in ℚ). A concrete witness that the equality is attainable is `parseval_std_concrete` (the standard basis).
[^11]: `coord_sq_le_normsq`, `l2cauchy_coord_cauchy`, `l2_limit`, and `l2_riesz_fischer` in `ProcessL2RieszFischer.v` (0 axioms). A concrete witness is `const_l2cauchy`.

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[04 Convergence Theorems Monotone and Dominated|Chapter 4. Convergence Theorems: Monotone and Dominated]] · [[06 Operators on L2 Self Adjointness Spectrum and Bridge to Quantum Dynamics|Chapter 6. Operators on L²: Self-Adjointness, Spectrum, and the Bridge to Quantum Dynamics]] →
