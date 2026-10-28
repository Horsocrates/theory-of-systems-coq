---
title: "Chapter 1. Orthonormal Systems and Fourier Coefficients"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/07 Гармонический анализ/01 Ортонормированные системы и коэффициенты Фурье.md"
sourceBlob: 249e4d3a7005b67e58672621e55ea33814d5f696
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part VII

Part VI carried measure and integration without the Axiom of Choice through to the end and concluded with the Hilbert layer: the inner product on processes, Bessel’s inequality, the Parseval criterion, the Riesz–Fischer theorem in its process reading, and the isometries of quantum dynamics. With this, the whole apparatus needed for the next step is in hand: *harmonic analysis*, the expansion of a function in an orthonormal system and the Fourier transform.

Part VII applies to this apparatus the same device that has guided the whole volume. Classical harmonic analysis takes as *completed objects* the complete orthonormal basis, the infinite Fourier series $\sum_{k=1}^{\infty} c_k e_k$, and the continuous transform with integrals of the transcendental $\sin$ and $\cos$. ToS takes each of them as a *process* or a *role-limit*: the finite orthonormal system and its partial sum as the provable core, and the completed basis and the infinite series as an honestly marked boundary. The central *presented* object of Part VII will be the rational Walsh–Hadamard transform (Chapter 7.2): an orthogonal $\pm1$ transform over the Boolean cube, “Fourier without transcendentals.”

The present chapter is a bridge from Part VI. It reformulates the already proved
L<sup>2</sup> apparatus as a theory of *Fourier coefficients*: what the coordinate of a function along a direction of an orthonormal system is, in what sense a partial sum is the best approximation, and how Bessel’s inequality and Parseval’s identity are read as exact finite statements about the conservation of energy.

### What This Chapter Claims—and What It Does Not

Honesty from the very start. The chapter works with a *finite* orthonormal system $\{e_k\}_{k<K}$ of $K$ vectors on $N$ coordinates over ℚ and proves about it everything needed for the theory of coefficients: the linearity of the inner product over a finite expansion, the orthogonality of the remainder of a projection to its carrier, the identity “energy $=$ captured part $+$ remainder,” Bessel’s inequality
$\sum_{k<K} c_k^2 \le \norm{f}^2$, and Parseval’s identity as a *criterion of completeness*—all of this *without a single axiom*.[^1]

What the chapter does *not* do: it does not build a completed *infinite* orthonormal basis, does not claim that the closed span of the system is the whole space, and does not introduce the normalization $1/\sqrt N$ otherwise than as an abstract parameter (it is irrational if $N$ is not a perfect square). The infinite Fourier series as a completed sum and continuous trigonometry are an honest P4 boundary, to which we will return in Chapters 7.3 and 7.4.

To keep the boundary in view, we distinguish three levels of rigor. The *first* is a finite orthonormal system on $N$ coordinates: here Bessel, the energy identity, and the completeness criterion are proved exactly over ℚ, without axioms. The *second* is the process *readings*: the coefficient as a coordinate-projection, the partial sum as the best approximation, completeness as the exhaustion of energy. The *third* is the completed infinite basis and the full Fourier series as ready objects—a role-limit and a direction, not a built theory. The chapter treats the first two levels as proved and the third as an honestly marked boundary.

### The E/R/R Framework of the Chapter

We set out the framework of the system in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis with a table and a check of correctness is in § “Analysis in the Generating Order.” The chapter introduces the system of expansion in an orthonormal system.

**Rules ($\leftrightarrow$ L5).** The inner product is bilinear and symmetric; orthonormality $\inner{e_i}{e_j}=\delta_{ij}$; the Fourier coefficient $c_k=\inner{e_k}{f}$; the energy identity
$\sum_{k<K} c_k^2 + \norm{r_K}^2 = \norm{f}^2$; Parseval’s identity holds if and only if the system fully recovers $f$.

**Roles ($\leftrightarrow$ L4).** The coefficient $c_k$ is the role-coordinate of the function along $e_k$; the partial sum $P_K$ is the role-of-best-approximation; the norm of the remainder $\norm{r_K}^2$ is the role-defect of completeness; “the complete basis” and the completed series are a role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational
coefficients $c_k$, coordinates $e_k(m)$ and $f(m)$, finite sums $\sum_{i<N}$ and
$\sum_{k<K}$; the completed infinite basis lies outside the elements (P4).

## The Orthonormal System and Fourier Coefficients

### The Inner Product on Processes

The Hilbert geometry of Part VI stands on one finite object, the inner product of vectors on the first $N$ coordinates:

$$
\inner{a}{b}_N \;=\; \sum_{i<N} a_i  b_i, \quad
  \norm{f}^2 \;=\; \inner{f}{f}_N \;=\; \sum_{i<N} f_i^2.
$$

This is a rational finite sum: neither a limit nor a completed infinity.[^2] It is symmetric and linear in each argument: these properties are not postulates but simple identities over ℚ, proved by one step of
`ring` under the summation sign.[^3]

An *orthonormal system* on these $N$ coordinates is a set of vectors
$\{e_k\}$, pairwise orthogonal and of unit norm:

$$
\inner{e_i}{e_j}_N \;=\;
  \begin{cases} 1, & i=j,\\[2pt] 0, & i\neq j.\end{cases}
$$

In the code this is the *hypothesis* `Hon` of the section on orthonormal systems—an explicitly presented condition on a concrete set $e$, not the existence of “some basis.”[^4] The system is finite and rational; no completed infinite basis is present here or required.

### The Fourier Coefficient and the Projection

The Fourier coefficient of a function $f$ with respect to a vector $e_k$ is its *coordinate* along this direction:

$$
c_k \;=\; \inner{e_k}{f}_N.
$$

The partial sum is the projection of $f$ onto the first $K$ directions:

$$
P_K(m) \;=\; \sum_{k<K} c_k  e_k(m)
         \;=\; \sum_{k<K} \inner{e_k}{f}_N  e_k(m).
$$

The key to the whole theory is the linearity of the inner product over this finite expansion: the pairing of any vector $h$ with a combination $\sum_{k<K} c_k e_k$ splits into a sum of pairings,

$$
\Big\langle h,\ \textstyle\sum_{k<K} c_k e_k\Big\rangle_N
  \;=\; \sum_{k<K} c_k  \inner{h}{e_k}_N .
$$

On the process L<sup>2</sup> this is a statement about the *interchange of a double finite sum* (the discrete Fubini theorem, proved in Part V): bring $h_m$ under the inner sum, swap the order of summation $m\leftrightarrow k$, take $c_k$ out.[^5]

*The Fourier coefficient $c_k$ is not a “part” of the function $f$ and not a self-standing object but a role: the coordinate of $f$ in the direction $e_k$, the value that the rule $\inner{e_k}{\cdot}$ assigns to the function. An expansion is a process of reading off such coordinates, direction by direction.*

## Best Approximation and Bessel’s Inequality

### The Remainder Is Orthogonal to the Carrier of the Projection

Let $r_K = f - P_K$ be the remainder after the first $K$ coordinates have been read off. The geometry of the projection rests on one fact: *the remainder is orthogonal to the subspace onto which we project*. First an intermediate step: the $K$-th vector is orthogonal to the span of the first $K$, since each term $c_k\inner{e_K}{e_k}$ for $k<K$ vanishes by orthonormality.[^6] The consequence: for all directions already read off, $j<K$, we have $\inner{e_j}{r_K}_N = c_j - c_j = 0$—the remainder is “invisible” to every vector along which the expansion has already been made.

### The Energy Identity: The Pythagorean Theorem for an Expansion

Hence the central identity of the chapter. The norm of the remainder is the full energy minus the sum of the squares of the coefficients read off:

$$
\norm{f - P_K}^2 \;=\; \norm{f}^2 \;-\; \sum_{k<K} c_k^2 .
$$

This is the *Pythagorean theorem* for an orthogonal expansion: the energy of the function splits into the part captured by the projection ($\sum_{k<K} c_k^2$) and the part that remains ($\norm{r_K}^2$), without cross terms.[^7]

### Best Approximation

Why exactly the coefficients $c_k=\inner{e_k}{f}$ and not some other weights $a_k$? Because they give the *best* approximation of $f$ in norm among all linear combinations of $\{e_k\}$. The norm of the error for any choice of weights splits into an irremovable part and a penalty for deviating from the Fourier coefficients:

$$
\Big\| f - \textstyle\sum_{k<K} a_k e_k \Big\|^2
  \;=\; \norm{f - P_K}^2 + \sum_{k<K} (a_k - c_k)^2 ,
$$

and this is a *proved identity*, not a heuristic: the right-hand side is no less than
$\norm{f-P_K}^2$, with equality if and only if $a_k = c_k$ for all $k<K$—the Fourier coefficients are the *unique* minimum.[^8]

*The partial sum $P_K$ is the role-of-best-approximation: among all ways of describing $f$ through $K$ directions of an orthonormal system, the Fourier coordinates minimize the residual. This is not a choice from a ready set of approximations but a rule that singles out the unique optimum.*

### Bessel’s Inequality

Since the norm of the remainder is nonnegative, the Pythagorean identity at once gives *Bessel’s inequality*:

$$
\sum_{k<K} c_k^2 \;\le\; \norm{f}^2 .
$$

The energy captured by any number $K$ of directions does not exceed the full energy of the function.[^9] Unlike the classical formulation, where a completed infinite sum stands on the right, here both the left and the right sides are finite rational quantities, and the inequality itself is a theorem about the construction, not a limiting postulate.

*Bessel is a rule of energy bookkeeping: however many coordinates we read off, their total “weight” cannot exceed the weight of the function itself. The expansion creates no “overflow.”*

## Parseval as a Finite Criterion of Completeness

### The Energy Split

Let us rewrite the Pythagorean identity as an *energy split*:

$$
\underbrace{\sum_{k<K} c_k^2}_{\text{captured}}
  \;+\;
  \underbrace{\norm{r_K}^2}_{\text{defect}}
  \;=\; \norm{f}^2 .
$$

The full energy of the function is divided exactly between what the expansion has grasped and what has remained in the residual.[^10] The norm of the remainder $\norm{r_K}^2$ plays the role of the *completeness defect*: it measures what the expansion lacks for an exact recovery of $f$.

### Parseval’s Identity and Its Equivalent—Completeness

Parseval’s identity $\sum_{k<K} c_k^2 = \norm{f}^2$ is the statement that the defect is zero. The energy split turns it into an exact equivalence: *Parseval holds if and only if the norm of the remainder is zero*. And over ℚ a finite sum of squares equals zero exactly when every term vanishes; hence a zero defect is equivalent to the expansion *fully recovering* $f$ on all $N$ coordinates:

$$
\sum_{k<K} c_k^2 = \norm{f}^2
  \quad\Longleftrightarrow\quad
  P_K(m) = f(m)\ \text{for all}\ m<N .
$$

This is the honest constructive content of the formula “Parseval $=$ criterion of completeness.”[^11]

*Completeness is not a property of a completed infinite basis but a finite criterion: whether a given system exhausts all the energy of $f$ on $N$ coordinates. Parseval’s identity is a role-equality (no loss of energy), and checking it for a finite system is an exact process-algebraic fact.*

### The Witness: The Equality Is Attained

So that the criterion does not remain empty, an explicit witness of the attainment of equality is presented: the standard basis on $N=2$ coordinates and the function $f=(3,4)$ give
$\sum_{k<2} c_k^2 = 3^2 + 4^2 = 25 = \norm{f}^2$—completeness on two coordinates.[^12] The smallness of the example matters here: it shows that the criterion *works*, not merely that it can be formulated.

### Where the Boundary Lies

The boundary lies exactly where completed infinity appears. Parseval for an *infinite* basis ($K,N\to\infty$), the claim that the closed span of the system is the whole space, and the unconditional equality for a completed orthonormal basis—all of these are role-limits: ToS does not build a completed basis.[^13] What is proved is finite: the completeness criterion on $N$ coordinates. This is enough to conduct the theory of Fourier series as a theory of *truncations* (Chapter 7.4) without summoning the completed series into existence.

## A Concrete Orthogonal System: Walsh–Hadamard

Everything above was said about an *abstract* orthonormal system given by the hypothesis `Hon`. A natural question arises: is there a concrete *rational* system on which this geometry works? The answer requires one reservation about the level. A rational *orthogonal* system—yes: Walsh–Hadamard gives it, and it will be the heroine of the next chapter. But literal *orthonormality* $\inner{e_i}{e_j}=\delta_{ij}$ requires the normalization
$1/\sqrt N$, and this is already the next layer.

The columns of the Hadamard matrix $H_N$ are vectors of $\pm1$ (purely rational), and they are pairwise orthogonal with squared norm $N$:

$$
\inner{H_i}{H_j}_N \;=\; N\cdot\delta_{ij} .
$$

This is proved *for all* $N=2^k$ as an exact identity over ℚ (by induction on Sylvester’s recursive structure), without axioms.[^14] To obtain from them an orthonormal system in the sense of `Hon` ($\inner{e_i}{e_j}=\delta_{ij}$), one must normalize: $e_k = H_k/\sqrt N$. And here lies the only irrationality: the factor $1/\sqrt N$ is rational only when $N$ is a perfect square (for example, $N=4$, $\sqrt N=2$), and in the general case it is introduced as an *abstract parameter* $s$ with the condition $s^2=N$, in full agreement with the device of Part VI (the root is parametrized and cancels in the observable quantities).

The conservation of energy itself requires no normalization and is proved directly: for the unnormalized Walsh transform

$$
\norm{H f}^2 \;=\; N \norm{f}^2
$$

(a discrete analogue of the Plancherel identity).[^15] Passing to the normalized system divides both sides by $N$ and returns Parseval in the form $\sum_k c_k^2 = \norm{f}^2$.

*The concrete orthogonal system is rational by construction (the Hadamard $\pm1$ vectors, orthogonality as an exact identity over ℚ). The only irrationality on the way to orthonormalization is the factor $1/\sqrt N$; it is separated from orthogonality and honestly moved into a role-limit. “Fourier without transcendentals” is orthogonality and the conservation of energy before normalization.*

## E/R/R Analysis: The Coefficient as a Role-Coordinate

### Setup

Let us analyze the constructed system—the expansion of a function in a finite orthonormal system—in terms of E/R/R. A reservation about the level: the “system of expansion” here is a substantive *interpretation* of the construction (the inner product plus orthonormality plus projection), not an object literally declared in the code as `System`. The analysis is an ontological comprehension of the structure of the chapter and a reading of the author’s E/R/R headers of the supporting files,[^16] not an attribution of new formal claims to the code.

Recall the distinction adopted in the volume: the abbreviation E/R/R sets the *epistemic* order (Elements $\to$ Roles $\to$ Rules, from the observable to the deep), while the generating (*ontological*) order is the reverse: Rules $\to$ Roles $\to$ Elements. Epistemically the chapter went from observable quantities (coefficients, norms) to laws; we conduct the analysis in the generating order.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the geometry of the inner product: it is bilinear and symmetric, and orthonormality fixes $\inner{e_i}{e_j}=\delta_{ij}$. Above it are the rule of reading off a coordinate, $c_k=\inner{e_k}{f}$, and the linearity of the pairing over a finite expansion ($\inner{h}{\sum c_k e_k}=\sum c_k\inner{h}{e_k}$). The construction is crowned by the rule of conservation of energy (the Pythagorean identity $\sum c_k^2 + \norm{r_K}^2 = \norm{f}^2$) and the completeness criterion (Parseval $\Leftrightarrow$ the exact recovery of $f$). The universal layer of these rules is the laws L1–L5; the concrete layer is the formula $c_k=\inner{e_k}{f}$ and orthonormality.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The coefficient
$c_k$ is the role-coordinate: the place that the function occupies along the direction $e_k$. The partial sum $P_K$ is the role-of-best-approximation. The norm of the remainder
$\norm{r_K}^2$ is the role-defect of completeness. “The completeness of the system” is a role-property (whether the expansion exhausts all the energy). And “the complete infinite basis” and the completed Fourier series are a role-limit: a place toward which the truncations tend, not actualized as an object.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The roles select bearers, and the bearers here are finite at every stage: the rational coefficients
$c_k$, the coordinates $e_k(m)$ and the values $f(m)$, the finite sums $\sum_{i<N}$ and
$\sum_{k<K}$. Under P4 no element is a completed infinity: only finite expansions are actual; the “completed basis” is not actualized as an element; what is actualized is the process of truncations toward it.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $\inner{e_i}{e_j}=\delta_{ij}$; $c_k=\inner{e_k}{f}$; Pythagoras; Parseval $\Leftrightarrow$ completeness | HOW the expansion and the conservation of energy are organized | Rules ($L5$) |
| coordinate $c_k$; best approximation $P_K$; defect $\norm{r_K}^2$; completeness; complete basis | WHAT FOR the bearers are significant: places in the system | Roles ($L4$) |
| $c_k\inℚ$; coordinates $e_k(m)$, $f(m)$; finite sums $\sum_{i<N}$, $\sum_{k<K}$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the expansion does *not* take as its element “the collection of all infinite harmonics” or a completed orthonormal basis. The system is finite, and completeness is checked as a *criterion* on $N$ coordinates, not as the membership of a function in the closure of a completed basis. It is precisely the absence of such self-reference that explains why the theory of Fourier coefficients needs here neither a completed infinite sum nor a postulate about the completeness of the basis: everything substantive is expressed by finite coordinates and the criterion of their sufficiency.

What the analysis yields. It translates the results of the chapter into the language of structure: *the Fourier coefficient is a Role* (a coordinate along a direction), *completeness is a Rule-criterion* (the exhaustion of energy), and the numbers $c_k$ and the values
$f(m)$ themselves are *Elements* (finite at every stage). To take the “Fourier series” as a completed infinite sum-object is to put a role-limit in the place of an Element—a confusion of categories of the same kind as “number as an object” instead of the role-quantity (Part II), “a point as an object” instead of a class (Chapter 4.3), and “uncountability as a property of a set” instead of a rule about processes (Chapter 4.4). The Fourier series begins here as a *family of finite* best approximations; its process convergence is the subject of Chapter 7.4, and as a completed object it is neither needed nor built.

The next chapter presents a concrete rational orthonormal system in full: the Walsh–Hadamard transform. There the abstract hypothesis `Hon` gives way to the proved identity $H_N^{\mathsf T}H_N = N\cdot I$, and the conservation of energy to the discrete Plancherel identity $\norm{Hf}^2 = N\norm{f}^2$: Fourier built without a single transcendental.

---

[^1]: The supporting files are `ProcessL2BesselGeneral.v` (directory `src/process/` of the ToS Rocq repository, 10 proved statements, 0 `Admitted`, 0 axioms) and `ProcessL2Parseval.v` (7 statements, 0 axioms). The lemma names in the notes below come from them and from `ProcessFourierON.v`.
[^2]: The definition `seq_inner` (file `ProcessCompactSpectral.v`); $\norm{f}^2$ is `seq_inner f f N`.
[^3]: `seq_inner_sym` (symmetry) and `seq_inner_sub_r` (linearity in a difference in the second argument) in `ProcessL2BesselGeneral.v`; both with 0 axioms.
[^4]: `Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)` in both files. A concrete system satisfying `Hon` (normalized Walsh) is in § “A Concrete Orthogonal System: Walsh–Hadamard.”
[^5]: `inner_proj_swap` in `ProcessL2BesselGeneral.v`: it is proved through `q_sum_swap` (interchanging the order of summation) and `q_sum_scale`. 0 axioms.
[^6]: `proj_ortho`: $\inner{e_K}{\sum_{k<K} c_k e_k}_N = 0$. Hence `coef_e_resid`: $\inner{e_K}{f-P_K}_N = \inner{e_K}{f}_N$—the projection does not touch a coordinate not yet read off. Both in `ProcessL2BesselGeneral.v`, 0 axioms.
[^7]: `resid_norm` in `ProcessL2BesselGeneral.v`: proved by induction on $K$ through the identity $\norm{F-cE}^2 = \norm{F}^2 - 2c\inner{E}{F} + c^2\norm{E}^2$ (`seq_inner_resid`) and the orthogonality of the remainder. 0 axioms.
[^8]: The best-approximation identity is `best_approx_eq`; the minimum corollary $\norm{f-P_K}^2\le\norm{f-\sum a_k e_k}^2$ is `best_approx_ge`; uniqueness (equality $\Leftrightarrow$ $a_k=c_k$) is `best_approx_unique` (through the lemma “a finite sum of squares over ℚ is zero only when each term is zero,” `q_sum_sq_zero`). All in `ProcessBestApproximation.v`, 0 axioms. Uniqueness here is *finite*, on a fixed range $k<K$; the convergence of the infinite series is the subject of Chapter 7.4.
[^9]: `bessel_general` in `ProcessL2BesselGeneral.v`: from `resid_norm` and the nonnegativity of the norm of the remainder in one step of `lra`. 0 axioms. This is the general Bessel inequality for an arbitrary finite orthonormal system, not tied to a concrete basis.
[^10]: `energy_split` in `ProcessL2Parseval.v`: a trivial consequence of `resid_norm` (one `lra`). 0 axioms.
[^11]: `parseval_iff_complete` in `ProcessL2Parseval.v` is the capstone of the file; it relies on `q_sum_sq_zero` (“a sum of squares is zero $\Rightarrow$ each term is zero” over ℚ) and `energy_split`. 0 axioms.
[^12]: `parseval_std_concrete` in `ProcessL2Parseval.v`: checked by `vm_compute`, that is, by exact rational arithmetic. (This is the Pythagorean triple $3,4,5$, read as the conservation of energy; the triple itself is a rational point of the unit circle, the value $t=1/2$ of the stereographic parametrization, derived rather than postulated—`PythagoreanTriples.v`.)
[^13]: The header of `ProcessL2Parseval.v` marks this directly: an infinite basis, closed span $=$ the whole space, and the unconditional equality for a completed basis are role-limits (the P4 boundary); a finite criterion of completeness is proved.
[^14]: `hadamard_orthogonal` in `ProcessWalshHadamard.v`: $\sum_{j<2^k} H_{ij}H_{i'j} = 2^k \delta_{ii'}$, proved by induction on $k$. 0 axioms. In detail, Chapter 7.2.
[^15]: `parseval_walsh` in `ProcessFourierON.v`: $\inner{Hf}{Hf}_N = N \inner{f}{f}_N$, derived from the self-adjointness of the Walsh transform and the identity $H(Hf)=N f$. 0 axioms.
[^16]: The headers give the labeling directly: `ProcessL2BesselGeneral.v`—Elements: the coefficients $c_k$, the coordinates $e_k(m)$, finite double sums; Roles: $\inner{h}{\sum c_k e_k}$ distributed over the expansion, Bessel as energy over $K$ directions; Rules: $\inner{h}{\sum c_k e_k}=\sum c_k\inner{h}{e_k}$. `ProcessL2Parseval.v`—Roles: $\inner{e_k}{f}$ is a coordinate, $\norm{r_K}^2$ is the completeness defect; Rules: the energy split and Parseval $\Leftrightarrow$ completeness.

---

Part: [[07 Harmonic Analysis|Part VII. Harmonic Analysis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[06 Operators on L2 Self Adjointness Spectrum and Bridge to Quantum Dynamics|Chapter 6. Operators on L²: Self-Adjointness, Spectrum, and the Bridge to Quantum Dynamics—Part VI]] · [[02 Walsh Hadamard Transform without Transcendentals|Chapter 2. Walsh–Hadamard: A Transform without Transcendentals]] →
