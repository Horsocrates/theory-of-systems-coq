---
title: "Chapter 3. Trigonometry and the Complex DFT: Where the Boundary Lies"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/07 Гармонический анализ/03 Тригонометрия и комплексный DFT где граница.md"
sourceBlob: 00e89f49c972ff02bbfa49a22f611794724c7844
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Boundary Chapter

Chapter 7.2 presented the rational core of harmonic analysis, the Walsh–Hadamard transform, and ended with the promise to outline the boundary from the other side: what happens when characters are taken not on the Boolean cube but on the circle. The present chapter does exactly this. Its subject is *not* a new rational result but an honest demarcation: where exactly harmonic analysis goes beyond ℚ, and why.

This is a boundary chapter, and its role in Part VII is special. The previous chapters built and proved; this one draws a line. But the line is drawn not rhetorically but exactly: we name the three transcendental ingredients of classical Fourier (the continuum integral, the values of $\sin/\cos$, the complex roots of unity), show which of them is irremovable, and—importantly—*isolate* the transcendental into a single explicit hypothesis. The proved result of the chapter is conditional: *if* one property of the roots of unity (the vanishing geometric sum) is accepted, *then* discrete orthogonality becomes a finite theorem over ℚ. Everything else is rational algebra; transcendence is compressed into one premise.

### Three Levels and What Is Proved Here

Let us distinguish, as before, the levels of rigor. The *first* is proved over ℚ: the discrete orthogonality of characters *under explicitly named algebraic hypotheses* (the character as a homomorphism plus the vanishing geometric sum); this is a finite theorem, 0 axioms.[^1] The *second* is the process readings: continuous orthogonality as the limit of Riemann sums over ℚ-grids (a process, Part V), not a completed integral. The *third* is the honest P4 boundary, which ToS does *not* build: the values of $\sin/\cos$ themselves, the imaginary unit $i$, the roots of unity $e^{2\pi ik/N}$, the field $ℂ$, the continuum integral as a ready object, and the completed infinite Fourier series. We treat the first level as conditionally proved (under explicit hypotheses about characters), the second as a process, and the third as an explicitly marked boundary.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.”

**Rules ($\leftrightarrow$ L5).** Harmonic analysis is the expansion in the characters of an abelian group; orthogonality follows from the homomorphism property of the characters and the vanishing geometric sum; the *boundary rule*: transcendence enters not through the idea of the analysis but through the field of values of the characters of the chosen group.

**Roles ($\leftrightarrow$ L4).** The character is a role; the group is the role-carrier of the structure; the hypothesis $\sum_j\chi_m(j)=0$ is the role-encapsulation of the transcendental; the values of $\sin/\cos$, $e^{2\pi ik/N}$, $i$, $\pi$ are role-limits.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Abstract values
of characters $\chi(k,j)\inℚ$ (given by a hypothesis), finite sums, $N$ sample points; transcendental values, $ℂ$, and the continuum integral lie outside the elements (P4).

## Continuous Trigonometry: Orthogonality as an Integral

### Where Transcendence Hides

The classical trigonometric system is $\{1,\cos x,\sin x,\cos 2x,\sin
2x,…\}$ on the interval $[-\pi,\pi]$, and its orthogonality is a family of integrals

$$
\int_{-\pi}^{\pi}\cos(mx)\cos(nx) dx = \pi \delta_{mn}
  \quad(m,n\ge1),
$$

while mixed products of sine and cosine integrate to zero:

$$
\int_{-\pi}^{\pi}\sin(mx)\cos(nx) dx = 0 .
$$

Let us compare this with the Walsh orthogonality of [[Library/Branches/Mathematics/Volume/07 Harmonic Analysis/02 Walsh Hadamard Transform without Transcendentals|Chapter 7.2 “Walsh–Hadamard: A Transform without Transcendentals”]], where there stood a *finite sum of signs* $\sum_{j<N}H_{ij}H_{i'j}=N\delta_{ii'}$. The difference is the boundary. Here transcendence enters by three paths at once: *first*, summation is replaced by an integral over the continuum—a completed object that ToS does not actualize; *second*, the integrand is a product of the transcendental $\sin$ and $\cos$; *third*, the value $\pi$ on the right is itself transcendental.

### The Integral as a Process, Not as a Taken Object

Within ToS the integral is not a ready number but a *process* of accumulation of Riemann sums over rational grids (this is how it was built in Part V). Therefore continuous orthogonality can be read as a statement about the *limit* of a process of partial sums—and in this reading it is in principle accessible. But this reading runs into the boundary of values: the limit of the diagonal integral is $\pi$ (transcendental), and the values of the integrand at each stage are values of $\sin/\cos$, rational only at exceptional points. Even where the result is rational (the off-diagonal integral equals zero), the *proof* of this zero relies on an antiderivative or on the periodicity of $\sin/\cos$, that is, on transcendental machinery.

*Continuous trigonometric orthogonality is not an exact rational identity, as with Walsh, but the limit of a process with transcendental values. This is an honest boundary: the process can be carried to any precision, but its limit and its terms lie outside ℚ.*

## The Complex DFT: Roots of Unity and the Imaginary Unit

### Characters of the Circle

The discrete Fourier transform (the $N$-point DFT) discretizes the circle: its characters are the powers of a primitive root of unity $\omega=e^{2\pi i/N}$,

$$
\chi_k(j) = \omega^{kj} = e^{2\pi i kj/N},
  \quad
  (Ff)_k = \sum_{j<N} f_j \omega^{-kj}.
$$

Orthogonality relies on the *vanishing geometric sum*: for $m\not\equiv
0\pmod N$

$$
\sum_{j<N}\omega^{mj} = \frac{\omega^{mN}-1}{\omega^{m}-1} = 0,
$$

since $\omega^{mN}=1$ while $\omega^m\neq1$. Hence $\sum_j\omega^{kj}\omega^{-k'j}=
N\delta_{kk'}$—exactly the same structure of characters as with Walsh, but over a different field.

### What Exactly Is Transcendental

The boundary here is different from that of continuous trigonometry: the sum is *finite*, and the mechanism of vanishing is *algebraic* (a geometric progression). What is transcendental and complex are the *values* themselves: $\omega=e^{2\pi i/N}$ requires the imaginary unit $i$ and the base $e$; the characters live in $ℂ^N$; ToS does not build a full-fledged field $ℂ$ as an already constructed carrier over the process reals, and the root of unity $\omega^{kj}$ is in general irrational and complex.[^2]

*The complex DFT is the same harmony of characters as Walsh, but on the group
$(ℤ_N,+)$, whose characters are roots of unity. The algebraic skeleton (the vanishing sum) becomes rational if the values of the characters are replaced by abstract rational parameters with the required laws; the *values* $e^{2\pi ik/N}$ themselves and the imaginary unit $i$ are transcendental and complex.*

## Discrete Sampling: What Becomes Rational

### Isolating the Transcendental into One Hypothesis

The previous section showed that what is transcendental is the *values* of the characters, while the mechanism of orthogonality is algebraic. This prompts a precise question: *which properties of the characters are needed for orthogonality, and how many of them are transcendental?* The answer is unexpectedly modest. Let us take the values of the characters $\chi(k,j)$ as *abstract* rational parameters (without building $e^{2\pi ikj/N}$) and require of them only three properties:

- (1) the zero frequency is constant: $\chi(0,j)=1$;
- (2) the character is a homomorphism in frequency: $\chi(k,j) \chi(k',j)=\chi(k+k',j)$;
- (3) the vanishing geometric sum: $\sum_{j<N}\chi(m,j)=0$ for $0<m<N$.

Properties (1)–(2) are purely algebraic; *only* property (3) is transcendental: it is the abstract form of the fact “the sum of the roots of unity equals zero.” And under these hypotheses discrete orthogonality is a finite theorem over ℚ (in the range
$k+k'<N$):

$$
\sum_{j<N}\chi(k,j) \chi(k',j)
  =
  \begin{cases} N, & k+k'=0,\\[2pt] 0, & 0<k+k'<N, \end{cases}
$$

proved by pure rational algebra.[^3] The full modular DFT formula $k+k'\equiv0\pmod N$ would require arithmetic of indices modulo $N$, which this file deliberately does not build; in the proved range
$k+k'<N$ the condition $k+k'\equiv0$ coincides with $k+k'=0$. In the classical DFT this is read as orthogonality with the inverse character $k'=-k\pmod N$, usually realized by complex conjugation—but the file builds neither the conjugation nor the modular arithmetic of characters: it proves the rational skeleton under explicit hypotheses.

*The boundary file builds nothing transcendental: it shows that the whole orthogonality of the DFT is the rational algebra of characters plus *one* input, the vanishing sum of the roots of unity. The boundary is compressed into a single explicit hypothesis.*

## Diagnosis: The Boundary Runs along the Choice of the Group

Let us bring the three sections together into one diagnosis. Harmonic analysis is always an expansion in the characters of an abelian group; the *idea* does not depend on the group and is rational. All transcendence enters through the *choice of the group*—more precisely, through the field of values of its characters:

| **Group** | **Characters** | **Status** |
|---|---|---|
| Boolean cube $(ℤ_2^{ n},\oplus)$ | $\pm1$ (Walsh) | rational, core ([[Library/Branches/Mathematics/Volume/07 Harmonic Analysis/02 Walsh Hadamard Transform without Transcendentals\|Chapter 7.2 “Walsh–Hadamard: A Transform without Transcendentals”]]) |
| cyclic $(ℤ_N,+)$ | roots of unity $e^{2\pi ik/N}$ | complex, role-limit |
| circle $(\mathbb{T},+)$ | $e^{2\pi ikx}$, continuum | transcendental, role-limit |

All three are *one and the same* theory of characters; only the group differs, and therefore the field of values. Hence the boundary of ToS runs not between “Fourier” and “non-Fourier” but between groups: rational harmonic analysis is analysis on the Boolean cube, while the cyclic group and the circle drag along roots of unity and the continuum.

*ToS does not lose harmonic analysis: it localizes its rational instance (Walsh) and honestly marks the others as role-limits tied to their groups. Transcendence is a property of the chosen group, not of the very idea of expansion in characters.*

This is the same diagnosis that guided Part IV: where a loss seems to be, there is in fact a renunciation of a completed object (here, of a group with transcendental characters) with all the constructive content preserved.

## E/R/R Analysis: The Boundary as a Choice of Carrier

### Setup

Let us analyze what has been built—the demarcation of the boundary and the conditional theorem of discrete orthogonality—in terms of E/R/R. A reservation about the level: there is one formal object here, the conditional theorem `discrete_orthogonality` under explicit hypotheses; everything else (continuous trigonometry, the complex DFT) is present as a *boundary*, marked, not built. The analysis is a comprehension of the structure of the boundary and a reading of the header of
`ProcessDiscreteTrig.v`,[^4] not an attribution of new claims to the code.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the rule of harmonic analysis: expansion in the characters of an abelian group, where orthogonality follows from the homomorphism property of the characters $\chi_k\chi_{k'}=\chi_{k+k'}$ and the vanishing geometric sum $\sum_j\chi_m=0$. Above it is the *boundary* rule: the field of values of the characters is set by the group, and precisely this field determines whether the result is rational or transcendental. The universal layer is L1–L5; the concrete one is the three hypotheses about characters.

**Roles ($\leftrightarrow$ L4).** The character $\chi_k$ is a role (the label of a harmonic as a homomorphism). The group is the role-carrier: its choice sets the field of values. The hypothesis $\sum_j\chi_m=0$ is the role-encapsulation: the only place into which the transcendental content of the roots of unity is drawn. And the values of $\sin/\cos$ themselves, $e^{2\pi
ik/N}$, the imaginary unit $i$, the number $\pi$, and the continuum integral are role-limits: places toward which processes tend but which ToS does not actualize.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite and
rational: the abstract values $\chi(k,j)\inℚ$ (given by a hypothesis), the indices
$k,k',j<N$, the finite sums $\sum_{j<N}$. Under P4 what remains outside the elements are the transcendental values, the field $ℂ$, and the continuum integral: they are role-limits, not actual objects.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $\chi_k\chi_{k'}=\chi_{k+k'}$; $\sum_j\chi_m=0$; boundary = field of values of the group | HOW orthogonality is arranged and where the boundary runs | Rules ($L5$) |
| character $\chi_k$; group-carrier; hypothesis-encapsulation; $\sin/\cos$, $e^{2\pi ik/N}$, $i$, $\pi$ | WHAT FOR the bearers are significant and what is a role-limit | Roles ($L4$) |
| values $\chi(k,j)\inℚ$; indices $<N$; finite sums $\sum_{j<N}$ | WHAT exists at each stage (finite, rational, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component is in one E/R/R category, and there is no self-reference (P1). What is essential is that the transcendental does not substitute for an Element here: it is honestly held either as a role-limit (the values, $ℂ$, the integral) or as an explicit input hypothesis (the vanishing sum). The conditional theorem does not pretend to have built the roots of unity; it shows that *given* their key property the whole orthogonality is rational.

What the analysis yields. It calls the boundary by its exact name: *the boundary runs along the choice of the group*, that is, along the field of values of the characters. The idea of harmonic analysis, the Rule, is rational and does not depend on the group; the character is a Role; the abstract values are Elements. To take $e^{2\pi ik/N}$, $i$, or $\pi$ for a ready Element is to put a role-limit in the place of an actual object, the same confusion of categories as in the previous chapters. This is why Part VII is arranged as it is: the rational core (Walsh, [[Library/Branches/Mathematics/Volume/07 Harmonic Analysis/02 Walsh Hadamard Transform without Transcendentals|Chapter 7.2 “Walsh–Hadamard: A Transform without Transcendentals”]]) is presented and proved, while the transcendental instances are marked and compressed into explicit hypotheses, without losing a single substantive theorem along the way.

The next chapter returns to the rational core from another side: to the *convergence* of Fourier series in L<sup>2</sup>. There the partial sum is the best approximation (Chapter 7.1), the truncation error equals the tail energy, and all of this is finite and rational; while the passage to the completed infinite series is again an honest P4 boundary.

---

[^1]: The supporting file is `ProcessDiscreteTrig.v` (directory `src/process/`, 2 proved statements, 0 `Admitted`, 0 axioms). It does *not* build $\sin/\cos$, complex numbers, or Euler’s formula; it formalizes *which hypotheses* turn trigonometric orthogonality into a statement about a finite sum.
[^2]: The process reals are $ℕ\toℚ$ (Part IV); complex numbers would require pairs of such processes, but the matter is not the pair but the *values*: $e^{2\pi ik/N}$ is transcendental. Therefore the complex DFT is a role-limit, not a built object.
[^3]: In `ProcessDiscreteTrig.v`: `char_sum_full` (the zero frequency sums to $N$, from (1) and the sum of constants) and `discrete_orthogonality` ($\sum_{j<N}\chi(k,j)\chi(k',j)=N$ for $k+k'=0$, otherwise $0$, for $k+k'<N$). The proof: the homomorphism (2) folds the product into $\chi(k+k',j)$, then (1) or (3). 0 axioms: the transcendence is in hypothesis (3), not in an axiom.
[^4]: The header of the file: Elements—the abstract values $\chi(k,j)\inℚ$; Roles—$\chi_k$ as a character, the hypotheses as the algebraic content of the roots of unity; Rules—$\chi_0=1$, $\chi_k\chi_{k'}=\chi_{k+k'}$, $\sum_j\chi_m=0$ $\Rightarrow$ orthogonality. The file is called a “boundary formaliser.”

---

Part: [[07 Harmonic Analysis|Part VII. Harmonic Analysis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[02 Walsh Hadamard Transform without Transcendentals|Chapter 2. Walsh–Hadamard: A Transform without Transcendentals]] · [[04 Convergence of Fourier Series in L2|Chapter 4. Convergence of Fourier Series in L²]] →
