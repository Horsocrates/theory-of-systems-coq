---
title: "Chapter 2. Walsh–Hadamard: A Transform without Transcendentals"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/07 Гармонический анализ/02 Уолш–Адамар преобразование без трансцендентностей.md"
sourceBlob: 88cd43cca4d965286a2625b5c4715f0b2bdc3f49
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Center of Part VII

The previous chapter built an *abstract* theory—an orthonormal system, Fourier coefficients, projection, Bessel, Parseval, best approximation—and ended with the promise to present a *concrete rational* system on which all this geometry works without a single transcendental. The present chapter fulfills this promise. Its heroine is the *Walsh–Hadamard* transform: an orthogonal $\pm1$ transform over the Boolean cube $ℤ_2^{ n}$, which plays for finite harmonic analysis the same role that the Fourier transform plays for continuous analysis, but requires neither sines nor cosines nor the complex exponential.

This is the central chapter of Part VII, and the choice of its subject is not accidental. Classical harmonic analysis is built on the characters of the circle, the functions $e^{2\pi i k x}$, which at once bring in transcendental values, the imaginary unit, and a completed infinite spectrum. ToS asks: *what in harmonic analysis remains purely rational, finite, and provable without axioms?* The answer: a whole parallel world, if the circle group is replaced by the *Boolean cube* $ℤ_2^{ n}$. Its characters, the Walsh functions, take only the values $\pm1$, their orthogonality is an exact identity over ℚ, and the conservation of energy is a finite sum. Transcendental trigonometry and the complex DFT remain an honest boundary and are analyzed in Chapter 7.3; here is the rational core.

### What This Chapter Claims—and What It Does Not

What is proved here is the following, and all of it *without a single axiom*.[^1] The Hadamard matrix $H_{2^k}$ is built by Sylvester’s recursion from the values
$\pm1$; its rows are pairwise orthogonal with squared norm $N=2^k$, that is, $H_N^{\mathsf T}H_N = N\cdot I$, and this is proved *for all* $2^k$. The Walsh functions are the characters of the group $(ℤ_2^{ n},\oplus)$: the value at the sum (modulo 2) of the arguments is the product of the values. The transform conserves energy, $\norm{Hf}^2 = N\norm{f}^2$ (the discrete Plancherel identity), and is invertible up to scale, $H(Hf)=N f$. Finally, the normalized case $N=2$, if $1/\sqrt2$ is moved out into an abstract parameter $s$ with the relation $s^2\cdot2=1$, is exactly the quantum Hadamard gate.

What the chapter does *not* claim. Literal *orthonormality*
$\inner{e_i}{e_j}=\delta_{ij}$ requires the factor $1/\sqrt N$, which is rational only when $N$ is a perfect square (for $N=2^k$, only for even $k$); therefore the normalization is introduced as an abstract parameter rather than computed. The complex DFT (roots of unity $e^{2\pi ik/N}$, the imaginary unit $i$) and continuous trigonometry are an honest P4 boundary (Chapter 7.3). And “frequency” here is not a real number but a character of a finite group; the ordering of the rows by the number of sign changes (*sequency*) is a permutation that does not change orthogonality.

### The E/R/R Framework of the Chapter

The framework of the system in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter introduces the system of the Walsh–Hadamard transform.

**Rules ($\leftrightarrow$ L5).** Sylvester’s recursion
$H_{2N}=\big[\begin{smallmatrix}H_N&H_N\\ H_N&-H_N\end{smallmatrix}\big]$; orthogonality $H_N^{\mathsf T}H_N=N\cdot I$; the character property
$\mathrm{w}_i(a\oplus b)=\mathrm{w}_i(a) \mathrm{w}_i(b)$; the conservation of energy
$\norm{Hf}^2=N\norm{f}^2$.

**Roles ($\leftrightarrow$ L4).** The row $\mathrm{w}_i$ is the role-character (frequency as a character of the group); $H$ is the role-transform; $\oplus$ is the role-operation of the group $ℤ_2^{ n}$; the normalization $1/\sqrt N$ is a role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The rational
values $\pm1$ of the matrix, indices $i,j<2^k$, amplitudes $f_j\inℚ$, finite sums; the completed spectrum and transcendental values lie outside the elements (P4).

## The Hadamard Matrix: Sylvester’s Recursion

### Doubling Instead of Oscillation

A trigonometric harmonic is given by *oscillation*: $\cos$ and $\sin$ run through a continuous range of values. A Walsh function is given by the *doubling of a sign table*. The base block is the unit matrix $H_1=[ 1 ]$. Each next level is obtained by Sylvester’s recursion:

$$
H_{2N} \;=\;
  \begin{pmatrix} H_N & H_N \\ H_N & -H_N \end{pmatrix},
$$

so that

$$
H_2 = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix},
  \quad
  H_4 = \begin{pmatrix}
    1 & 1 & 1 & 1 \\ 1 & -1 & 1 & -1 \\ 1 & 1 & -1 & -1 \\ 1 & -1 & -1 & 1
  \end{pmatrix}.
$$

Each entry is $+1$ or $-1$, that is, a purely rational number; no passage to the limit, no transcendental values.[^2] The sign of the entry $(i,j)$ is determined by the high-order bits of the indices $i$ and $j$: the upper-left, upper-right, and lower-left blocks repeat $H_N$, and the lower-right one is taken with a minus sign—exactly what the recursive formula encodes.

### Rows as Walsh Functions

The $i$-th row of the matrix is the *Walsh function* $\mathrm{w}_i$: it assigns to column $j$ the sign $H_{ij}\in\{\pm1\}$. This is a discrete analogue of the $i$-th harmonic: the “higher the frequency,” the more often the function changes sign along the row. The analogy with trigonometry here is literal in structure and diverges only in the *carrier*: instead of a continuous interval, a finite set of $N=2^k$ points; instead of the real values of an oscillation, the signs $\pm1$.

*A Walsh harmonic is not an oscillation but a sign pattern built by doubling. “Frequency” is measured by the number of sign changes, not by the real argument of a sine; the whole spectrum is finite and rational.*

Let us note one technical nuance. Sylvester’s recursion numbers the rows in the so-called *natural* (Hadamard) ordering, which does not coincide with the ordering by an increasing number of sign changes (*sequency*), the true analogue of increasing frequency. The passage to the sequency ordering is a *permutation* of rows; it changes neither orthogonality nor the conservation of energy, so everything proved below does not depend on the choice of ordering.

## Orthogonality: $H_N^{\mathsf T}H_N = N\cdot I$

### An Exact Identity Instead of an Integral

The heart of all harmonic analysis is the orthogonality of the basis functions. In trigonometry it is expressed by the integrals $\int \sin(mx)\sin(nx) dx = 0$ for $m\neq n$—and this is already a transcendental object: an integral of a product of transcendental functions. For Walsh the same orthogonality is a *finite sum of products of signs*:

$$
\sum_{j<N} H_{ij} H_{i'j}
  \;=\;
  \begin{cases} N, & i=i',\\[2pt] 0, & i\neq i', \end{cases}
$$

that is, $H_N^{\mathsf T}H_N = N\cdot I$. Different rows are orthogonal, and each has squared norm $N$. And this is proved *for all* $N=2^k$—by induction on Sylvester’s recursive structure, as an exact identity over ℚ, without a single axiom.[^3]

*Walsh orthogonality is not an integral that has to be “taken” but a finite sum of
$\pm1$ that is *computed*. Where trigonometry relies on the analysis of transcendental functions, Walsh relies on the addition of integers.*

It is precisely this that makes Walsh–Hadamard the point of support of rational harmony: an orthogonal system on which the whole abstract theory of Chapter 7.1 (coefficients, projection, Bessel, Parseval) is literally fulfilled, and each of its premises, $\inner{e_i}{e_j}=N\delta_{ij}$, is not a postulate but a proved equality.

## Walsh Functions as Characters of the Boolean Cube

### What Harmonic Analysis Really Is

Behind all of harmonic analysis stands one idea: to expand a function in the *characters of a group*, the homomorphisms of the group into the multiplicative group of values. For the circle the characters are $x\mapsto e^{2\pi i k x}$, and their key property is turning the addition of arguments into the multiplication of values: $e^{2\pi ik(x+y)} = e^{2\pi ikx} e^{2\pi
iky}$. It is precisely this property that stands behind the convolution theorem, behind the conservation of energy, behind the whole algebra of Fourier.

The Walsh functions have *exactly the same* property—but for a different group and with rational values. The group here is the Boolean cube $(ℤ_2^{ n},\oplus)$ with the operation of bitwise addition modulo 2 (XOR), and the values of the characters are $\pm1$. It is proved:

$$
\mathrm{w}_i(a\oplus b) \;=\; \mathrm{w}_i(a) \mathrm{w}_i(b)
  \quad (i,a,b<2^k),
$$

that is, each Walsh function $\mathrm{w}_i$ is a homomorphism
$(ℤ_2^{ n},\oplus)\to(\{\pm1\},\cdot)$, a *character* of the Boolean cube.[^4]

*A Walsh function is a character of the Boolean cube: it turns the group operation
$\oplus$ into multiplication. The “frequency” $i$ is not a number but a *label of a character*. Walsh harmonic analysis is Fourier analysis on $ℤ_2^{ n}$, where the rational cube has replaced the transcendental circle.*

### Why This Is the “Real Fourier”

From this one sees in what exact sense Walsh is not a “simplified imitation” of Fourier but its full-fledged sibling. The structure is one and the same: *an orthogonal basis of characters of an abelian group*—and after the normalization $1/\sqrt N$ it becomes orthonormal; in the Walsh layer the orthogonal structure itself is rational, while the normalization is moved out as a separate boundary. Only the group changes: instead of the circle $\mathbb T$ (or $ℤ_N$ with roots of unity), the Boolean cube $ℤ_2^{ n}$. The circle drags transcendence and complexity along with it; the cube remains in ℚ. What in Fourier analysis rests on the character property is the conservation of energy and the convolution theorem. We have already conserved energy; the convolution theorem $H(f\ast g)=(Hf)\cdot(Hg)$ rests on the same character and is proved *for all* $2^k$—through the reindexing of a finite sum under the XOR bijection—and is unfolded in Chapter 7.5.[^5]

## Conservation of Energy and the Hadamard Gate

### The Discrete Plancherel Identity

From orthogonality follows the conservation of energy. The Walsh transform of a function $f$ is the vector of its coefficients $(Hf)_i = \sum_{j<N} H_{ij} f_j$. Then

$$
\norm{Hf}^2 \;=\; N \norm{f}^2 ,
$$

a discrete analogue of the Plancherel identity: the energy of the spectrum equals the energy of the signal with a factor $N$.[^6] The transform is, moreover, invertible: applied twice, it only rescales the signal,

$$
H(Hf) \;=\; N f,
$$

so that the inverse transform is $H^{-1} = \tfrac1N H$, again without any transcendence.[^7] Passing to the normalized system divides both sides by $N$ and returns the Parseval of Chapter 7.1 in the form $\sum_i c_i^2=\norm{f}^2$—but the factor
$1/\sqrt N$ that makes $H/\sqrt N$ an isometry is rational only for even $k$ and in the general case remains a role-limit.

### The Hadamard Gate: A Bridge to Quantum Computing

The case $N=2$ has its own name. The matrix $H_2=\big[\begin{smallmatrix}1&1\\
1&-1\end{smallmatrix}\big]$, normalized by the factor $1/\sqrt2$, is the *quantum Hadamard gate*, the elementary brick of quantum computing (it creates superposition in the algorithms of Grover, Deutsch–Jozsa, and others). Its two defining features are proved as rational facts, with the only transcendence, the normalization, moved out into an abstract parameter.

First, the gate is an *involution*: $H^2=I$; applied twice, it returns the initial state.[^8] Second, it creates an *equal superposition*: from the basis state $\lvert0\rangle$ it makes a vector with equal amplitudes $1/\sqrt2$ on both outcomes.[^9]

*The conservation of energy is an exact rational fact ($\norm{Hf}^2=N\norm{f}^2$); the quantum Hadamard gate is the normalized Walsh transform on two points. The only transcendence, the normalization $1/\sqrt N$, is separated and marked; the structure of the gate (involution, superposition) is rational.*

## E/R/R Analysis: The Transform as Characters of a Group

### Setup

Let us analyze the constructed system—the Walsh–Hadamard transform—in terms of E/R/R. A reservation about the level: the “Walsh system” here is a substantive *interpretation* of the concrete matrix $H_{2^k}$ and its action, not an object declared in the code as `System`. The analysis is an ontological comprehension of the structure of the chapter and a reading of the author’s E/R/R headers of the supporting files,[^10] not an attribution of new formal claims to the code.

We conduct the analysis in the generating order Rules $\to$ Roles $\to$ Elements (epistemically the chapter went the other way, from the observable matrix to its group meaning).

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the generating rule of the matrix: Sylvester’s recursion, which doubles the sign table. Above it are the rules that sustain this table: orthogonality $H_N^{\mathsf T}H_N=N\cdot I$, the character property $\mathrm{w}_i(a\oplus b)=\mathrm{w}_i(a)\mathrm{w}_i(b)$ (a homomorphism into
$\{\pm1\}$), and the conservation of energy $\norm{Hf}^2=N\norm{f}^2$. The universal layer is the laws L1–L5; the concrete layer is precisely Sylvester’s recursion and the group operation $\oplus$.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The row
$\mathrm{w}_i$ is the role-character: the place that the “frequency” $i$ occupies as a homomorphism of the group. $H$ itself is the role-transform (reading off all coordinates at once). The operation
$\oplus$ is the role of group structure on the set of indices. And the normalization $1/\sqrt N$ is a role-limit: what turns an orthogonal system into an orthonormal one; for square $N$ it is rational, but in the general case it is not actualized over ℚ.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The roles select
bearers, and the bearers are finite and rational: the values $\pm1$ of the entries of the matrix, the indices
$i,j<2^k$, the amplitudes $f_j\inℚ$, the finite sums $\sum_{j<N}$. Under P4 no element is a completed infinity and no value is transcendental: only the finite matrix and finite sums are actual; the completed spectrum and the value
$1/\sqrt N$ for odd $k$ are not actualized.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| Sylvester’s recursion; $H^{\mathsf T}H=N\cdot I$; $\mathrm{w}_i(a\oplus b)=\mathrm{w}_i(a)\mathrm{w}_i(b)$; $\norm{Hf}^2=N\norm{f}^2$ | HOW the transform is built and preserved | Rules ($L5$) |
| character $\mathrm{w}_i$; transform $H$; operation $\oplus$; normalization $1/\sqrt N$ | WHAT FOR the bearers are significant: places in the system | Roles ($L4$) |
| values $\pm1$; indices $i,j<2^k$; $f_j\inℚ$; finite sums $\sum_{j<N}$ | WHAT exists at each stage (finite, rational, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

{
The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the system takes as its element neither a completed infinite spectrum nor a transcendental value. “Frequency” is not a real number-element but a *role*-character of a finite group; the group $(ℤ_2^{ n},\oplus)$ is finite, it has exactly $N$ characters, and all of them are presented as rows of a concrete matrix.}

What the analysis yields. It reveals why Walsh is genuine harmonic analysis and not a surrogate for it: *a Walsh function is a Role* (a character of a group), *the transform is a Rule* (recursion plus orthogonality plus the conservation of energy), and the $\pm1$ values and amplitudes are *Elements* (finite, rational). Transcendence enters classical Fourier not through the *idea* of harmonic analysis but through the *choice of the group*: the circle. Replacing the circle by the Boolean cube, we obtain the same idea in a purely rational execution. To take “frequency” for a real number or the spectrum for a completed infinite object is to put a role-limit in the place of an Element, the same confusion of categories that guided Parts II and IV.

The next chapter outlines the boundary from the other side: what happens when the group taken is *after all* the circle—continuous trigonometry and the complex DFT with roots of unity. There one sees what exactly becomes transcendental and why ToS holds this as an honest P4 boundary, while keeping Walsh–Hadamard as the rational core of harmonic analysis.

---

[^1]: The supporting file is `ProcessWalshHadamard.v` (directory `src/process/` of the ToS Rocq repository, 12 proved statements, 0 `Admitted`, 0 axioms), supplemented by `ProcessFourierON.v` (5 statements), `ProcessWalshCharacter.v` (7 statements), and `ProcessHadamardGate.v` (5 statements). The lemma names are in the notes below.
[^2]: In the code the matrix is given recursively: `had k i j` returns the entry $(i,j)$ of the matrix $H_{2^k}$ as a value from $\{+1,-1\}$ (`ProcessWalshHadamard.v`); the size $N=2^k$ is `pow2 k`. The sign nature is fixed by the lemma `had_sq`: each entry squared equals $1$.
[^3]: The central theorem `hadamard_orthogonal` in `ProcessWalshHadamard.v`: $\sum_{j<2^k} H_{ij}H_{i'j} = 2^k \delta_{ii'}$, proved by induction on $k$. The diagonal case ($i=i'$) is `walsh_norm`: each row has squared norm $N$. The concrete $N=2,4$ are `hadamard_2_orthogonal`, `hadamard_4_orthogonal`. All: 0 axioms.
[^4]: The theorem `had_character` in `ProcessWalshCharacter.v`: $`had `k i (a\oplus b) = `had `k i a \cdot `had `k i b$, proved by induction on $k$ with an analysis of the bit structure of `Nat.lxor` (XOR). 0 axioms. XOR here is the operation of the group $ℤ_2^{ n}$.
[^5]: The general convolution is `walsh_convolution` in `ProcessWalshConvolutionGeneral.v`: $H(f\ast g)=(Hf)\cdot(Hg)$ for all $2^k$, through the character (`had_character`) and the lemma `xor_perm_q_sum` (the invariance of `q_sum` under the XOR bijection, proved by Sylvester’s block recursion). 0 axioms.
[^6]: The theorem `parseval_walsh` in `ProcessFourierON.v`: $\inner{Hf}{Hf}_N = N \inner{f}{f}_N$, derived from the self-adjointness of the transform (the Walsh matrix is symmetric, `had_symmetric`) and the identity $H^2=N\cdot I$. 0 axioms.
[^7]: `walsh_HH` in `ProcessFourierON.v`: $H(Hf)=N f$ (Fourier inversion up to $1/N$); it follows from $H_N^{\mathsf T}H_N=N\cdot I$ and the symmetry of $H$.
[^8]: `hgate_involution` in `ProcessHadamardGate.v`: for the normalized gate $`hgate`(`hgate ` f)=f$. The normalization $1/\sqrt2$ is introduced as an abstract parameter $s$ with the relation $s^2\cdot2=1$; the identity $H(Hf)=2f$ (the special case $N=2$) then gives $s^2\cdot 2\cdot f=f$. The entries of $H_2$ themselves are from $\{\pm1\}$ (`hadamard_2x2`).
[^9]: `hgate_superposition`: $`hgate` e_0 = (s,s)$, equal amplitudes on two coordinates. This is the passage from a definite state to a superposition performed by the Hadamard gate.
[^10]: The headers give the labeling directly: `ProcessWalshHadamard.v`—Elements: the $\pm1$ matrix, size $2^k$; Rules: Sylvester’s recursion, $H^{\mathsf T}H=N\cdot I$. `ProcessWalshCharacter.v`—Rules: $\mathrm{w}_i(a\oplus b)=\mathrm{w}_i(a)\mathrm{w}_i(b)$; Roles: $\mathrm{w}_i$ is a character $(ℤ_2^{ n},\oplus)\to\{\pm1\}$. `ProcessFourierON.v`—Rules: $\norm{Hf}^2=N\norm{f}^2$.

---

Part: [[07 Harmonic Analysis|Part VII. Harmonic Analysis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[01 Orthonormal Systems and Fourier Coefficients|Chapter 1. Orthonormal Systems and Fourier Coefficients]] · [[03 Trigonometry and Complex Dft Where the Boundary Lies|Chapter 3. Trigonometry and the Complex DFT: Where the Boundary Lies]] →
