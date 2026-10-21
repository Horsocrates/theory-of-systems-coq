---
title: "Chapter 5. Compression, Fast Transform, Convolution"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/07 Гармонический анализ/05 Сжатие, быстрое преобразование, свёртка.md"
sourceBlob: a99833759dee6fc7ef5790c4264f005217394b77
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### Applications and the Closing of Part VII

Chapter 7.4 gave the finite core of truncation control: the truncation error equals the discarded tail energy, does not increase when coefficients are added, and vanishes at Parseval. The present chapter draws three *applications* from this core—the very ones for which the Fourier transform is valued in practice—and shows that for Walsh each of them is purely rational: *compression* (discard the insignificant coefficients), the *fast transform* (compute the spectrum in $O(N\log N)$ instead of $O(N^2)$), and *convolution* (turn the convolution of signals into a pointwise product of spectra). After them Part VII closes: rational harmonic analysis has been built from coefficients to convolution, and transcendental trigonometry has been left as an honest boundary.

### What Is Proved—and What Is the Boundary

Proved over ℚ, without axioms.[^1] The truncation error for the first $K$ coefficients equals the sum of the squares of the discarded ones and is monotone in $K$; for Walsh it is controlled by the Plancherel identity; a *band-limited* signal (spectrum in the first $K$ modes) is recovered *without loss*. The fast Walsh transform, a recursive butterfly, gives *exactly* the same result as the matrix transform, for all $N=2^k$. And the convolution theorem
$H(f\ast g)=(Hf)\cdot(Hg)$ is proved for all $2^k$.

What the chapter does *not* claim. The complexity $O(N\log N)$ in itself is an operational property (a count of steps), not an equational identity; what is proved is the *equality* of the fast and matrix transforms, not an estimate of cost. *Optimal* $K$-term compression—the selection of the $K$ coefficients *largest* in magnitude—requires a layer of comparison and sorting; the proved core is truncation by the *first* $K$. Continuous and complex convolutions are the honest boundary of Chapter 7.3.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Setup and Analysis.”

**Rules ($\leftrightarrow$ L5).** Compression error = the sum of the squares of the discarded coefficients (monotone); a band-limited signal gives a zero tail; fast Walsh $=$ the matrix transform; $H(f\ast g)=(Hf)\cdot(Hg)$.

**Roles ($\leftrightarrow$ L4).** Compression is the role-truncation; fast Walsh is the role-algorithm; convolution is the role-product; $O(N\log N)$ is the role-cost (operational); selection by magnitude is a role that requires sorting.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational
coefficients $c_i$, amplitudes $f,g$, XOR indices, finite sums, $N=2^k$; the completed spectrum and cost as a meta-object lie outside the elements (P4).

## Compression as Spectral Truncation

### The Compression Error Is the Discarded Energy

Compression of the spectral type is simple: compute the spectrum, keep the first $K$ coefficients, discard the rest. The quality of compression is the reconstruction error, and it is exactly the *discarded tail energy*:

$$
\norm{f}^2
  \;=\;
  \underbrace{\sum_{i<K} c_i^2}_{\text{kept}}
  \;+\;
  \underbrace{\sum_{K\le i<N} c_i^2}_{\text{discarded}} ,
$$

so the error equals the second sum, exactly what the truncation threw away.[^2] The captured energy grows monotonically with $K$ (and the error decreases)—the same property that carried the finite core of convergence in Chapter 7.4. For Walsh all of this is exact over ℚ: both the coefficients and the energies are rational finite sums. A reservation about scale: here $c_i$ are the coefficients in the *normalized* orthonormal scale (Chapter 7.1); for the raw Walsh spectrum $(Hf)_i$ the same formula is read with the scale $N$, since $\sum_i
(Hf)_i^2 = N\norm{f}^2$ (Plancherel, Chapter 7.2).

### A Band-Limited Signal: Lossless Compression

A special case makes the meaning of compression extremely clear. If the spectrum of a signal is *concentrated* in the first $K$ modes (relative to the chosen Walsh ordering)—that is, $c_i=0$ for $i\ge K$—then the discarded energy is zero, and the first $K$ coefficients recover the signal *without loss*: the captured energy coincides with the full energy.[^3] This is exact compaction: where a signal is *poorer* than the full spectrum, compression comes for free.

### An Honest Boundary: The First $K$ versus the Best $K$

Here runs an important boundary that is easy to miss. The proved core is truncation by the *first* $K$ coefficients (indices $0,…,K-1$): it is exact, rational, and finite. *Optimal* compression into $K$ terms—keeping the $K$ coefficients *largest in absolute value*, wherever they stand—requires *comparing and sorting* them, that is, adding a layer of comparison/selection. The proved core does not build this layer; to confuse “the first $K$” with “the best $K$” is an error.

*Compression error = discarded energy is an exact rational identity (for Walsh), and a band-limited signal is compressed without loss. The proved core is truncation by the first $K$; selecting the best $K$ by magnitude is a separate layer of sorting, an honest boundary.*

## The Fast Transform: The Algorithm Equals the Matrix

The matrix Walsh transform computes $N$ coefficients, each a sum of $N$ terms: $O(N^2)$ operations. But Sylvester’s recursive structure (Chapter 7.2) gives a *butterfly*: a transform of size $2N$ is assembled from two transforms of the halves by additions and subtractions ($\text{lo}+\text{hi}$ and $\text{lo}-\text{hi}$), and this takes $O(N\log N)$ operations. This is how the fast Walsh transform is arranged (an analogue of the fast Fourier transform).

What is proved is the main thing: *the fast butterfly gives exactly the same result as the matrix transform*, for all $N=2^k$.[^4] That is, the optimization does not change the result: the process-algorithm and the matrix-definition coincide as functions.

*Fast Walsh is a process-algorithm provably equal to the matrix transform (exactly over ℚ, all $2^k$). The estimate $O(N\log N)$ itself is an operational property (a count of steps); it is read on top of the proved equality but does not enter the equational core.*

## Convolution: The Seal of Fourier

The applications are crowned by the convolution theorem, that very “seal of Fourier” for which transforms are applied to signals in the first place: *convolution turns into a pointwise product*. For Walsh this is the *dyadic* (XOR) convolution

$$
(f\ast g)(n) = \sum_{m<N} f(m) g(n\oplus m),
$$

and the theorem states that its spectrum is the pointwise product of the spectra:

$$
H(f\ast g) = (Hf)\cdot(Hg),
$$

and this is proved *for all* $N=2^k$ over ℚ.[^5] The practical meaning is direct: convolution, an operation of quadratic cost, can be computed as a transform, a pointwise multiplication, and an inverse transform. Since the unnormalized Walsh satisfies $H^2=N\cdot I$, the inverse step is $H/N$: transform $f,g$, multiply the spectra, apply $H$, and divide by $N$; with the fast Walsh all of this takes $O(N\log N)$.

The proof is the culmination of the group view of Chapter 7.2: convolution turns into a product *because* the Walsh functions are characters of the group $(ℤ_2^{ n},\oplus)$, and characters turn the group operation $\oplus$ into multiplication. The seal of Fourier in Walsh is rational.

*The convolution theorem $H(f\ast g)=(Hf)\cdot(Hg)$, the seal of genuine Fourier, holds for Walsh exactly over ℚ for all $2^k$. Its source is the character property of the group; its consequence is fast convolution through the fast transform.*

## E/R/R Analysis: Applications as Roles over the Transform

### Setup and Analysis

Let us analyze the system of applications—compression, the fast transform, convolution—in terms of E/R/R. A reservation about the level: this is a substantive *interpretation* of three constructions over the already built Walsh transform, not an object `System` in the code; the analysis reads the headers of the supporting files rather than attributing new claims to them.

**Rules ($\leftrightarrow$ L5).** The rules of the applications are built on top of the transform: compression error $=$ discarded energy (monotone in $K$); a band-limited signal $\Rightarrow$ zero tail; fast Walsh $=$ the matrix transform; $H(f\ast g)=(Hf)\cdot(Hg)$. The universal layer is L1–L5; the concrete one is Sylvester’s recursion and the group character.

**Roles ($\leftrightarrow$ L4).** Compression is the role-truncation (keep the first $K$); fast Walsh is the role-algorithm (the same result, lower cost); convolution is the role-pronunciation of the group operation through multiplication. $O(N\log N)$ is the role-cost (operational, on top of the equality); “the best $K$” is a role that requires sorting. The completed spectrum is a role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite and
rational: the coefficients $c_i\inℚ$, the amplitudes $f,g$, XOR indices, finite sums,
$N=2^k$. Under P4 cost as a meta-object and the completed spectrum are not elements: only finite data and finite operations are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| error $=$ discarded energy; band-limited $\Rightarrow$ tail $=0$; fast $=$ matrix; $H(f\ast g)=(Hf)\cdot(Hg)$ | HOW the applications over the transform are arranged | Rules ($L5$) |
| compression-truncation; fast Walsh-algorithm; convolution-product; $O(N\log N)$-cost; best-$K$ | WHAT FOR the bearers are significant; what is operational/boundary | Roles ($L4$) |
| $c_i\inℚ$; $f,g$; XOR indices; finite sums; $N=2^k$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

{
The system is well-formed: each component is in one E/R/R category, and there is no self-reference (P1). What is essential is that the cost $O(N\log N)$ and the selection of “the best $K$” do not substitute for Elements: the first is an operational role on top of the proved equality, the second is a role that requires a separate layer of sorting. The proved core consists of equalities over finite rational data.}

## The Closing of Part VII: Rational Harmonic Analysis

### The Arc of the Part

Part VII has gone through harmonic analysis from end to end, and has carried it out while keeping the proved core separate from the honest boundary. *Chapter 7.1* reformulated the L<sup>2</sup> apparatus of Part VI as a theory of Fourier coefficients: an orthonormal system, projection, Bessel, Parseval, best approximation. *Chapter 7.2* presented a concrete rational system, Walsh–Hadamard, with orthogonality $H^{\mathsf T}H=N\cdot I$, the conservation of energy, and the characters of the Boolean cube: “Fourier without transcendentals.” *Chapter 7.3* drew the boundary: trigonometric and complex Fourier are transcendental not by their idea but by the *choice of the group*. *Chapter 7.4* gave the finite core of truncation control: the truncation error equals the tail energy and monotonically does not increase. *Chapter 7.5* drew out the applications: compression, the fast transform, convolution.

### What Is Proved Rationally and Where the Boundary Lies

The proved rational core of Part VII, over ℚ, without new axioms: Walsh orthogonality for all $2^k$, the discrete conservation of energy (Plancherel), the character property
$\mathrm{w}_i(a\oplus b)=\mathrm{w}_i(a)\mathrm{w}_i(b)$, Bessel’s inequality and the Parseval criterion, best approximation, the finite core of truncation control, compression with an exact error, fast Walsh $=$ matrix, and the convolution theorem. The honest P4 boundaries, marked and not passed off as something larger: the normalization $1/\sqrt N$ (rational only for even $k$), the complex DFT (roots of unity, $i$), continuous trigonometry, the completed infinite series, pointwise convergence and Gibbs, the complexity $O(N\log N)$ as a meta-estimate, and the selection of the best $K$ by sorting.

*Rational harmonic analysis is Fourier analysis on the Boolean cube: characters, orthogonality, the conservation of energy, best approximation, the finite core of truncation control, compression, the fast algorithm, and convolution—all exact over ℚ. Transcendence enters with the normalization $1/\sqrt N$ and especially with the choice of the circle group—and is honestly left as a boundary.*

### A Bridge to Spectral Methods and Physics

Part VII is not an end in itself: it prepares the spectral language for what follows. The Hadamard gate (Chapter 7.2) is already a bridge to quantum computing; the transform as a self-adjoint operator with the conservation of energy (Part VI) leads to the spectral methods of the physics volume, where eigenvalues, evolution, and observables are read in the same process-finite language. Walsh has given a model: genuine harmonic analysis is possible without a single transcendental if the carrier is chosen rationally. The same device—to keep the finite and rational core and to mark the transcendental as a boundary—will carry physics as well.

With this Part VII is closed. The next part goes beyond harmonic analysis, to differential equations on processes, while keeping the recurring method of the volume: every analytic object is a process that can be carried to any precision, not a completed object.

---

[^1]: The supporting files (directory `src/process/`): `ProcessFourierCompression.v` (6 statements), `ProcessWalshCompaction.v` (1), `ProcessFastWalsh.v` (2), `ProcessWalshConvolutionGeneral.v` (7); all with 0 `Admitted`, 0 axioms.
[^2]: In `ProcessFourierCompression.v`: `captured`$(c,K)=\sum_{i<K}c_i^2$; `truncation_error_eq` gives the balance `captured`$(c,N)=$`captured`$(c,K)+$ tail; `captured_mono` is the monotonicity in $K$. For Walsh the full energy is $N\norm{f}^2$ (Plancherel), so the error is controlled by Parseval, `walsh_captured_le_energy`. 0 axioms.
[^3]: `walsh_compaction` in `ProcessWalshCompaction.v`: if $c_i=0$ for $K\le i<N$, then `captured`$(c,N)=$`captured`$(c,K)$—the tail is zero. 0 axioms. Exact rational compression of a band-limited signal.
[^4]: `fwht_correct` in `ProcessFastWalsh.v`: `fwht`$ k f i =$`op_apply`$ (`had` k) f (2^k) i$ for $i<2^k$, by induction on $k$ through Sylvester’s block structure. 0 axioms. “Fast $=$ matrix”: the algorithm as a process equal to the transform.
[^5]: `walsh_convolution` in `ProcessWalshConvolutionGeneral.v`: $H(f\ast g)=(Hf)\cdot(Hg)$ for all $2^k$. The proof relies on the Walsh character property (`had_character`, Chapter 7.2) and on the reindexing of a finite sum under the XOR bijection ($`xor_perm_q_sum`$, proved by Sylvester’s block recursion). 0 axioms.

---

Part: [[07 Harmonic Analysis|Part VII. Harmonic Analysis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[04 Convergence of Fourier Series in L2|Chapter 4. Convergence of Fourier Series in L2]] · [[01 Cauchy Problem and Solution as Process|Chapter 1. The Cauchy Problem and the Solution as a Process—Part VIII]] →
