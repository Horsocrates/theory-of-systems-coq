---
title: "Chapter 2. The Zeta Function as a Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/02 Дзета-функция как процесс.md"
sourceBlob: d26be5965af46fc1c87e6590b2ed4ff1fa852be8
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 13.1 established the arithmetic base: the primes as atoms, factorization with uniqueness, Euclid’s infinitude as an algorithm, the counter $\pi(x)$. Now we introduce the object that gathers these data *analytically*—the Riemann zeta function

$$
\zeta(s) \;=\; \sum_{n=1}^{\infty}\frac{1}{n^{s}}.
$$

Classically $\zeta$ is a *function* defined on (almost all of) the complex plane. In ToS the leading reading is different, and it is the flagship of this chapter:

> *the zeta function is a process of partial sums*—the sequence $\zeta_N(s)=\sum_{n=1}^{N}
> n^{-s}$, considered as a Cauchy process, not as a completed object.

This is exactly the move that in Part IV gave $ℝ$ as a Cauchy process, not as a ready continuum. Zeta inherits the same ontology: on one level it is a process (a sequence of rational partial sums at an integer exponent), on another an analytic function (a role-limit). The pole, the zeros, analytic continuation are structural features of this process, not properties of a totality given in advance.[^1]

## Definition through Partial Sums

For an integer exponent $k\ge 2$ zeta is given directly—as a process of partial sums over $ℚ$:

```coq
Definition zeta_term (k n : nat) : Q := 1 / nat_power (S n) k.
Definition zeta_partial (k N : nat) : Q := (* sum of zeta_term k n over n < N *).
Definition zeta_process (k : nat) : nat -> Q := fun N => zeta_partial k N.
```

Here $\texttt{nat\_power} (n) k = n^{k}$ is an exact integer power, so that each partial sum $\zeta_N(k)=\sum_{n=1}^{N} 1/n^{k}$ is a *concrete rational number*. The *process* $\texttt{zeta\_process} k$ is the sequence $N\mapsto\zeta_N(k)$.[^2]

**The restriction on the exponent.**  We work with *integer* $k\ge 2$ precisely because for them $n^{k}$ is exactly computable over $ℚ$—by finite data, without recourse to $ℝ$. For a non-integer $s$ (for example, $s=3/2$) already $n^{s}$ itself requires the exponential and the logarithm, that is, a transfer into the mode of Cauchy processes; this step honestly belongs to the continuum boundary of the part (the map is in 13.7).

## Convergence for $k\ge 2$

The main result about this process is its convergence for all integer $k\ge 2$:

> **Theorem.** For every integer $k\ge 2$ the process $\texttt{zeta\_process} k$ is a Cauchy
> process.[^3]

The proof is a *telescoping comparison*. Since for $k\ge 2$

$$
\frac{1}{(n+1)^{k}} \;\le\; \frac{1}{(n+1)^{2}} \;\le\; \frac{1}{n(n+1)} \;=\; \frac1n-\frac1{n+1},
$$

the partial sums are dominated by the telescoping sum $\sum_n\bigl(\tfrac1n-\tfrac1{n+1}\bigr)=1$. Hence $\zeta(k)\le 2$ and, more importantly, the telescoping estimate of the tail is *explicit*: for a given $\varepsilon>0$ one writes out $N(\varepsilon)$ for which $|\zeta_N(k)-\zeta_M(k)|<\varepsilon$ for $M,N\ge N(\varepsilon)$. This estimate itself does not use the Axiom of Choice; at the same time, the passage “monotone bounded sequence $\Rightarrow$ Cauchy process” in the current formal layer goes through `MonotoneConvergence` and inherits `classic` (L3, not AC).

This is the meaning of the word “process”: convergence is not postulated by the existence of a limit in a ready $ℝ$ but *presented* as the controlled behavior of a rational sequence.

## Divergence at $s=1$: The Pole as a Role-Singularity

At $s=1$ the picture breaks off: the harmonic series diverges.

> **Lemma.** The process $\texttt{zeta\_process} 1$ is *not* a Cauchy
> process.[^4]

Ontologically this is essential: at $s=1$ zeta has a *pole*. In ToS a pole is not an “infinite value” but a *role-singularity*: a point where the process *goes beyond every bound*, that is, ceases to be a Cauchy process. The pole is a property of the *behavior* of the process, not a number in a completed table of values. This single singularity at $s=1$ organizes, as we will see, the whole analytic theory: it is precisely the pole at $s=1$ that serves as the key input to the classical proofs of the zero-free region near the line $\Re s=1$ (Chapter 13.5).

## The Complex Extension

For complex $s=\sigma+it$ zeta is defined analogously:

$$
\zeta(\sigma+it) \;=\; \sum_{n\ge 1}\frac{1}{n^{\sigma+it}}
                  \;=\; \sum_{n\ge 1}\frac{1}{n^{\sigma}} e^{-it\ln n}.
$$

What is formalized in Rocq is a *complex-structural* layer: a complex number as a pair of rational coordinates (`TComplex`), partial sums at an *integer* exponent (`zeta_complex_at_integer`—with zero imaginary part), norms, the modulus estimate $|\zeta_N(\sigma+it)|\le\zeta_N(\sigma)$, the pole, and the dichotomy “$k=1$ diverges / $k\ge 2$ converges.”[^5]

Complexity adds no new ontology here—it only doubles the bearer: one coordinate for $\Re$, the other for $\Im$. We do not build the *completed* complex zeta at an arbitrary $s$ as an object; what is formalized is the structural layer and the dichotomy of convergence, and the full continuum zeta is honestly marked as a boundary.

## Analytic Continuation

The main nontrivial fact of the classical theory: $\zeta$ continues to the whole complex plane except $s=1$ (where the pole is). Classically this is done through the functional equation (Chapter 13.4), an integral representation, or the Mellin transform.

In ToS analytic continuation is read operationally—as a *new process*, *consistent* with the original one in the region of convergence $\Re s>1$. The key is *analytic rigidity*: an analytic function is uniquely determined by its values in a neighborhood, and therefore the continuation is unique.[^6]

**An honest reservation.** The full analytic continuation to the *whole* plane is already work with the continuum (non-integer/complex $s$ as completed objects), and it belongs to the boundary of the part (13.7). In the repository `ComplexZeta.v` formalizes processes for separate regions and the dichotomy of convergence; we do not build the *completed* function on the whole plane as an object—we describe the rule of its consistent continuation and honestly mark the continuum price.

## Special Values and the Identity $\zeta(-1)=-\tfrac1{12}$

### Even Values and the Bernoulli Numbers

The concrete values of zeta at even points are classical:

$$
\zeta(2)=\frac{\pi^{2}}{6},\quad \zeta(4)=\frac{\pi^{4}}{90},\quad
  \zeta(2k)=(\text{rational})\cdot\pi^{2k}.
$$

These are deep identities (Euler’s Basel problem, 1735, and Euler’s general formula through the Bernoulli numbers). *Honestly:* the closed form $\zeta(2)=\pi^2/6$ is a classical result about a transcendental quantity, and we do not present it as a completed Rocq equality; what is machine-checked is the *process*—the convergence of the partial sums and partial products to this limit (Chapter 13.3). What is *proved* in the repository is the Bernoulli numbers themselves as exact rationals and the exact rational values of the Bernoulli layer.[^7]

### $\zeta(-1)=-\tfrac1{12}$: A Diagnosis of Two Processes

One of the best-known identities, and one of the most paradoxical for the general public, is

$$
1+2+3+4+… \;\overset{?}{=}\; -\tfrac1{12}.
$$

The left-hand side is a divergent series of positive integers; the right-hand side is a negative fraction. In ToS the paradox is *laid open* as a category confusion of *two different processes*.

- **The process of convergence** ($\Re s>1$): $\zeta_{\mathrm{conv}}(s)=\sum 1/n^{s}$ is a Cauchy process converging to a concrete number.
- **The process of analytic continuation** ($s<0$): $\zeta_{\mathrm{anal}}(s)$ is another process, given by another formula (through the functional equation / the Bernoulli numbers), also converging to a concrete number.

In the region $\Re s>1$ both processes give *one and the same* number (by the uniqueness of continuation, “Analytic Continuation”). The value $\zeta(-1)$ is the value of the *second* process at $s=-1$, computed by an explicit formula:

$$
\zeta_{\mathrm{anal}}(-1) \;=\; -\frac{B_2}{2} \;=\; -\frac{1/6}{2} \;=\; -\frac1{12}.
$$

The *strict* statement, then, is not “the sum $1+2+3+…$ equals $-1/12$” (as a process of convergence it diverges) but: “the analytic continuation of the function $\sum 1/n^{s}$, defined for $\Re s>1$, to the point $s=-1$ gives $-1/12$.” The everyday notation pulls two processes together into one equals sign—and this is the error being diagnosed.

**The physical meaning.**  The value $\zeta(-1)=-1/12$ has real applications: the Casimir effect (a finite force between plates after the regularization of a divergent sum of vacuum modes) and the critical dimension of the bosonic string ($D=26$). The ToS reading: in physically measurable quantities the divergent formal series is replaced by a *regularized* process, and ToS diagnoses this as a *change of rule*, not as the literal sum of a divergent series; the finite quantity is the result of *another*, algorithmically rigid process—analytic continuation. A detailed discussion belongs to physics; here we only record the mathematical basis.[^8]

### Odd Values: $\zeta(3)$ as a Process

For the odd values no closed forms through $\pi$ are known. The irrationality of $\zeta(3)$ was proved by Apéry (1979); for $\zeta(5),\zeta(7),…$ even this is unknown for most of them—an open field. In ToS $\zeta(3)$ naturally lives as a *process*: two rational procedures of approximation are formalized—the standard partial sums and the first Apéry-accelerated values—with exact computations and comparisons (brackets).[^9]

## E/R/R Analysis: Zeta as a Process-System

**Rules (L5).**  The constituting rule is the *summation of the process of partial sums*: $\zeta_N(k)=\sum_{n\le N}n^{-k}$ with an explicit modulus of convergence for $k\ge 2$. A separate rule is the *singularity at $s=1$* (the divergence of the harmonic series). Analytic continuation is a *new rule*, consistent with the original one in $\Re s>1$ (unique by analytic rigidity).

**Roles (L4).**  “Zeta” is a *role-process*: on one level a sequence of rational partial sums, on another an analytic function (a role-limit). “The pole $s=1$” is a *role-singularity*. The values $\zeta(2k)$, $\zeta(3)$ are *role-limits* (results of the process). $\zeta(-1)$ is a value of *another* process (the continuation).

**Elements (L1${}+{}$P4).**  At each stage, finite data: the partial sums $\zeta_N(k)$ (rational for integer $k\ge 2$), pairs of rationals for the complex case, exact Bernoulli numbers. *Not* elements: the completed function $\zeta$ on the whole plane, the “sum” of a divergent series as a number, $n^{s}$ for non-integer $s$ as a ready object.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the summation of partial sums; the modulus of convergence ($k\ge 2$); the continuation consistent in $\Re s>1$ | the constitution of zeta as a process | Rule (L5) |
| “zeta” ${}={}$ process; “the pole $s{=}1$” ${}={}$ singularity; $\zeta(2k),\zeta(3)={}$ role-limits | the status of an object within the process | Role (L4) |
| partial sums $\zeta_N(k)$; pairs of rationals; Bernoulli numbers | the bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes (diagnosis).**  The root error is the reification of zeta as a *completed function-object* and the ascription of a “sum” to a divergent series. ToS separates: zeta is a process; $\zeta(-1)=-1/12$ is a value of *another* process (the continuation), which coincides with the first only in $\Re s>1$; the pole is behavior (going beyond a bound), not an “infinite value.” This is the same discipline that in Part IV did not allow a Cauchy process to be confused with the completed continuum $ℝ$.

## What the Chapter Has Prepared

Zeta has been established as a *process of partial sums*: with an explicit telescoping estimate for integer $k\ge 2$ (the Cauchy formulation in the file inherits `classic` through `MonotoneConvergence`), divergent at $s=1$ (the pole as a role-singularity), doubled into a structural complex layer, and continued as a consistent new process. The famous $\zeta(-1)=-1/12$ has been read as a diagnosis of two processes, not as an identity of a divergent series.

Next:

- Chapter 13.3—the Euler product: zeta as a process over the primes (resting on the uniqueness of factorization from Chapter 13.1);
- Chapter 13.4—the functional equation and the critical line;
- Chapter 13.5—the zeros, the zero-free region, and the counting of zeros;
- Chapter 13.6—von Mangoldt’s explicit formula, which links the zeros with the distribution of primes;
- Chapter 13.7—three forms of the Riemann Hypothesis and the map of boundaries of the part (where the continuum price, the classical reading, and openness are all gathered).

---

[^1]: Zeta as a process is formalized in `src/zeta/ZetaProcess.v` and in the complex-structural layer `src/zeta/ComplexZeta.v`—parts of the `src/zeta/` corpus (exact counts per the current build accounting). *A reservation about axioms:* `ZetaProcess.v`, in the Cauchy formulation, inherits `classic` (L3—the excluded middle, one of the two base axioms of the volume) through `MonotoneConvergence`; this is L3, not the Axiom of Choice.
[^2]: `ZetaProcess.v`: `zeta_term`, `zeta_partial`, `zeta_process`.
[^3]: `zeta_process_cauchy` in `ZetaProcess.v`: $\forall k,\ 2\le k\Rightarrow \texttt{is\_cauchy}(\texttt{zeta\_process} k)$. The explicit telescoping estimate is given by `zeta_term_2_le_shifted_tele` and `zeta_partial_bounded`; the Cauchy formulation inherits `classic` through `MonotoneConvergence`.
[^4]: `zeta_1_not_cauchy` in `ZetaProcess.v`. The standard grouping $1+\tfrac12+(\tfrac13+\tfrac14)+\dots>1+\tfrac12+\tfrac12+\dots$ gives unbounded growth: for every $M$ there is an $N$ with $\sum_{n\le N}1/n>M$. This is an algorithmic statement of divergence.
[^5]: `ComplexZeta.v`: `TComplex`, `zeta_complex_at_integer`, norm estimates, `pole_unbounded`, `zeta_dichotomy`. *Honestly:* the full formula $n^{-s}=e^{-s\ln n}=n^{-\sigma}\bigl(\cos(t\ln n)-i\sin(t\ln n)\bigr)$ for an arbitrary complex $s$ is *not* built in this file (it stands in the header as an intention); its realization requires the exponential and the logarithm and belongs to the continuum boundary of the part (13.7).
[^6]: This principle (the “algorithmic rigidity” of analytic functions) is discussed in detail in the line on analytic functions in Part VII; here we use only its consequence—the uniqueness of the consistent continuation.
[^7]: `src/experimental/BernoulliNumbers.v`: the Bernoulli numbers $B_0=1$, $B_1=-\tfrac12$, $B_2=\tfrac16$, $B_3=0$, $B_4=-\tfrac1{30}$, … as exact rationals. The same file defines the Bernoulli layer $\texttt{zeta\_neg}(k):=-B_{k+1}/(k+1)$ and machine-computes the first values (`zeta_neg_0..3`, including $\texttt{zeta\_neg\_1}=-\tfrac1{12}$). This formalizes the exact *rational* side of the values of the continuation but does *not* prove the analytic continuation itself.
[^8]: In the repository, regularization and the Casimir effect are touched on separately (`src/experimental/CasimirProcess.v`, `AbelRegularization.v`); full-fledged physics lies beyond this chapter.
[^9]: `src/foundation/AperyConstantERR.v`: the standard and Apéry-accelerated partial sums of $\zeta(3)$, exact rational values and comparisons, $\zeta(3)\approx 1.202\dots$; the E/R/R analysis: $\zeta(3)$ is a process, not an Element. The *equality* of the limit values of both procedures and the *irrationality* of $\zeta(3)$ (Apéry, 1979) are a classical mathematical reading, not reformalized here.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/01 Primes in Operational Ontology|Chapter 1. Prime Numbers in the Operational Ontology]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/03 Euler Product and the Link to Primes|Chapter 3. The Euler Product and the Link to the Primes]] →
