---
title: "Chapter 3. The Euler Product and the Link to the Primes"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/03 Произведение Эйлера и связь с простыми.md"
sourceBlob: 64513fed8c2fad6cf9d2a640177c427042edc2e5
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 13.1 gave the primes as atoms, Chapter 13.2 zeta as a process of partial sums. This chapter links them by one identity—the *Euler product*:

$$
\zeta(s) \;=\; \prod_{p\ \text{prime}} \frac{1}{1-p^{-s}}
           \;=\; \prod_{p}\frac{p^{s}}{p^{s}-1}.
$$

This is the *main* link between zeta and the primes: on the left is a sum over *all* naturals, on the right a product over the *primes*. And the key to the equality is exactly the fact that we machine-proved in Chapter 13.1: *the uniqueness of prime factorization*. Here the elementary base pays off in analysis.

## Why the Formula Holds: The Uniqueness of Factorization

For each prime $p$ the geometric series gives

$$
\frac{1}{1-p^{-s}} \;=\; 1 + p^{-s} + p^{-2s} + p^{-3s} + …
$$

Let us multiply these series over all primes and expand the brackets. Each term of the product is a choice of one term $p^{-a_p s}$ from each factor, that is, the number

$$
\bigl(\textstyle\prod_p p^{a_p}\bigr)^{-s} \;=\; n^{-s},
  \quad n=\prod_p p^{a_p}.
$$

For *each* $n^{-s}$ to arise *exactly once* in the expansion, each $n$ must correspond to a *unique* tuple of exponents $(a_p)$. This is precisely the fundamental theorem of arithmetic—the *existence and uniqueness* of factorization, which we proved in Chapter 13.1.[^1]

Thus the Euler product is not an accidental identity but a *recoding* of one and the same object:

$$
\prod_p\bigl(1+p^{-s}+p^{-2s}+…\bigr) \;=\; \sum_{n\ge 1} n^{-s},
$$

where the left side is organized *multiplicatively* (by atoms), the right side *additively* (by all numbers), and the bridge between them is the uniqueness of factorization. In the terminology of the part this is the *rule of recoding* a sum into a product.

## The Constructive Side: Partial Products

An infinite product is, like the sum in Chapter 13.2, a *process*: a sequence of *partial* products over the primes up to a bound $N$. For an integer exponent $k\ge 2$ it is given directly over $ℚ$:

```coq
Definition euler_factor (p k : nat) : Q := (* p^k / (p^k - 1) *).
Definition euler_partial (k : nat) (primes_up_to_N : list nat) : Q :=
  Qprod (map (fun p => euler_factor p k) primes_up_to_N).
```

Each factor $`euler_factor` p k = p^{k}/(p^{k}-1)$ is a concrete rational number greater than $1$; the partial product $`euler_partial`$ is the product of these factors over the primes from the sieve. Machine-checked are the positivity, the bounds $>1$ and $\le 2$ for the factors, and also the positivity and *nonvanishing* of each finite partial product; all over $ℚ$, for integer $k\ge 2$, *without axioms*.[^2]

**The honest boundary.**  What is machine-checked is the *constructive side*: the partial products over $ℚ$ for integer $k\ge 2$ and their properties. The *full* infinite identity $\prod_p 1/(1-p^{-s})=\zeta(s)$ for arbitrary $s$ is a classical analytic result; the repository formalizes the process of partial products and the comparison, not a completed transcendental equality. This is the same cut by status as in Chapter 13.2.

## No Zeros for $\Re s>1$

The most important qualitative consequence of the Euler product: in the region of convergence zeta *does not vanish*.

> **Idea.** Each factor $1/(1-p^{-s})\ne 0$ (since $|p^{-s}|<1$). A product of nonzero
> factors with rapidly decreasing deviations from one stays nonzero. Hence $\zeta(s)\ne 0$
> for $\Re s>1$.

The repository formalizes the *finite* side of this fact: each *partial* Euler product (over the primes from the sieve, for integer $k\ge 2$) is positive and not equal to zero.[^3] The limiting $\zeta(k)>0$ and the complex nonvanishing are classical consequences; what matters for us is the qualitative final reading:

> *all the “interesting” zeros of zeta lie in the critical strip $0<\Re s<1$.*

The region $\Re s>1$ is free of zeros (the Euler product), the region $\Re s<0$ holds the trivial zeros (the functional equation, Chapter 13.4). What remains is the strip, where the Riemann Hypothesis lives.

## The Link to the Distribution of Primes

The Euler product is the main link in the classical proof of the prime number theorem (PNT). Taking the logarithm of the product, one obtains the link between zeta and the primes (the logarithmic derivative, Chapter 13.6); the strategy of Hadamard and de la Vallée Poussin is as follows:

1. zeta does not vanish on the line $\Re s=1$ (the main technical statement);
2. the logarithmic derivative of zeta is expressed through the primes;
3. from (1) and (2) the PNT is derived by Tauberian theorems.

**Honestly:** as was stressed in Chapter 13.1, the PNT is *not proved* in this volume. Steps (1) and (2) have operational analogues in `src/zeta/` (the zero-free region, the logarithmic derivative—Chapters 13.5 and 13.6); step (3) and the full asymptotics remain a classical reading. The Euler product here is a *conceptual bridge*: it shows *why* the analysis of zeta speaks about the primes at all.

## A Parallel with the Dynamical Zeta Function

The structure “a product over prime objects” is not unique to arithmetic. In dynamical systems one introduces the *dynamical zeta function*

$$
\zeta_{\mathrm{dyn}}(z) \;=\; \exp\!\Bigl(\sum_{n\ge 1}\frac{N(n)}{n} z^{n}\Bigr),
$$

where $N(n)$ is the number of points of period $n$; its singularities count periodic orbits just as the Riemann zeta function “counts” the primes through the Euler product.[^4] The structural correspondence:

| **Analytic zeta (number theory)** | **Dynamical zeta (dynamics)** |
|---|---|
| prime numbers $p$ | prime periodic orbits |
| $n=p_1^{a_1}\cdots p_k^{a_k}$ | composite orbits (iterations) |
| the counter $\pi(x)$ | the number of points of period $n$ |
| $\zeta(s)=\prod_p 1/(1-p^{-s})$ | $\zeta_{\mathrm{dyn}}(z)$ |
| the Euler product over primes | the product over prime orbits |
| the zeros and the pole of $\zeta$ | the singularities of $\zeta_{\mathrm{dyn}}$ |

This is a deep structural connection: number theory and the theory of dynamics speak one language of zeta functions. In modern mathematical physics it is actively studied (Montgomery’s conjecture, the spectral interpretation of the zeros)—but as an *analogy and a program*, not as a proved identity; its place is Volume III.

## E/R/R Analysis: The Product as a Rule of Recoding

**Rules (L5).**  The constituting rule is *recoding*: the passage from the additive organization (a sum over all $n$) to the multiplicative one (a product over the primes). This rule is *well-formed precisely because* another rule is at work—the uniqueness of factorization (Chapter 13.1). Additionally: the rule of the positivity of the factors (whence $\zeta(k)>0$).

**Roles (L4).**  “The Euler product” is a *role-process* (a sequence of partial products over the primes), the double of the sum-process of Chapter 13.2. “The factor $1/(1-p^{-s})$” is the *role-contribution* of a single atom $p$. “Freedom from zeros for $\Re s>1$” is a *role-consequence* of the positivity of the contributions.

**Elements (L1${}+{}$P4).**  At each stage, finite data: concrete $`euler_factor` p k\inℚ$, partial products over the primes from a finite sieve. *Not* elements: the completed infinite product as an object, the identity for arbitrary $s$ as a ready equality.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the recoding sum ${}\leftrightarrow{}$ product (through the uniqueness of factorization) | the constitution of the link between zeta and the primes | Rule (L5) |
| “the Euler product” ${}={}$ process; factor ${}={}$ the contribution of an atom; freedom from zeros ${}={}$ consequence | the status of objects within the recoding | Role (L4) |
| concrete $`euler_factor` p k$; partial products over the sieve | the bearers at each stage | Element (L1${}+{}$P4) |

**What the analysis removes.**  The Euler product is often presented as a “magical” identity. ToS shows its *mechanism*: it is a recoding whose legitimacy rests on the uniqueness of factorization—that is, on the well-formedness of the role “atom” from Chapter 13.1. The link between zeta and the primes ceases to be a mystery and becomes a consequence of the multiplicative arrangement of $ℕ$.

## What the Chapter Has Prepared

The Euler product has been read as a *rule of recoding* a sum into a product, legitimate by virtue of the uniqueness of factorization (Chapter 13.1); its constructive side (partial products, positivity, $\zeta(k)>0$) is machine-checked over $ℚ$ without axioms, and the full transcendental identity is honestly left classical. Hence the region $\Re s>1$ is free of zeros, and all the interesting zeros are in the critical strip.

Next:

- Chapter 13.4—the functional equation $s\leftrightarrow 1-s$, the trivial zeros, and the critical line;
- Chapter 13.5—the nontrivial zeros, the zero-free region, the zero count $N(T)$;
- Chapter 13.6—the logarithmic derivative and von Mangoldt’s explicit formula (where taking the logarithm of the Euler product of this chapter is exactly what gives the link between the zeros and the primes);
- Chapter 13.7—three forms of the Riemann Hypothesis and the map of boundaries of the part.

---

[^1]: `prime_factorization_unique` and `fundamental_theorem_of_arithmetic` in the new layer `src/numbertheory/PrimeFactorization.v` (existence ${}+{}$ uniqueness up to permutation, Euclid’s lemma through `Nat.gauss`; 0 axioms, by `Print Assumptions`). It is uniqueness that guarantees the bijection “tuples of exponents $\leftrightarrow$ natural numbers,” without which expanding the product would give each $n$ with the wrong multiplicity.
[^2]: `src/zeta/EulerProduct.v` (its header says “AXIOMS: none,” 0 axioms): `Qprod` (a finite product over $ℚ$), `euler_factor`, `euler_partial`, the properties of the factors (`euler_factor_pos`, `euler_factor_gt_1`, `euler_factor_le_2`), and the nonvanishing of the partial product (`euler_partial_nonzero`). The Cauchy *convergence* of the Euler process for $k\ge 2$ is set up separately in `src/zeta/EulerExtension.v` (`euler_convergent_k2`), but it *inherits* `classic` through `MonotoneConvergence`. The file `src/stdlib/EulerProductQ.v` gives a concrete $ℚ$ layer of the first factors at $k=2$ and a comparison with the rational approximation $\pi^2/6\approx 1645/1000$ (`pi_sq_from_euler`)—this is a finite comparison, *not* a proof of $\zeta(2)=\pi^2/6$.
[^3]: `zero_free_partial` and `euler_partial_nonzero` in `EulerProduct.v`: each finite partial product is positive/nonzero (from the positivity of `euler_factor`); 0 axioms. The limiting $\zeta(k)>0$ and the full *complex* nonvanishing $\zeta(s)\ne 0$ for $\Re s>1$ are classical consequences (a product of nonzero factors under absolute convergence), not set up in the current file as limit/complex theorems.
[^4]: The dynamical zeta function is formalized separately in `src/stdlib/DynamicalZeta.v`; its detailed analysis is in the line on dynamical systems (Part VIII). Here we draw only a *structural analogy* and do not prove an identity between the two zeta functions.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/02 Zeta Function as Process|Chapter 2. The Zeta Function as a Process]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/04 Functional Equation|Chapter 4. The Functional Equation]] →
