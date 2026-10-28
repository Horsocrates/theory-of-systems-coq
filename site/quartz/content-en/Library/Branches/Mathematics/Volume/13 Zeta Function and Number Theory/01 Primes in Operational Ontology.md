---
title: "Chapter 1. Prime Numbers in the Operational Ontology"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/13 Дзета-функция и теория чисел/01 Простые числа в операциональной онтологии.md"
sourceBlob: 9d5a00e1ab5e51ca73945a60c2d38e72d917e8d1
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part XIII

Part XII reread geometry: a point turned out to be a *role-position*, curvature an *angular defect*, a manifold a *process of refining triangulation*, not a ready continuum thing. Part XIII turns to number theory and to its central analytic object—the Riemann zeta function. For a classical mathematician this is perhaps the most intriguing part of the volume: here lives the Riemann Hypothesis, unsolved since 1859, and here, too, we carefully separate what is *proved* from what is *assumed* or *remains open*.

The through-line of the part is short: *the zeta function is a process of partial sums; the theory of prime numbers is the study of this process; the zeros and the pole of zeta are its structural features; the Riemann Hypothesis is an open statement about the structure of the zeros*. In ToS all of this is carried out *without the Axiom of Choice*, through explicit algorithmic constructions.

Before taking up zeta (Chapter 13.2), we lay the foundation—the prime numbers. And here it is important to state at once that in ToS the primes are not points of a “set of all primes” given in advance but a *role* in the multiplicative arrangement of the natural series. This chapter unfolds them in four positions:

- *Structural inevitability.* The primes arise not as one possible way of classifying but as structurally inevitable generators—atoms.
- *Operational divisibility.* A natural number $n$ is considered on several levels: as an object, as a product of primes, as a process of factorization.
- *Sets as a mode.* “The set of all primes” is a mode of operation; what is real is “prime” as a classification of the naturals by a decidable predicate.
- *Positive ontology.* Prime divisors are structurally nonnegative; multiplicities are nonnegative; Dirichlet series in the region of convergence work with positive terms.

**A remark on confirmation.** As throughout the volume, the leading role belongs to the *description of the system*; the Rocq repository serves as *confirmation* that the construction is machine-checkable. The names of files, the formulations, and the numbers of checked statements are moved to the notes. For this part we have additionally checked all the cited numbers against the current state of the repository and give exactly those.[^1]

## A Prime Number as a Decidable Predicate

In ToS “being prime” is not a property of an element of a preexisting set but a *rule of the constitution*: a number $n\ge 2$ is prime if it is divided only by $1$ and by itself. Divisibility and primality are given directly:

```coq
Definition divides (d n : nat) : Prop := exists k, n = d * k.

Definition is_prime (n : nat) : Prop :=
  2 <= n /\ forall d, 2 <= d -> d < n -> ~ divides d n.
```

The key word here is *decidability*. Alongside the predicate a Boolean check `is_prime_bool` is defined, which runs through the divisors in the finite range $2,…,n-1$; for each concrete $n$ the question “is $n$ prime?” is decided in a finite number of steps. A separate function `smallest_factor` searches for the smallest divisor by trial division and stops as soon as $d^2>n$.[^2] This corresponds exactly to P4: primality is not “read off” a ready infinite table but *computed* on a concrete finite bearer.

- $2,3,5,7,11,…$ are prime;
- $4,6,8,9,10,…$ are composite;
- $1$ is the *unit*: neither prime nor composite (its only divisor is itself), but the *first act of counting* (Part II);
- $0$ is a special case: it is divisible by everything and carries no multiplicative status.

The position “sets as a mode” is already visible here: we do not introduce “the set $\mathbb P$ of all primes” as a completed object-totality. The predicate `is_prime` itself is, of course, perfectly legitimate—what is ruled out is only the *completed infinite collection* as an Element. The prime is a *classification* of the naturals by a predicate; “all primes” is a mode of traversing this classification, not an object lying before us in its entirety.

## Primes as Atoms: The Fundamental Theorem of Arithmetic

What makes the primes *fundamental*? The answer is the fundamental theorem of arithmetic: every natural number $n\ge 1$ factors uniquely (up to order) into a product of primes. In ToS both halves of this statement—*existence* and *uniqueness*—are machine-proved.[^3]

**Existence as an algorithm.**  The factorization is not postulated but *built*: for $n\ge 2$ one takes the smallest divisor (it is prime), divides the number by it, and repeats the procedure. For a concrete $n$ it terminates in a finite number of steps—this is trial division. The factorization is represented as a finite list of primes whose product equals $n$.

**Uniqueness through Euclid’s lemma.**  The heart of uniqueness is *Euclid’s lemma*: if a prime $p$ divides a product $a\cdot b$, then $p$ divides $a$ or $b$.[^4] It follows that two factorizations of one number are permutations of each other. Thus the *multiplicity* of each prime in the factorization turns out to be an invariant of the number—its constitutive characteristic.

This is structural inevitability in pure form. The primes are not a “convenient” classification: they are *uniquely* determined by divisibility and are the *generators* of the multiplicative monoid $ℕ$. From any nontrivial view of the natural numbers the primes emerge as fundamental points. The machine-checked uniqueness of factorization is the *well-formedness* of the role “atom”: atoms not only exist but compose every number *unambiguously*.

A concrete example checked by computation: $12 = 2\cdot 2\cdot 3$, and every prime factorization of the number $12$ is a permutation of the list $[2;2;3]$.[^5]

## The Infinitude of Primes: An Algorithm, Not a Completed Set

The most famous statement about the primes is their infinitude. In ToS it takes a form that answers exactly to P4: not “there exists an infinite set” but *an algorithm of unbounded construction*.

> **Theorem (Euclid, constructively).** For every $N$ there exists a prime number greater than $N$.

The proof is *algorithmic*: consider $N! + 1$. It is $\ge 2$, so it has a prime divisor $p$. If $p\le N$, then $p$ would divide both $N!$ and $N!+1$, and hence their difference $1$—impossible. Therefore $p > N$.[^6] Given a finite collection of primes, we *programmatically build* a new one.

This is infinity in the sense of P4: *infinity is a property of a process, not of a completed object*. “There are infinitely many primes” means “the procedure for building the next prime never runs into a wall,” not “somewhere there lies a ready infinite set $\mathbb P$.” The equivalent formulation—“for every $N$ there is a prime $>N$”—fixes exactly this unboundedness as a rule, not as an object.

## The Distribution of Primes: The Counting Function

Since the primes thin out but are never exhausted, it is natural to *count* them. The counting function $\pi(x)$—the number of primes not exceeding $x$—is in ToS a *role-counter*: for each concrete $x$ it is a concrete number, computed in finite time as the length of a sieve.[^7]

| $x$ | $\pi(x)$ |  | $x$ | $\pi(x)$ |
|---|---|---|---|---|
| $10$ | $4$ |  | $100$ | $25$ |
| $30$ | $10$ |  | $1000$ | $168$ |

The empirical picture of the initial values shows thinning: on larger intervals there are relatively fewer primes, while the counter grows monotonically and without bound (the latter is a direct consequence of Euclid’s infinitude from “The Infinitude of Primes: An Algorithm, Not a Completed Set”). “Thinning” itself, as an exact statement, is already analytic and belongs to the asymptotics below.

**The prime number theorem.**  The main asymptotic result of the classical theory states:

$$
\pi(x) \sim \frac{x}{\ln x}\quad (x\to\infty),
$$

that is, $\lim_{x\to\infty}\pi(x) \ln x / x = 1$ (Hadamard and de la Vallée Poussin, 1896). In ToS this is an *operational* statement about the asymptotics of two processes—$\pi(x)$ and $x/\ln x$. **The PNT is not proved in this chapter.** In Chapters 13.2–13.5 we bring up the operational analytic mechanism through which such asymptotics is proved classically: zeta as a process, the Euler product, the zeros, and the zero-free region. What exactly of this mechanism is machine-checked is honestly outlined in 13.5 and in the map of boundaries of the part (13.7). Here it matters only that the asymptotics of the primes is a statement about the *behavior of the counter*, not about a property of a ready infinite set.

## E/R/R Analysis: The Prime as a Functional System

Let us gather what has been said into the standard Elements/Roles/Rules analysis, in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).**  The constituting rule is *divisibility*: a prime is defined as indecomposable with respect to multiplication (`is_prime`). At the level of the whole series the rule strengthens to *factorization with uniqueness*—the fundamental theorem of arithmetic. It is the rule (and not a list) that says what “being an atom” means.

**Roles (L4).**  A natural number receives a *multiplicative status*: “prime” is the role of an *atom* (a generator of the monoid); “composite” is the role of a *product of atoms*; “$1$” is the role of the *unit* (the empty product). The number $n$ is, moreover, multilayered: an object of counting, a product of primes, a process of factorization.

**Elements (L1${}+{}$P4).**  At each stage, finite data over $ℕ$: concrete primes, finite lists of divisors and factorizations, values of the counter $\pi(x)$ up to a finite $x$. *Not* elements: “the set of all primes,” a completed table of primality, an infinite collection of factorizations.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| the predicate of divisibility; the fundamental theorem (existence ${}+{}$ uniqueness) | the constitution of the prime and the unambiguity of factorization | Rule (L5) |
| “prime” ${}={}$ atom, “composite” ${}={}$ product, “$1$” ${}={}$ unit | the multiplicative status of a number | Role (L4) |
| concrete naturals; finite lists of divisors/factorizations; $\pi(x)$ | the bearers at each stage | Element (L1${}+{}$P4) |

**Well-formedness check.**  Each component falls into exactly one category. The role “atom” is *well-formed* precisely because the uniqueness of factorization is machine-proved: atoms compose every number unambiguously. The infinitude of the primes is well-formed as a rule (an algorithm of construction), not as an object.

**What the analysis removes (diagnosis).**  The root category mistake is the reification of “the set of all primes” as a completed object and the ascription to it of properties available only to finite data. ToS separates the levels: the prime is a role (an atom); “all primes” is a mode of traversal; infinity is a rule of unbounded construction (P4). This is the same discipline that allowed Part IV not to confuse a process with a completed continuum; here it is applied to the multiplicative structure of $ℕ$.

## Primes and Quantum Chaos: A Bridge to Physics

One of the most striking connections of modern mathematical physics deserves mention already here, although its unfolding is the business of physics. Studying the spacings between the nontrivial zeros of zeta, Hugh Montgomery (1973) noticed a statistical coincidence with the distribution of spacings between the eigenvalues of random Hermitian matrices (the Gaussian Unitary Ensemble, GUE)—a model of the spectra of complex quantum systems. The connection is *not proved*, but it is numerically confirmed for trillions of computed zeros.

Consonant with this is the earlier Hilbert–Pólya conjecture (1910s): the zeros of zeta are the eigenvalues of some self-adjoint operator, a “quantum Hamiltonian of number theory.” No such operator has been found, and the search for it is an active field. In the operational reading this is an *inverse problem*: the distribution of the spectrum (the zeros of zeta) is given, and an operator is required. We record here only the philosophical frame: if the picture is right, the distribution of primes is the classical trace of some quantum system, and the zeros of zeta are its energy levels. We present no formalization of this connection; in the repository it corresponds only to the analogy “zeros $\leftrightarrow$ zeros of partition functions,” drawn separately.[^8] A detailed discussion belongs to physics.

## What the Chapter Has Prepared

The primes have been established as the *atoms* of the multiplicative arrangement of $ℕ$—a role whose well-formedness is guaranteed by the machine-checked fundamental theorem of arithmetic; their infinitude has been read as an algorithm (P4), and their distribution as the behavior of the counter $\pi(x)$. This elementary foundation is what classical analytic number theory usually presupposes tacitly; here it is unfolded as a finite operational program and machine-checked from scratch (0 axioms, by `Print Assumptions`).

Next:

- Chapter 13.2—the zeta function as a process of partial sums;
- Chapter 13.3—the Euler product, which links zeta with the primes (and rests precisely on the uniqueness of factorization from “Primes as Atoms: The Fundamental Theorem of Arithmetic”);
- Chapter 13.4—the functional equation and the critical line;
- Chapter 13.5—the zeros and the zero-free region (the analytic mechanism through which the asymptotics of “The Distribution of Primes: The Counting Function” is proved classically);
- Chapter 13.6—von Mangoldt’s explicit formula;
- Chapter 13.7—three equivalent forms of the Riemann Hypothesis and the map of boundaries of the part.

---

[^1]: The elementary number-theoretic foundation of this chapter is collected in the directory `src/numbertheory/` (9 files, 138 `Qed`, 0 `Admitted`, 0 axioms—all statements pass `Print Assumptions` as “Closed under the global context”). Chapter 13.1 rests on `stdlib/Primes.v` (21 `Qed`), `PrimeFactorization.v` (21 `Qed`), `EuclidInfinitude.v` (5 `Qed`), and `PrimeCounting.v` (9 `Qed`).
[^2]: `stdlib/Primes.v`: `divides`, `divides_bool`, `is_prime`, `is_prime_bool` (a search through $2,\dots,n-1$), the sieve `sieve`, `smallest_factor` (stopping at $d^2>n$). It is machine-checked that `is_prime_bool` gives `true` on $2,3,5$ and `false` on $0,1,4$; the sieve `sieve 8` evaluates to $[2;3;5;7]$. `Primes.v` itself has the partial reflection lemmas `prime_ge_2` and `prime_not_composite`; the full *reflection* lemma `is_prime_bool_true_is_prime` (a Boolean result implies propositional primality) is proved in `PrimeFactorization.v` and is used below.
[^3]: `PrimeFactorization.v`: `factor_exists` (the existence of a factorization—strong induction on $n$), `prime_factorization_unique` (uniqueness up to *permutation*, formalized by the type `Permutation`), and `fundamental_theorem_of_arithmetic`, which combines both. 21 `Qed`, 0 axioms.
[^4]: `euclid_lemma` in `PrimeFactorization.v`. It is proved through the standard number-theoretic fact `Nat.gauss` (if $\gcd(p,a)=1$ and $p\mid a\cdot b$, then $p\mid b$), with a bridge between the repository’s divisibility `divides` and the library’s `Nat.divide`. From it, by induction on the list, it follows that a prime dividing a product of primes coincides with one of them, and hence the uniqueness of factorization as the permutation equivalence of two lists.
[^5]: `factorization_12` and `factorization_12_unique` in `PrimeFactorization.v`.
[^6]: `EuclidInfinitude.v`: `exists_larger_prime` (for every $N$ there exists a prime $>N$, through a prime divisor of $N!+1$; the auxiliary `divides_fact`: every $1\le d\le n$ divides $n!$), and `primes_not_finite` (no finite list contains all the primes). 5 `Qed`, 0 axioms. It rests on `exists_prime_divisor` from `PrimeFactorization.v`.
[^7]: `PrimeCounting.v`: `pi x := length (sieve x)`; machine-checked are $\pi(10)=4$, $\pi(30)=10$, $\pi(100)=25$, $\pi(1000)=168$; proved are the characterization of membership in the sieve (`in_sieve_iff`) and monotonicity (`pi_monotone`). 9 `Qed`, 0 axioms.
[^8]: `src/zeta/LeeYangAnalogy.v` draws a structural analogy between the zeros of zeta and the zeros of partition functions (Lee–Yang); this is an analogy, not a proof of the Montgomery or Hilbert–Pólya conjecture.

---

Part: [[13 Zeta Function and Number Theory|Part XIII. The Zeta Function and Number Theory]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/06 Synthesis and Map of Boundaries|Chapter 6. Synthesis and the Map of Boundaries—Part XII]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/02 Zeta Function as Process|Chapter 2. The Zeta Function as a Process]] →
