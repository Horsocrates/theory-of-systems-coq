---
title: "Chapter 6. Kolmogorov Complexity and Algorithmic Information"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/06 Колмогоровская сложность и алгоритмическая информация.md"
sourceBlob: 8694861bb7371311f494221fc078c5e12ccd6131
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Information has a second measure. Shannon entropy (Chapter 5) measures a *distribution*—how many distinctions on average; Kolmogorov complexity $K(x)$ measures a *concrete string*—the length of the shortest program that generates it. Shannon is statistical, Kolmogorov algorithmic; together they are two measures of information on the two sides of the finitization boundary.

*Compression realizes $K$ **from above**—this is an Element (a finite code); $K$ itself is
**uncomputable** by the same diagonal engine as halting and uncountability—the
**fourth face** of one boundary (role-limit).*

The chapter builds a bridge between the two measures. The uncomputability of $K$ is *cited* here, not re-proved (its diagonal derivation belongs to the computational part, Part XV); the chapter puts it in its place as a face of the common boundary and links it with Shannon.

## Two Measures of Information

Kolmogorov complexity $K(x)$ is the length of the shortest program (on a fixed model of computation) that outputs the string $x$. This is a *role-limit*: a minimum over all programs. Incompressible strings exist—by pure counting: there are only $2^n-1$ binary programs of length $<n$, while there are exactly $2^n$ strings of length $n$, so at least one string of length $n$ has no description shorter than $n$[^1] (the same pigeonhole as in the first chapter of the part).

The difference from Shannon is fundamental. Shannon ascribes information to a *distribution* (one must know the probabilities); Kolmogorov, to the *string itself* (no probabilities are needed). Randomness in Kolmogorov’s sense is incompressibility: a string is random if its shortest description is the string itself.

## Compression Realizes $K$ from Above

Although $K$ is uncomputable, it can be *approximated from above*: every concrete compressor gives a length no smaller than $K$. And here the Element side is at work: prefix codes are *verified*—a binary tree gives a prefix-free code, the Kraft sum $\sum 2^{-l_i}=1$, and on the concrete dyadic distribution $\{\tfrac12,\tfrac14,\tfrac18,\tfrac18\}$ the optimal tree attains an average length of $\tfrac74$ bits—exactly the entropy of this distribution[^2]. Compression also receives a *physical reading*: the observer is modeled as a compressor, and compression itself fits into the same type of process (modes, spectrum, energy) as physical processes do[^3].

*Concrete compression is an Element: a finite code, a computable upper bound on $K$. It is a terminating process of description.*

## $K$ Is Uncomputable—the Fourth Face of One Boundary

$K$ itself, unlike its approximations, is *uncomputable*: in a fixed model there is no total algorithm that outputs $K(x)$ for all $x$. And this uncomputability is *the same diagonal* as halting, Cantor’s Boolean diagonal ($A\to\mathsf{bool}$; uncountability, Part IV), and [[Russells Paradox|Russell’s paradox]], not a separate fact: the assumption of a $K$-decider is defeated by the same diagonal engine[^4].

*$K(x)$ is the fourth face of ONE boundary: discriminant / halting / Cantor / $K(x)$. One diagonal engine, four faces.*

This is the bridge from the applied part to the finitization boundary of the whole project[^5]. The uncomputability of $K$ is a P4 status, neither a defect nor an exclusion: $K$ is a role-limit, a minimum over a never-completable family of programs, reachable only as a process of approximation from above.

## The Shannon $\leftrightarrow$ Kolmogorov Bridge

The two measures are linked: for a computable distribution the expected Kolmogorov complexity coincides with the Shannon entropy up to a constant (the classical coding theorem; here it is background, not derived): statistical and algorithmic information converge. But the finitization boundary runs *between* them, along decidability.

*Shannon on a finite distribution and concrete compression are Element (decidable, computable). The exact $K$ is a role-limit (uncomputable). Two measures of information, two sides of one boundary.*

The Shannon measure on a finite space is a computable process over ℚ (in dyadic cases, an exact finite number of bits; in general, a number-process, like $\log_2 3$ in Chapter 5); compression gives a computable upper bound on $K$ (Element); but the *exact* $K$ escapes beyond the boundary (role-limit). The measure of information, like everything in this part, is cut by finitization: its finitely computable side is reachable; its exactly minimal side is a process, not a completed object.

## E/R/R Analysis: Algorithmic Information as a System

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *minimization of description*: $K(x)$ is the shortest program that outputs $x$. Adjoining it is the diagonal rule that defeats every presumed $K$-decider (the same as for halting).

**Roles (L4).** $K(x)$ is a role-limit (a minimum over a family of programs); compression is the role of approximation from above; incompressibility is the role of randomness. Shannon and Kolmogorov are two measures (roles) of one information (statistical / algorithmic).

**Elements (L1 + P4).** The bearers are concrete strings and concrete program-codes (Huffman); finite compressions. Under P4 it is they that are actual, together with any *computable upper bound* on $K$; a total $K$-oracle is a role-limit (the diagonal), not a completed object.

**Well-formedness check.** Minimization and the diagonal are Rules; $K$, compression, and the two measures are Roles; strings and codes are Elements; there are no overlaps. In a correct setting the rule of minimization is not a program of its own language; the collapse arises precisely in the attempt to *reify* it as a total decider within the same computational arena—that very diagonal collapse (a P1 shadow).

**What the analysis yields.** It shows that algorithmic information repeats the structure of the whole part: the finitely computable side (compression, upper bounds) is Element, the exactly minimal side ($K$) is a role-limit; and that this boundary is *the same* one that the whole project carries—$K(x)$ as the fourth face of the diagonal boundary.

The two measures of information are brought onto each other; the last step of the part remains—the limit of information itself. In the next chapter: the uncertainty principle in information and the bridge to von Neumann and quantum information (physics).

---

[^1]: `incompressible_exists` (in `cs/KolmogorovRoleLimit`): for any budget $n$ there are finitely many short programs, so some object is not describable within $n$—pigeonhole, 0 axioms.
[^2]: `VerifiedHuffman` (`huffman_synthesis`): a prefix-free tree, the Kraft equality $\sum 2^{-l_i}=1$, the concrete `tree_4_optimal` with average length $\tfrac74$ for the dyadic $\{\tfrac12,\tfrac14,\tfrac18,\tfrac18\}$ (coinciding with its entropy). This is a *prefix-free structure and a concrete example*, not a general theorem of Huffman optimality among all prefix codes. Informativeness as a measure of the reduction in search cost is `complexity/Informativeness`. Machine-checked, 0 axioms.
[^3]: `ObserverCompressor` (`observer_compressor_synthesis`: measurement/collapse as maximal compression) and `crown/CompressionIsPhysics` (`compression_is_physics_synthesis`: compression as a process of the same type—$N$ modes, spectrum, energy—as sound/light/QM). A structural reading and a bridge to Landauer (Chapter 5) and to physics, not a full thermodynamic model of compression. Machine-checked, 0 axioms.
[^4]: `kolmogorov_role_limit_drawn` and `complexity_decidable_no_diagonal` (in `cs/KolmogorovRoleLimit`): the complexity criterion is drawn *as a role-limit*—given the self-negating Berry/Chaitin diagonal, there is no total terminating decider (an instance of `diagonal_defeats_decider`); a role-limit, not an exclusion, and with no claim to the invariance of $K$ across machines. Machine-checked, 0 axioms.
[^5]: `one_boundary_four_faces` (in `cs/KolmogorovRoleLimit`) extends `one_boundary_three_faces`: $K$ is added to the discriminant, halting, and Cantor. Machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/05 Shannon Entropy|Chapter 5. Shannon Entropy]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/07 Uncertainty Principle in Information|Chapter 7. The Uncertainty Principle in Information]] →
