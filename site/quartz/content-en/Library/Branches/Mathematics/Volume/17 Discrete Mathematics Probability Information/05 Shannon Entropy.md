---
title: "Chapter 5. Shannon Entropy"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/05 Энтропия Шеннона.md"
sourceBlob: 0eef21622687ca0e1e43d47f41fe081adc72f7c0
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Combinatorics counted distinctions (Chapter 1), probability distributed them (Chapter 3), the Markov process mixed them (Chapter 4). Shannon entropy *measures* them: it is the quantitative measure of acts of distinction—the central thread of the part.

*The flagship: information is the number of acts of distinction, and Shannon entropy is the
**unique** measure of distinctions compatible with additivity under independent
union and the normalization $H(2)=1$, *on the dyadic/multiplicative
Element core*. This core is machine-supported; the full Shannon–Khinchin
axiomatics (with additional regularity conditions) and the non-dyadic
extension lie on the role-limit side.*

Entropy is $H=-\sum_i p_i \log p_i$. The chapter leads from “entropy as a count of distinctions” through the measures of connection (mutual information, KL, cross-entropy) to the uniqueness theorem and closes with the finitization boundary: the dyadic is exact (Element), the irrational (the trit) is a role-limit, and Landauer’s principle links information with physics.

## Entropy as the Number of Distinctions

At the base is an identity of counting. To distinguish one of $2^n$ equiprobable outcomes means to ask $n$ binary questions; the number of configurations is $2^n$, and the entropy is exactly $n$ bits, that is, $n$ acts of distinction[^1]. This gives entropy a direct ToS meaning: it is about the *number of distinctions* needed to specify an outcome, not about “disorder.”

Hence at once two structural properties. The number of configurations is *multiplicative* over independent systems ($2^{n+m}=2^n\cdot 2^m$), and entropy is *additive* ($n+m$ bits for a pair of independent systems)[^2]. The information content of a single outcome (for $p>0$) is $-\log p$, and a certain outcome ($p=1$) carries zero information[^3]—one who already knows distinguishes nothing.

## Measures of Connection: Mutual Information, KL, Cross-Entropy

Over entropy a family of measures of connection is built, and all of them are structural identities over ℚ (with an abstract $\log$ as a parameter: for these identities a logarithmic symbol and the algebra of *differences* of entropies suffice): mutual information $I(X;Y)=H(X)+H(Y)-H(X,Y)$ is symmetric; the Kullback–Leibler divergence vanishes on coinciding distributions; the cross-entropy of a distribution with itself coincides with its entropy; the chain rule works[^4]. These identities are the rules by which distinctions are *connected* between systems: how many distinctions are shared, how many are redundant. What is machine-closed is precisely the *identities*; the inequalities (Gibbs’ nonnegativity $D_{KL}\ge 0$, the concavity of entropy) and the limit properties would require additional properties of the logarithm (monotonicity, concavity) and lie beyond this Element layer.

## Entropy Is the Unique Measure

Why exactly $-\sum p_i\log p_i$ and not some other formula? On the multiplicative lattice this measure is *unique* among those satisfying additivity and normalization. This Element core of uniqueness is machine-closed; the full Shannon–Khinchin axiomatics (with regularity conditions) is broader—see the end of the section.

Take a measure $f$ on “$n$ equiprobable outcomes,” additive under independent union ($f(m n)=f(m)+f(n)$) and normalized by a fair coin ($f(2)=1$). Then it is *forced* to coincide with $\log_2$ on the whole multiplicative lattice: $f(2^k)=k$, and in general $f(b^k)=k f(b)$—this is proved, and any two such measures coincide on the dyadic lattice[^5].

*Additivity is the same as in the counting of distinctions (Section 5.2): the information of independent systems adds up. It is what forces the logarithm—the unique function that translates the multiplication of configurations into the addition of distinctions.*

Full uniqueness—on *all* $n$, not only on the lattice—requires monotonicity, and here the finitization boundary enters (the next section): monotonicity *squeezes* the non-dyadic values into a narrowing interval, pinning them to an irrational limit. The full theorem in real analysis (via continuity) remains a horizon; the Element core of uniqueness is closed.

## The Dyadic Is an Element, the Irrational a Role-Limit; Landauer

Where does entropy cross the finitization boundary? Along the decidability of the logarithm. The dyadic case is exact: $\log_2 2^k = k$—a finite bit length, Element. The trit case is not: $\log_2 3$ is irrational, it has no finite bit representation, it is a role-limit[^6]. The same squeeze as in the uniqueness theorem: monotonicity pins $\log_2 3$ by a narrowing ℚ-process—measure-as-process, not a completed number.

And entropy is linked with physics: Landauer’s principle—the erasure of one bit has an energy cost, in physical units $kT\ln 2$[^7]. Information is not an abstraction: an act of distinction has an energy cost, and this links the part with physics.

## E/R/R Analysis: Entropy as a System

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rules are the axioms of the measure of information: additivity under independent union, normalization, nonnegativity; from them the uniqueness theorem forces the form $-\sum p\log p$. Information is a quantity *structured by a logarithmic Rule*: a rule that translates the multiplication of configurations into the addition of measures.

**Roles (L4).** Entropy is the role-measure of uncertainty; mutual information, KL, and cross-entropy are roles of connections between systems; the dyadic value is an Element role (exact bits), the irrational one a role-limit role (a process).

**Elements (L1 + P4).** The bearers are finite distributions over ℚ, concrete numbers of configurations $2^n$, dyadic lengths. Under P4 it is they that are actual; the true $\log_2$ of the non-dyadic (the trit) and the full real-valued measure are role-limits, not completed objects.

**Well-formedness check.** The axioms of the measure and the uniqueness theorem are Rules; entropy and the measures of connection are Roles; finite distributions and dyadic lengths are Elements; there are no overlaps. There is no self-application: the axioms of the measure stand above the distributions.

**What the analysis yields.** It unfolds the flagship: entropy is the number of acts of distinction, and it is unique precisely because the logarithm is the unique function that translates the multiplicativity of configurations into the additivity of the measure. And it names the boundary: the dyadic is exact (Element), the irrational is a role-limit; the same finitization boundary, now in the very measure of information.

The Shannon measure is statistical: it is about a *distribution*. In the next chapter a second measure of information appears—the algorithmic, Kolmogorov measure: about a *concrete string*—and we will build a bridge between the two measures on the two sides of the boundary.

---

[^1]: `entropy_count_is_definitional` (in `EntropyCountDefinitional`): `config_count` $n = 2^n$, `entropy_bits` $n = n$, and $2^{ \mathtt{entropy\_bits} n}=\mathtt{config\_count} n$—entropy is the $\log_2$ of the number of configurations *by the definition of counting*. Machine-checked, 0 axioms.
[^2]: `W_multiplicative` and `entropy_additive`: the number of configurations is multiplicative, entropy is additive under independent union. Machine-checked, 0 axioms.
[^3]: `info_content` $p=-\log p$ (defined for $p>0$); `info_content_certain`: $-\log 1 = 0$. Zero probability is a boundary, excluded case (the content is unbounded), not a finite Element content. Machine-checked, 0 axioms.
[^4]: `mutual_info` ($=H_x+H_y-H_{xy}$, `mutual_info_symmetric`), `kl_divergence` (`kl_divergence_self_zero`—precisely the *self*-zero $D_{KL}(p\|p)=0$), `cross_entropy` (`cross_entropy_self_eq_entropy`), `chain_rule_entropy`, `mutual_info_via_cond` (in `InformationTheory`). Machine-checked, 0 axioms.
[^5]: `f_two_pow` ($f(2^k)=k$), `f_pow_self` ($f(b^k)=k f(b)$), `uniqueness_dyadic` (any two additive normalized measures coincide on $2^k$), the summary theorem `shannon_measure_M1` (in `ShannonUniqueness`). Machine-checked, 0 axioms.
[^6]: `ShannonSynthesis`: the dyadic ($2^k$) is an Element (an exact length of $k$ bits), the trit case ($\log_2 3$) is a role-limit (irrational); it relies on `DyadicBits` (`log2_3_irrational`). As for the peak of binary entropy at $\tfrac12$: what is machine-closed is the *rational Padé-surrogate* measure $S_2$ (`S2_peaks_34`, `S2_peaks_13`: at the points $\tfrac34$ and $\tfrac13$ it is strictly lower than $S_2(\tfrac12)=\tfrac23$)—a check at sample points for $S_2$, not a universal maximum and not the continuous Shannon entropy (its concavity is a horizon). Machine-checked, 0 axioms.
[^7]: `LandauerConnection`: what is machine-closed is the *proportionality structure* of the erasure cost—$\mathtt{landauer\_cost} T b=T\cdot b$ (the cost is $\propto T$, $\propto$ the number of bits, zero at $T=0$; `landauer_connection_synthesis`); the factor $k\ln 2$ is absorbed into natural units. This is a structural/symbolic law linking information and energy, not a full thermodynamic model—a bridge to physics. Machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/04 Random Processes and Markov Chains|Chapter 4. Random Processes and Markov Chains]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/06 Kolmogorov Complexity and Algorithmic Information|Chapter 6. Kolmogorov Complexity and Algorithmic Information]] →
