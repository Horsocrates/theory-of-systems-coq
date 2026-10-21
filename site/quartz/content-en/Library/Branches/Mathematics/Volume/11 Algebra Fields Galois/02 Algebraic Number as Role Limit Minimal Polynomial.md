---
title: "Chapter 2. Algebraic Number as Role-Limit; Minimal Polynomial"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/02 Алгебраическое число как роль-предел; минимальный многочлен.md"
sourceBlob: 02326710447de8b92de640b8faba704ece17d398
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 11.1 gave the *algebraic* side of a number: in the field $ℚ[\sqrt2]$ the symbol $\sqrt2$ is a finite coordinate with the rule $x^2=2$. But the same number has a second side—the *analytic* one: $\sqrt2$ as the *limit of a process of approximations* $(n\mapsto q_n)$, which never closes in $ℚ$. Parts II–IV already worked with this side: $ℝ$ there is not a completed object but the type of processes `RealProcess`${}={}(ℕ\toℚ)$, and an irrational number is a *role-limit* of a process, not a point of a ready continuum.

The present chapter joins the two sides. Its protagonist is the *minimal polynomial*: the rule that turns a nonterminating process of approximation into a *finite algebraic role* of fixed degree. An algebraic number lives in two categories at once: as a *role-limit* of a process (the infinite side) and as a root of a *finite rule* (the minimal polynomial). Algebraicity is precisely this coexistence: *a finite rule taming an infinite process*.

*An algebraic number is a role-limit of a process tamed by a finite rule (the minimal polynomial). “Irrational” means “the process does not terminate in $ℚ$”; the degree of the polynomial is the same tier as in 11.1.*

## Algebraic Number as Role-Limit of a Process

What does “$\sqrt2$ is irrational” mean in the optics of ToS? Not “$\sqrt2$ is a defective thing without a rational name,” but *the process of approximation to $\sqrt2$ closes at no rational stage*. The formal core is *infinite descent*: if one supposes that an irreducible fraction $p/q$ gives $\sqrt2$ (that is, $p^2=2q^2$), then a strictly smaller pair with the same property is built, and so on without bottom—which cannot happen in the natural numbers. Hence there is no rational point: the process is forever open.[^1]

This is the positive reading of irrationality: $\sqrt2$ is a *role-limit* of the process $(q_n)$. As a process object, $\sqrt2$ is built by approximations in the already developed theory of the reals of Parts II–IV (`RealProcess`${}={}(ℕ\toℚ)$); the formal support of *this* chapter, however, is a negative fact: no rational stage closes the rule $x^2=2$. “Irrationality” turns from a defect into a *characteristic of the process*: it does not terminate in $ℚ$.

The model example is the *golden ratio* $\varphi$. It is the limit of the ratios of consecutive Fibonacci numbers $F_{n+1}/F_n$ and the value of the simplest continued fraction $[1;1,1,1,…]$—the most slowly converging of all. No convergent (no $F_{n+1}/F_n$) equals $\varphi$ exactly, and no rational number satisfies the defining relation $x^2=x+1$.[^2]
Therefore $\varphi$ is the purest illustration of a role-limit: the process (Fibonacci / continued fraction) is fully determined and finitely actual at each stage, and its limit exists only as a *role* that the process approaches without ever reaching it in $ℚ$.

*Irrationality is not a defect but a property of a process: the process does not close in $ℚ$ (infinite descent is its formal core). The numbers $\sqrt2$, $\varphi$ are role-limits of a process (of approximations, Fibonacci, a continued fraction), not completed points of the continuum.*

## The Minimal Polynomial as the Rule of Algebraicity

If a number is a role-limit of a nonterminating process, then by what can it be *grasped* at all? The answer of ToS: by a *finite rule*—the minimal polynomial. $\sqrt2$ obeys the rule $x^2-2=0$, $\sqrt[3]{2}$ the rule $x^3-2=0$, $\varphi$ the rule $x^2-x-1=0$. Each such rule is *finite data* (a short list of rational coefficients), and it is precisely the rule that turns an infinite process of approximation into a *finite algebraic role* of fixed degree.[^3]

Here the generating order of ToS is seen in all its purity. The *rule* (the minimal polynomial) is primary: it says what the number must obey. The *role* (being an algebraic number of degree $d$—a role-limit tamed by this rule) is secondary. The *Elements* (rational approximations $q_n$, convergents of a continued fraction, steps of descent) are actual at each finite stage. The degree of the rule is exactly the tier from 11.1: $x^2-2$ is tier 2, $x^3-2$ is tier 3.

Hence a clean definition of algebraicity in the spirit of ToS: *a number is algebraic if its infinite process of approximation is tamed by a finite rule*. And at once the contrast with *transcendental* numbers ($\pi$, $e$) comes into view: these are processes *without* a finite algebraic rule of the form $p(x)=0$, $p\inℚ[x]$—role-limits that no polynomial with rational coefficients catches.[^4] Minimality, though, is here a mathematical reading: in the formal layer (`FieldExtension.v`) the polynomial is given as a *supporting* one and its degree is *computed*, while *minimality* is read off from separate lemmas. For $\sqrt2$: the irreducibility of $x^2-2$ over $ℚ$ is its irrationality—a quadratic polynomial without a rational root is irreducible.

*The minimal polynomial is a finite rule-bridge: it tames an infinite process of approximation, making the number an algebraic role of degree $d$. The order: rule (polynomial)
$\to$ role (algebraic number) $\to$ Elements (approximations). The transcendental is a process without such a rule.*

## The General Rational Root Test: One Rule Instead of Many

How do we know that a process will *not* close in $ℚ$—that $\sqrt2$, $\sqrt3$,
$\sqrt5$, $\sqrt[3]{2}$ are irrational? Each case can be handled by a separate descent (this is how the irrationality files are built). But there is *one rule* covering all these cases at once—*Gauss’s lemma* in general form: if integers $x,y$ are coprime and $x$ divides the power $y^{ n}$, then $x=\pm1$. Hence the *rational root test*: the $n$-th root of an integer is either an integer or irrational—no middle (non-integer rational) is given.[^5]

This rule is *economical* in the sense that ToS values: instead of a set of uniform descents (for $\sqrt2$, $\sqrt3$, $\sqrt5$, $\sqrt[3]2$, …) it gives a *single criterion* that decides by divisibility whether the process of root extraction will close in $ℚ$. All quadratic surds are the special case $n=2$, cubic ones $n=3$; none of them (except roots of exact powers) is rational. The rule-tier and the rule-irrationality merge here: the test says that $\sqrt[3]2$ is *irrational* ($x^3-2$ has no rational root); and since for a *cubic* the absence of a rational root is equivalent to irreducibility over $ℚ$, the minimal polynomial has *degree 3* (tier 3).

This at once prepares Chapter 11.3. If $\sqrt[3]2$ is tier 3, then it is unreachable by the quadratic tower (by tiers of the form $2^k$): it is proved that $\sqrt[3]2\notinℚ[\sqrt2]$.[^6] Doubling the cube, trisecting the angle, the heptagon—all these are attempts to close a *cubic* process by *quadratic* means; the impossibility here is a theorem about the tier (the rule of the test), not a shortage of tools. This is the topic of the next chapter.

*Gauss’s lemma in general form is one rule instead of many descents: the $n$-th root of an integer is an integer or irrational. It settles irrationality at one stroke and fixes the tier ($\sqrt[3]2$ is tier 3, unreachable by the quadratic tower).*

## E/R/R Analysis

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the minimal polynomial as the rule of algebraicity ($\sqrt2\mapsto x^2-2$, $\sqrt[3]2\mapsto x^3-2$, $\varphi\mapsto x^2-x-1$); the general Gauss’s lemma / rational root test as a rule: whether the process of the root will close in $ℚ$; infinite descent as the rule of irrationality |
| *Roles* (L4) | algebraic number ${}={}$ a role-limit of a process tamed by a finite rule; “irrational” ${}={}$ a nonterminating process; degree ${}={}$ tier; $\varphi$ ${}={}$ the role-limit of Fibonacci / the continued fraction $[1;1,1,…]$ |
| *Elements* (L1${}+{}$P4) | at each stage, finite data: rational approximations $q_n$, convergents of a continued fraction, Fibonacci ratios, steps of descent, lists of coefficients of a polynomial; the completed irrational as a point of the continuum is *not* an Element |

**Well-formedness.** A number is well-formed as an algebraic role when its process is a Cauchy process (the approximations converge, in the sense of the theory of the reals of Parts II–IV) *and* there exists a finite algebraic rule $p(x)=0$, $p\inℚ[x]$, which the limit obeys (minimality and degree—by separate lemmas). Irrationality is a property of the process (it does not terminate), not a missing property of an imaginary object.

**What it yields.** The irrationality of $\sqrt2,\sqrt3,\sqrt5,\sqrt[3]2,\varphi$ consists of theorems about processes (descent; “never reached”). Algebraicity is a finite rule over a process. The general Gauss’s lemma is a single criterion instead of a scattering of descents. Degree is a tier, immediately yielding an obstruction (tier 3 vs the quadratic tower).

**Diagnosis.** The root error is “an irrational number as a ready defective object.” ToS returns it to its category: a number is a role-limit of a process; irrationality is a characteristic of the process; algebraicity is the presence of a finite rule.

**Honest boundaries.** The minimality of the polynomial in the strict sense goes through the absence of a rational root (for $\sqrt2$ this is irrationality; the general analysis of irreducibility is by the rational root test). ToS does not build a formal theory of *transcendence* ($\pi$, $e$) here—the contrast “a process without a finite rule” is given conceptually, not as a proved theorem.

*An algebraic number is a role-limit of a process plus a finite rule (the minimal polynomial); irrationality is a property of the process; the general Gauss’s lemma is a single rule of closure. The substantive core is a rule that tames a process, not a ready object.*

## Summary and Transition

The chapter has joined the two sides of a number. *The analytic*: an algebraic number is a role-limit of a nonterminating process (of approximations, Fibonacci, a continued fraction), and “irrationality” is a positive property of this process (it does not close in $ℚ$; the formal core is infinite descent). *The algebraic*: the minimal polynomial is a finite rule that tames the process and sets the tier-degree. Gauss’s lemma in general form has given a single criterion of irrationality and of tier instead of a scattering of separate descents, generalizing the earlier cubic test to any degree.

Next comes Chapter 11.3: *constructibility as reachability by tier 2*. The quadratic tower is the limit of compass and straightedge; everything that requires tier 3 (doubling the cube, trisection, the heptagon) lies outside it. The Greek impossibilities will turn out to be not a shortage of tools but theorems about the tier—a direct consequence of the rule unfolded in this chapter.

*A number is a role-limit of a process; irrationality is the property of the process not to close in $ℚ$; the minimal polynomial is a finite rule that tames the process and sets the tier. Algebraicity is the coexistence of an infinite process and a finite rule; such is the frame in which 11.3 will read constructibility and the Greek impossibilities as theorems about the tier.*

---

[^1]: `no_rational_sqrt2` (`analysis/Sqrt2Irrational.v`): $\forall r\inℚ,\ r\cdot r\neq2$, via descent over $ℤ$. Similarly `no_rational_sqrt3` (`Sqrt3Irrational.v`) and `no_rational_sqrt5` (`Sqrt5Irrational.v`). For the cube root—`cbrt2_irrational` with the explicit descent lemma `descent_to_zero_2` (`stdlib/CubicRoleLimit.v`).
[^2]: `golden_never_exact` and `no_rational_golden` ($\lnot\exists q\inℚ,\ q^2=q+1$) in `stdlib/GoldenFibonacci.v`; `cf_phi_never_reached` and the link of the convergents with the Fibonacci numbers (`cf_ones_fib`) in `stdlib/ContinuedFractions.v`; `golden_ratio_irrational` in `stdlib/MetallicRatios.v`.
[^3]: `FieldExtension.v`: `sqrt2_poly`${}=x^2-2$, `cbrt2_poly`${}=x^3-2$ (as lists of coefficients), `eval_poly`, `is_root`, `poly_degree`; `ext_degree_cbrt2_is_3` ($\sqrt[3]2$ is tier 3).
[^4]: This is a *heuristic E/R/R reading*, not a formal definition of transcendence (ToS does not build one here). The contrast: algebraic ${}={}$ process ${}+{}$ a finite algebraic rule $p(x)=0$, $p\inℚ[x]$; transcendental ${}={}$ a process *without* such a rule (its approximations may have a different finite generating rule, but not a polynomial one over $ℚ$).
[^5]: `coprime_div_pow_unit` and `nth_root_integer_or_irrational` (`algebra/RationalRootTest.v`, 0 axioms). This is a *generalization* of the earlier test, which in the repository existed only for the cube (`coprime_div_cube_unit`, `AngleTrisection.v`); now it covers any degree $n$. The corollaries `gauss_square`/`gauss_cube` recover the special cases $n=2,3$.
[^6]: `cbrt2_not_in_Qsqrt2` (`stdlib/CubicRoleLimit.v`): no element $a+b\sqrt2$ gives $2$ when cubed.

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/01 Field as Role Extension Degree as Tier|Chapter 1. Field as Role-Extension; Degree as Tier]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/03 Constructibility as Reachability by Degree 2 Greek Impossibilities|Chapter 3. Constructibility as Reachability by Degree 2; Greek Impossibilities]] →
