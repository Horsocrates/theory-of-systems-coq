---
title: "Chapter 5. The Analytic Bridge eval and Tannery’s Theorem: Closing the Logarithm Equation"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/05 Аналитический мост eval и теорема Таннери замыкание уравнения логарифма.md"
sourceBlob: effddd32e0fd893879790c1a2d28a0ba0b62811f
translated: 2026-10-20
status: draft
---

## The Plan of the Chapter: What We Connect

By this chapter we have two ready but not yet *connected* pieces. From Chapter 16.3, the *formal heart* $e^{-\ln(1-x)} = 1/(1-x)$: an equality of formal series, on coefficients, with 0 axioms. From Chapter 16.4, $\exp_{ℝ}$, the real exponential *of a process*, with the addition theorem and injectivity. One piece is an identity about coefficients; the other is an operator on number-processes. This chapter brings them together and reaches the goal of the whole of Part XVI: a genuine *functional equation of the logarithm* over number-processes,

$$
L(x) + L(y) \;\sim\; L(x\oplus y), \quad x\oplus y := x + y - xy,
$$

where $L(x) = -\ln(1-x)$ is the logarithm process and $\sim$ is the equality of number-processes.

The bridge rests on two new tools. The first is the *evaluation homomorphism* $\mathrm{eval}$: a formal series evaluated at a point becomes a number-process, and this evaluation respects the whole algebra of Chapter 16.2. The second is *Tannery’s* theorem: an analytic license to interchange a limit with an infinite sum. Without it the diagonal of $\exp_{ℝ}$ and the one-step summation of the series cannot be glued together.

The tier, as in Chapter 16.4, is *analytic*, on L3. But the core here is surprisingly clean: Tannery’s theorem itself, the decay $n z^n \to 0$, the finite Fubini interchange, and the additivity of $\mathrm{eval}$ are *axiom-free*; L3 enters only into the final assembly of the equalities.

## The Evaluation Bridge: $\mathrm{eval}${eval} as a Homomorphism

A formal series is a coefficient process (Chapter 16.1). Fix a point $x$, $0\le x<1$. The partial sums $\sum a_n x^n$ form a Cauchy process—the *value* of the series at the point:

$$
\mathrm{eval} a x \;:=\; \operatorname{series_limit}\Bigl(\textstyle\sum_n a_n x^n\Bigr).
$$

This evaluation is a *homomorphism* from the formal calculus of Chapter 16.2 into number-processes:

$$
\mathrm{eval}(a + b) x \sim \mathrm{eval} a x + \mathrm{eval} b x, \quad
  \mathrm{eval}(a \cdot b) x \sim \mathrm{eval} a x \cdot \mathrm{eval} b x, \quad
  \mathrm{eval}(a^{k}) x \sim (\mathrm{eval} a x)^{k},
$$

where on the left $\cdot$ is the convolution of series and on the right the product of processes. And it *identifies* the named series with their classical values:

$$
\mathrm{eval} `exp_fps` t \sim \exp(t), \quad
  \mathrm{eval} `log1m_fps` x \sim L(x).
$$

Here $L$ is, throughout the chapter, the *positive* logarithm process $L(x) = -\ln(1-x) = \sum_{n\ge1}
x^n/n$; accordingly, `log1m_fps` is read as the series for $-\ln(1-x)$, *not* for $\ln(1-x)$. That is, $\mathrm{eval}$ plays the role of a *functor* “formal $\to$ analytic” (in a categorical reading; in the formalization itself it is an *evaluation homomorphism*, without a separate categorical layer): it carries the coefficient algebra of Chapter 16.2 over into equalities of *numbers* and fixes the two heroes—the exponential and the logarithm—to their analytic meaning.[^1]

## The Formal Heart, Evaluated

The formal heart of Chapter 16.3 was the equality of series $E\circ L = `geom`$. Let us apply $\mathrm{eval}$ at the point $x$:

$$
\mathrm{eval} (`exp_fps` \circ `log1m_fps`) x \;\sim\; \frac{1}{1-x}.
$$

The identity that lived on coefficients now holds as an equality of *number*-processes—at every point $0\le x<1$. Under the hood, the evaluation of the composition requires a finite Fubini interchange—at stage $n$, swapping the order of summation in $\mathrm{eval}(f\circ g)$—which is legitimate when $g(0)=0$ and is itself *axiom-free*. Thus the bridge carries the formal heart over to the other side—at a finite price.[^2]

## Tannery’s Theorem: The Analytic Glue

A gap remains. $\exp_{ℝ}(L(x))$—by the construction of Chapter 16.4—is a *diagonal*: $\exp_{ℝ}(P) = \operatorname{diag}_n \exp(P_n)$; the exponential is taken of the rational approximations of the process $P = L(x)$ and then diagonalized. The value $\mathrm{eval}(E\circ L) x$, by contrast, is one series summed at once. To prove their equality, one must interchange two passages to the limit: the diagonal over $n$ (the approximation of $L(x)$) and the infinite sum over the series of the exponential. A naive interchange of a limit and an infinite sum is illegitimate. Tannery’s theorem gives the license.

Let us state it. Let a double sequence $a(k,n)\ge 0$ be dominated termwise by a summable dominating sequence $a(k,n)\le M(k)$ (with convergent $\sum_k M(k)$), and for each fixed $k$ let the column $a(k,n)\to 0$ as $n\to\infty$. Then the diagonal partial sum tends to zero:

$$
\sum_{k<n} a(k,n) \;\xrightarrow[n\to\infty]{}\; 0.
$$

We use precisely this *specialized tail* form of Tannery—the vanishing of the diagonal error—rather than the general passage $\lim_n\sum_k = \sum_k\lim_n$: it is sufficient for our interchange. Two details make it a *needed* and at the same time *honest* tool:

- The dominating sequence here is supplied by the decay $n z^n \to 0$: the $k$-th block is bounded by $\sigma^k$ with summable $\sigma<1$—exactly Tannery’s $M(k)$.
- Tannery’s theorem in our system is *axiom-free*—“Closed under the global context”—and so are the decay $n z^n\to0$ and the finite Fubini. The analytic glue that licenses the interchange is fully constructive; L3 is carried only by the framing constructions of the real equalities (`series_limit`, $\exp_{ℝ}$).

The result is the key junction lemma:

$$
\exp_{ℝ}(L(z)) \;\sim\; \mathrm{eval} (E\circ L) z.
$$

The diagonal exponential of the logarithm process equals the one-step evaluation of the formal composition.[^3]

## The Key, the Multiplicative Lock, and the Closure

Let us chain the junction with the evaluated heart:

$$
\exp_{ℝ}(L(z)) \;\sim\; \mathrm{eval} (E\circ L) z \;\sim\; \frac{1}{1-z}.
$$

This is the *key*: the real exponential of the logarithm process *is* the geometric process representing $1/(1-z)$. The formal heart of Chapter 16.3, raised by the exponential of Chapter 16.4 and the bridge of Chapter 16.5, becomes a statement about genuine real numbers.

The geometric process has its own group arithmetic:

- it is the inverse of $(1-z)$: $(1-z)\cdot \dfrac{1}{1-z} \sim 1$;
- products multiply by the law of *complementary* factors, 
$$
\frac{1}{1-x}\cdot\frac{1}{1-y} \;\sim\; \frac{1}{1-(x\oplus y)}, \quad x\oplus y = x+y-xy.
$$

The strange argument $x\oplus y$ is no accident: it is exactly what makes the *complements* multiply, $(1-x)(1-y) = 1-(x\oplus y)$. From here also comes the *domain*: for $0\le x<1$ and $0\le y<1$ we have $1-(x\oplus y) = (1-x)(1-y) > 0$, so that $0\le x\oplus y<1$—and $L(x\oplus y)$ is defined (exactly the hypotheses on which the formalized equation rests).

Now everything is in place to close the equation. Let us read the chain:

$$
\exp_{ℝ}\bigl(L(x)+L(y)\bigr)
  \;\sim\; \exp_{ℝ}(L(x))\cdot\exp_{ℝ}(L(y))
  \;\sim\; \frac{1}{1-x}\cdot\frac{1}{1-y}
  \;\sim\; \frac{1}{1-(x\oplus y)}
  \;\sim\; \exp_{ℝ}\bigl(L(x\oplus y)\bigr),
$$

where the first step is the addition theorem of Chapter 16.4, the middle ones are the key and the $\oplus$ law, and the last is the key in reverse. Both ends are $\exp_{ℝ}$ of something; by the *injectivity* of $\exp_{ℝ}$ (Chapter 16.4)

$$
L(x) + L(y) \;\sim\; L(x\oplus y), \quad\text{that is}\quad L(x)+L(y)\sim L(x+y-xy).
$$

This is exactly `ln_mul_closed`. A statement that the system previously carried only as a *horizon*—written out as a Prop and deliberately *not* faked via Admitted—is now a proved theorem.[^4]

## E/R/R Analysis, the Tier, and What the Chapter Has Achieved

| component of the chapter | role in the system | E/R/R layer |
|---|---|---|
| partial sums of $\mathrm{eval}$, finite convolutions and blocks at stage $n$ | bearers, finite | Element (P4) |
| $\mathrm{eval}$—the evaluation homomorphism | bridge formal $\to$ analyt.\ (functor.\ reading) | Role |
| key and closure $L(x){+}L(y)\sim L(x\oplus y)$ | additivity of $L$ over $\oplus$ | Role |
| Tannery, $n z^n\to0$, finite Fubini | axiom-free estimates | Rule (0 ax.) |
| geom.\ group law, key, injectivity of $\exp_{ℝ}$ | process estimates | Rule (L3) |

**Elements.** At every stage $n$ there are finite rational partial sums of $\mathrm{eval}$, finite Fubini interchanges, and finite Tannery blocks. The Element side is intact.

**Roles.** $\mathrm{eval}$ has the role of the *evaluation homomorphism* (formal $\to$ analytic); Tannery, the role of the *license for the interchange*; $\exp_{ℝ}$ and $L$ are the real exponential and the logarithm process; the functional equation has the role of the *additivity* of $L$ over the multiplicative $\oplus$.

**Rules.** The decay $n z^n\to0$, the geometric group law, the key, and injectivity are the rules by which process estimates are assembled into the closed equation.

**P4 diagnostics and the tier.** The whole movement is genuine real analysis over $ℚ$-processes; its *analytic* closure rests on L3, as marked from Chapter 16.4 on. But the analytic *core* is unusually clean—the separation is machine-checked (`Print Assumptions`):

| axiom-free (0 ax., “Closed”) | only L3 (`Classical_Prop.classic`) |
|---|---|
| `tannery`, `n_times_pow_limit`, `eval_compose_swap`, `eval_add` | `eval_mul`, `eval_exp`, `eval_log1m`, `eval_pow`, `eval_compose_exp_log1m_geom`, `geom_inv`, `geom_mul`, `ln_mul_from_key`, `boss`, `exp_R_ln_proc_is_geom`, `ln_mul_closed` |

That is, Tannery’s theorem, the decay $n z^n\to0$, the finite Fubini, and the additivity of $\mathrm{eval}$ depend on no axiom at all; L3 enters only into the assembly of the real equalities.

**What is new.** The heroes—Mertens, Tannery, the functional equation of the logarithm—are classical analysis. What is new is (a) $\mathrm{eval}$ as an *explicit* homomorphism carrying formal identities over into equalities of number-processes; (b) a constructive, axiom-free reading of Tannery and of the decay that feeds it; (c) the closure of the equation that the system carried as an open horizon (not Admitted)—now a theorem; (d) the structural reading of $x+y-xy$ as the law that multiplies complements. The level is *new framing and assembly* of classical analysis over processes.

**What the chapter has achieved.** *Number $\to$ function*: the function is a process (16.1); the calculus of such processes (16.2); composition and the formal heart (16.3); the real exponential of a process (16.4); and now the analytic bridge that closes a genuine functional equation (16.5). The ladder is one rung from the top: Chapter 16.6 will read the whole reification ladder *number $\to$ function $\to$ functional*, where $\mathrm{eval}$ itself—a map that takes a function and returns a number—is the first *functional*.

---

[^1]: `src/FPSEval.v` (32 Qed, 0 Admitted): `eval_add` is *axiom-free*; `eval_mul`, `eval_pow`, `eval_exp` ($\mathrm{eval} `exp_fps` t \sim `exp_limit` t$), `eval_log1m` ($\mathrm{eval} `log1m_fps` x \sim `ln_proc` x$) use no new axioms, only L3. Machine-checked.
[^2]: `src/FPSEval.v`: `eval_compose_exp_log1m_geom` ($\mathrm{eval}(E\circ L) x \sim `geometric_limit` x$)—no new axioms, only L3; its support `eval_compose_swap` (the finite Fubini under $g(0)=0$) is *axiom-free*.
[^3]: `src/Tannery.v` (4 Qed, 0 Admitted): `tannery` is *axiom-free*. `src/PolyTimesGeom.v` (2 Qed): `n_times_pow_limit` ($n z^n\to0$) is *axiom-free*. The junction `boss` (`src/LnMulClosed.v`) uses no new axioms, only L3. Machine-checked.
[^4]: `src/LnMulReduction.v` (6 Qed, 0 Admitted): `geom_inv`, `geom_mul` (the $\oplus$ law), `ln_mul_from_key` (“key $\Rightarrow$ equation”). `src/LnMulClosed.v` (11 Qed, 0 Admitted): `exp_R_ln_proc_is_geom` (the key), `ln_mul_closed` (the closure). No new axioms, only L3. The Prop formulation itself, `ln_mul_functional_equation`, lives in `src/Log2FunctionalEq.v` (7 Qed, 0 Admitted) as a horizon—here that horizon is removed. Machine-checked.

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/04 Process Exponential Exp R|Chapter 4. The Process Exponential exp_ℝ]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/06 Reification Ladder Number Function Functional|Chapter 6. The Reification Ladder: Number → Function → Functional]] →
