---
title: "Chapter 2. The Calculus of Process Functions"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/02 Исчисление функций-процессов.md"
sourceBlob: 0b9528f1e971e88eb185bfa64be38c01a00373f7
translated: 2026-10-20
status: draft
---

## The Plan of the Chapter

Chapter 16.1 gave the *carrier*: the function is reified as a coefficient process $`FPS` = ℕ \to
ℚ$, and the Element/role-limit boundary ran through it (polynomial versus nonpolynomial series). But a carrier without operations is inert. For reified functions to *live*—to be added, multiplied, differentiated—the coefficient processes need a *calculus*.

This chapter builds it. Under the Cauchy convolution, formal power series carry a *ring structure*: multiplication is commutative, associative, and has a unit (a commutative monoid), addition and scaling are pointwise, and the formal *derivative* is coordinated with multiplication by the Leibniz and power rules. And this whole calculus has one common feature for the sake of which reification is worth undertaking: *every* operation here is finite arithmetic of coefficients. Not a single limit, not a single $\varepsilon$-$\delta$. The sum, the product, and the derivative of a process function are computed in a finite number of steps from a finite number of coefficients. The calculus lies entirely on the *Element* side—and therefore has 0 axioms.

The order of the chapter. First, pointwise addition and scaling, and the non-pointwise multiplication, the Cauchy convolution (§ 16.2.2). Then the ring laws: commutativity, associativity, unit (§ 16.2.3). Then the formal derivative and the observation that for a process function it is an Element operation rather than a limit (§ 16.2.4). Then the Leibniz and power rules (§ 16.2.5). And finally the E/R/R analysis with the transition to composition and the chain rule (§ 16.2.6), on which Chapter 16.3 will assemble the *formal heart* of the identity $e^{-\ln(1-x)} = 1/(1-x)$.

## Addition, Scaling, and Convolution

Two operations on coefficient processes are pointwise and therefore trivially Element. *Addition* adds the coefficients; *scaling* multiplies them by a constant:

$$
(a+b)_n = a_n + b_n, \quad (c\cdot a)_n = c  a_n .
$$

Each stage $n$ is one rational addition or multiplication.[^1]

Multiplication of functions is *not* pointwise. The coefficient of the product $f\cdot g$ is the *Cauchy convolution*—the finite sum of all products of coefficients whose indices add up to $n$:

$$
(f\cdot g)_n \;=\; \sum_{i+j=n} f_i  g_j \;=\; \sum_{i=0}^{n} f_i  g_{n-i}.
$$

This is the *only* law under which coefficient processes multiply as functions, not an arbitrary choice: this is exactly how the series $\bigl(\sum_i a_i x^i\bigr)\bigl(\sum_j b_j x^j\bigr)$ multiply. And—key for P4—each $(f\cdot g)_n$ is a *finite* sum: for a given $n$ there are finitely many indices $i+j=n$. Multiplication of process functions is a role-*convolution*: a rule that assembles a third coefficient process from two, and assembles it in a finite number of steps.[^2]

```coq
Definition fps_mul (f g : FPS) : FPS := conv f g.   (* (f*g)_n = sum_{i+j=n} f_i*g_j *)
```

## The Ring Structure: Commutativity, Associativity, Unit

Convolution endows coefficient processes with the structure of a *commutative ring with unit*—and each ring law is checked on coefficients.

*Commutativity*: $f\cdot g = g\cdot f$. At the level of coefficients this is the symmetry of the sum $\sum_{i+j=n}
f_i g_j$ under the swap $i \leftrightarrow j$.[^3]

*Unit*: the series $`fps_one` = (1,0,0,…)$ (coefficient $1$ at $x^0$, zeros after it) is the neutral element: $`fps_one`\cdot f = f$.[^4]

*Associativity*: $(f\cdot g)\cdot h = f\cdot(g\cdot h)$—the most substantive law. Both sides equal one *triple* Cauchy sum $\sum_{i+j+k=n} f_i g_j h_k$; to reduce the left and right groupings to it, one must regroup the triangle of indices $\{(i,j): j\le i\le n\}$ by column. This *triangular Fubini swap* of finite sums had to be proved separately—the earlier library did not have it; associativity rests on it.[^5]

Together these laws mean: under convolution, formal series form a *commutative monoid* with unit $`fps_one`$, and together with pointwise addition and scaling, a ring structure over $ℚ$. What is machine-confirmed is precisely the *multiplicative* laws of convolution (commutativity, associativity, unit) and their coordination with the derivative (below); the distributivity of convolution over pointwise addition and the laws of the additive group are routine and are not singled out as separate lemmas.[^6]
The reified functions have acquired an algebra. Its first nontrivial fact was already met in Chapter 16.1: the defining equation of the geometric function $(1-x)\cdot\frac{1}{1-x} = 1$ is exactly the statement that $`geom_fps`$ is the *inverse* of $(1-x)$ in this ring. What in Chapter 16.1 was the first evidence that “the process function works” is now seen as an equality in the ring of process functions.

## The Formal Derivative: Differentiation without a Limit

The derivative on a coefficient process is given by one rule: the coefficient at $x^n$ of $f'$ is $(n+1) c_{n+1}$—a shift of the index by one and multiplication by the index:

$$
(f')_n = (n+1)  c_{n+1},
  \quad\text{since}\quad
  \frac{d}{dx}\sum_n c_n x^n = \sum_n (n+1) c_{n+1} x^n .
$$

```coq
Definition fps_deriv (f : FPS) : FPS := fun n => inject_Z (Z.of_nat (S n)) * f (S n).
```

And here is the observation for the sake of which reification was undertaken. *Classically* the derivative is the *limit* of a difference quotient—an object of the role-limit side, $\varepsilon$-$\delta$, an infinite process of approximation. But for a function *reified as a coefficient process*, the derivative is *finite arithmetic*: a shift of the sequence by one step and multiplication of the $n$-th term by $(n+1)$. Neither limit nor analysis. The differentiation of a process function is an *Element* operation: it is *computed*, not *taken as a limit*. What classically lives on the role-limit side passes, on the reified function, to the Element side—exactly as multiplication reduced to a finite convolution.

And the reified basic functions satisfy their defining identities *at the level of coefficients*—in the formal sense, as equalities of coefficient processes, without any convergence. The formal exponential is a *fixed point* of the formal derivative: $(e^x)' = e^x$, because $(n+1)\cdot\frac{1}{(n+1)!} = \frac{1}{n!}$. And the series $-\ln(1-x)$—which is exactly $`log1m_fps`$ (with coefficients $c_0 = 0$, $c_{k+1} = 1/(k{+}1)$)—gives the geometric function: $\bigl(-\ln(1-x)\bigr)' =
\frac{1}{1-x}$, because $(n+1)\cdot\frac{1}{n+1} = 1$ is the constant coefficient of the geometric function. Both identities are finite equalities of coefficients, not passages to the limit.[^7]

## The Leibniz Rule and the Power Rule

The derivative is coordinated with ring multiplication through the Leibniz rule:

$$
(f\cdot g)' = f'\cdot g + f\cdot g'.
$$

At the level of coefficients this is an equality of convolutions, and it is proved by a *convolution recurrence*—the factorial form of Vandermonde’s identity, without any binomial coefficients.[^8]

From Leibniz, induction gives the *power rule*. The power of a series is defined by the usual recursion—$g^0 = `fps_one`$, $g^{k+1} = g\cdot g^k$—and for it

$$
\bigl(g^{k+1}\bigr)' = (k+1)  g^{k}  g' .
$$

The proof is an induction on $k$ on top of the Leibniz rule, with one application of associativity ($g\cdot(g^k\cdot g') = (g\cdot g^k)\cdot g' = g^{k+1}\cdot g'$) and of commutativity to collect the terms. The ring of § 16.2.3 works here at full strength.[^9]

These two rules are the last piece of the calculus before composition. Having the derivative, Leibniz, and the power rule, Chapter 16.3 will build the *chain rule* $(f\circ g)' = (f'\circ g)\cdot g'$—and through it obtain the formal heart $e^{-\ln(1-x)} = 1/(1-x)$.

## E/R/R Analysis and What the Chapter Prepares

| component of the chapter | role in the system | E/R/R layer |
|---|---|---|
| coefficients $c_n \in ℚ$, finite sums $\sum_{i+j=n}$ | bearers and counting | Element (P4) |
| multiplication $=$ Cauchy convolution | role-convolution | Role |
| derivative $=$ shift ${+}$ multiplication by $(n{+}1)$ | role-operation | Role |
| convolution: comm.{/}assoc.{/}unit (monoid) | algebra of the carrier | Rule (constructively) |
| Leibniz and power | coordination of the derivative with the ring | Rule (constructively) |

**Elements.** Everything the chapter operates with is rational coefficients and *finite* sums over indices $i+j=n$. Every stage is finitely actual; there is not a single completed-infinite object.

**Roles.** Multiplication plays the role of *convolution*, the derivative the role of a *weighted shift*. These are operations *on* the process function that turn the carrier into a living algebra with differentiation.

**Rules.** The ring laws (commutativity, associativity, unit) and the rules of the calculus (Leibniz, power) are *rules* of coordination. Each is an equality of coefficients checkable by finite computation; associativity rests on the triangular Fubini swap, which the library did not have.

**P4 diagnostics.** The whole calculus of process functions is finite arithmetic of coefficients: sum, convolution, weighted shift. There is not a single limit here. Therefore, unlike classical analysis, where the multiplication of series and differentiation drag convergence along with them, the *formal* calculus lies entirely on the Element side and has 0 axioms. A sharp formulation: on a reified function *differentiation is counting, not a limit*. And here is the exact edge of P4: *infinity* belongs to the *whole* series-object (role-limit), not to an individual coefficient operation—every coefficient of a sum, a convolution, and a derivative is computed by a finite rule. The whole series may be a role-limit, but every coefficient step remains an Element.

**What is new.** The ring structure of formal series (the commutative monoid of convolution and pointwise addition), the formal derivative, and the Leibniz and power rules are classical algebra. What is new here is the *framing*: the calculus is built on the coefficient process (the function-as-process of § 16.1), and every operation is read as a finitely actual Element operation; plus a constructive detail—the associativity of convolution via the triangular Fubini swap. The level is a *new framing*, with an honest 0-axiom construction of the whole calculus.[^10]

**What the chapter prepares.** We have a ring of process functions and a derivative with the Leibniz and power rules. On them Chapter 16.3 builds the *composition* of series (well defined when $g(0)=0$) and the *chain rule*, and through them the formal heart $e^{-\ln(1-x)} = 1/(1-x)$: the inverse-function identity that has become a checkable process recurrence on coefficients.

---

[^1]: `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**): `fps_add`, `fps_neg`, `fps_sub`, `fps_scale`—all pointwise in the coefficients.
[^2]: Ibid.: `fps_mul := conv`—multiplication of FPS is the Cauchy convolution `conv`. Machine-checked, 0 axioms.
[^3]: `src/FormalPowerSeries.v`: `conv_comm` (reindexing $i \mapsto n-i$). Machine-checked, 0 axioms.
[^4]: Ibid.: `conv_one_l`, `conv_one_r`. Machine-checked, 0 axioms.
[^5]: Ibid.: `conv_assoc` via `partial_sum_triangle_swap` (regrouping of a triangular double sum). Machine-checked, 0 axioms.
[^6]: Ibid.: `fps_mul_comm`, `fps_mul_assoc`, `fps_mul_one_l`, `fps_mul_one_r`—the multiplicative laws of convolution (a commutative monoid over `conv`). Machine-checked, 0 axioms.
[^7]: `src/FormalPowerSeries.v`: `exp_fps_deriv` ($`fps_deriv` `exp_fps` = `exp_fps`$) and `log1m_deriv` ($`fps_deriv` `log1m_fps` = `geom_fps`$). Machine-checked, 0 axioms.
[^8]: `src/FormalPowerSeries.v`: `fps_deriv_mul`—the Leibniz rule on coefficients. Machine-checked, 0 axioms.
[^9]: Ibid.: `fps_pow` (the power of a series), `fps_pow_deriv`, and `fps_pow_deriv_eq`—the power rule. Machine-checked, 0 axioms.
[^10]: All the material of the chapter comes from `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**; `Print Assumptions` = “Closed under the global context” for the key lemmas).

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/01 Finitization Boundary at the Level of Functions|Chapter 1. The Finitization Boundary at the Level of Functions]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/03 Composition Chain Rule and the Formal Heart E L|Chapter 3. Composition, the Chain Rule, and the Formal Heart E∘L]] →
