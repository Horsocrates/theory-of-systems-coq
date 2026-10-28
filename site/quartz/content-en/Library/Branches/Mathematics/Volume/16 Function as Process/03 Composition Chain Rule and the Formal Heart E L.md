---
title: "Chapter 3. Composition, the Chain Rule, and the Formal Heart E∘L"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/03 Композиция, цепное правило и формальное сердце E∘ L.md"
sourceBlob: 29831e4ae060167d3741595f91b60bcd488e792d
translated: 2026-10-20
status: draft
---

## The Plan of the Chapter

Chapter 16.2 gave the calculus: coefficient processes are multiplied by convolution and differentiated formally, with the Leibniz and power rules. One last tool of analysis remains—*composition*, $f\circ g$, and its *chain rule*. With them the part reaches its summit.

This summit is a concrete identity:

$$
e^{-\ln(1-x)} = \frac{1}{1-x}.
$$

It says that the exponential and $-\ln(1-x)$ *mutually cancel* each other down to the geometric function. And it was precisely this identity that was the *obstacle* to the whole program “the function is a process.” As long as the function remained an external map, the inversion identity was stated about the function *as a whole*, across the entire domain—and the pointwise, process machinery “did not see” it. This was diagnosed as a *second-order finitization boundary*: not a wall but an *unfinished object*—a function that had not yet become a process.

This chapter removes the obstacle. Having reified the function as a coefficient process (Chapter 16.1) and built a calculus on it (Chapter 16.2), we turn the inversion identity into a *coefficient process recurrence*: all the coefficients of the series $e^{-\ln(1-x)}$ turn out to equal one—that is, it is the geometric series—and this is checked by finite induction, with 0 axioms. The obstacle was an object awaiting reification, not a wall.

The order of the chapter: the composition of series and why the condition $g(0)=0$ makes it finite (§ 16.3.2); the chain rule (§ 16.3.3); the structural heart—the uniqueness of the solution of the ODE of the geometric function (§ 16.3.4); and the assembly—the *formal heart* $e^{-\ln(1-x)} = 1/(1-x)$ (§ 16.3.5). The chapter closes with the E/R/R analysis and the honest boundary: this heart is *formal* (on coefficients); the analytic bridge to an equality of number-processes is built by Chapter 16.5, relying on the process exponential of Chapter 16.4 (§ 16.3.6).

## The Composition of Series

To substitute one series into another means to compute $f(g(x))$ coefficient by coefficient. If $f = \sum_k f_k y^k$, then $f(g(x)) = \sum_k f_k  g(x)^k$, and the coefficient at $x^n$ is assembled from all the powers $g^k$ (with the convention $g^0 = \texttt{fps\_one}$, the unit series):

$$
(f\circ g)_n \;=\; \sum_{k=0}^{n} f_k  (g^k)_n .
$$

```coq
Definition fps_compose (f g : FPS) : FPS :=
  fun n => partial_sum (fun k => f k * fps_pow g k n) n.
```

There is a subtlety here, and ToS resolves it by *finiteness*. An infinite substitution $\sum_k f_k g^k$ would threaten an infinite sum at every coefficient. But under the *condition* $g(0)=0$—$g$ has no constant term—the power $g^k$ has *order* at least $k$: its first $k$ coefficients are zero.[^1]
Hence for $k>n$ the term $f_k(g^k)_n$ vanishes, and the sum over $k$ is *truncated* to $k\le n$: every $(f\circ g)_n$ is a *finite* sum. The condition $g(0)=0$ is exactly what makes composition a well-defined operation on coefficient processes, not a technical restriction: the substitution of a series without a constant term is computed in a finite number of steps. And at zero the composition behaves as it should: $(f\circ g)(0) =
f(0)$.[^2]

## The Chain Rule

Composition is coordinated with the formal derivative by the usual chain rule—under the same condition $g(0)=0$:

$$
(f\circ g)' = (f'\circ g)\cdot g' .
$$

[^3]

At the level of coefficients this is an equality of convolutions, and it is proved by the same geometric device as associativity in § 16.2.3: the double sum over the triangle $(i,k)$ can be rewritten as a square and the order of summation exchanged, while the vanishing of high powers ($(g^k)_i=0$ for $k>i$) cuts off the excess. This *square–triangle swap* with vanishing is the core of the chain rule.[^4] The classical chain rule, usually derived through limits of difference quotients, is here a finite identity of coefficients.

## The Structural Heart: The ODE of the Geometric Function

Before assembling the identity, we need one structural fact: that the geometric function is *uniquely* determined by a simple differential equation.

The series `geom` itself satisfies the equation $\texttt{geom}' = \texttt{geom}\cdot\texttt{geom}$—that is, $h' = h\cdot\texttt{geom}$ for $h = \texttt{geom}$ (equivalently, $(1-x)h' = h$).[^5] And—this is the key—*no other* process function with the condition $h(0)=1$ satisfies the equation $h' = h\cdot\texttt{geom}$:

$$
h' = h\cdot\texttt{geom}\quad\text{and}\quad h(0)=1
  \quad\Longrightarrow\quad
  h = \texttt{geom}.
$$

[^6]

Why uniqueness is so transparent on coefficients. Since `geom` is a series of ones only, convolution with it is simply a *partial sum*: $(h\cdot\texttt{geom})_n = \sum_{i\le n} h_i$.[^7] Therefore the equation $h' = h\cdot\texttt{geom}$ on coefficients is the recurrence

$$
(n+1) h_{n+1} = \sum_{i=0}^{n} h_i .
$$

With the initial condition $h_0 = 1$ it unwinds uniquely: $h_1 = h_0 = 1$; $2h_2 = h_0+h_1 = 2$, that is, $h_2 = 1$; and by induction—if $h_0,…,h_n$ are all ones, then $\sum_{i\le n} h_i = n+1$, and hence $(n+1)h_{n+1} = n+1$, whence $h_{n+1}=1$. All the coefficients equal one—this is exactly `geom`. The differential equation *pins down* the geometric function as its unique normalized process function, and does so by finite induction.

## The Formal Heart: $e^{-\ln(1-x)} = 1/(1-x)$

Now we assemble the summit. Consider the composition $h := \exp\circ(-\ln(1-x))$—that is, the substitution of the series $-\ln(1-x)$ into the exponential. (Here $\texttt{log1m\_fps}$ denotes precisely the series $-\ln(1-x) = \sum_{n\ge1}
x^n/n$—the *positive* logarithmic series, not $\ln(1-x)$; the sign is chosen so that the derivative is $+ \texttt{geom}$.) The substitution is well defined: $-\ln(1-x)$ has no constant term, $\bigl(-\ln(1-x)
\bigr)(0)=0$, so § 16.3.2 applies.

Let us show that $h$ satisfies that very ODE. By the *chain rule* (§ 16.3.3):

$$
h' = \bigl(\exp'\circ(-\ln(1-x))\bigr)\cdot\bigl(-\ln(1-x)\bigr)'.
$$

But both derivatives are known from § 16.2.4: the exponential is its own derivative, $\exp' = \exp$; and the derivative of $-\ln(1-x)$ is the geometric series, $\bigl(-\ln(1-x)\bigr)' = \texttt{geom}$. Substituting:

$$
h' = \bigl(\exp\circ(-\ln(1-x))\bigr)\cdot\texttt{geom} = h\cdot\texttt{geom}.
$$

And the initial condition: $h(0) = \exp\bigl((-\ln(1-x))(0)\bigr) = \exp(0) = 1$. So $h' = h\cdot\texttt{geom}$ and $h(0)=1$—and by the structural heart of § 16.3.4 such an $h$ is unique and equals `geom`. Hence

$$
\boxed{ e^{-\ln(1-x)} = \frac{1}{1-x} }
$$

*at the level of coefficient processes*: all the coefficients of the formal series $e^{-\ln(1-x)}$ equal one, that is, it is the geometric series.[^8]

This is the meaning of this result for our program. The inversion identity—the very one that *resisted* while the function was an external map—has become a *finite process recurrence* $c_n = 1$ and has been proved by machine induction without a single axiom. The obstacle *fell away*: it was not a wall but a function that had not yet become a process. Reification gave it the being of a process—and the identity, previously invisible, became checkable.

## E/R/R Analysis and What the Chapter Prepares

| component of the chapter | role in the system | E/R/R layer |
|---|---|---|
| coefficients and truncated sums $\sum_{k\le n}$ | bearers and counting | Element (P4) |
| composition $=$ substitution of a series | role-substitution | Role |
| ODE $h'=h\cdot\texttt{geom}$, $h(0)=1$ | role-constraint, pins down `geom` | Rule |
| chain rule, uniqueness for the ODE, heart $c_n=1$ | process recurrences | Rule (constructively) |

**Elements.** Composition under $g(0)=0$ is a *finite* truncated sum $\sum_{k\le n} f_k(g^k)_n$; the recurrence of the heart $(n+1)h_{n+1}=\sum_{i\le n}h_i$ is a finite step. Everything is computed in a finite number of operations on coefficients.

**Roles.** Composition plays the role of the *substitution* of one series into another; the differential equation plays the role of a *constraint* whose unique solution (with $h(0)=1$) turns out to be the geometric series.

**Rules.** The chain rule, the uniqueness of the solution of the ODE, and the heart $e^{-\ln(1-x)}=1/(1-x)$ itself are *equalities of coefficient processes* checkable by finite induction.

**P4 diagnostics.** Before reification the inversion identity was a *second-order* statement about the function *as a whole*—across the entire domain, and therefore invisible to the pointwise, process machinery. Having *reified* the function as a coefficient process, we turn it into a *family of first-order* equalities of coefficients—the recurrence $c_n=1$, finite at every step (Element). The finitization boundary of *functions* is crossed here *at the formal coefficient level*; the analytic transfer to number-processes remains the task of the following chapters.

**What is new, and the honest boundary.** The composition of series, the chain rule, the uniqueness of the solution of the ODE, and the identity $e^{-\ln(1-x)}=1/(1-x)$ are classical mathematics of formal series. What is new is the *framing*: the obstacle that previously stood before the program “the function is a process” is read as an unfinished object and *removed* by reification, and the whole chain up to the concrete inverse-function identity is machine-checked, without axioms.[^9] The honest boundary: this heart is *formal*, at the level of coefficients. That the computed series $e^{-\ln(1-x)}$ equals the geometric function *as a number-process* at every point $|x|<1$ is a separate, analytic statement; Chapter 16.5 builds it through the evaluation bridge, and it requires the *process exponential* of a real argument.

**What the chapter prepares.** The formal heart has been obtained on coefficients. To transfer it into an equality of *number*-processes, we need an exponential able to take as its argument a whole process rather than a rational number—the real $\exp_{ℝ}$. Chapter 16.4 builds it: from Mertens’ theorem on the product of series to the addition theorem, the group homomorphism $(ℚ,+)\to(ℝ^{+},\times)$, and injectivity.

---

[^1]: `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**): `fps_pow_low_order`—if $g(0)=0$, then $(g^k)_i = 0$ for $i<k$. Machine-checked, 0 axioms.
[^2]: Ibid.: `fps_compose_zero`. Machine-checked, 0 axioms.
[^3]: `src/FormalPowerSeries.v`: `fps_chain_rule` (under $g(0)=0$). Machine-checked, 0 axioms.
[^4]: Ibid.: `conv_compose_swap`—the basis of the chain rule (`partial_sum_swap` ${+}$ `fps_pow_low_order`). Machine-checked, 0 axioms.
[^5]: `src/FormalPowerSeries.v`: `geom_satisfies_ode`—$\texttt{fps\_deriv} \texttt{geom} = \texttt{fps\_mul} \texttt{geom} \texttt{geom}$. Machine-checked, 0 axioms.
[^6]: Ibid.: `ode_geom_unique`. Machine-checked, 0 axioms.
[^7]: Ibid.: `conv_ones`—$\texttt{conv} a \texttt{geom} n = \texttt{partial\_sum} a n$.
[^8]: `src/FormalPowerSeries.v`: `compose_exp_log1m_is_geom`—$\texttt{fps\_compose}\ \texttt{exp\_fps}\ \texttt{log1m\_fps} = \texttt{geom\_fps}$. Machine-checked, **0 axioms**.
[^9]: All the material of the chapter comes from `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**; `Print Assumptions` = “Closed under the global context” for the key lemmas, including `compose_exp_log1m_is_geom`).

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/02 Calculus of Process Functions|Chapter 2. The Calculus of Process Functions]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/04 Process Exponential Exp R|Chapter 4. The Process Exponential exp_ℝ]] →
