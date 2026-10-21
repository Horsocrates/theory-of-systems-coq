---
title: "Chapter 6. The Fundamental Theorem of Calculus"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/06 Основная теорема анализа.md"
sourceBlob: 86ea1f9cd09cb626e873cef76da9c637889ca0c2
translated: 2026-10-20
status: draft
---

## The Fundamental Theorem as a Process Connection

### What the Previous Chapters Built

Part V has built analysis layer by layer: distance, topology, continuity, the derivative, the integral. The last two chapters gave two processes. Chapter 5.4 built the derivative as the process of difference quotients `deriv_process` and the grid mean value theorem via walk points. Chapter 5.5 built the integral as the process of accumulation of Riemann sums `integral_process`. The present chapter is where these two processes close together. The fundamental theorem of calculus connects differentiation and integration: the integral of the derivative restores the increment of the function.

The connection was prepared in advance. The telescoping sum `telescope_collapse`, which collapses a sum of increments into the difference of the endpoints, was introduced in § 5.5.1; the grid form of the theorem, `ftc_grid`, was named in § 5.5.2 as a bridge. Here they become the subject rather than an auxiliary means.

### The Classical Theorem and Why It Cannot Be Taken Directly

The classical fundamental theorem of calculus has two parts. The first part: if $F(x)=\int_a^x f$, then $F'=f$—integration with a variable upper limit is inverse to differentiation. The second part: $\int_a^b f' = f(b)-f(a)$—the integral of the derivative equals the increment.

What prevents carrying this over into ToS directly is the arrangement of the current layer, not logic. The classical theorem cannot simply be imported as a ready statement about the real line: the current layer has no primary completed $ℝ$, no integral function $F(x)=\int_a^x f$ with a variable upper limit on quotient classes, and the integral itself is represented by a process of Riemann sums (§ 5.5). Therefore the classical formula has to be restored as a *grid-process connection*, not as an equality of completed limits. This is an honest boundary, and we name it at the very beginning of the chapter: what is built below is the grid form of the theorem plus exact special cases, rather than the full classical two-part theorem.

### The Grid Form: `ftc_grid`{ftc_grid}

{ The substantive core of the chapter is the theorem `ftc_grid` from `RiemannIntegration.v`. If a function $f$ is uniformly differentiable on $[a,b]$ with derivative $f'$ (the condition `udiff_on` from § 5.4), then for every $\varepsilon>0$ there is a level $N$ at which the Riemann sum of the derivative on a grid of $N+1$ subintervals approximates the increment:

$$
\bigl| `riemann_sum`\;f'\;a\;`step`\;(N{+}1)
\;-\;\bigl(f(y_{N+1}) - f(a)\bigr) \bigr|
\;\le\; \varepsilon\cdot(b-a),
$$

where $y_{N+1}=`walk_point` a `step` (N{+}1)$ and $N{+}1$ corresponds to `S N` in the code. There is no limiting division by $h$ here: the derivative enters through the division-free criterion `udiff_on` (§ 5.4). The grid itself, of course, uses safe rational division in choosing the step $(b-a)/(S N)$—the denominator is nonzero, and this is a legitimate finite division, not an inadmissible passage to the limit. The form is a grid form. The proof is assembled from two lemmas of § 5.5.1: `telescope_collapse` identifies the sum of increments with the difference of the endpoints, and `rs_tele_error_bound` estimates the distance between the Riemann sum of $f'$ and this telescope. It is here that the probative force of the whole chapter lies.}

One point of precision is worth naming at once (Qeq hygiene). The theorem compares the Riemann sum with $f(y_{N+1})-f(a)$, where $y_{N+1}$ is the last walk point, and *not* literally with $f(b)-f(a)$. The lemma `walk_endpoint_qeq` gives that $y_{N+1}$ equals $b$ in the sense of the relation `Qeq`; but to carry this under $f$ and read $f(y_{N+1})$ as $f(b)$, the function $f$ must respect `Qeq` (be `Proper`). For an arbitrary $f:ℚ\toℚ$ this requires a separate caveat. Below, reading `ftc_grid` as “the sum of $f'$ approximates $f(b)-f(a)$,” we keep this subtlety in mind.

### The Process Wrapper: `ftc_error_process`{The process wrapper: ftc_error_process}

A process layer is built on top of the grid estimate—the file `ProcessFTC.v`. It defines the error of the fundamental theorem as a process:

```coq
Definition ftc_error (f f' : Q -> Q) (a b : Q) (n : nat) : Q :=
  Qabs (integral_process f' a b n - (f b - f a)).

Definition ftc_error_process (f f' : Q -> Q) (a b : Q) : RealProcess :=
  fun n => integral_process f' a b n - (f b - f a).
```

At level $n$ this is the difference between the Riemann sum of the derivative and the increment of the function; `ftc_error` is its absolute value. The theorem `ftc_is_process_construction` presents this error process as a construction (the E/R/R form).

Let us name the status honestly (safeguards C1 and C4). This is a *process wrapper*: the definitions of `ProcessFTC.v` record the error of the fundamental theorem in process form, but by themselves they do *not* prove that this error decreases or forms a Cauchy process. The substantive estimate is given by `ftc_grid` from `RiemannIntegration.v`, not by `ProcessFTC.v`. Moreover: although the header of `ProcessFTC.v` names `ftc_grid` among its “rules,” `ftc_grid` is not invoked in the proofs of the file itself—the file builds a process record, while the probative work remains with `RiemannIntegration.v`. We separate this explicitly, so as not to pass the wrapper off as the source of the theorem.

### E/R/R Analysis: The Fundamental Theorem as a Connection of Systems

The fundamental theorem is a *connection* between two systems already analyzed—the derivative (Chapter 5.4) and the integral (Chapter 5.5)—rather than a new separate system. But this connection too has an E/R/R arrangement, and the headers of the supporting files give it directly. `FTC.v` labels the objects: *$f$—the integrand, $f'$—the derivative, $K$—the Lipschitz bound; rule—the FTC equation (constitution), the Lipschitz estimate (constraint)*. `ProcessFTC.v` labels the processes: *elements—the derivative and integral processes; role—the bridge between differentiation and integration; rule—`ftc_grid`*.[^1] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. The caveat on status is the same as in Chapters 5.1–5.5: we are dealing with functions $ℚ \to ℚ$, not with quotient classes; and the theorem here is in grid form, not the classical two-part one (§ 6.1.2).

*Rules* (the law $L5$). The constitution is the *equation of the fundamental theorem* itself: the integral of the derivative restores the increment of the function; in the current layer it is written in grid form (`ftc_grid`, § 6.2.3). Adjoining the constitution are the condition of *uniform differentiability* (`udiff_on`) and the Lipschitz estimate as a constraint controlling the remainder (§ 6.3); the probative support is the telescope (§ 6.2.1). An honest boundary: this is a grid, approximate form, exact only for affine functions (§ 6.3.2)—so the constitution here is a *process* one, a family of estimates rather than one completed equality.

*Roles—the significance of positions* (the law $L4$). At the level of objects the theorem distributes roles: $f$ plays the role of the *integrand*, $f'$ that of the *derivative*, $K$ that of the *Lipschitz bound* (this is how `FTC.v` labels them). And at the level of processes the central role of the theorem itself is one—to be the *bridge* between the derivative-process (§ 5.4) and the integral-process (§ 5.5). By $L4$ these roles are grounded by the FTC equation: it is precisely this equation that makes $f'$ “what is integrated in order to get $f$ back.”

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are functions, their derivatives and integrals (Riemann sums), and at the process level, the derivative and integral processes themselves, linked by the theorem. By $L1$ each preserves its identity. By $P4$ both are processes of approximation, not completed limits—and the connection between them is also a process one: a family of grid estimates, sharpening with refinement.

 Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| functions, derivatives, integrals; the derivative and integral processes | bearers | Element |
| $f \to$ integrand, $f' \to$ derivative, $K \to$ bound; the theorem as a bridge | roles | Role |
| the FTC equation (`ftc_grid`, grid form) | constitution | Rule |
| uniform differentiability, the Lipschitz estimate | condition / constraint | Rule |
| the telescope | probative support | Rule |
| the laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The fundamental theorem connects two *already well-formed* systems—the derivative and the integral—without a confusion of categories: $f$ remains the element-integrand, $f'$ its role-derivative, the FTC equation a rule. There is no self-reference. One honest clarification: the loud theorem `derivative_integral_duality` (§ 6.7.1) is modest by itself—the real connection rests on the *pair of bridges* (`ftc_grid` and `deriv_process_converges`), not on it, and it is precisely this pair that is well-formed.

 The analysis closes the E/R/R thread of Part V. The fundamental theorem is a *rule connecting two dual systems*: the derivative (the process of the slope, § 5.4) and the integral (the process of the area, § 5.5). Both have one role pattern—a process converging to a value—and the FTC joins them so that one action is restored by the other. Under $P4$ the connection itself is a process, not a completed identity. Thus the analytic layer of Part V—metric, topology, continuity, derivative, integral—is assembled into a single whole, and each of its links has been read as a system with its own E/R/R structure.

### The Plan of the Chapter

From here the chapter proceeds as follows. § 6.2: the grid theorem and the telescope (the substantive proof). § 6.3: exact and regular cases—the affine function exactly, the uniformly differentiable one approximately. § 6.4: corollaries—the estimate of the increment, monotonicity, the difference. § 6.5: the product rule and integration by parts (here, at last, a full analysis of the applications). § 6.6: the uniqueness of the antiderivative and the affine change of variables. § 6.7: the duality of the derivative and the integral as processes, and the bridge to weak derivatives. § 6.8: the summary.

The supporting files are distributed as follows. The substantive anchors are `RiemannIntegration.v` (`ftc_grid`, the telescope) and `FTC.v` (the Lipschitz property, monotonicity, affine substitution). The applications are in `IntegralApplications.v` (the product rule, integration by parts, the uniqueness of the antiderivative). `ProcessFTC.v` is the process wrapper. The chapter gives the caveat on the status of axioms in § 6.8.

## The Grid Theorem and the Telescope

### The Telescope: The Sum of Increments Is the Difference of the Endpoints

{ The proof of the grid fundamental theorem rests on the telescoping sum. Let us define it as the sum of the increments of the function over consecutive nodes of the walk grid: $`tele_sum` f a `step` n =
\sum_{k=0}^{n-1}\bigl[f(y_{k+1})-f(y_k)\bigr]$, where $y_k=`walk_point` a `step` k$. The lemma `telescope_collapse` collapses it exactly:

$$
`tele_sum`\;f\;a\;`step`\;n \;=\; f(y_n) - f(a).
$$

The intermediate values cancel in pairs; the difference of the endpoints remains. This is the constructive kernel of the fundamental theorem: the accumulation of the increments of a function over the grid equals its total change from $a$ to $y_n$. The coincidence is *Leibniz-exact*, since the nodes are given by the recursive `walk_point` of § 5.4 rather than by a closed formula—the same honest detail that was examined in the chapter on the derivative.}

### Estimating the Error of the Telescope: `rs_tele_error_bound`{Estimating the error of the telescope}

The second brick connects the telescope of a function with the Riemann sum of its derivative. The lemma `rs_tele_error_bound`: under uniform differentiability `udiff_on` $f f' a b$, for every $\varepsilon>0$ there is a level $N$ at which

$$
\bigl| `riemann_sum`\;f'\;a\;`step`\;(N{+}1)
\;-\; `tele_sum`\;f\;a\;`step`\;(N{+}1) \bigr|
\;\le\; \varepsilon\cdot(b-a).
$$

The idea of the proof is an inner induction on the number of steps of the grid. On one step the Riemann term $f'(y_k)\cdot`step`$ differs from the increment $f(y_{k+1})-f(y_k)$ exactly by the error of the linear approximation of the derivative, and this error, by uniform differentiability, is smaller than $\varepsilon\cdot`step`$ (the one-step estimate $|f(x+h)-f(x)-f'(x)h|<\varepsilon|h|$). Summing over $k$ steps, we accumulate $k\cdot\varepsilon\cdot`step`$; for $k=N{+}1$, where $(N{+}1)\cdot`step`=b-a$, this gives $\varepsilon\cdot(b-a)$. The full code is a large induction; what matters here is the scheme: uniformity gives the estimate of one step, the addition of the steps gives the overall one.

### The Grid Theorem as the Result

{ Putting the two bricks together, we obtain `ftc_grid`. The telescope equals the difference of the endpoints (`telescope_collapse`), and the Riemann sum of the derivative is close to the telescope (`rs_tele_error_bound`); hence the Riemann sum of the derivative is close to the difference of the endpoints:

$$
\bigl| `riemann_sum`\;f'\;a\;`step`\;(N{+}1)
\;-\;\bigl(f(y_{N+1}) - f(a)\bigr) \bigr|
\;\le\; \varepsilon\cdot(b-a).
$$

This is the central theorem of § 6.2. Let us name its status honestly (safeguard C1): the form is *division-free*, *grid*, *approximate*—it is not the exact equality $\int_a^b f' =
f(b)-f(a)$. Where classical analysis puts an equals sign, here there stands $\le\varepsilon\cdot(b-a)$ for a sufficiently fine grid.}

And again the Qeq precision of § 6.1.3: on the right-hand side stands $f(y_{N+1})$, not $f(b)$. The lemma `walk_endpoint_qeq` gives $y_{N+1}=b$ in the sense of `Qeq`; reading $f(y_{N+1})$ as $f(b)$ is correct when $f$ respects `Qeq`. The prose phrase “the sum of $f'$ approximates $f(b)-f(a)$” keeps this caveat in mind.

### Why This Is Already the Fundamental Theorem

It may seem that an “approximate” theorem is weaker than the classical one. But under $P4$ this is not so. `ftc_grid` contains the whole essence of the fundamental theorem: the integral of the derivative restores the increment of the function. “Approximateness” here is the very nature of the object, not a defect: no completed limit is taken, and the process of approximations *is* the theorem. This is the same intonation as in § 5.4 with the bridge `deriv_process_converges`: there the process of difference quotients converged to the slope; here the process of Riemann sums of the derivative converges to the increment. The two chapters—the derivative and the integral—close together, and the closing is also a process one. The duality of differentiation and integration (§ 6.7 will return to it) lives precisely in this pair of bridges. In the terms of the analysis of § 6.1.5, the fundamental theorem is exactly that rule which connects two dual systems—the derivative and the integral.

## Exact and Regular Cases

### Zero Derivative

The simplest case of the fundamental theorem is the zero derivative. The lemma `ftc_zero_deriv` states: $`integral_process` 
(\lambda_. 0) a b n = 0$ pointwise at each level $n$. The integral of the zero derivative is zero—exactly, without approximation; it is proved by direct induction on the number of nodes. This agrees with the fundamental theorem: if $f$ is constant, then $f'=0$, the increment $f(b)-f(a)=0$, and the integral of the derivative is also zero. Safeguard C1: here the result is *exact*; the process is identically zero.

### Constant Derivative: An Exact Theorem for the Affine Function

{ The next case is a constant derivative, that is, an affine function. The lemma `ftc_error_const` is the only nontrivial substantive fact of the file `ProcessFTC.v`: for $f(x)=c\cdot x$ with derivative $f'=c$ the error process of the fundamental theorem is equivalent to the constant process zero,

$$
`ftc_error_process`\;(\lambda x. c x)\;(\lambda_. c)\;a\;b
\;\sim\; `const_process`\;0.
$$

That is, $\int_a^b c = c (b-a) = f(b)-f(a)$ *exactly*: the error is identically zero at each level. This is the *exact process case* of the fundamental theorem.}

{ Here two close results must be separated (safeguard C1). What is exact is precisely `ftc_error_const`—the process zero for $f(x)=c x$. The lemma `ftc_affine` from `RiemannIntegration.v`, by contrast, casts the same affine theme in the *grid* $\varepsilon$-form through `ftc_grid` (of the form “there exists $N$ at which the error is $\le\varepsilon(b-a)$”), not as a separate exact equality at each level. To place them in one row as “exact” would be wrong: `ftc_error_const` is exact, `ftc_affine` is an $\varepsilon$-estimate. (A third relative, `ftc_const_deriv`, re-exports `integral_process_const` from § 5.5.) In substance: for a straight line the area under the derivative is exactly equal to the increment, and the same fact is visible in grid form.}

### Uniformly Differentiable Functions: A Grid Estimate

For general uniformly differentiable functions the fundamental theorem is a grid one rather than exact: `ftc_grid` gives an error $\le\varepsilon(b-a)$, but not zero. The boundary between the exact and the approximate runs exactly along linearity. Affine functions—exactly, because their increment is linear in the step and the Riemann sum catches it without remainder. Nonlinear ones—approximately, because a remainder of higher order appears (the same theme as with the square in § 5.4: the error of the linear approximation was $h^2$). The finer the grid, the smaller this remainder.

{ The grid estimate `ftc_grid` itself stands on uniform differentiability (`udiff_on`), the telescope (`telescope_collapse`), and the estimate `rs_tele_error_bound`—it needs no additional regularity. However, `FTC.v` builds a regularity layer on top of it: lemmas such as `udiff_implies_bounded` (an estimate of the values of the function through the derivative) and `lipschitz_bounded` (the boundedness of a Lipschitz function) help to control the classes of functions on which grid arguments apply stably—this is useful for the applications of § 6.4–6.5, not for the central estimate itself.}

### The Nonnegativity of the Integral of the Derivative

The last case connects the fundamental theorem with order. The lemma `ftc_nonneg_integral` (`RiemannIntegration.v`): for $f'\ge 0$ the Riemann sum of the derivative is nonnegative up to the grid error. In substance: a nonnegative derivative gives a nondecreasing increment—if the rate of the function is nowhere negative, its value does not fall. This is the grid FTC form of motif M4 from § 5.5 and a bridge to the monotonicity of § 6.4: the sign of the derivative governs the growth of the increment.

## Corollaries of the Fundamental Theorem

### The Estimate of the Increment

The first corollary is the estimate of the increment through the derivative. The lemma `ftc_increment_bound` (`FTC.v`) is in essence the same `bounded_deriv_bounded_increment` from the mean value theorem of § 5.4 §4.6: a bounded derivative gives a bounded increment of the function. Safeguard C4: this is the same lemma as in the chapter on the derivative, read here in the context of the fundamental theorem. The connection is direct—the grid mean value theorem was one of the forerunners of `ftc_grid`, and the estimate of the increment carries over unchanged.

### Monotonicity from the Sign of the Derivative

{ The second corollary is monotonicity. The lemma `ftc_monotone`: for $f'\ge 0$ the function grows on the grid (the increment is nonnegative); `ftc_strict_monotone` (the same as `pos_deriv_increases` from § 5.4) gives strict growth for a derivative bounded away from zero. The fundamental theorem turns the local property “the derivative is positive” into the global one “the function grows”: the sign of the derivative governs the growth of the accumulated increment. These are grid results, like everything in § 6.2–6.4.}

### The Difference and the Linearity of Increments

The third corollary is linearity. The lemma `ftc_difference` gives the increment of a difference of functions, and `ftc_sum_rule` (also known as `ftc_linearity`) and `ftc_scale_rule` (through `udiff_scale`) the increments of a sum and of a scalar multiple. The fundamental theorem respects linear operations: the increment of a sum is the sum of the increments, in full agreement with the linearity of the integral in § 5.5.3 and of the derivative in § 5.4.2. This is a manifestation of the fact that both operations of analysis are linear and that the connection between them preserves linearity; it is nothing new.

### The Absolute Estimate

The fourth corollary is the absolute estimate. The lemma `ftc_absolute_value_bound` (`FTC.v`): for $|f'|\le M$ the Riemann sum of the derivative does not exceed $M\cdot(b-a)$ in absolute value. This is the FTC form of the estimate of § 5.4.4, now applied to the derivative. It will be needed in § 6.5: in the product rule and in integration by parts the factors will have to be bounded, and this lemma gives the needed control.

## The Product Rule and Integration by Parts

### The Product Rule for Uniform Differentiability

{ The main nonlinear application of the fundamental theorem is the product rule, the lemma `udiff_product` from `IntegralApplications.v`. If $f$ and $g$ are uniformly differentiable on an interval with bounded values and derivatives, then their product $f\cdot g$ is uniformly differentiable with the derivative

$$
(f\cdot g)' = f' g + f g'.
$$

We give the proof as an idea in three steps. First, `product_decomp` decomposes the increment of the product into three terms—on the pattern of the decomposition from the derivative rule of § 5.4 §4.4.2. Second, each term is bounded by a share $\varepsilon/3$. Third, the factors are controlled by the bounds $M_f, M_g, M_{f'}, M_{g'}$ on the values and derivatives. The sum of the three estimates of $\varepsilon/3$ each gives what is required. This is a full theorem (safeguard C1), a direct uniform version of the product rule for the derivative—but on an interval, as integration requires. A special case is `udiff_square`: the derivative of the square, $(f^2)' =
2f f'$.}

### The Fundamental Theorem for a Product

Applying `ftc_grid` to the derivative of the product, we obtain the lemma `ftc_product`: the Riemann sum of the expression $f'g + fg'$ approximates the increment of the product $fg$. This is a direct corollary of the product rule and the grid theorem: since $(fg)' = f'g + fg'$, the integral of the right-hand side restores the increment of $fg$. The lemma is a bridge to integration by parts.

### Integration by Parts

{ Regrouping `ftc_product`, we obtain integration by parts—the lemma `integration_by_parts`. In grid form it states: the Riemann sum of $f'g$ approximates the boundary term $fg$ minus the Riemann sum of $fg'$,

$$
\bigl| `RS`(f'g) - \bigl(f(\text{end})g(\text{end}) -
f(a)g(a)\bigr) + `RS`(fg') \bigr| \;\le\;
\varepsilon\cdot(b-a).
$$

The proof is `ftc_product` plus the linearity of Riemann sums (`riemann_sum_add`, `riemann_sum_sub`). Safeguard C1: this is an $\varepsilon$-grid form, not an exact equality. Special cases: `ibp_self` gives $2\int f'f \approx
f(\text{end})^2 - f(a)^2$, and `ibp_identity` a formula with the identity factor, $\int g \approx xg |_a^b - \int xg'$.}

### What Integration by Parts Means

The geometric and operational meaning of integration by parts is worth naming directly. The formula redistributes the derivative between the factors: the derivative can be *transferred* from one function to the other—at the price of the boundary term $fg |_a^b$. This is a direct corollary of the product rule integrated over the interval: since the increment of the product breaks up into two contributions, $f'g$ and $fg'$, knowing the increment of the product and one of the integrals, we restore the other. Transferring differentiation from factor to factor is exactly the device that in the analysis of functions of several variables will become the definition of the *weak* derivative; the chapter will return to this bridge in § 6.7.

## The Uniqueness of the Antiderivative and the Change of Variables

### The Uniqueness of the Antiderivative

{ One more classical corollary is the uniqueness of the antiderivative. The lemma `antiderivative_unique` from `IntegralApplications.v`: if functions $f$ and $g$ have one and the same derivative $h$ on $[a,b]$, then their increments coincide (up to the grid error $\varepsilon(b-a)$). The proof relies on `udiff_sub`: the difference $f-g$ has a zero derivative, and then `ftc_grid` with a zero derivative gives a small increment of the difference. In substance this is the grid form of the statement “an antiderivative is determined up to a constant”: two antiderivatives of one function differ by something with a zero derivative, that is, something nearly constant. A direct parallel with `zero_deriv_near_constant` from § 5.4 §4.7: a zero derivative implies near-constancy.}

### Change of Variables: Only the Affine Case

The change of variables is formalized only partially, and this must be named honestly (safeguards C1 and C4). The core has no general chain rule, as already noted in § 5.4 and § 5.5. There is only the *affine* case: `udiff_chain_affine` (`FTC.v`)—the chain rule for the inner function $g = c\cdot x + d$ with $c>0$—and `udiff_chain_affine_neg` with $c<0$. On them is built the affine change of variables in the integral, `ftc_u_substitution_affine`. That is, the substitution $u = g(x)$ is proved only for a linear $g$; the general substitution with an arbitrary smooth $g$ is not formalized. The boundary is outlined concretely.

### The Lipschitz Property and Uniform Continuity

{ The regularity on which the FTC estimates stand forms a hierarchy, but it must be named carefully. There is one strict bridge: `lipschitz_uniform_cont` (`FTC.v`) proves that a Lipschitz function is uniformly continuous. The notions `Lipschitz_on` and `uniformly_continuous_on` are defined right there.}

{ Beyond this, one should be careful. The file does not contain a separate theorem of the form “`udiff_on` $\Rightarrow$ `Lipschitz_on`” in standard form, and the hierarchy should not be presented as a ready chain. What is there for certain: `lipschitz_bounded`—the boundedness of a function if it is already Lipschitz; `udiff_implies_bounded`—an estimate of the values through the layer of the mean value theorem. For uniformly differentiable functions there are grid and MVT estimates of increments (for example, `bounded_deriv_bounded_increment` from § 5.4 and its relatives), but this is not one simple theorem “uniformly differentiable, hence Lipschitz.” The connection with § 5.3, where the Lipschitz property was introduced as a condition, and with § 5.4, where MVT estimates of increments close to Lipschitz ones were derived from a bounded derivative, rests precisely on these particular lemmas, not on a single implication.}

## The Duality of the Derivative and the Integral. The Bridge to Weak Derivatives

### The Derivative and the Integral as Dual Processes

In `ProcessFTC.v` the duality of the derivative and the integral is declared by a theorem with the loud name `derivative_integral_duality`. Let us name its content honestly (safeguard C1). For $a<b$ the theorem states two things: first, that a process exists, and that under `has_derivative` $f x (f' x)$ the derivative-process is Cauchy (through `deriv_process_cauchy`); second, that `integral_process` $f' a b$ exists.

The name “duality” sounds stronger than the formal content. In the code the first process `proc_d` is *fictitious* (literally $\lambda_. 0$, with the author’s comment “dummy”); the real content is a re-export of `deriv_process_cauchy` from § 5.4 plus the trivial existence of `integral_process`. This is *not* a proof of the duality of $d/dx$ and $\int$ as operations; it is a statement that both processes exist and that the derivative-process is Cauchy when the derivative exists. It should be called exactly that—a conjunction of existences, not a duality theorem.

### In What Sense the Duality Is Real

What has been said does not mean that there is no duality—it means only that the duality rests on two separate bridges, genuinely proved, rather than on the theorem with the loud name. The first bridge is `ftc_grid` of this chapter: the integral of the derivative restores the increment of the function. The second is `deriv_process_converges` from § 5.4: the derivative-process converges to the slope. Together they make up the substantive duality of differentiation and integration: one action is restored by the other, at the level of processes. The honest separation is this: the loud name `derivative_integral_duality` is modest by itself, and the real duality lies in the pair `ftc_grid` and `deriv_process_converges`.

### Interval Splitting

The lemma `ftc_interval_split` (`ProcessFTC.v`) states that for $a<m<b$ there exist processes on $[a,m]$ and $[m,b]$ pointwise equal to `integral_process`. Let us name its status directly (safeguard C1): it is *not* the additivity of the integral over intervals, $\int_a^b = \int_a^m + \int_m^b$. The proof is the presentation of two processes and `reflexivity`; the lemma asserts only the *existence* of subprocesses on the subintervals, not the equality of the integral to their sum. Full additivity over intervals would require a separate theorem, which the supporting files do not have. This is an honest boundary, and the name of the lemma should not be read as saying more than it proves.

### The Bridge to Weak Derivatives

The integration by parts of § 6.5 opens a door into analysis that goes beyond the limits of this chapter—and it is worth naming this door, marking clearly that the door itself is not built here. The integration-by-parts formula transfers the derivative from one function to another at the price of a boundary term. If the boundary term is made zero (taking test functions that vanish at the endpoints), a pure transfer results: $\int f' \varphi = -\int f \varphi'$. It is this equality that is taken as the *definition* of the weak (generalized) derivative—a derivative given through its action on test functions rather than pointwise. Weak derivatives are the entry point of Sobolev spaces and of the modern theory of partial differential equations.

Let us stress with the utmost clarity: the supporting files of this chapter have *no* weak derivatives and no Sobolev spaces. Integration by parts shows only the *formal pattern* they need—the transfer of differentiation with a boundary term. These notions themselves are a motivating program for future parts of the volume, not the proved content of `FTC.v` or `IntegralApplications.v`. We name the direction without attributing to the repository what it does not yet contain. In the terms of the analysis of § 6.1.5, integration by parts is a rule (Rule) that transfers differentiation; it only sketches the pattern of weak derivatives, without building them.

## What Has Been Built and What Is Being Prepared. Summary of the Chapter

### The Summary in Three Columns

Let us gather what has been done in infrastructure mode.

**Built and checked:**

- the grid fundamental theorem `ftc_grid` (the Riemann sum of $f'$ approximates the increment of $f$ under `udiff_on`)—the substantive core; the telescope and `rs_tele_error_bound`;
- the exact process case for the affine function (`ftc_error_const`); the zero derivative (`ftc_zero_deriv`); the affine $\varepsilon$-form (`ftc_affine`);
- the process wrapper `ftc_error_process`, `ftc_is_process_construction`;
- corollaries: the estimate of the increment, monotonicity, the difference, the absolute estimate;
- the product rule `udiff_product`, integration by parts `integration_by_parts`, `ibp_self` and `ibp_identity`, the uniqueness of the antiderivative `antiderivative_unique`;
- the affine change of variables `ftc_u_substitution_affine`;
- the Lipschitz property implies uniform continuity (`lipschitz_uniform_cont`).

**Not built in this chapter:**

- the classical two-part theorem ($F(x)=\int_a^x f$, $F'=f$) in general form—what is proved is the grid form plus the exact affine case; the two-part formulation is a substantive reading, not a theorem;
- the fundamental theorem for functions on the classes `RealPoint`—here only $ℚ$-functions (safeguard C2);
- the general chain rule and the general change of variables—only the affine case;
- the additivity of the integral over intervals as a theorem (`ftc_interval_split` is only the existence of subprocesses);
- weak derivatives and Sobolev spaces—a motivating program for future parts, not the content of the supporting files.

**Prepares next:**

- Fubini (Chapter 5.7): 2D step functions, the interchange of a double process;
- weak derivatives and Sobolev—through integration by parts;
- measure (Part VI): on the foundation of the step integral of § 5.5.

### What Would Remain for the Classical Two-Part Theorem

The chapter has proved the grid form; let us name concretely what is missing for the classical two-part theorem—just as § 5.8 named what was missing for the integral on classes. It would be necessary, first, to define the integral function with a variable upper limit $F(x)=\int_a^x f$ as a process and to prove the first part of the theorem, $F'=f$—the supporting files do not contain this. Second, an exact equality (rather than a grid estimate) would require passing to the quotient classes `RealPoint` and proving well-definedness with respect to equivalence. The heading here says “classical two-part,” not “full”: for its own grid-process task the chapter is complete; what is missing is precisely the classical superstructure.

### A Caveat on the Status of Axioms

{ The Part V safeguard requires precision about axioms. The cores—`RiemannIntegration.v`, `FTC.v`, `IntegralApplications.v`—declare “none” or “0 axioms” in their headers; `ProcessFTC.v`, “8 Qed, 0 axioms.” But *some* of these files import layers in which classical logic occurs: for example, `EVT_idx.v` with a local `classic`, or `ProcessArithmetic.v`, where `classic` is used in `monotone_bounded_Cauchy`. `Differentiation.v` and `MeanValueTheorem.v` themselves declare the absence of axioms in their headers. One should not say wholesale “they all drag in classic”: an import by itself does not mean that every lemma depends on `classic`—the status of a particular theorem is established only by the command `Print Assumptions` for that theorem itself.}

`Print Assumptions` is written out at the end of `RiemannIntegration.v` (for `ftc_grid` and others) and of `FTC.v` (for `lipschitz_uniform_cont`, `ftc_u_substitution_affine`, and others); `ProcessFTC.v` and `IntegralApplications.v` have no final block—for the theorem one needs, it is run separately. And honest facts for the completeness of the picture: `ftc_grid` is named in the header of `ProcessFTC.v` among the rules but is not invoked in the proofs of the file; the theorem `derivative_integral_duality` contains a fictitious process; `ftc_interval_split` is not additivity; many lemmas of `ProcessFTC.v` are re-exports of what has already been proved.

### Summary of the Chapter

The chapter has connected the derivative and the integral—two processes built in § 5.4 and § 5.5. The main turn lies in what the connection itself turned out to be. Under $P4$ the fundamental theorem of calculus is a *process connection*, not one completed limit identity $\int_a^b f' = f(b)-f(a)$: a family of approximations in which at each level of the grid the Riemann sum of the derivative approximates the increment of the function, and the precision grows with refinement. The substantive core is the division-free grid estimate `ftc_grid`; for affine functions the connection is exact, for general uniformly differentiable functions it is grid-approximate, and the approximation is controlled precisely by the estimate `ftc_grid`. The main caution: this is not the full classical two-part theorem, the loud names have been named honestly, and weak derivatives are left to future parts as a program.

*Built: the grid fundamental theorem `ftc_grid` through the telescope; the exact affine case; corollaries (monotonicity, estimates of the increment); the product rule, integration by parts, the uniqueness of the antiderivative; the affine change of variables.*

*What it stands on: the telescope and the uniform differentiability of § 5.4–5.5, and the grid ontology of $P4$, in which the connection of the derivative and the integral is a process of approximations, not a completed equality; the real duality rests on the pair of bridges `ftc_grid` and `deriv_process_converges`.*

*Next: Fubini for 2D step functions (Chapter 5.7); weak derivatives and Sobolev through integration by parts; general measure on the foundation of the step integral (Part VI).*

---

[^1]: The E/R/R labeling is in the headers of the files `FTC.v` (objects) and `ProcessFTC.v` (processes); here it is unfolded on the pattern of Part I.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/05 Integral|Chapter 5. The Integral]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/07 Fubini Theorem on Processes|Chapter 7. Fubini’s Theorem on Processes]] →
