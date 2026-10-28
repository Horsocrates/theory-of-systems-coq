---
title: "Chapter 4. The Derivative"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/04 Производная.md"
sourceBlob: 77f8dd767cb710af619f0235c76b77783437f99a
translated: 2026-10-20
status: draft
---

## What a Derivative without Division Is For

### What the Previous Chapters Built

Part V builds analysis layer by layer. Chapter 5.1 introduced distance and showed that between processes it is itself a process. Chapter 5.2 built topology: open balls, neighborhoods, compactness. Chapter 5.3 defined continuity—through $\delta$-$\varepsilon$—and proved the intermediate value theorem by bisection and the extreme value theorem by a grid. By this point we have an apparatus with which one can say: a function is *continuous*—its values make no jumps.

The derivative is the next layer. It answers the question “how fast does the function change?” rather than “does the function make jumps?” From continuity to *smoothness*: from the increment being small for a small step to the increment being *linear* in the step up to a correction of higher order. Continuity has already given us the $\delta$-$\varepsilon$ language; the derivative is built directly on top of it, and therefore the chapter will refer to § 5.3 many times.

### Division and the Limit as a Problem

The classical definition of the derivative looks like this:

$$
f'(x) \;=\; \lim_{h \to 0} \frac{f(x+h) - f(x)}{h}.
$$

Before carrying it over into ToS, it is worth understanding precisely what *constitutes* the difficulty here and what does not.

*Division by a nonzero rational step* constitutes no difficulty. If $h$ is a concrete nonzero rational number, then $\bigl(f(x+h)-f(x)\bigr)/h$ is a perfectly legitimate rational expression; there is nothing problematic in it, and below in this chapter we will use such division freely.

The difficulty lies elsewhere, and it is twofold. First, the classical definition makes the limit of the *quotient* as $h \to 0$ the *primary object*. But $h$ then runs through values tending to zero, and one cannot divide by zero; for the limit to be defined, one has to consider the quotient on ever smaller steps and pass to the limit. Second, this limit itself is a completed object “$\lim$,” and under $P4$ there are no completed limits: a “real” in ToS is itself a process. What is needed is a formulation in which the limit of the quotient at $h=0$ does *not* stand in the place of the primary definition.

### The Division-Free Criterion: $o(h)$

The first layer of the derivative in ToS is a *criterion*: a rule answering the question “which number $L$ is the derivative of the function $f$ at the point $x$?” And we formulate this criterion *without division*.

The idea is simple. To say “the slope of $f$ at the point $x$ equals $L$” is to say that the increment $f(x+h)-f(x)$ is well approximated by the *linear* expression $L\cdot h$. How well? So well that the approximation error is small *to the order of $h$*: smaller than any prescribed fraction of $|h|$. Let us write this down:

$$
\forall \varepsilon>0\;\;\exists \delta>0\;\;\forall h:\;
0<|h|<\delta \;\Longrightarrow\;
\bigl|f(x+h) - f(x) - L\cdot h\bigr| < \varepsilon\cdot|h|.
$$

Here there is an estimate of the form $o(h)$ and no division: the error of the linear approximation decreases faster than the step itself. In Rocq this definition bears the name `has_derivative` and is written in the file `Differentiation.v`:

```coq
Definition has_derivative (f : Q -> Q) (x L : Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists delta : Q, 0 < delta /\
      forall h : Q, 0 < Qabs h -> Qabs h < delta ->
        Qabs (f (x + h) - f x - L * h) < eps * Qabs h.
```

Let us read it carefully. $L\cdot h$ is the linear approximation of the increment. The difference $f(x+h)-f(x)-L\cdot h$ is the error of this approximation. The criterion requires the error to be smaller than $\varepsilon\cdot|h|$—that is, an arbitrarily small fraction of the step—as soon as the step is small enough. The limit is present here as an $\varepsilon$-$\delta$ quantifier, not as a completed object—exactly the same device by which $\delta$-$\varepsilon$ continuity was defined in § 5.3. The criterion says *which* $L$ is the derivative without making the limit of the quotient primary.

Let us note the level of the type precisely (the Part V safeguard). Here $f :
ℚ\toℚ$ is a function taking a rational number to a rational one. It is *not* a process and *not* a function on the quotient classes `RealPoint`; the chapter works with rational-valued functions of a rational argument, and this honest limitation is named at once.

One more detail calls for a word. The step $h$ is taken to be *nonzero*: the condition is written as $0<|h|<\delta$. The main reason is substantive: the derivative checks the behavior of the function under small *nonzero* shifts, that is, in a *punctured* neighborhood of the point $x$. A zero step is uninformative: for $h=0$ the estimate turns into $0<0$ on the left and is trivially true; it carries no local content. In the code the nonzeroness of $h$ additionally helps to get around technical subtleties of the rational representation and of the relation `Qeq`—but this is a secondary motive, not the main one. The same device was applied to `continuous_at` in § 5.3; it is a deliberate detail, not an oversight.

### The Derivative-Process: `deriv_process` and the Bridge

The criterion of § 4.1.3 says *which* number $L$ is the derivative. But it does not *compute* $L$: it is a predicate, a check, rather than a construction. The computational side needs a second layer—the derivative as a *process*.

The idea of the process layer answers directly to the ontology of $P4$. Instead of speaking of the limit as $h\to 0$, we fix a *concrete* decreasing sequence of nonzero steps

$$
h_n \;=\; \frac{1}{n+1} \quad (n = 0, 1, 2, …)
$$

and at each step compute the ordinary *difference quotient*. We obtain a process: at level $n$, the rational number $\bigl(f(x+h_n)-f(x)\bigr)/h_n$. Under $P4$ the derivative is *the process itself* of step-by-step rational approximations of the slope, not a completed limit of this process. In the file `ProcessDerivative.v` this is written as follows:

```coq
Definition deriv_step (n : nat) : Q :=
  1 / inject_Z (Z.of_nat (S n)).

Definition deriv_process (f : Q -> Q) (x : Q) : RealProcess :=
  fun n =>
    let h := deriv_step n in
    (f (x + h) - f x) / h.
```

Here there *is* division—but it is division by $h_n$, and $h_n$ is positive by construction: the lemma `deriv_step_pos` establishes $0<h_n$ for every $n$. This is legitimate division by a nonzero rational step, not the inadmissible limit at $h=0$. On the simplest functions the process behaves as expected: `deriv_process_const` shows that for a constant it is equivalent to the constant process $0$, and `deriv_process_id` that for the identity $w\mapsto w$ it is equivalent to the constant process $1$.

The two layers—the criterion and the process—are linked by a *bridge*: the theorem `deriv_process_converges`. It states: if $L$ is the derivative of $f$ at the point $x$ in the sense of the criterion `has_derivative`, then the process of difference quotients is equivalent to the constant process $L$:

$$
\texttt{has\_derivative}\;f\;x\;L
\;\Longrightarrow\;
\texttt{deriv\_process}\;f\;x \;\sim\; \texttt{const\_process}\;L.
$$

In substance the bridge says: the division-free criterion and the computational process *agree*—the number $L$ satisfying the criterion is exactly what the process of difference quotients converges to. The proof is direct: the criterion gives $\delta$, the lemma `deriv_step_vanishes` finds a level $N$ from which on $h_n<\delta$, and then $\bigl|(f(x+h)-f(x))/h - L\bigr| = |f(x+h)-f(x)-L h|/|h| <
\varepsilon$. Two more facts follow at once from the bridge: `deriv_process_cauchy` (the process of difference quotients is a Cauchy process) and `derivative_is_process_construction` (the derivative is presented as a Cauchy process equivalent to the constant $L$—the E/R/R form of the result).

It is worth separating three statuses so as not to confuse them later (the Part V safeguard). `has_derivative` is a *criterion*, a predicate. `deriv_process` is a *process*, a construction. `deriv_process_converges` is the *bridge theorem* between them. These are three different things, and the chapter will indicate every time which of them is meant.

And right here comes an important caveat about what `deriv_process` *is not*. By itself the process of difference quotients is a *candidate* for the derivative, not a full definition of differentiability. It takes one fixed sequence of *positive* steps $h_n=1/(n+1)$—that is, in essence, it is a right-sided process of difference quotients. Therefore its convergence by itself does not replace the two-sided criterion `has_derivative`, which checks *all* small nonzero $h$, in both directions. The classical counterexample is the function $|x|$ at zero: the right-sided difference quotients converge to $1$, but there is no two-sided derivative (the chapter will return to this example in § 4.3.3). The full meaning of the derivative is given precisely by `has_derivative`; the theorem `deriv_process_converges` asserts only *one direction*—if the derivative exists in the division-free sense, then the chosen process of difference quotients converges to it. To define differentiability as “the process `deriv_process` is a Cauchy process” would be a mistake.

On the status of axioms: `ProcessDerivative.v` declares “0 axioms, 16 Qed” in its header; it imports `ProcessCore`, `ProcessArithmetic`, and `Differentiation`. The chapter will return in § 4.8 to the recurring caveat that a file header does not replace an audit of a particular theorem.

### E/R/R Analysis: The Derivative as a System

The derivative is a system, and the E/R/R methodology (Part I) applies to it. The analysis unfolds the labeling from the header of the supporting file, where it is given directly: *elements—difference quotients; role—a Cauchy process converging to the slope; rule—the condition `has_derivative`*.[^1] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. The caveat on status is the same as in Chapters 5.1–5.3: we are dealing with functions $ℚ \to ℚ$, not with maps of quotient classes; the “system” is a substantive ontological interpretation, not an object `System` $L$.

*Rules* (the law $L5$). The constitution of the derivative is the *division-free* criterion $o(h)$ (`has_derivative`, § 4.1.3): the error of the linear approximation is smaller than $\varepsilon\cdot|h|$. This rule says *which* number is the slope without making the limit of the quotient primary. Adjoining the constitution is a concrete layer—the rules of differentiation (linearity, § 4.2; product and power, § 4.4), the bridge between criterion and process (§ 4.1.4), and the uniqueness of the slope (§ 4.5.1). Over $ℚ$ the rules have a *strengthening*: the mean value theorem needs *uniform* differentiability rather than pointwise (`udiff_on`, § 4.6)—the same interchange of quantifiers that distinguished uniform continuity in § 5.3.

*Roles—the significance of positions* (the law $L4$). The central role is the *slope*: the coefficient of the linear approximation that differentiation assigns to the function at a point. By $L4$ this role is structurally grounded: the criterion $o(h)$ singles out the slope unambiguously (uniqueness, § 4.5.1). The computational side of the role is carried by the *process of difference quotients*—a Cauchy process converging to the slope (this is how the role is named in the file header). The function itself thereby receives one of the qualitative positions: *differentiable*, *uniformly differentiable*.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are functions $ℚ \to ℚ$, and in the process, the difference quotients $q(n) = \bigl(f(x+h_n)-f(x)\bigr)/h_n$ with $h_n = 1/(n+1)$. By $L1$ the slope, if it exists, is identical to itself (unique). By $P4$ the bearers of the process are finite at each step—rational difference quotients, surveyable at any level; the derivative is actual as a process of approximations of the slope, and there is no completed “limit as $h\to 0$.”

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| functions $ℚ \to ℚ$; difference quotients $q(n)$ | bearers | Element |
| the slope $L$; the process converging to the slope | roles | Role |
| the $o(h)$ criterion `has_derivative` | constitution (division-free) | Rule (constr.) |
| linearity, product, power | rules of differentiation | Rule (constr.) |
| the criterion–process bridge; uniqueness of the slope | agreement | Rule |
| uniform differentiability (`udiff`) | strengthening for the mean value theorem | Rule |
| the laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: functions and difference quotients are elements, the slope is a role, the criterion $o(h)$ is a rule. The derivative as a role is defined correctly: the criterion singles out the slope as *unique* (§ 4.5.1)—this is $L1$ for the role. There is no self-reference: the criterion quantifies over steps $h$ and stands *above* the values of the function—by $L5$ the operation stands above its operands. The derivative is well-formed.

 The analysis clarifies the arrangement of the chapter. The *two layers*—criterion and process—are the distinction between *rule* and *bearer*: the $o(h)$ criterion (Rule) says *what* the slope *is*, while the process of difference quotients (an Element construction) *approximates* it; the bridge of § 4.1.4 links them. Hence also the warning of § 4.1.4 about the function $|x|$: the one-sided process is only a candidate bearer, and what defines the derivative is precisely the two-sided criterion-rule. And the Lipschitz property of § 4.7.3 shows how the Rules of the derivative *yield* what in § 5.3 had to be required for continuity. The same analysis also sets the pattern for Part V: every analytic concept is read as a system with its own E/R/R structure.

### The Plan of the Chapter

From here the chapter proceeds as follows. § 4.2: the basic rules of differentiation—the derivative of a constant, of the identity, linearity. § 4.3: the connection with § 5.3—differentiability implies continuity. § 4.4: product and power, the main nonlinear rules. § 4.5: the uniqueness of the derivative and an application to optimization—Fermat’s theorem. § 4.6: the mean value theorem via “walk points.” § 4.7: corollaries of the mean value theorem—monotonicity, the Lipschitz property. § 4.8: the summary.

There are three supporting files. `Differentiation.v`: the division-free criterion and the rules. `ProcessDerivative.v`: the derivative as a process and the bridge to the criterion. `MeanValueTheorem.v`: the grid mean value theorem and its corollaries. All three declare the status “AXIOMS: none” in their headers; the chapter gives in § 4.8 the precise caveat on what this header means and what it does not.

## Basic Rules of Differentiation

### The Derivative Does Not Depend on How the Function Is Written

Before proving the substantive rules, it is worth fixing two “hygienic” lemmas. They say that the derivative is a property of the *function* and of the *number*, not of their syntactic notation.

The first lemma is extensionality in the function. If two functions $f$ and $g$ are pointwise equal, that is, $f w = g w$ for every $w$, then a derivative of one is a derivative of the other. In `Differentiation.v` this is `has_derivative_ext`: from `forall w, f w == g w` and `has_derivative f x L` follows `has_derivative g x L`. The proof is evident: the difference $g(x+h)-g(x)-L h$ is pointwise equal to $f(x+h)-f(x)-L h$, and the estimate carries over unchanged.

The second lemma is extensionality in the value of the derivative. If $L=L'$ as rational numbers (in the sense of `Qeq`), then $L'$ is a derivative whenever $L$ is. This is `has_derivative_eq`. Together the two lemmas mean that the notion “derivative” is well defined: it does not distinguish pointwise equal functions and does not distinguish `Qeq`-equal values. From here on we use this without comment.

### The Simplest Cases: Constant and Identity

The two simplest rules set the base for everything else.

The derivative of a constant is zero. If $f$ is the constant function $w\mapsto c$, then its derivative at any point equals $0$. In the code this is `deriv_const`. The proof is trivial: the error of the linear approximation here is

$$
c - c - 0\cdot h \;=\; 0,
$$

that is, identically zero, and the inequality $0 < \varepsilon\cdot|h|$ holds for any positive $\varepsilon$ and nonzero $h$. In substance: a constant function does not change; its rate of change is zero.

The derivative of the identity is one. For the function $w\mapsto w$ the derivative at any point equals $1$—this is `deriv_id`. The approximation error is again identically zero:

$$
(x+h) - x - 1\cdot h \;=\; 0.
$$

In substance: the identity function changes at the same rate as the argument changes. These two rules—`deriv_const` and `deriv_id`—will serve as the base of the induction in § 4.4.3, where the power rule will grow out of them.

### The Linearity of the Derivative

Differentiation is a linear operation. This means four rules, collected in `SECTION 2` of the file `Differentiation.v`.

The derivative of a scalar multiple: $(c\cdot f)' = c\cdot f'$. If $L$ is the derivative of $f$, then $c\cdot L$ is the derivative of the function $w\mapsto
c\cdot f(w)$—this is `deriv_scale`. The derivative of the opposite function: $(-f)' = -f'$—this is `deriv_neg`. The derivative of a sum: $(f+g)' = f'+g'$—this is `deriv_sum`. The derivative of a difference: $(f-g)' = f'-g'$—this is `deriv_sub`.

The device used in proving the sum rule deserves a name; it is typical of the whole chapter. The error of the linear approximation of a sum splits into two errors:

$$
\bigl(f(x+h)+g(x+h)\bigr) - \bigl(f(x)+g(x)\bigr) - (L_f+L_g)h
=
\bigl(f(x+h)-f(x)-L_f h\bigr) + \bigl(g(x+h)-g(x)-L_g h\bigr).
$$

Each term is small by its own derivative; for their sum to fit within $\varepsilon\cdot|h|$, an estimate with $\varepsilon/2$ is taken for each, and the triangle inequality for the absolute value assembles the result. This device of splitting $\varepsilon$ into parts is common to all the rules in which the increment breaks up into a sum.

Let us note the economy of means. The difference rule `deriv_sub` is derived from `deriv_sum` and `deriv_neg` through the extensionality lemmas of § 4.2.1, with no fresh proof: the difference $f-g$ is rewritten as the sum $f+(-g)$, and the result carries over. Each next rule is set on top of those already proved rather than built from scratch.

Linearity carries over into the process layer as well. The file `ProcessDerivative.v` lifts the sum and the scalar multiple into process form: `deriv_sum_process` states that the process of difference quotients of the sum $f+g$ is equivalent to the constant process $L_f+L_g$, and `deriv_scale_process` that the process for $c\cdot f$ is equivalent to the constant process $c\cdot L$. Both are proved uniformly and briefly: the bridge `deriv_process_converges` is applied, and then the corresponding rule `deriv_sum` or `deriv_scale` from `Differentiation.v`. That is, the process rules are a superstructure over the criterion rules via the bridge of § 4.1.4, not separate proofs.

### What Linearity Means for the Theory

The linearity of the derivative reflects the arrangement of the definition itself; it is no accidental coincidence. In the criterion `has_derivative` the approximating expression is $L\cdot h$, and it is linear in $h$. Differentiation assigns to a function its linear approximation; and since the approximation is linear, linear operations on functions pass into linear operations on approximations. A sum of functions gives a sum of slopes; a scalar multiple, a multiple of the slope.

It is worth warning in advance, however, that linearity ends here. The product of two functions is *not* described by a linear rule—the slope of a product is not the product of the slopes. Why this is so, and by what rule the product is described after all, is the subject of § 4.4.

## Differentiability Implies Continuity

### The Smooth Is Continuous

Chapter 5.3 introduced continuity; the present section connects it with the derivative. The statement is simple: if a function is differentiable at a point, then it is continuous at that point. In `Differentiation.v` this is `deriv_implies_continuous`: from `has_derivative f
x L` follows `continuous_at f x`, where `continuous_at` is the definition of continuity from § 5.3.

In substance the connection is evident. If the increment $f(x+h)-f(x)$ is approximated by the linear $L\cdot h$ with an error of order $o(h)$, then the increment itself is small for a small step: it is no greater than the sum of the linear part $|L|\cdot|h|$ and the small error. Both tend to zero together with $h$—hence $f$ makes no jump at the point $x$.

The proof specifies exactly how to choose $\delta$ for continuity. One takes $\delta$ as the minimum of two quantities: the $\delta$ supplied by the criterion of the derivative for $\varepsilon=1$, and the number $\varepsilon/(|L|+1)$. On such a step the approximation error is smaller than $|h|$, and the linear part is no more than $|L|\cdot|h|$; the sum does not exceed $(|L|+1)\cdot|h|$, which by the choice of $\delta$ is smaller than $\varepsilon$. We will not give the full code—what matters is the idea: the $\delta$ of continuity is assembled from the $\delta$ of the derivative and a correction for the size of the slope.

### Boundedness near a Point

One more technical fact is extracted from continuity, and it will be needed in § 4.4. The lemma `continuous_bounded_near` states: a function continuous at the point $x$ is *bounded* in some punctured neighborhood of $x$—there exist a number $M$ and a radius $\delta>0$ such that $|f(x+h)|\le M$ for $0<|h|<\delta$.

The proof is short: continuity with $\varepsilon=1$ gives a $\delta$ on which $|f(x+h)-f(x)|<1$; then $|f(x+h)|\le|f(x)|+1$, and $|f(x)|+1$ is taken as $M$. By itself the fact is modest, but in § 4.4.2 it will turn out to be essential: in the proof of the product rule the factor $g(x+h)$ will have to be bounded by something, and it is precisely this lemma that bounds it. Its role is named in advance so that the appearance of `continuous_bounded_near` in § 4.4 does not look unexpected.

### The Hierarchy: Smooth $\subset$ Continuous

The summary of the section is one line of hierarchy: differentiability is strictly stronger than continuity. Every differentiable function is continuous—this is `deriv_implies_continuous`. The converse is false. The standard example is the function $|x|$ at zero: it is continuous but not differentiable, since on the left the increment behaves with slope $-1$ and on the right with slope $+1$, and there is no single linear approximation. Over $ℚ$ this example works just as it does over $ℝ$.

We present $|x|$ precisely as standard intuition, not as a separate Rocq theorem: there is no lemma of the form “$|x|$ is not differentiable at zero” in `Differentiation.v`, and it should not be attributed to the repository. The same example shows clearly why the process `deriv_process` of § 4.1.4—with positive steps only—cannot be a self-standing definition of the derivative: for $|x|$ at zero the right difference quotients converge to $1$, and the process `deriv_process` would be a Cauchy process, whereas there is no two-sided derivative. Only the two-sided criterion `has_derivative` gives the full definition. The substantive summary is this: the chapter has climbed one step—from the continuity of § 5.3 to smoothness. From here on, this step carries the rules of differentiation.

## Product and Power

### The Square: A Direct Computation

Before taking on the general product rule, a warm-up is useful—the derivative of the square. The statement: for the function $w\mapsto w\cdot w$ the derivative at the point $x$ equals $2x$. In the code this is `deriv_square`.

The proof is a direct algebraic computation. The error of the linear approximation here is

$$
(x+h)\cdot(x+h) - x\cdot x - 2x\cdot h \;=\; h\cdot h,
$$

that is, exactly $h^2$. It remains to note that $|h\cdot h| =
|h|\cdot|h| < \varepsilon\cdot|h|$ as soon as $|h|<\varepsilon$—for which it suffices to take $\varepsilon$ itself as $\delta$. What matters in substance is this: the approximation error of the square is exactly the quadratic remainder $h^2$, and it is precisely this remainder that goes into $o(h)$. This theme—“nonlinearity gives a quadratic remainder”—will recur in the general product rule.

### The Product Rule

The main nonlinear rule: the derivative of a product. If $f$ has derivative $L_f$ and $g$ has derivative $L_g$, then the function $w\mapsto
f(w)\cdot g(w)$ has the derivative

$$
L_f\cdot g(x) + f(x)\cdot L_g.
$$

In `Differentiation.v` this is `deriv_product`—the longest proof of the file (`SECTION 4`, about one hundred fifty lines). We will not give it in full; let us name the idea.

The idea is an algebraic decomposition of the approximation error into three terms:

$$
\begin{aligned}
&f(x+h) g(x+h) - f(x) g(x) - \bigl(L_f g(x)+f(x) L_g\bigr)h \\[2pt]
&\quad=\;
\underbrace{\bigl(f(x+h)-f(x)-L_f h\bigr) g(x+h)}_{T_1}
\;+\;
\underbrace{L_f h \bigl(g(x+h)-g(x)\bigr)}_{T_2} \\[2pt]
&\quad\phantom{=\;}+\;
\underbrace{f(x) \bigl(g(x+h)-g(x)-L_g h\bigr)}_{T_3}.
\end{aligned}
$$

Each of the three terms is bounded by the quantity $(\varepsilon/3)\cdot|h|$—hence the splitting of $\varepsilon$ into three parts. The term $T_1$ contains the approximation error of $f$ multiplied by $g(x+h)$; to bound it, the factor $g(x+h)$ must be bounded—and here the lemma `continuous_bounded_near` from § 4.3.2, prepared in advance for this purpose, does its work. The term $T_2$ is bounded through the continuity of $g$ (the difference $g(x+h)-g(x)$ is small). The term $T_3$ is bounded through the derivative of $g$ (the error of its approximation is small to the order of $h$). The sum of the three bounds of $(\varepsilon/3)\cdot|h|$ each, together with the triangle inequality, gives what is required.

This is a full theorem, not a grid or approximate version (the Part V safeguard). The rule also has a process form: `deriv_product_process` in `ProcessDerivative.v` states that the process of difference quotients of the product is equivalent to the constant process $L_f g(x)+f(x) L_g$. It is proved, like the process rules of § 4.2.3, through the bridge `deriv_process_converges` and `deriv_product` itself—again a superstructure, not a separate proof.

### The Power Rule by Induction

The power rule grows out of the product rule: for every natural $n$ the derivative of the function $w\mapsto w^{n+1}$ at the point $x$ equals $(n+1)\cdot x^n$. In the code this is `deriv_power_succ`.

The proof is induction on $n$. Base: for $n=0$ we are dealing with the derivative of $w\mapsto w^1$, that is, of the identity, and the rule gives $1\cdot x^0=1$—this is `deriv_id` from § 4.2.2. Step: the power $w^{n+2}$ is written as the product $w\cdot w^{n+1}$, and the product rule is applied to it—the factor $w$ gives slope $1$, the factor $w^{n+1}$ gives slope $(n+1)x^n$ by the induction hypothesis—and algebra reduces the result to $(n+2)\cdot x^{n+1}$.

The power of a rational number is `Qpow`, a recursive function; it was built earlier in the chain of dependencies, in the file `SeriesConvergence.v`, not here. That is, the chapter receives exponentiation ready-made. In substance `deriv_power_succ` is an infinite family of rules, one for each $n$, folded by induction into a single theorem.

### Why the Product Breaks Linearity

It is worth returning to the warning of § 4.2.4. The derivative of a product is *not* the product of the derivatives: the rule gives $L_f g(x) +
f(x) L_g$, not $L_f\cdot L_g$. The product is nonlinear by its very nature, and differentiation inherits this.

This can also be seen algebraically. Multiplying the two linear approximations—$f(x)+L_f h$ and $g(x)+L_g h$—we obtain

$$
f(x)g(x) + \bigl(L_f g(x)+f(x)L_g\bigr)h + L_f L_g h^2.
$$

The part linear in $h$ is exactly $L_f g(x)+f(x)L_g$, the slope from the product rule. And the term $L_f L_g h^2$ is the quadratic remainder, and it is precisely this term that goes into $o(h)$. This is the same theme as in § 4.4.1, where the error of the square turned out to equal $h^2$: whenever a first-order approximation interacts with itself through multiplication, a remainder of order $h^2$ appears, and the definition $o(h)$ is arranged exactly so as to absorb such a remainder.

## Uniqueness and Fermat’s Theorem

### The Derivative Is Unique

The criterion `has_derivative` checks whether a given number $L$ is the derivative. But could several different numbers satisfy the criterion at once? The lemma `deriv_unique` answers: no. If both $L$ and $L'$ are derivatives of $f$ at the point $x$, then $L=L'$ (in the sense of `Qeq`).

The proof is by contradiction. Let $L\ne L'$; then $|L-L'|>0$, and one can take $\varepsilon = |L-L'|/4$. Both criteria—for $L$ and for $L'$—supply their error estimates; adding them and applying the triangle inequality, we obtain for a suitable nonzero $h$

$$
|L-L'|\cdot|h| \;<\; \tfrac{1}{2} |L-L'|\cdot|h|,
$$

which is impossible. Hence $L=L'$. In substance: if a linear approximation of the increment exists at all, there is exactly one—therefore the phrase “the derivative of $f$ at the point $x$” is correct: it names a unique object. The process form of this fact is `deriv_process_unique` in `ProcessDerivative.v`: two constant processes corresponding to two derivatives of one function are equivalent. In terms of the analysis of § 4.1.5, this is the $L1$-correctness of the role “slope”: the derivative is defined unambiguously.

### The Affine Function and the Quadratic Loss

Before Fermat’s theorem come two preparatory derivatives from `SECTION 5` of the file. The derivative of the affine function $w\mapsto
a\cdot w + b$ at any point equals $a$—this is `deriv_affine`; the error of the linear approximation here is identically zero. The derivative of the quadratic loss: for the function $w\mapsto (w-w_\star)^2$ the derivative at the point $x$ equals $2(x-w_\star)$—this is `quadratic_loss_derivative`, a direct computation in the spirit of § 4.4.1.

The quadratic loss is a model objective function: its minimum is attained at $w=w_\star$, and it will be needed in § 4.5.4 as an example for gradient descent.

### Fermat’s Theorem: A Minimum Makes the Derivative Vanish

The main result of the section is Fermat’s theorem. If a function $f$ has a local minimum at the point $x$ and is differentiable at this point, then its derivative there equals zero. In the code this is `local_min_zero_deriv`: from `local_min f x` and `has_derivative f x L` follows $L=0$.

In substance the theorem says the following. At a point of local minimum the linear approximation of the increment cannot have a nonzero slope. Were the slope $L$ positive, a step to the left (negative $h$) would decrease the value; were $L$ negative, a step to the right would decrease the value. Both contradict the fact that at a point of minimum $f(x)\le f(x+h)$ for all small $h$. Hence $L=0$.

The proof examines the sign of $L$. If $L\ne 0$, one takes $\varepsilon=|L|/2$; the criterion of the derivative gives a $\delta$ on which the approximation error is smaller than $\tfrac{|L|}{2}|h|$. Then for a step of the appropriate sign—to the left for $L>0$, to the right for $L<0$—the increment $f(x+h)-f(x)$ turns out to be strictly negative, which contradicts minimality. What remains is $L=0$.

This is a full theorem. As for the axiom audit (the Part V safeguard): at the end of `Differentiation.v` there stands, among others, `Print Assumptions local_min_zero_deriv`—and it is by this output, not by the file header, that the factual axiom status of the theorem is established. The chapter will return to the general caveat in § 4.8.3.

### The Connection with Gradient Descent

The last subsection is a bridge to optimization. The lemma `gradient_step_uses_derivative` connects a step of gradient descent with the derivative of the quadratic loss: the first step is

$$
\texttt{gd\_weight}\;w_0\;w_\star\;\eta\;1
\;=\;
w_0 - \eta\cdot\bigl(2(w_0-w_\star)\bigr).
$$

The right-hand side is “the weight minus the learning rate times the derivative of the loss”: the factor $2(w_0-w_\star)$ is exactly the derivative of the quadratic loss from § 4.5.2.

An honest remark on the status of this lemma (the Part V safeguard: loud names are to be called what they are). `gradient_step_uses_derivative` is not a deep theorem. Its proof is the unfolding of the definitions `gd_weight`, `gd_error`, `contraction` and the identity `ring`. In essence it is a consistency check: the object `gd_weight` introduced in `GradientDescent.v` does implement a “gradient step” in the sense of the derivative of this chapter. A useful stitching of two files—but it has no self-standing content, and it should be called exactly that.

The chapter does not go into the theory of gradient descent itself—the convergence of the weights, the rate, the choice of $\eta$: that is the material of `GradientDescent.v` and, possibly, of a separate future chapter. One thing matters here—the identification of the direction of the step with the derivative of the quadratic loss; with this the bridge is exhausted.

## The Mean Value Theorem: Walk Points

### The Classical Mean Value Theorem and Why It Cannot Be Taken Directly

The classical mean value theorem states: for a function $f$ differentiable on the interval $[a,b]$, there is an interior point $c$ at which

$$
f'(c) \;=\; \frac{f(b)-f(a)}{b-a}.
$$

Division by $b-a$ poses no fundamental difficulty here: since $a<b$, the denominator is nonzero and the quotient is legitimate. What is essential is something else—the very *form* of the theorem: the phrase “there is an interior point $c$.” This is a pure existence statement, and constructively it is weak—the same difficulty as with `argmax` in the extreme value theorem of § 5.3, where an index version had to be taken instead of the point of maximum.

Therefore `MeanValueTheorem.v` proves the *constructive corollaries* of the classical form rather than the form with the point $c$ itself—those estimates of the increment through bounds on the derivative for the sake of which the mean value theorem is usually applied. The move is the same as in § 5.3: in place of an elusive point, a grid construction yielding checkable inequalities.

### Walk Points: A Leibniz-Exact Chain

The grid construction is built on *walk points*—the chain $x,\;x+s,\;(x+s)+s,\;…$ with a fixed step $s$. In `MeanValueTheorem.v` this is a recursive function:

```coq
Fixpoint walk_point (x step : Q) (n : nat) : Q :=
  match n with
  | O => x
  | S n' => walk_point x step n' + step
  end.
```

A question may arise: what is the recursion for, if the $n$-th point is simply $x+n\cdot s$? The reason is an honest detail, and it is named directly in the file header. The telescoping on which the whole proof of § 4.6.4 rests adds up the increments of the function over consecutive points of the chain. For the terms to fit together, the $n$-th point of one expression and the $n$-th point of another must coincide *in the Leibniz sense*—syntactically, as terms—and not merely under the relation `Qeq`. The recursive definition of `walk_point` ensures this coincidence; the closed formula $x+n\cdot s$ does not. The lemma `walk_point_qeq` proves separately that a walk point is `Qeq`-equal to $x+n\cdot s$, and `walk_point_in_interval` that with the step $(b-a)/(N+1)$ all the points stay within the interval $[a,b]$.

Here the file also introduces *uniform differentiability* on an interval—a strengthening of the pointwise criterion:

```coq
Definition udiff_on (f f' : Q -> Q) (a b : Q) : Prop :=
  a < b /\
  forall eps : Q, 0 < eps ->
    exists delta : Q, 0 < delta /\
      forall x h : Q, a <= x -> x <= b ->
        0 < Qabs h -> Qabs h < delta ->
        Qabs (f (x + h) - f x - f' x * h) < eps * Qabs h.
```

The difference from `has_derivative` lies in the order of the quantifiers. In the pointwise criterion each point $x$ has its own $\delta$. In `udiff_on` one and the same $\delta$ serves *for all* points of the interval at once. This is exactly what is needed: to cover all the steps of the grid with one estimate, however many there are. In the terms of § 4.1.5 this is a strengthening of the Rules: uniform differentiability plays the same role as uniform continuity in § 5.3.

### The Archimedean Grid: The Step Can Be Made Arbitrarily Small

For the grid to approximate the interval as precisely as desired, its step must be arbitrarily small. The lemma `walk_step_pos` establishes that the step $(b-a)/(N+1)$ is positive, and `walk_step_small` that for every $\delta>0$ there is a number of subdivisions $N$ for which this step is smaller than $\delta$.

The proof of `walk_step_small` relies on the Archimedean property. In `MeanValueTheorem.v` itself a lemma named `Archimedean_nat` is used; kindred Archimedean lemmas in other files of the chain may be named differently. In substance it is one and the same step of reasoning: to find a finite $N$ at which the rational grid becomes finer than the given $\delta$. The Archimedean property—that very “fuel” of $\varepsilon$-arguments which in § 5.1 already made the scale of processes arbitrarily fine—here allows the grid to be made as dense as desired in a *finite* number of subdivisions. No completed infinity is needed for this.

### The Main Theorem: Bounded Derivative, Bounded Increment

The main theorem of the file is `bounded_deriv_bounded_increment`. If on the interval $[a,b]$ a function is uniformly differentiable and its derivative is bounded in absolute value by the number $M$, then the total increment of the function from $a$ to the end of the grid is estimated as follows:

$$
\bigl|f(\text{walk endpoint}) - f(a)\bigr| \;\le\; (M+\varepsilon)\cdot(b-a),
$$

where any $\varepsilon>0$ may be taken.

The idea of the proof is *telescoping*. The total increment from $a$ to the end of the grid is written as a sum of increments over the individual steps of the walk chain. Each step is estimated by uniform differentiability: the increment on one step is no greater than $(M+\varepsilon/2)$ times the length of the step. Induction on the number of steps $k$ assembles these estimates: after $k$ steps the accumulated increment does not exceed $k\cdot(M+\varepsilon/2)\cdot s$, and for $k$ equal to the full number of subdivisions this gives $(M+\varepsilon)\cdot(b-a)$. The full code is a large induction; what matters here is the scheme: uniformity gives the estimate of one step, the telescope adds up the steps.

Let us name the result honestly (the Part V safeguard). This is a grid *corollary* of the mean value theorem: an estimate of the total increment through an upper bound of the derivative—*not* the classical mean value theorem with a point $c$. The picture is completed by the lemma `walk_endpoint_qeq`: the end of the walk chain with step $(b-a)/(N+1)$ is `Qeq`-equal to the right endpoint $b$; that is, the grid really does traverse the whole interval from $a$ to $b$.

## Corollaries: Monotonicity and Lipschitz

### Zero Derivative: Near-Constancy

The first corollary of the main theorem is the case of a zero derivative. If on the interval $[a,b]$ the derivative of a function is identically zero, then the total increment of the function is arbitrarily small: for every $\varepsilon>0$

$$
\bigl|f(\text{walk endpoint}) - f(a)\bigr| \;\le\; \varepsilon\cdot(b-a).
$$

In the code this is `zero_deriv_near_constant`—a direct corollary of § 4.6.4 with $M=0$.

The formulation is worth reading carefully. The theorem does *not* assert the full form “$f$ is constant on the whole interval.” The current file proves precisely the grid $\varepsilon$-form: the increment between the ends of the walk chain can be made arbitrarily small. The full statement of the equality of all values—say, $f(x)=f(y)$ for any $x,y$ in the interval—is perfectly formulable as a proposition, but it would require a separate theorem and additional bridges; it is not proved here. Under $P4$ the grid $\varepsilon$-form is appropriate and substantive: it says that the difference of $f$ at the ends can be driven below any threshold. This is a grid result—an estimate over the grid of walk points.

### The Sign of the Derivative Sets Monotonicity

The second corollary connects the sign of the derivative with growth and decrease. The lemma `pos_deriv_increases`: if on the interval the derivative is bounded below by a positive number $c$, then the function has grown on the grid—the increment $f(\text{walk endpoint})-f(a)$ is strictly positive. The dual lemma `neg_deriv_decreases`: if the derivative is bounded above by a negative number, the function has decreased.

In substance this is the classical corollary of the mean value theorem—“a positive derivative means growth”—but in grid form and without the point $c$. The proofs repeat the telescope of § 4.6.4, except that the estimate of one step is taken from below rather than from above. These are grid results, like everything in § 4.6–4.7.

### The Lipschitz Property from a Bounded Derivative

The third corollary is the Lipschitz property. The lemma `bounded_deriv_lipschitz_local` gives a local estimate: near a point $|f(x+h)-f(x)| \le (|L|+1)\cdot|h|$—the increment of the function is proportional to the step with a constant coefficient. The lemma `nonneg_deriv_approx_nondec` states that a nonnegative derivative makes the function approximately nondecreasing. The lemma `udiff_continuous_at` closes the connection with § 4.3: uniform differentiability implies continuity at every point of the interval—through `udiff_pointwise` (uniform differentiability gives pointwise differentiability) and `deriv_implies_continuous` from § 4.3.1.

Here it is worth noting how the circle has closed. In § 5.3 the Lipschitz property was introduced *as a condition*—a constructive substitute for uniform continuity, which over $ℚ$ cannot be had for free. Now the Lipschitz property *is derived*—from a bounded derivative. In the analysis of § 4.1.5 this means: the Rules of the derivative yield a rule that in § 5.3 had to be required for continuity. What the chapter on continuity had to require, the chapter on the derivative proves.

### Exact Cases: The Affine and the Quadratic

The section closes with exact cases—functions for which the grid picture and the classical mean value theorem meet. The lemma `affine_udiff` establishes that an affine function is uniformly differentiable on any interval; `quadratic_udiff`, the same for the square. And the lemma `mvt_quadratic_midpoint` gives for the square the *exact* equality of the mean value theorem:

$$
2\cdot\frac{a+b}{2}\cdot(b-a) \;=\; b^2 - a^2.
$$

In substance: for the square, that very “point $c$” of the classical theorem is found explicitly and exactly—it is the midpoint of the interval, $(a+b)/2$. Here the grid picture of § 4.6 and the classical formulation meet at one checkable point.

One honest remark about the file. `MeanValueTheorem.v` ends with the lemma `mvt_quadratic_midpoint`—without the final block of `Check` and `Print Assumptions` that is present, for example, in `Differentiation.v`. This is *not* a sign that the proofs are incomplete: all eighteen lemmas of the file are closed with `Qed`. It is only the absence of a summary axiom audit at the end of the file; such an audit for the theorem one needs is run separately with the command `Print Assumptions`.

## What Has Been Built and What Is Being Prepared. Summary of the Chapter

### The Summary in Three Columns

Let us gather what has been done in infrastructure mode—what has been built, what has not, and what the chapter prepares next.

**Built and checked:**

- the division-free *criterion* of the derivative `has_derivative` and its extensionality lemmas;
- the derivative as a *process* of difference quotients `deriv_process` with the safe nonzero step $h_n=1/(n+1)$; the bridge `deriv_process_converges` between criterion and process; `deriv_process_cauchy`;
- the linearity of differentiation (scalar, opposite, sum, difference)—in criterion form and in process form (`deriv_sum_process`, `deriv_scale_process`);
- differentiability implies continuity;
- the product rule (a full theorem, the $\varepsilon/3$ splitting)—in criterion form and in process form (`deriv_product_process`); the power rule by induction; the uniqueness of the derivative;
- Fermat’s theorem `local_min_zero_deriv`;
- uniform differentiability `udiff_on` and walk points;
- `bounded_deriv_bounded_increment`—a grid corollary of the mean value theorem—and monotonicity together with the Lipschitz property as further corollaries.

**Not built in this chapter:**

- the classical mean value theorem with a point $c$—only grid corollaries are proved, and this is a deliberate choice;
- the derivative of a function on the quotient classes `RealPoint`—the chapter works only with functions $ℚ\toℚ$;
- higher-order derivatives and the Taylor series—beyond the supporting files;
- the chain rule for composition—`Differentiation.v` does not contain it;
- L’Hôpital’s rule—moved outside the chapter; the repository has a separate file for it, but including it would require a section of its own and a separate check, which would overload an already dense chapter.

**Prepares next:**

- the integral—the next analytic layer of Part V;
- gradient descent as an application—the bridge to it is sketched in § 4.5.4; the full theory is contained in `GradientDescent.v`.

### What Would Remain for the Derivative on Classes

The chapter has honestly confined itself to functions $ℚ\toℚ$. Let us name concretely which step is missing for a derivative on the quotient classes `RealPoint`—just as § 5.1 named the missing link for distance on classes.

It would be necessary, first, to prove that the criterion `has_derivative` is well defined with respect to equivalence—that the derivative does not change when a representative of a class is replaced by another, equivalent one. Second, to lift the definition itself from rational functions to functions of quotient classes. Neither is present in the supporting files; this is the honest boundary of the chapter, outlined concretely rather than in general words.

### A Caveat on the Status of Axioms

The Part V safeguard requires precision on the question of axioms. All three supporting files—`Differentiation.v`, `ProcessDerivative.v`, `MeanValueTheorem.v`—declare the status “AXIOMS: none” in their headers (`ProcessDerivative.v`: “0 axioms, 16 Qed”). However, all of them import files through which the classical layer passes: `Differentiation.v` relies on `SeriesConvergence.v` and `GradientDescent.v`, and these on `MonotoneConvergence.v`, which carries the axiom `classic`; `ProcessDerivative.v` relies on `Differentiation.v`. Moreover, `MeanValueTheorem.v` imports `EVT_idx.v`, and in `EVT_idx.v` the axiom `classic` is declared locally (this file was examined in § 5.3). This does not mean that every mean value theorem depends on `classic`—it means only that for a particular theorem one has to look at `Print Assumptions`.

The precise formulation—and precisely not a wholesale one—is this. The imports pass through files with a classical layer, and therefore a file header by itself does *not* replace the command `Print Assumptions` for a particular theorem (a rule adopted as early as Chapter 4.6). One should not assert “the dependencies drag in `classic`” as a blanket verdict on every theorem—the factual axiom status is given only by `Print Assumptions` for that very theorem. At the end of `Differentiation.v` such a check is written out for the key theorems—`deriv_product`, `deriv_power_succ`, `local_min_zero_deriv`, `gradient_step_uses_derivative`—and it is these outputs that give the factual picture. `MeanValueTheorem.v` and `ProcessDerivative.v` have no final block of `Print
Assumptions`; for the theorem one needs, it should be run separately.

For the completeness of the audit, let us also name two honest facts from the depths of the chain, established by a verbatim check of the source files: the lemma `partial_sum_tail` in `SeriesConvergence.v` is left unfinished via `Abort` (with the author’s comment that the direct formulation of the telescope is inconvenient and the Cauchy property is proved differently), and the proof of `mct_inc_least` in `MonotoneConvergence.v` contains `Restart`—the first attempt at the proof is abandoned and replaced by a second. This does not affect the theorems of the present chapter, but in an honest picture of the dependencies such places must be named.

### Summary of the Chapter

The chapter has built the derivative—the layer of analysis above the continuity of § 5.3. The main turn lies in how the concept itself is arranged. The *existence* of the derivative is given without division—by the division-free criterion $o(h)$, which says which number linearly approximates the increment. The *computational* side is the process of difference quotients with a safe nonzero step, and the bridge `deriv_process_converges` links the two sides. The chapter’s main caution: what is proved of the mean value theorem is its grid corollaries, not the classical form with a point $c$.

*Built: the division-free criterion of the derivative and the derivative-process, linked by a bridge; linearity, the product rule, the power rule, uniqueness; Fermat’s theorem; the grid mean value theorem and its corollaries—monotonicity and the Lipschitz property.*

*What it stands on: the $\delta$-$\varepsilon$ apparatus of continuity of § 5.3, the Archimedean property as the fuel of $\varepsilon$-arguments, and the process ontology of $P4$, in which the derivative is a process of approximations of the slope, not a completed limit.*

*Next: the integral as the next analytic layer of Part V; gradient descent as an application of the derivative to optimization.*

---

[^1]: The E/R/R labeling is in the header of the file `ProcessDerivative.v`; here it is unfolded on the pattern of Part I.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/03 Continuity|Chapter 3. Continuity]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/05 Integral|Chapter 5. The Integral]] →
