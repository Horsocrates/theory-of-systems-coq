---
title: "Chapter 1. The Finitization Boundary at the Level of Functions"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/01 Граница финитизации на уровне функций.md"
sourceBlob: 56ea1d38f4cbb46b48c2c569fb507d47a841a319
translated: 2026-10-20
status: draft
---

## Where the Part and the Chapter Stand

Part XV carried one storyline through to the end: *computation is the finitization boundary made algorithmic*. The very line that in Part IV separated the rational from the irrational ran there between the *decidable* and the *undecidable*: an algorithm over finite data either halts—and then it is on the *Element* side—or it does not—and then it is a *role-limit*. But all of this is the boundary at the level of *numbers* and *algorithms over numbers*. The object it divided was a number: a rational number, the length of a run, the code of a program.

This part raises the same line one rung higher—to the level of *functions*. The claim of the part is simple and parallel to the previous one:

> **a function reified as a process is divided by the same Element/role-limit boundary:
> a polynomial (finite support of coefficients) is an Element; a nonpolynomial formal series
> (infinite support) is a role-limit relative to the polynomial layer.**

Transcendental functions are a stronger sublayer of this role-limit side: not every infinite series is transcendental (the geometric $1/(1-x)$ is rational but nonpolynomial). And just as for numbers this boundary was an *arrangement* rather than a defect (the irrational is a number-process that does not reduce to a finite fraction, not a spoiled rational), so here a nonpolynomial series is a process function whose coefficient tail does not break off, not an object that “fell short of a polynomial.”

The chapter lays the foundation of the whole part. It answers three questions. *The first*: why in our system numbers are already processes while functions are not yet, and what this asymmetry consists in (§ 16.1.2). *The second*: how to remove it—how to reify a function as a process (§ 16.1.3). *The third*: where the Element/role-limit boundary runs on functions, and how a polynomial differs from a nonpolynomial series exactly as the rational differs from the irrational (§ 16.1.4). Then come the ladder of objects number $\to$ function $\to$ functional (§ 16.1.5) and the E/R/R analysis with the transition to the calculus of series (§ 16.1.6).

Further on, the part will unfold this foundation: the calculus of process functions (Chapter 16.2), their composition and the *formal heart* of the identity $e^{-\ln(1-x)} = 1/(1-x)$ (Chapter 16.3), the process exponential over a real process argument (Chapter 16.4), and the analytic bridge that closes the functional equation of the logarithm (Chapter 16.5). The part ends with a synthesis of the reification ladder (Chapter 16.6).

## The Ontological Asymmetry: Numbers Are Reified, Functions Are Not

Let us return to what was done with *number*. In Part IV the real number ceased to be a completed point of the line and became a *process*: `RealProcess` is $ℕ \to ℚ$—a sequence of rational approximations, finite at every stage and never completed in the limit. The number *is* this process (more precisely, a class of equivalent processes). The irrational number is not given as an object; it *unfolds* as a mode of being of the finitely actual (P4).

Now let us see what happens with *function* in our construction. Here we discover an asymmetry. All the analysis of the volume quantifies over $f$ as over an *external map*: $f\colon ℚ \to ℚ$ or $f\colon `CauchySeq` \to `CauchySeq`$—a meta-level object, a Rocq function that the theory *uses* but does not *build* as an object-in-the-theory. Continuity, the derivative, the integral—all these are properties attached to an ambient $f$ from outside. The number is reified; the function is not.

This is an *ontological incompleteness*. The system says: “a process is the mode of being of the finitely actual”—and carries this through to the end for numbers. But its own functions do not have this mode of being: they live one storey higher, as meta-maps not reduced to the process ontology. As long as this is so, the claim “everything in our mathematics is a process” remains incomplete: it is true of numbers and false of functions.

And this is the same finitization boundary as in Part IV, only about an *object of another level*. At the level of numbers it distinguished the rational (Element) from the irrational (role-limit). At the level of functions it is natural for it to distinguish the *polynomial* (Element) from the *nonpolynomial series* (role-limit). But for the boundary to be able to *run* through functions, the function must first become an object along which there is something to draw—that is, a process. This is what the next section turns to.

## Reification: The Function as a Coefficient Process

Reification repeats the move of Part IV exactly one rung higher. There a number became the process of its rational approximations. Here *a function becomes the process of its coefficients*.

Let us write an analytic function $f$ as a power series:

$$
f(x) = \sum_{n=0}^{\infty} c_n  x^n .
$$

The function *is* the sequence of its Taylor coefficients $c_0, c_1, c_2, …$—that is, a process $ℕ \to ℚ$ that assigns to each index $n$ its coefficient. This is reification: a formal power series whose carrier is a *coefficient process*.[^1]

```coq
Definition FPS := nat -> Q.
```

The resemblance to the number-process is exact, and it is worth spelling out. `RealProcess` was $ℕ \to ℚ$—the $n$-th stage gave a rational *approximation* to the number. `FPS` is also $ℕ \to ℚ$—but the $n$-th stage gives a rational *coefficient* of the function. In both cases there is a finite rational datum at every stage (P4, the Element side), while the function itself is a potentially unending process of these data. The only difference is *what* indexes the process: for a number, the precision of approximation; for a function, the power of $x$.

In this language the basic functions of analysis are concrete coefficient processes:[^2]

- the geometric function $\dfrac{1}{1-x} = \sum_n x^n$ is the process with constant coefficient $c_n = 1$;
- the exponential $e^x = \sum_n \dfrac{x^n}{n!}$ is the process $c_n = 1/n!$;
- the logarithm $-\ln(1-x) = \sum_{m\ge 1} \dfrac{x^m}{m}$ is the process $c_0 = 0$, $c_m = 1/m$.

Each of them is a *rule* that yields the $n$-th coefficient in a finite number of steps, not a completed object. Already here it is worth noting a difference to which the chapter will return: the geometric $1/(1-x)$ is a *rational* function (its series is infinite, but the function itself is a ratio of polynomials), whereas the exponential and the logarithm are classical *transcendental* functions. All three are nonpolynomial; transcendence is a finer cut *within* the nonpolynomial layer. The function has become what the number became in Part IV: a process.

## The Element/Role-Limit Boundary on Functions

Having reified the function, we obtain an object along which the finitization boundary can run. And it runs exactly where it does for numbers: along whether the process *breaks off*.

A process function is an *Element* if its coefficient process *terminates*: from some index $N$ on, all coefficients are zero. This is exactly a *polynomial*—a finite sum of powers. In our system it is written as follows:

```coq
Definition is_polynomial (f : FPS) : Prop :=
  exists N, forall n, (N <= n)%nat -> f n == 0.
```

A polynomial *terminates* in the same sense in which a rational number and a halting algorithm terminate: after a finite amount of data nothing new arises, and the tail of the process is identically zero. A constant function, the identity, any polynomial—all are on the Element side.[^3]

A process function is a *role-limit* if its coefficient process does *not* terminate: whatever threshold $N$ we take, a nonzero coefficient will be found beyond it. This is exactly a *nonpolynomial* formal series: the coefficient process has no zero tail (transcendence is a stronger property and does not coincide with being nonpolynomial: the geometric function is nonpolynomial but rational). And this status is proved directly: the geometric function and the exponential are *not* polynomials.[^4] All the coefficients of the geometric function equal one; those of the exponential equal $1/n!$, and neither ever vanishes. There is no zero tail—the process does not break off—the function is a role-limit.

It is worth seeing how much this is *the very same* boundary as in Part IV. There a number was an Element if and only if its process of approximations stabilized on a finite fraction (the rational), and a role-limit when the approximations went on without end (the irrational). Here a function is an Element if and only if its process of coefficients stabilizes at zero (the polynomial), and a role-limit when the coefficients go on without end (the nonpolynomial series). *One cut*—whether the process breaks off or not—applied to objects of different levels.

And just as the irrational number was a process rather than a hole (Part IV), so the nonpolynomial function here is a full-fledged process object rather than an unfinished polynomial. That this is a *working* object and not an empty name is visible already now: the defining equation of the geometric function $(1-x)\cdot
\frac{1}{1-x} = 1$ is checked *at the level of coefficients*—the convolution of the processes $(1,-1,0,…)$ and $(1,1,1,…)$ gives $(1,0,0,…)$.[^5]

## The Reification Ladder: Number $\to$ Function $\to$ Functional

What has been done in this chapter takes its place in a common series. The process program of the volume proceeds along a *ladder of objects*, and the Element/role-limit boundary runs through each of its rungs in the same way—along whether the process breaks off or not.

| level of the object | Element (terminates) | role-limit (does not break off) |
|---|---|---|
| number | rational | irrational |
| function | polynomial | nonpolynomial series |
| functional | *(finitary)* | *(general)—horizon* |

The first row is Part IV (and, in algorithmic form, Part XV). The second is this part; and within its role-limit layer the nonpolynomial series are further divided into rational, algebraic, and transcendental—a finer classification to which the part will return. The third is the *horizon*: functionals (maps of functions to numbers or to functions) await their reification just as functions awaited it before this part; in our system this rung has not yet been built, and we honestly hold it as a direction, not as a ready storey.

What matters is that this is *one* boundary rising through the levels, not three different boundaries. The same P4 triad: at every rung the Element side is the finitely actual, computable in a finite number of steps; the role-limit side is a process not reducible to a completed object. The reification of the function is the *ontological completion* of the program at the next rung, not a separate trick: after numbers, functions too become processes.

Honestly about the *status* of this observation. The distinction polynomial / nonpolynomial series is classical, and the series themselves are a classical object. What is new here is the *framing*, not the mathematical content: the function introduced as a process-in-the-theory (rather than as an external map), and the reading of the boundary as the same Element/role-limit cut one rung higher. The level of the result is *synthesis and observation* (as with the finitization boundary itself), not a new theorem. But this framing *works*: on it, as the part will show, the calculus of process functions is built and a concrete inverse-function identity is closed.

## E/R/R Analysis and What the Chapter Prepares

Let us gather the chapter into the E/R/R triad—as it is read in the very carrier of the process function.

| component of the chapter | role in the system | E/R/R layer |
|---|---|---|
| coefficients $c_n \in ℚ$ (finite data at stage $n$) | bearers | Element (P4) |
| `FPS`—the function as a process of coefficients | role-function | Role |
| polynomial $\Leftrightarrow$ tail of coefficients $\equiv 0$ | termination | Rule (Element) |
| nonpolynomial series $\Leftrightarrow$ no such tail | non-termination | Rule (role-limit) |

**Elements.** The coefficients $c_n$ are rational numbers, finitely actual at every stage $n$. This is the Element side: data available in a finite number of steps.

**Roles.** `FPS` plays the role of a *function* reified as a process. The function here is an object-in-the-theory, a rule that yields a coefficient, not an external map. This removes the ontological asymmetry with which the chapter began.

**Rules.** The boundary is set by one rule about the *tail* of the process: if there is a terminating zero tail, the function is an Element (a polynomial); if not, a role-limit (a nonpolynomial series). The same rule about the breaking off of a process that divided numbers in Part IV now works on functions.

**P4 diagnostics.** The function-as-coefficient-process is divided by the finitization boundary exactly as the number-as-process-of-approximations: Element $\Leftrightarrow$ the process terminates, role-limit $\Leftrightarrow$ it does not terminate. This is *the same* boundary raised one level higher in the hierarchy of objects (number $\to$ function). It requires no new axiom: everything built in the chapter has 0 axioms and is machine-checked.[^6]

**What the chapter prepares.** We have a carrier—the function as a coefficient process—and a boundary on it. For reified functions to *live*, this carrier needs operations: addition, multiplication (convolution), the derivative—that is, a *calculus*. Chapter 16.2 builds it: formal power series form a commutative ring on which the derivative and the Leibniz and power rules are defined. And the defining equation of the geometric function that appeared briefly here ($(1-x)\cdot\frac{1}{1-x}=1$ on coefficients) will turn out to be the first example of how the identities of analysis become checkable *process recurrences*.

---

[^1]: `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**): `Definition FPS := nat -> Q`. The reification of a function as the process of its coefficients; the name `FPS` stands for formal power series.
[^2]: Ibid., `src/FormalPowerSeries.v`: `geom_fps := fun _ => 1` (the geometric $1/(1-x)$, all $c_n = 1$); `exp_fps := fun n => / Qfact n` (the exponential, $c_n = 1/n!$); `log1m_fps` ($-\ln(1-x)$, $c_0 = 0$, $c_{k+1} = 1/(k{+}1)$). Machine-checked, 0 axioms.
[^3]: `src/FormalPowerSeries.v`: `fps_one_polynomial` (one is a polynomial), `fps_X_polynomial` (the monomial $x$ is a polynomial). Machine-checked, 0 axioms.
[^4]: Ibid.: `geom_not_polynomial` ($1/(1-x)$ is not a polynomial—all $c_n = 1 \neq 0$) and `exp_fps_not_polynomial` ($e^x$ is not a polynomial—$1/n! \neq 0$ for every $n$). Machine-checked, 0 axioms.
[^5]: `src/FormalPowerSeries.v`: `geom_inverse_fps`—$(1-X)\cdot`geom` = `1`$ on coefficients. Machine-checked, 0 axioms. This is already the calculus of process functions—Chapter 16.2 turns to it.
[^6]: The whole carrier and the boundary of the chapter come from `src/FormalPowerSeries.v` (37 Qed, 0 Admitted, **0 axioms**, `Print Assumptions` = “Closed under the global context” for the key lemmas).

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/07 Synthesis One Diagonal One Discriminant|Chapter 7. Synthesis: One Diagonal, One Discriminant—Part XV]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/02 Calculus of Process Functions|Chapter 2. The Calculus of Process Functions]] →
