---
title: "Chapter 6. The Reification Ladder: Number → Function → Functional"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/06 Лестница реификации число → функция → функционал.md"
sourceBlob: 2e68ff3e44daaede46614f46a0199fd367d34abb
translated: 2026-10-20
status: draft
---

## The Ladder Climbed in Five Chapters

This part has built *one ladder* rather than proved five separate results. Let us gather its rungs into one ascent.

- **16.1.** The function is *reified* as a process—the coefficient process $\texttt{FPS} = ℕ\toℚ$. And the boundary shows through at once: a polynomial has finitely many nonzero coefficients, its tail breaks off (Element); a nonpolynomial series is a coefficient process without a zero tail (role-limit).
- **16.2.** On this carrier, a full calculus: the convolution ring, the derivative, Leibniz, powers.
- **16.3.** Composition and the chain rule give the *formal heart* $E\circ L = \texttt{geom}$, $e^{-\ln(1-x)} = 1/(1-x)$—as the recurrence $c_n = 1$, with 0 axioms.
- **16.4.** The real exponential of a process, $\exp_{ℝ}$: the group homomorphism and injectivity.
- **16.5.** The bridge $\mathrm{eval}$ and Tannery’s theorem close the functional equation $L(x)+L(y) \sim L(x\oplus y)$, $x\oplus y = x+y-xy$.

Each rung rests on the previous one; together they form a single ascent from the reification of the function to a genuine functional equation over number-processes. A caveat about the word: in this part “function” means above all a function reified as a formal power series (a coefficient process); a general function in Bishop’s sense—approximations with a modulus of continuity—is outlined below as a horizon.

| chapter | rung | tier |
|---|---|---|
| 16.1 | function $=$ coefficient process; boundary finite/infinite support | 0 axioms |
| 16.2 | calculus of process functions (convolution ring, derivative) | 0 axioms |
| 16.3 | composition $+$ formal heart $E\circ L$ | 0 axioms |
| 16.4 | real $\exp_{ℝ}$ (Mertens, homomorphism, injectivity) | only L3 |
| 16.5 | bridge $\mathrm{eval}$ $+$ Tannery $\to$ closure of the $\ln$-equation | only L3 |
| 16.6 | ladder number $\to$ function $\to$ functional (synthesis) | observation |

## One Boundary, Raised by a Rung

The organizing boundary of the whole Volume is Element / role-limit, the boundary of *finitization*. At the level of *numbers* (Parts IV–V) it reads as follows: the rational is a process that reduces to finite data (it stabilizes in a finite description); the irrational is a process that genuinely does *not* close. This is the frontier between Element (reduces to finite actuality) and role-limit (a process that does not close).

Part XVI shows: *the same boundary*, one rung higher. Among functions the Element is the *polynomial*: finitely many nonzero coefficients, the coefficient process terminates (tail $\equiv 0$); the role-limit relative to the polynomial layer is the *nonpolynomial* series: a coefficient process without a zero tail. Transcendental functions are a finer sublayer of this infinite side (the geometric $1/(1-x)$ is already nonpolynomial but *rational*, not transcendental), and they do not coincide with it. The witnesses are explicit and *0-axiom*: neither the geometric function nor the exponential is a polynomial, and the predicate “to be a polynomial” catches exactly the breaking-off tail.[^1]

The level of this is—honestly—*synthesis and observation*, *not a new theorem*: the same status as thesis H1, raised by a rung. The value is ontological: the finitization boundary is a *structural feature* of mathematics-as-process, recurring at every level of the hierarchy of objects, not a fact about numbers.

## Why Reification Removes Walls

A methodological reading. Twice in this part a “wall” turned out to be a rung.

*The formal heart $E\circ L$* (16.3): the obstruction was an *object that had not been built*—a function taken as a ready thing rather than as a process—not a theorem that could not be proved. Reified as a coefficient process, the identity $e^{-\ln(1-x)} = 1/(1-x)$ became the simple recurrence $c_n = 1$, with 0 axioms.

*The horizon of $\ln$-multiplication* (16.5) closed exactly when the exponential became a real *operator* on processes and $\mathrm{eval}$ carried the formal identity over to the other side.

The law here is P4 (Finite Actuality): a process is *potential*, it is never a completed whole. A “wall” between objects is often a category mistake: a process taken for a closed object. Reify the object as a process—and the wall becomes a step. That is why the program advances by *reification*, not by force.

## The Third Rung: The Functional

The ladder has a visible next rung. A *functional* is a map that takes a function and returns a number. We have already built one: $\mathrm{eval}$ (16.5) takes a function—a coefficient process—and a point, and returns a number—a Cauchy process. Hence $\mathrm{eval}$ is the *first functional* of the ladder

$$
\text{number} \;\to\; \text{function} \;\to\; \text{functional},
$$

where each rung reifies the next object as a process (or as a process-respecting map). *Number*: a real is a process $ℕ\toℚ$. *Function*: a function is a coefficient process. *Functional*: $\mathrm{eval}$ is a map functions $\to$ numbers, consistent with the process structure.

The general rung is a *horizon*, mathematically: the next step of the hierarchy, and nothing more. A general theory of functionals-as-processes; the *Bishop* form of an arbitrary function (a sequence of approximations with a modulus of continuity) as a process form beyond the analytic / FPS case; a calculus of such functionals. They are named here as the next ascent of the system—not as something done.

## The Part as One System; Its Place in the Volume

| component of the Part | role in the system | E/R/R layer |
|---|---|---|
| coefficients, partial sums, finite blocks (stage $n$) | bearers, finite | Element (P4) |
| function-as-process (FPS) | reified object | Role |
| $\exp_{ℝ}$ (operator), $\mathrm{eval}$ (bridge functional) | carry the structure across | Role / Rule |
| boundary finite/infinite support | witness diagnostics | Rule, 0 ax |
| Mertens, Tannery | analytic rules of transfer | Rule, L3 |

**The tier of the whole Part, honestly.** Chapters 16.1–16.3 (function-as-process, the calculus, the formal heart) have *0 axioms*. Chapters 16.4–16.5 (the real $\exp_{ℝ}$, the bridge $\mathrm{eval}$, the closure of the equation) use *only L3* (the Law of Excluded Middle), and with axiom-free analytic cores. No other axioms—neither choice nor functional extensionality.[^2]

**Place in the Volume.** Part XV studied computation and the finitization boundary; Part XVI is this same boundary *one rung higher*, among functions. The thread to H1 and to the general thesis of the Volume: the Element / role-limit boundary is the *backbone* of process mathematics, not a local observation about one class of objects. Next, Part XVII turns to the discrete—as the next synthesis after the functional layer.

**Conclusion.** The reification program now has two rungs climbed—*number* (IV–V) and *function* (XVI)—and a third in view. This is the ontological backbone of the whole enterprise: mathematics done as processes, where the former walls between completed objects show through as *rungs* of a single ladder—and the next step arises where the next object is reified as a process.

---

[^1]: `src/FormalPowerSeries.v`: `geom_not_polynomial`, `exp_fps_not_polynomial` (direct witnesses of the role-limit), `is_polynomial` (breaking-off tail $=$ Element)—all “Closed under the global context,” 0 axioms. Machine-checked.
[^2]: In summary, machine-checked across Chapters 16.1–16.5: the 0-axiom formal layer (`FormalPowerSeries.v`) and the L3 analytic layer (`exp_R`, `eval`, `ln_mul_closed`)—`Print Assumptions` gives either “Closed under the global context” or exactly `Classical_Prop.classic`.

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/05 Analytic Bridge Eval and Tannery Theorem Closing the Logarithm Equation|Chapter 5. The Analytic Bridge eval and Tannery’s Theorem: Closing the Logarithm Equation]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/01 Combinatorics Process Counting|Chapter 1. Combinatorics: Process Counting—Part XVII]] →
