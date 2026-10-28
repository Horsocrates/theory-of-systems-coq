---
title: "Chapter 2. Finitization without Cutoff"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/20 Заключительный синтез/02 Финитизация без обрезания.md"
sourceBlob: 8cfdb3478215136c4ddedd29a9f8752cd6cc48f5
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The previous chapter closed one line: in each instance analyzed, the rule of generation either *presents* a finite terminus—a finitely actual Element—or we *prove the impossibility* of such a terminus, and then the “value” remains a role-limit, which the process approaches but no finite stage fills with an Element (we do not presuppose a universal decider of termination for all processes). This dividing line we called the finitization boundary.

There remains, however, one tempting reading, and the present chapter exists to remove it. The stance of P4—“there is no completed infinity; only finite stages are actual”—is easily heard as a statement about the *substrate*: as if there existed a smallest grain, a finite resolution, a limiting precision beyond which there is nothing. As if finitization *cut the world off* from below. This reading is wrong, and its wrongness is provable.

*Finite actuality is not a finite substrate.* P4 requires that every *actualized stage* of a process be finite; it introduces neither a smallest grain nor an upper bound on resolution. The role-limit is an *unbounded* process, not a cutoff.

The difference between these two stances—“a finite stage” and “a finite substrate”—is not a philosophical nuance. It is drawn exactly, and it is drawn by number. The role-limit side is approached by rational Elements with an error that has *no positive bottom*: whatever bound of precision one names, there is a more precise stage. A theory with a *fixed* resolution—with a cutoff—has such a bottom and is therefore distinguishable from an unbounded process. It is this distinguishability that the chapter analyzes.

## What the Chapter Establishes and What It Does Not

Honesty is again needed from the very start. What is proved here is the *numerical core* and the *dichotomy*: for every role-limit of the form $\sqrt D$ (where $D$ is not a perfect square), the error of a rational approximation is bounded below by $1/q^2$, where $q$ is the denominator of the approximation; a theory of bounded resolution $q\le Q$ gets stuck on the uniform bottom $1/Q^2$, whereas the unbounded process *beats* this bottom—descends below any $1/Q^2$. The lower bound for a fixed denominator is a finite integer fact; and “beating any fixed floor” uses the *unbounded Pell process* (the infinite family of solutions of $p^2-Dq^2=\pm1$). Both are machine-checked without additional axioms[^1].

What is *not* asserted is a new physical prediction. On the contrary: for quantities representable by such role-limits, rational approximations can be made arbitrarily precise, so that observationally the ℚ-view coincides with the usual continuum description. The contribution of the chapter is not a theory competing with the familiar one but an *exact demarcation*: the separation of “finite actuality” (our stance) from “a finite substrate” (the stance of programs that cut the world off from below), and a proof that the second—but not the first—yields a fixed deviation, falsifiable in principle[^2].

## The Granular Floor

Take the role-limit $\sqrt D$ for a natural $D>0$ that is *not* a perfect square (a non-terminating process)[^3]. Its approximations are rational numbers $p/q$ (with denominator $q\ge 1$), and each of them is a finitely actual Element. Let us ask about the *square error*: how far $(p/q)^2$ lies from $D$.

It is convenient to measure this error by an integer. Let

$$
g(p,q)\;=\;q^2 D - p^2 \;\in\; ℤ.
$$

This is an *integer*—a combination of integers from the integer coordinates of the approximation. And here termination is at work: *$g(p,q)$ never becomes zero*. For $g=0$ would mean $q^2 D = p^2$, that is, $(p/q)^2 = D$—and that is precisely the rational value of the process $\sqrt D$, its termination in an Element. For a non-square $D$ there is no such termination; hence $g(p,q)\neq 0$[^4]. And a nonzero integer is at least one in absolute value:

$$
|g(p,q)| \;=\; |q^2 D - p^2| \;\ge\; 1.
$$

*This is the granular floor.* The square error[^5] $\bigl|D - (p/q)^2\bigr| = |g(p,q)|/q^2$ cannot be less than $1/q^2$: between a rational square and the non-square $D$ there always lies an integer “gap” at least one wide.

It is essential that this floor is neither a postulate nor an additional assumption about the grain of the world. It is a *consequence of the non-termination* of $\sqrt D$: precisely because the process does not close into an Element, the integer gap $g$ does not become zero. The number that in the previous chapter locked rotations and symmetries here locks precision: it does not let the square of a rational approximation coincide with $D$, and the gap does not collapse at any stage.

## Bounded Resolution versus the Unbounded Process

The floor $1/q^2$ depends on the denominator $q$—on the “resolution” of the approximation. Here lies the whole difference between a cutoff and a process.

**Bounded resolution.** Let a theory admit only denominators $q\le Q$—a finite grain is imposed, an upper bound on precision. Then $q\le Q$ implies $1/q^2 \ge 1/Q^2$, and therefore *every* approximation of the theory has the error

$$
\bigl|D - (p/q)^2\bigr| \;\ge\; 1/q^2 \;\ge\; 1/Q^2.
$$

The deviation from the role-limit does not go below the fixed quantity $1/Q^2$, and no admissible approximation defeats this quantity[^6]. A cutoff leaves a *non-collapsing* gap—a fixed bottom.

**The unbounded process.** Our role-limit side introduces no grain: the denominator is a quantity of the process, bounded above by nothing. And then the bottom *is beaten*—this is ensured by the *Pell process*: for a positive non-square $D$ the equation $p^2-Dq^2=1$ has solutions with arbitrarily large $q$, for which the integer gap is minimal, $|g(p,q)|=1$, and hence the error is exactly $1/q^2 < 1/Q^2$[^7]. The process descends below any bottom given in advance.

*Bounded resolution gets stuck above the floor $1/Q^2$; the unbounded process beats this floor and drives the error toward zero, without reaching zero at any stage.* The first is a cutoff; the second is a role-limit.

This clarifies the ontological status of the role-limit. It is approached by rational Elements *arbitrarily precisely*—the error has no positive bottom—but it is *not reached* at any stage, for the integer gap is never zero. This is the non-terminating process in exact form: improvable everywhere, completed nowhere. The finite actuality of each stage (a rational approximation) gets along perfectly well with the absence of a smallest grain.

## Finitization Is Not a Cutoff

Now let us assemble the verdict. Two stances that are easy to confuse are separated once and for all by the numerical dichotomy.

*Finite actuality* (P4) requires that every actualized stage of a process be a finite rational Element. *A finite substrate* is a stance of another kind: a smallest grain, bounded resolution $q\le Q$, a cutoff of the world from below. The previous section showed that these are not the same: the unbounded process (P4) beats any floor, whereas a finite substrate holds a non-collapsing gap $1/Q^2$. P4 gives the first and does not imply the second.

*From “amplitudes are processes” it does not follow that “the substrate is granular.” To obtain a cutoff, a separate assumption about a smallest grain is needed—an assumption that P4 does not make.*

Hence an honest summary for the application to physics[^8]. Programs that cut the world off from below with a finite resolution—models introducing a finite rational resolution (a maximal denominator $q\le Q$)—by their very stance predict a fixed deviation from the continuum description: the floor $1/Q^2$, which experiment, descending to smaller gaps, refutes in principle[^9]. The ℚ-view predicts *zero* such deviation: its error beats any floor. For quantities representable by such role-limits, it coincides with the continuum description.

Therefore the contribution here is not a prediction but a *demarcation*. The ℚ-ontology of process is empirically indistinguishable from ordinary mechanics; it differs from the programs that introduce a finite substrate—and this distinguishability is provable: they predict a non-collapsing floor, and it does not. Non-termination as the openness of a process (the future is not predetermined, the digit has not yet been issued) is, on our side, compatible with the ordinary predictions[^10]; a finite substrate is not.

## E/R/R Analysis: The Floor as a System

The granular floor is itself a *system* in the sense of ToS, and it should be analyzed by E/R/R. Epistemically we went from the observed approximations (Elements) to their numerical law (Rules); ontologically the structure is generated in the reverse, generating order: Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *criterion of termination of the root*: the integer gap $g(p,q)=q^2D-p^2$ becomes zero if and only if $\sqrt D$ terminates in an Element, that is, when $D$ is a perfect square. For a role-limit the gap is not zero, whence $|g|\ge 1$—the floor. The second layer of the rule is sorting by *resolution*: whether it is bounded ($q\le Q$) or not. These two rules stand above the approximations themselves and set their status.

**Roles (L4).** Two roles played by a configuration of approximation: the *configuration of bounded resolution* (an Element stuck above the floor $1/Q^2$—the cutoff side) and the *unbounded process* (a role-limit that beats every floor). The positions are grounded by structure: the role is defined not by the “nature” of the number but by whether the resolution is bounded by a rule—that is, by its relation to the Rules.

**Elements (L1 + P4).** The bearers are the integer gap $g(p,q)$ and the rational approximations $p/q$ that the process gives at each finite stage. Actualization under P4 is finite: only the stages and their integer gaps are actual; $\sqrt D$ itself as a completed limit is *not* actualized as an Element—only the approximations are actual. That is exactly why the error has no positive bottom, yet does not reach zero either.

**Well-formedness check.** Once the mode of resolution is fixed, each configuration is classified unambiguously (the resolution is bounded or not); no component is assigned to two at once. There is no self-application, which P1 rules out: the rule about resolution stands one level above the approximations it sorts and does not sort itself as an approximation.

**What the analysis yields.** First, it shows that “is there a smallest grain?” and “is the world cut off from below?” are the same confusion of categories as “is $\sqrt2$ a completed number”: they demand that an unbounded process be a bounded substrate-object. Second, it names the source of the demarcation: the floor is positive precisely because the root does not terminate—that is, granular deviation is a theorem about numbers, and it is precisely its absence that distinguishes the unbounded process from a finite substrate.

Thus the role-limit side, outlined in the previous chapter, receives an exact form here: it is an *unbounded* process, not a cutoff. The finite actuality of a stage and the finiteness of the substrate are different stances, and number separates them; from here on the present work uses this distinction as ready, separating process non-termination from any assumption about a smallest grain.

---

[^1]: The statements of the chapter are checked as “Closed under the global context” (without the Law of Excluded Middle and without additional witness axioms). The Pell part, `tos_beats_granular`, relies on the infinite sequence of Pell solutions and does not follow from `nonsquare_gap_nonzero` alone.
[^2]: The substantive illustration lies in the application to physics—in finite-precision readings of quantum mechanics; here they serve as an image of a single numerical form, not as the subject of the present volume. See § “Finitization Is Not a Cutoff.”
[^3]: “$\sqrt D$ is a role-limit $\Leftrightarrow$ $D$ is not a perfect square” is proved in general form: a rational value of the square root would force $D$ to be a perfect square. This is `rational_square_is_perfect`; for each individual $D$ the impossibility of a rational value is `not_perfect_square_irrational`.
[^4]: This statement—`nonsquare_gap_nonzero`—reduces “the impossibility of an exact hit” to a theorem about the root: the termination of $\sqrt D$ is exactly “$D$ is a perfect square.” The physical consequence, as we will see, turns out to be this theorem about numbers.
[^5]: The floor is formulated for the *square* error $|D-r^2|$; for the error of the value itself, $|\sqrt D-r|$, a related estimate is obtained by dividing by $\sqrt D+r$.
[^6]: The uniform lower bound for all configurations of resolution $q\le Q$ is `granular_deviation`; on the integer scale it is $q^2 \le Q^2 |q^2 D - p^2|$.
[^7]: The existence of such approximations with arbitrarily large denominator is a property of the process going back to Pell’s equation: the integer gap takes the value $1$ at infinitely many stages, while the denominator grows without bound. The corresponding statement is `tos_beats_granular`.
[^8]: This section is an application to physics; it illustrates the numerical form on finite-precision readings of quantum mechanics and is not part of the subject of the present volume.
[^9]: As a *numerical illustration* (not a physical Bell model): the correlation optimum is the role-limit $\sqrt8=2\sqrt2$; the rational approximation $14/5$ to it has the square error $8-(14/5)^2=4/25$. Any model that fixes a maximal denominator $Q$ leaves a similar nonzero floor; the unbounded process has no such floor. Likewise “a ceiling on the number of qubits”: a finite rational resolution gives an upper bound on the complexity of an exactly representable state, whereas the denominator $2^{m}$ of the process is unbounded.
[^10]: This is the same side that the previous chapter called constructive non-termination: the process $\sqrt D$ has an exact nonzero error at every stage and does not reach a terminus—all without axioms. “The finite precision of a stage” and “a finite substrate” diverge precisely here.

---

Part: [[20 Final Synthesis|Part XX. The Final Synthesis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/20 Final Synthesis/01 Finitization Boundary|Chapter 1. The Finitization Boundary]] · [[Library/Branches/Mathematics/Volume/20 Final Synthesis/03 Reduction Atlas|Chapter 3. The Reduction Atlas]] →
