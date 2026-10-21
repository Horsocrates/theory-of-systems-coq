---
title: "Chapter 1. Metric on Processes"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/01 Метрика на процессах.md"
sourceBlob: 3880e5ba624de6fa068ff303592ba8f235cb73cf
translated: 2026-10-20
status: draft
---

## What Part V Needs a Metric For

### What Lies Behind and What Lies Ahead

Part IV built the process mathematics of the real number. Infinity became a process, a number became a process of approximations, and a point became a class of equivalent processes; uncountability was proved, the process continuum was outlined, and the whole corpus was honestly measured for inferential strength. By the end of Part IV we held the *material*: rational processes, the equivalence relation, and the Cauchy apparatus.

Part V takes this material and sets about *analysis*. Its task is to unfold on a process basis what in classical mathematics makes up the edifice of mathematical analysis: topology, metric, continuity, the derivative, and the integral. The seven chapters of Part V will travel this path in order—from the local to the global, from a single point to integration over a domain.

And the first step on this path is *distance*. Without the notion of distance nothing further can be built: neither topology (what does it mean for processes to be “close”?), nor convergence (what does it mean for a process to “approach” something?), nor continuity (what does it mean that a small displacement of the argument gives a small displacement of the value?). The metric is the foundation, and that is why Part V opens with a chapter on it.

### How to Read This Part: Three Caveats

Before building, we must agree on *how* Part V speaks of what has been done, because there is a danger here, and it is more honest to name it at once.

The temptation, when unfolding analysis, would be to declare that “classical analysis has been fully restored on a process basis.” Part V declines this temptation. It is more accurate to put it otherwise: the ToS Rocq repository contains a *grid-process infrastructure* of analysis—a working framework of rational metrics, interval methods, finite sums, modulus estimates, and Cauchy representatives. Part V shows how this framework *gradually* restores classical analysis, and for each result it honestly marks its status. Hence three caveats that hold throughout.

The first concerns what *“process analysis”* means. It is infrastructure, not a ready edifice: a set of constructions in which analytic notions receive a process form. Some results in it are already proved as full theorems; others exist so far as $\varepsilon$-versions, grid approximations, or constructions that work up to a finite horizon; still others are sketched as a direction. Part V *distinguishes* these statuses and does not pass one off as another.

The second concerns the words *“without the Axiom of Choice.”* They will recur, and they mean a precise thing: without an *external* set-theoretic axiom of choice and without choice from completed infinite families. They do *not* mean that every file of the repository is fully constructive: some of the results rely on the laws of logic of ToS—$L3$ and, locally, $L4$. The status of each result in this respect is stated in place. (For the present chapter, however, the caveat works in the strong direction: all its supporting files are free of axioms altogether; more on this below.)

The third concerns *local status marking*. Whenever the chapter says “proved,” it specifies *what* exactly is proved: a full theorem, or an $\varepsilon$-approximation, or a notion introduced by definition, or a direction of further work. This is the same discipline of honesty as in Chapter 4.6, now carried over to every step of analysis.

### The Third Layer of the Exposition

One more word about genre. Parts I–IV kept to two layers: formal construction and ontological interpretation. Part V adds a *third*, the *computational* one. Where appropriate, the chapter will give concrete examples of computation: tables, runs, numbers. The goal is simple: the reader should *see* that process analysis is a working practice, not a detached abstraction. In the present chapter the third layer will appear in § 1.7, where the Archimedean property turns from a philosophical motif into a concrete table: how many steps suffice to reach a given precision.

### The Plan of the Chapter

The chapter moves from the simple to the composite. First comes the distance between rational numbers, the simplest case (§ 1.2). Then the abstract metric space as a general frame (§ 1.3). Then the central turn: the *pointwise* distance between processes is naturally itself a process—a process of rational discrepancies; and here we will have to separate it carefully from another construction of the repository, the *finite-horizon* distance `process_dist`, which measures the discrepancy up to a chosen horizon (§ 1.4). Next come the general scheme of processes and the bridges between their types (§ 1.5). A separate section, the most cautious one, concerns *completeness*: why it is a *notion* here rather than a proved theorem (§ 1.6). Then the Archimedean property as the “fuel” of $\varepsilon$-reasoning, with a computational example (§ 1.7). And finally the summary: what is built, what is not, and what is being prepared next (§ 1.8).

There are seven supporting files, and all of them have been checked against the repository verbatim. Let us note something important at once: by their headers and their verified key theorems, all seven have the status “0 axioms”—not a single axiom. For the first chapter of Part V this is a fortunate beginning: the foundation of analysis is laid on a fully constructive basis. (§ 1.7 will additionally draw on one more file, on the Archimedean property; its status will be discussed separately there.)

## Distance between Rational Numbers

### The Simplest Case

It is worth beginning with the simplest distance there is in ToS: the distance between two *rational* numbers. Every rational number is finite *as written*: a fraction $p/q$ is given by finite integer data—a pair of integers (Part III)—and it contains neither process, nor approximation, nor infinity. (The type $ℚ$ as such is, of course, infinite—but we are speaking of each individual object in it.) We define the distance between two such numbers just as simply and completely, as the *absolute value of their difference*: the distance between rationals $x$ and $y$ is $|x-y|$. No infinity is involved here: subtracting rationals and taking the absolute value are finite operations, and the result is again rational. In Rocq this is written in the file `MetricSpace.v`:

```coq
Definition Q_dist (x y : Q) : Q := Qabs (x - y).
```

{
Let us note one peculiarity of the repository at once: the same definition occurs in it under several names. In `ProcessTopMetric.v` it is called `qdist`; in `ProcessGeneral.v`, `Qdist`. All three—`Q_dist`, `qdist`, `Qdist`—are one construction: $|x-y|$ for rational $x,y$. This is one notion in three files, not three different notions. From here on the chapter will use the working name `qdist`; the reader need only remember that behind all three names stands one and the same absolute value of a difference.
}

| Name | File | Role |
|---|---|---|
| `Q_dist` | `MetricSpace.v` | the metric in the `stdlib` frame |
| `qdist` | `ProcessTopMetric.v` | the process-topological metric |
| `Qdist` | `ProcessGeneral.v` | the distance in the general scheme of processes |

All three are defined identically—`Qabs (x - y)`—and differ only in the file in which, and the purpose for which, they are introduced.

### The Four Axioms of a Metric

For $|x-y|$ to deserve the name of *distance*, it must satisfy four properties that since Fréchet have made up the definition of a metric. And for the rational distance we do not *postulate* these four properties; we *prove* them, each by direct rational arithmetic. In `MetricSpace.v` four lemmas correspond to them.

*Non-negativity*: $|x-y| \geq 0$ for any $x,y$—distance is never negative (lemma `Q_dist_nonneg`).

*Zero on the diagonal*: $|x-x| = 0$—the distance from a number to itself is zero (`Q_dist_zero`).

*Symmetry*: $|x-y| = |y-x|$—the distance from $x$ to $y$ and from $y$ to $x$ is the same (`Q_dist_sym`).

*The triangle inequality*: $|x-z| \leq |x-y| + |y-z|$—the direct path is no longer than the path through an intermediate point (`Q_dist_triangle`).

The proofs are simple: all four rest on properties of the absolute value of a rational number (`Qabs`)—the absolute value is non-negative, the absolute value of zero is zero, the absolute value does not depend on the sign, and the absolute value of a sum does not exceed the sum of the absolute values. All four properties are obtained by purely rational arithmetic, without any appeal to infinite objects.

Let us note what is *not* in this list. The property of zero on the diagonal is *diagonal*: it says only $|x-x| = 0$. Strict separation—$|x-y| = 0 \Rightarrow x = y$, zero distance only between coinciding numbers—does not stand among these four properties as a separate lemma. For the rational metric it is, of course, true; and it is proved, but *separately*: the lemma `qdist_zero_iff` in `ProcessTopMetric.v` establishes that $|x-y| = 0$ if and only if $x = y$. The chapter will return to this distinction—between zero on the diagonal and strict separation—in § 1.3, where it will prove essential for the abstract frame.

### Distance Is Positive by Its Nature

It is worth dwelling on the first of the four properties, non-negativity. In ToS it manifests a recurring motif of the whole volume and is no accidental technical detail: distance is *structurally positive*. The absolute value of a rational number is non-negative because the absolute value *is* an operation that discards the sign by construction; convenience of postulation plays no part here. A “negative distance” does not occur because of how distance is arranged, and nothing needs to rule it out: from the very start it is a quantity without a sign.

This agrees with the general positive ontology of ToS. Distances, norms, lengths, volumes—all measures of separatedness and extension—are non-negative structurally, not by convention. The chapter will meet this motif more than once: it will return when we come to the integral of a non-negative function. The metric is its first example in Part V; in the E/R/R analysis (§ 1.3.2) non-negativity will turn out to be one of the *rules* (Rules) that sustain distance.

### The Level of Rational Numbers

And the last remark of this section—an important one, because it sets the tone for the whole chapter. Everything built in § 1.2—`qdist` and its four properties—works at the level of *rational numbers*. This is the distance between two $ℚ$-numbers, not between processes and not between classes of processes.

Levels will have to be distinguished constantly, and the chapter draws the boundary from the very beginning. Distance on $ℚ$—completed, rational, simple—is the *foundation*. But the object of interest for analysis is a *process*, not a rational number; and the distance between processes is arranged in a more complex way than $|x-y|$. The chapter will move on to it in § 1.4, after first building the general frame, the abstract metric space.

## The Abstract Metric Space

### The Metric Space as a System

Distance on $ℚ$ is a particular case. To speak of distance in general—between processes, between vectors, between anything at all—we need a general frame: the notion of a *metric space* as such.

At once, one caveat about precision. The abstract frame that we are about to build fixes metric structure *without* a general axiom of separation ($d(x,y)=0 \Rightarrow x=y$); strictly speaking, it would be more honest to call it *metric-like*, or pseudometric. For the rational metric, separation holds and is proved separately (§ 1.3.4); the frame, for its part, takes exactly those hypotheses that are needed for general reasoning. The chapter uses the familiar words “metric space”—this is also the name of the Rocq section itself—but let the strict reader keep this caveat in view from the very beginning.

In ToS terms a metric space is a system with a characteristic set of roles and rules. The elements are the points of the space. The role is distance, the measure of separatedness of two points. The rules are those very four axioms: non-negativity, zero on the diagonal, symmetry, and the triangle inequality; among them the triangle plays the role of the constitution that binds the space into a whole.

We formalize this frame *parametrically*, so that everything proved in it holds at once for every concrete metric space. The means is the Rocq mechanism `Section`: inside the section one fixes a *carrier* (an arbitrary type), a *distance function*, and four *hypotheses* about it, and everything proved inside is automatically true for any carrier and any function that satisfies these hypotheses. In `MetricSpace.v` this is written as follows:

```coq
Section MetricSpaces.

Variable X : Type.
Variable d : X -> X -> Q.

Hypothesis d_nonneg : forall x y, 0 <= d x y.
Hypothesis d_zero : forall x, d x x == 0.
Hypothesis d_sym : forall x y, d x y == d y x.
Hypothesis d_triangle : forall x y z, d x z <= d x y + d y z.
```

$X$ is an arbitrary carrier, $d$ is the distance function, and the four `Hypothesis` entries are the properties that $d$ is obliged to satisfy. Everything proved inside the section is proved *for any* such $X$ and $d$. This is the general theory: one frame, fit for every concrete metric space.

Let us note the methodological choice. Rocq would also allow this frame to be set up through type classes; the ToS formalization deliberately takes a `Section` with explicit parameters. The reason is that explicit parametricity makes dependencies *visible*: looking at a lemma from the section, one sees at once exactly which hypotheses about $d$ it depends on—nothing is hidden in implicit class inference.

### E/R/R Analysis: The Metric as a System

Since a metric space is a *system*, the E/R/R methodology unfolded in Part I applies to it: every system can be analyzed into three aspects—Elements, Roles, Rules. Let us carry out this analysis. It imposes nothing on the space from outside; it *unfolds* the same labeling that already stands in the header of the supporting file: *elements—points; role—distance as a measure of separatedness; rules—the triangle inequality (as constitution), symmetry, positivity*.[^1] We will conduct the analysis in the *ontological* order—Rules $\to$ Roles $\to$ Elements—although cognitively we traveled the reverse path: first we saw points, then the distance between them, and only then the axioms to which it is subject.

The caveat about status is the same as in the analysis of the `Distinction` record in Part I. In calling a metric space a *system*, we carry out a *substantive* ontological interpretation; in the code it is a parametric `Section` with a carrier and four hypotheses, not an object of type `System` $L$ with an assigned level of the hierarchy. The analysis *reads* the structure; it does not ascribe new formal content to the file.

*Rules—those that hold the space together* (the law $L5$: rules stand above what they organize). Two layers work here. The *universal* one: the laws $L1$–$L5$, common to every system. The *concrete* one: the four axioms of a metric, specific to distance—non-negativity, zero on the diagonal, symmetry, and, above all, the triangle inequality, which plays the role of the *constitution* that binds the space into a connected whole (without it the separate distances would not add up to a single measure). Here too runs the honest boundary noted in § 1.3.4: the abstract `Section` does *not* take strict separation as a general hypothesis and therefore fixes a structure slightly weaker than a full metric. The arrangement of the rules also shows how the positions are filled: the carrier is *given* as a parameter, and the points are not *selected* by an algorithm—the `Section` sets the *potential* (carrier, distance, hypotheses), while concrete spaces—$ℚ$ with `qdist` or the vectors `QVec` with the $L^\infty$ distance—*actualize* it.

*Roles—the significance of positions* (the law $L4$: every role is structurally grounded). There is one role in this system, and it is central: the *distance* $d$, the measure of separatedness of two points, that *for which* the points are significant to one another. This role is not arbitrary: by $L4$, its sufficient reason is the four axioms themselves, thanks to which $d$ is precisely a distance and not just any function of two arguments. From the role of distance unfold the qualitative *positions* on which all further analysis rests: “close” ($d < \varepsilon$) and “far” ($d \geq \varepsilon$), and, when distance is applied along a process, “converges” and “diverges.”[^2]

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are the points of the space. In the rational metric these are the numbers of $ℚ$ themselves, finite as written; in the process metric (§ 1.4) the bearers will be *processes*, finite at every stage. By $L1$ each point is identical to itself—without this it could not be stably recognized across different comparisons. And the principle $P4$ explains the already noted feature of the type `d : X -> X -> Q`: the value of the distance at each comparison is a *finite rational* number, not an element of a completed “$ℝ$.” Actualization here is finite by the very arrangement; a “real” distance, should it be needed, will itself turn out to be a process (§ 1.4), not a ready element.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| carrier $X$ (points) | what is in the space | Element |
| $d : X \to X \to ℚ$ | measure of separatedness | Role |
| “close”/“far,” “converges”/“diverges” | role positions | Role |
| non-negativity, zero, symmetry | hold $d$ as a distance | Rule (concr.) |
| triangle inequality | constitution | Rule (concr.) |
| laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: points are elements, distance is a role, the axioms are rules, and no component lays claim to two categories at once. There is no self-reference: distance works *over* points—by $L5$, an operation stands one level above its operands—and is not applied to itself. By the criterion of well-formedness introduced in Part I, the metric space is well-formed.

The analysis is no end in itself: it explains choices already made in the chapter. Why distance is *rational-valued* (§ 1.3.3): because elements are actualized finitely ($P4$). Why *separation* is placed outside the axioms of the abstract frame (§ 1.3.4): because it belongs to the *concrete* layer of rules of particular spaces, not to the universal one. Why precisely the *triangle* is called the constitution: because among the rules it alone binds scattered distances into a connected whole. And the same analysis sets the pattern for all of Part V: we will read topology, continuity, the derivative, and the integral as systems, each with its own E/R/R structure, unfolding it from the header of the corresponding file.

### Distance with Values in the Rationals

One detail of the definition is essential and deserves a separate word. The distance function has the type `d : X -> X -> Q`: distance takes values in the *rational* numbers, not in some “real” ones.

At this level of formalization ToS chooses a *rational-valued* metric: every finite test of distance gives a value in $ℚ$. The choice has a rationale. Under $P4$ there is no completed set of real numbers; the “real” in ToS is itself a process. If distance took values in “$ℝ$,” it would no longer be a simple measure that outputs a ready number but a process—with its own representatives, equivalence, and proof of independence from the choice of representative. Metrics with values in the process reals *can* be introduced—this does not contradict $P4$, so long as such a distance is itself read in process terms—but they require a separate, later layer. The abstract frame of § 1.3 does not build this layer: it takes distance to be *rational*, so that at each comparison of two points $d$ outputs a concrete rational number. And when distance has to be considered as a process, this is done, as § 1.4 will show, not by replacing $ℚ$ with “$ℝ$” in the type of $d$, but by applying $d$ itself along a process, so that it generates a sequence of rational values.

### Metric or Pseudometric: A Precise Caveat

Care is needed here; otherwise the abstract frame will sound stronger than it is. Among the four hypotheses of the section there is `d_zero`—but let us look closely at its form. `d_zero` asserts *only* that $d(x,x) = 0$: the distance from a point to itself is zero. This is *zero on the diagonal*.

{
The classical definition of a metric requires more, namely *strict separation*: $d(x,y) = 0 \Rightarrow x = y$, that is, zero distance is possible only between coinciding points. And precisely this stronger hypothesis is *absent* from the abstract section of `MetricSpace.v`: it is not among the four `Hypothesis` entries.
}

What does this mean? That the abstract section, strictly speaking, fixes not a full metric but a slightly weaker structure—if we keep to strict terminology, closer to a *pseudometric*. This is no omission: for many arguments (convergence, Cauchy, contraction) strict separation is not even needed, and the section honestly takes exactly the hypotheses that do the work. Where separation is required, it is proved *separately* for the concrete space. The rational distance has it: in `ProcessTopMetric.v` the lemma `qdist_zero_iff` establishes that $|x-y| = 0$ if and only if $x = y$. That is, the rational metric has separation, while the abstract frame does not presuppose it as a general hypothesis. The chapter marks this line between them so that a reader who strictly distinguishes a metric from a pseudometric does not take the abstract section for more than it asserts.

### What Is Proved in the General Frame

{
Within this frame we introduce the key notions of analysis—those that all of Part V will need later—and prove several general lemmas. There are three notions: a *Cauchy sequence* in a metric space (its values come arbitrarily close to one another beyond some cutoff), the *limit* of a sequence, and a *contraction mapping*. In `MetricSpace.v` they correspond to `is_cauchy_metric`, `is_limit_metric`, and `is_contraction_metric`.
}

{
The lemmas are general facts, true in *every* metric space. Non-negativity with the arguments swapped (`d_nonneg_alt`). If a sequence converges to two limits, the distance between these limits is arbitrarily small (`limit_dist_zero`)—the germ of the uniqueness of the limit. Every convergent sequence is Cauchy (`cauchy_of_limit`)—one of the two classical implications between convergence and the Cauchy property. And several lemmas on contraction mappings: the contraction factor is non-negative and strictly less than one, and a contraction does not increase distances.
}

All this is general theory, proved once, for every metric space. `MetricSpace.v` carries eighteen verified lemmas and uses not a single axiom; of these, seven belong to the abstract section, and the rest belong to the metric on $ℚ$ and the $L^\infty$ metric on `QVec`, discussed below. Further constructions will rest on this general frame, beginning with the next section, where distance first becomes a process.

## Two Process Distances: Pointwise and Finite-Horizon{Two Process Distances}

### Distance Ceases to Be a Number

Here is the ontological center of the chapter. In classical mathematics the distance between two real numbers $x$ and $y$ is *one number*, $d(x,y) \in ℝ$, ready and completed. Under $P4$ there is no completed $ℝ$, and the “reals” themselves are processes. What, then, is the distance between two processes?

The answer is predictable from the whole logic of Part IV: the distance between processes *is itself a process*. It is a quantity unfolding through levels of refinement, not a completed number. This agrees with the general ontology: everything that was a “real number” in the classical picture is a process in ToS, and distance is no exception. In the terms of the E/R/R analysis (§ 1.3.2) this means that the bearers, the Elements, are now processes—finite at every stage by $P4$—while the role of distance is preserved.

But caution is needed here, and in it lies the whole content of the section. The repository contains *two* different process constructions of distance, and they must not be confused. One is pointwise; the other is truncated, finite-horizon. Let us examine both.

### Pointwise Distance and the Metric Cauchy Condition

The first construction is the most direct. Two processes $P$ and $Q$ are given; each is a function from the step number to a rational approximation. At each step $n$ they have rational values $P(n)$ and $Q(n)$, and between these rational values there is a distance—that very $|P(n) - Q(n)|$. Gathering these distances over all steps, we obtain a process:

$$
n \;\longmapsto\; |P(n) - Q(n)|.
$$

This is the *pointwise* distance: a process that gives, at each level, the rational discrepancy of the approximations. The object itself is the process, not its “limit value.”

Let us state precisely the status of this definition in the code. There is *no* ready name `rp_dist` for the function $n \mapsto |P(n)-Q(n)|$ in the supporting files of the chapter; the chapter introduces this pointwise distance as a notion. On the other hand, `ProcessTopMetric.v` contains a closely related construction that matters more for analysis—the *metric Cauchy condition*:

```coq
Definition metric_cauchy (a : RealProcess) : Prop :=
  forall eps, 0 < eps ->
    exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
      qdist (a m) (a n) < eps.
```

{

A process $a$ satisfies `metric_cauchy` if its values, measured by the rational distance `qdist`, come arbitrarily close to one another beyond some cutoff. And `ProcessTopMetric.v` proves that this is exactly the ordinary process Cauchy condition:
}

```coq
Theorem metric_cauchy_equiv : forall a,
  is_Cauchy a <-> metric_cauchy a.
```

`metric_cauchy_equiv` is a bridge between two formulations: “being Cauchy” in the sense of Chapter 4.2 and “being Cauchy” in metric terms via `qdist` are one and the same. This is the best anchor for the thesis “metric as process”: the rational distance `qdist` is applied along a process, and the metric language fits exactly onto the Cauchy apparatus already built.

And one more caveat, concerning a natural expectation. One would like to say: if $P$ and $Q$ are both Cauchy processes, then the pointwise process of distances $n \mapsto |P(n)-Q(n)|$ is Cauchy too. In substance this is true, and the proof is short—by the triangle inequality for the rational absolute value:

$$
\bigl||P_m-Q_m| - |P_n-Q_n|\bigr| \;\leq\; |P_m-P_n| + |Q_m-Q_n|,
$$

so that if the right-hand terms are small (and they are small, since $P$ and $Q$ are Cauchy), the left-hand discrepancy is small as well. A lemma of exactly this kind—“the process of distances of two Cauchy processes is Cauchy”—is now proved: it is `cauchy_abs_is_cauchy` from the file `RealPointMetric.v`. It was not among the seven *supporting* files of this chapter, but the repository has it; so what is given here is no longer only a proof sketch: the estimate is secured by a separate theorem, and § 1.8.2 will show that, together with compatibility, it yields the metric on classes.

### The Finite-Horizon Observable Distance

The second construction is a different one, and it must not be confused with the first. It is defined in `ProcessSpace.v` and is called `process_dist`:

```coq
Fixpoint process_dist_aux (f g : RealProcess) (n : nat) : Q :=
  match n with
  | O => Qabs (f 0%nat - g 0%nat)
  | S n' => process_dist_aux f g n' + Qpow (1#2) n * Qabs (f n - g n)
  end.

Definition process_dist (f g : RealProcess) (N : nat) : Q :=
  process_dist_aux f g N.
```

Let us read it carefully. `process_dist` $f\;g\;N$ for fixed $N$ is a *finite weighted sum*: over all steps from $0$ to $N$ the discrepancies $|f(k)-g(k)|$ are taken, each with the weight $(1/2)^k$, and added up. The result has an argument $N$, the horizon, and the sum *depends* on it.

Let us name this construction precisely: `process_dist` is a *finite-horizon observable distance*. It is the distance between two processes as seen *up to level $N$*, up to a finite horizon of observation. The farther the horizon $N$ is pushed, the more steps are taken into account; but for every fixed $N$ this is a finite rational quantity.

It is essential to see what `process_dist` is *not*. It is *not* the pointwise process of distances $n \mapsto |P(n)-Q(n)|$ from the previous subsection: there each step carries one discrepancy, here each horizon $N$ carries the accumulated weighted sum of all discrepancies up to it. (If, however, $f$ and $g$ are fixed and $N$ is let run through the step numbers, then the map $N \mapsto `process_dist` f g N$ is itself a process—a process of *accumulated finite-horizon* distances; this is a different process from the pointwise $n \mapsto |P(n)-Q(n)|$, and the two must not be confused.) Nor is `process_dist` a limit distance between classes of processes: there is no passage to a limit in the definition, only a finite horizon. `process_dist` is a convenient measure of how far two processes have diverged *within the surveyable range*; the weight factor $(1/2)^k$ guarantees that distant steps contribute less and less.

Let us gather the three constructions of distance on processes into a table; it fixes the distinction on which the whole section rests:

| Construction | Type | What it measures |
|---|---|---|
| $n \mapsto |P(n)-Q(n)|$ | process over $ℚ$ | pointwise discrepancy at each level (a notion of the chapter; there is no separate name in the code) |
| `process_dist` $P Q N$ | $ℚ$, for fixed $N$ | weighted sum of discrepancies up to horizon $N$ |
| $N \mapsto `process_dist` P Q N$ | process over $ℚ$ | accumulated finite-horizon distances |

{

The first row is the pointwise distance of § 1.4.2; the second is `process_dist` itself from `ProcessSpace.v`, a rational number for a given horizon; the third is the same `process_dist` read as a process in the horizon. All three are legitimate; mixing them is not.
}

### ProcessSpace.v as an Infrastructure Layer

{
Around `process_dist` it is natural to build a small topological apparatus—and it has been built: `cylinder` (agreement of processes on the first $N$ coordinates within a radius), `process_ball` (a ball in the finite-horizon distance), `process_bounded` (boundedness of a process). Basic facts are proved: the distance from a process to itself is zero, the center lies in its ball, a constant process is bounded. All of this is gathered in the file `ProcessSpace.v`.
}

Here it is important to outline precisely what this layer *is* and what it is not. `ProcessSpace.v` is an *infrastructure* layer: it lays down the rudiments of a topology on the space of processes, but it does not build a full metric on the type of classes `RealPoint`. It contains a theorem with a grand name, `process_space_complete`, and here the chapter is obliged to call things by their proper names. Contrary to its name, `process_space_complete` is *not* a theorem about the completeness of the space of processes. If one reads its proof closely, it turns out to be a simple *conjunction of two already proved trivial lemmas*: “the distance from a process to itself is zero” and “the center lies in its ball.” It is a useful summary of two elementary facts, but not a statement that every Cauchy sequence of processes converges. The name promises more than the theorem gives, and our audit notes this directly. Genuine completeness—and why it is a *notion* here rather than a proved theorem—is the subject of § 1.6.

## The Metric over Processes and the General Scheme

### The Universal Process Type

Up to now processes have been Cauchy processes over $ℚ$—functions from the step number to a rational approximation. But the notion of a process is broader, and it is worth formalizing in the most general form: a process over an arbitrary type $A$ is simply a function from step numbers to $A$, a step-indexed computation that outputs a value of type $A$ at each step. In `ProcessGeneral.v` this is written as follows:

```coq
Definition GenProcess (A : Type) := nat -> A.
```

A Cauchy process is a particular case, $A = ℚ$. The binary process of Chapter 4.5 is a particular case, $A = `bool`$. `GenProcess` is the general form of them all.

Over this general type we also build a general apparatus: `observe` (read the value at step $n$), `prefix` (collect the first $n$ values into a list—a finite observation, in the spirit of $P4$), `process_map` (apply a function at each step), `const_process` (the constant process). All this is the content of `ProcessGeneral.v`.

### The Generalized Cauchy Condition

The main thing the general scheme gives is the *generalized Cauchy condition*. Over any type $A$ equipped with a distance function $\mathit{dist} : A \to
A \to ℚ$, one can ask whether a process stabilizes:

```coq
Definition is_cauchy_gen {A : Type} (dist : A -> A -> Q)
                         (p : GenProcess A) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat -> dist (p m) (p n) < eps.
```

Note that the distance $\mathit{dist}$ here again has values in $ℚ$—the same logic as in the abstract metric frame of § 1.3. `is_cauchy_gen` generalizes the Cauchy condition of Chapter 4.2 to any type with a rational distance. And it is worth making sure that the generalization has not drifted away from the original notion: for $A = ℚ$ with the distance $|x-y|$, the generalized condition coincides exactly with the ordinary Cauchy condition. This coincidence is confirmed by the lemma `cauchy_Q_equiv` from `ProcessGeneral.v`: `is_cauchy` and `is_cauchy_gen Qdist` are equivalent. In the terms of the analysis of § 1.3.2 this is the same role—distance as a measure of separatedness—generalized to an arbitrary carrier type $A$: the Elements change, while the role of distance itself remains.

{
A useful lemma of this layer is `process_map_cauchy`: a map that does not *increase* distances sends a Cauchy process to a Cauchy process. And a related one, already in `ProcessTopMetric.v`, is `cauchy_map_lipschitz`: a Lipschitz map preserves the Cauchy property. These lemmas are groundwork for continuity: they say that “good” maps respect convergence. We will return to continuity in § 5.3 of the volume.
}

### The Name process_equiv in Different Files

A caveat about names is needed here—a small but important one, because without it confusion comes easily. The name `process_equiv` occurs in the repository in more than one sense.

In `ProcessGeneral.v`, `process_equiv` is a *generalized pointwise* relation: two processes are equivalent if they agree at each step with respect to a given relation $\mathit{eq}_A$ on $A$. In `ProcessCore.v` the name `process_equiv` is borne by a *different* relation, that of *the same limit* for rational processes: two Cauchy processes are equivalent if they converge to the same number (this is the relation of Chapter 4.3 by which the point was built as a class). And in `CauchyReal.v` the related relation of the same limit is called `cauchy_equiv`.

These are different relations, and the coincidence of names is only a coincidence of names. The chapter uses each in its *local* sense and, whenever it mentions `process_equiv`, means the relation defined in the file under discussion. Pointwise agreement (`ProcessGeneral.v`) and the same limit (`ProcessCore.v`) are not the same thing, and the chapter keeps this boundary.

### The Bridge between Process Types

Part V constantly moves between two types: `CauchySeq` from `CauchyReal.v`, a record that combines a sequence with a proof of its Cauchy property, and `RealProcess` from `ProcessCore.v`, the bare process `nat -> Q`. One type is convenient when the Cauchy property has to be carried along; the other, when the process is regarded as pure computation.

So that the two lines do not remain non-communicating branches, a *bridge* must be built between these types—transitions there and back that preserve the Cauchy property and equivalence. This bridge is built in the file `ProcessBridge.v`: the link is technical but necessary, for without it the `CauchyReal` line and the `ProcessCore` line would develop separately. One more span is added to the same bridge by `ProcessGeneral.v`, in the lemma `cauchy_seq_is_gen_process`: every `CauchySeq` is, in particular, a `GenProcess` over $ℚ$ satisfying the generalized Cauchy condition. Thus the three levels—`CauchySeq`, `RealProcess`, and the general `GenProcess`—turn out to be stitched into one consistent picture, through which the following chapters of Part V will move freely.

## Completeness: Notion and Boundary

### A Bold Line

This section is the most cautious in the chapter, and it has to begin with a direct thesis, stated without circumlocution.

**In this chapter completeness is introduced as a *notion*; it is not proved as a property of a concrete space.**

This must be said at once, because here runs the boundary beyond which the careful plan of Part V parts ways with the tempting but false claim that “process analysis is complete.” Chapter 5.1 builds the *definition* of completeness and honestly shows *where* it still remains a definition not yet turned into a theorem.

### The Definition of Completeness

Let us begin with what it means for a metric space to be *complete*. This is the property of having “no holes”: a process whose values come close together necessarily converges to something, and this “something” is a point of the space itself. In other words, a space is complete if every Cauchy sequence of its points has a limit. In the abstract section of `MetricSpace.v` we write this as follows:

```coq
Definition is_complete_metric : Prop :=
  forall f : nat -> X, is_cauchy_metric f -> exists l : X, is_limit_metric f l.
```

And here the key word is `Definition`. `is_complete_metric` is a *definition*, a predicate: the *formulation* of the property “being complete.” By itself it asserts nothing about any concrete space. It says *what it means* to be complete, but it does not say that even one space has this property.

### What Is Not in the Supporting Files

Now for an honest inventory. The seven supporting files of Chapter 5.1 contain *no* theorem that would prove completeness. There is no statement “$ℚ$ is complete” (nor can there be: $ℚ$ is precisely incomplete, since a process of rational approximations to an irrational number is Cauchy but has no rational limit). There is no statement “`CauchyReal` is complete.” There is no statement “the space of processes is complete.” The notion `is_complete_metric` is introduced, but it is not applied, as a proved theorem, to any space.

This is an *honest boundary*, neither a gap nor an unfinished piece of work: the completeness of a concrete process space is a substantive task of formalization, and Chapter 5.1 does *not* close it. It introduces the notion and leaves the proof of completeness for one space or another as a direction of further work.

It is worth specifying what exactly *is proved* about `CauchyReal`. The file `CauchyReal.v` contains the lemma `cauchy_complete_
self` and related ones—properties of *the Cauchy representatives themselves*: say, that a process of rational approximations agrees with itself in a suitable sense. These are useful basic facts. But this is *not* full metric completeness of the quotient space of classes: a lemma about a property of a representative and a theorem that every Cauchy sequence of *classes* has a limit are statements of different scale, and the second is absent from the supporting files.

And—as already said in § 1.4—`process_space_complete` from `ProcessSpace.v`, despite its grand name, does not prove completeness: it is a conjunction of two trivial lemmas. The name contains the word “complete”; the theorem behind it does not.

### The Cauchy Proof and a Computable Modulus

There is a tempting argument that must be examined carefully here, because it contains both a true kernel and a dangerous exaggeration. The argument runs as follows: the classical proof of the completeness of a metric space usually relies on the axiom of dependent choice—for each level of precision a suitable index has to be *chosen*; whereas in ToS, supposedly, no choice is needed, because a Cauchy process “already carries” a modulus of convergence.

There is a grain of truth here. The type `CauchySeq` combines a sequence with a proof of its Cauchy property; and in a constructive reading a Cauchy proof does indeed *point to a rule*: to a way of naming the cutoff for a given precision.

But the exaggeration is close at hand too, and it must be named. `CauchySeq` stores the proof of the Cauchy property in Prop—in the world of logical propositions. This is enough for a *logical* formalization of the Cauchy property. But it does *not automatically follow* that from such a proof one can *computationally extract* a modulus of convergence as *data*—as a function “given $\varepsilon$, produce $N$” that can be run to obtain a number. Extracting the modulus as a computable object requires an *informative* variant of the property—for example, the regular Cauchy condition (`is_Regular_
Cauchy` from `ProcessCore.v`) or an explicitly attached modulus. It is no accident that ToS
*distinguishes* `is_Cauchy` and `is_Regular_
Cauchy`: this distinction is exactly what separates the logical property from the one that carries computable data.

Therefore the chapter formulates this cautiously. Not “a Cauchy proof already is an algorithm,” but this: in the ToS reading, a Cauchy proof *points to* a rule for finding the cutoff; and for a computable implementation of this rule an *explicit* modulus or a regular variant of the Cauchy property is useful. The ontological thesis that in ToS existence and constructibility draw close remains in force as a recurring process motif of ToS and as an *interpretation*—but it is not an automatic property of every Prop proof, and the chapter does not pass it off as one.

### What Remains

{
Let us draw a line under the section. Completeness in Chapter 5.1 is a *notion*: the definition `is_complete_metric`, clean and checkable. The application of this notion to a concrete process space—a proof that one space of classes or another is complete—has *not been carried out* in the supporting files of the chapter and is honestly left as a direction. This is the “infrastructure mode” of which § 1.1 gave warning: the notion is built, the boundary is named, and neither is passed off as the other.
}

## The Archimedean Property as Fuel

### What the Metric Needs the Archimedean Property For

The metric is built—but for it to *work* in analysis, one more property is needed, without which $\varepsilon$-arguments would hang in the air. This is the *Archimedean property*.

Almost every analytic argument has the form: “set a precision $\varepsilon$, and there is a level $N$ from which on the discrepancy is less than $\varepsilon$.” For such a move to make sense, this $N$ must *exist* for every $\varepsilon$, however small. In other words, the refinement of precision must sooner or later *break through* any given threshold. This is the Archimedean property, which the process metric inherits from the rational numbers $ℚ$ (Chapter 3.4 of the volume).

Concretely, the following form of it matters for the metric: for any $\varepsilon > 0$ there is a natural number $N$ such that $(1/2)^N < \varepsilon$. Halving—$1, 1/2, 1/4,
1/8,…$—sooner or later drops below any threshold.

### The Archimedean Property Makes Algorithms Finite

This property has not only an ontological meaning—“precision is attainable”—but also a direct *computational* one. The Archimedean property *makes analytic algorithms finite*.

Consider a typical $\varepsilon$-algorithm: interval bisection. At each step the width of the current interval is halved; the work goes on until the width becomes less than the required $\varepsilon$. The question is whether this loop will stop. The Archimedean property gives the answer: since there is an $N$ with $(1/2)^N < \varepsilon$, after $N$ steps the width is certainly small, and the loop terminates *in at most $N$ iterations*. The Archimedean property supplies the loop with *an upper bound on the number of steps*, and for a concrete rational $\varepsilon$ this $N$ is found by explicit search through powers of two. It is worth keeping a distinction in mind, however: the formal theorem that such an $N$ exists and an executable procedure for finding it are close but technically different layers; if a runnable algorithm is what is needed, it is specified separately.

Herein lies the link between ontology and computation. What is ontologically finite (a process whose precision is *attainable*) turns out to be *algorithmically* finite as well (a computation that *terminates* within a surveyable number of steps). The Archimedean property is a bridge between two finitudes.

### A Computational Example: How Many Steps Suffice

Here is the promised third layer of the exposition. Let us make the Archimedean property *tangible* by counting how many halving steps suffice for several concrete levels of precision.

The task: for a given $\varepsilon$, find the least $N$ such that $(1/2)^N < \varepsilon$. This $N$ is *computable*: it is found directly by searching through powers of two. Here is the result for three typical thresholds:

| Required precision $\varepsilon$ | Sufficient $N$ | Check |
|---|---|---|
| $1/10$ | $4$ | $(1/2)^4 = 1/16 < 1/10$ |
| $1/100$ | $7$ | $(1/2)^7 = 1/128 < 1/100$ |
| $1/1000$ | $10$ | $(1/2)^{10} = 1/1024 < 1/1000$ |

Let us read the table. For the discrepancy to fall below one tenth, four halving steps suffice: $1/16$ is already less than $1/10$. Below one hundredth, seven steps: $1/128 < 1/100$. Below one thousandth, ten: $1/1024 < 1/1000$. The numbers in the middle column are computed, not guessed, and each row can be checked by a direct comparison of fractions, as is done in the right-hand column.

This is the Archimedean property at work: a concrete table showing how many steps suffice, in place of the philosophical thesis that “precision will be attained someday.” The reader *sees* that $\varepsilon$ is attained in a finite number of steps computable in advance—and sees that when $\varepsilon$ decreases tenfold, the required $N$ grows by only three or four steps. The $\varepsilon$-arguments of process analysis stand on this computable ground.

### A Caveat on the Status of Axioms

And an honest caveat, in the spirit of the whole chapter. The seven *main* supporting files of Chapter 5.1 declare in their headers the status “0 axioms”—not a single axiom; this was said in § 1.1. For a strict audit of a concrete theorem, the status is still checked with the command `Print Assumptions`: a declaration in a file header does not replace it.

{
The present section, however, additionally relies on a separate file, `Archimedean_ERR.v`, where the Archimedean property of $ℚ$ is formalized. Therefore the chapter makes no sweeping claim that “the whole chapter stands on zero axioms.” The precise formulation is this: the seven main files are axiom-free; the section on the Archimedean property draws on `Archimedean_ERR.v` in addition, and its dependence on axioms, if any, has to be established separately—with the command `Print Assumptions` for the corresponding theorem. This is the same discipline as in Chapter 4.6: axiom status is checked for a concrete theorem, not ascribed wholesale to a file or a chapter.
}

## What Has Been Built and What Is Being Prepared. Summary of the Chapter

### The Summary in Three Columns

The chapter opened Part V, and it is most honest to sum it up as “infrastructure mode” requires: with three lists—what is built, what is *not* built, and what is being prepared next, without mixing one with another.

**Built and checked.**

- The rational metric on $ℚ$: the distance $|x-y|$ and the four axioms of a metric, all proved (one construction under three names—`Q_dist`, `qdist`, `Qdist`).
- The abstract metric frame: the metric space as a parametric `Section`, with the notions of Cauchy, limit, and contraction and with general lemmas—without axioms (the file records eighteen verified results, including the $ℚ$ and `QVec` layers).
- The process Cauchy condition via the rational distance: `metric_cauchy`, provably equivalent to the ordinary `is_Cauchy` (theorem `metric_cauchy_equiv`).
- The finite-horizon observable distance on the space of processes: `process_dist`, a weighted sum of discrepancies up to level $N$.
- Bridges between process types: `CauchySeq`, `RealProcess`, and the general `GenProcess` are stitched into one consistent picture (`ProcessBridge.v`, `cauchy_seq_is_gen_process`).

**Not built in this chapter.**

- The quotient type `RealPoint` as a Rocq object is not built here: the chapter worked with processes and rational distances.
- The metric on the classes `RealPoint` as a separate Rocq structure is not introduced *in this chapter*, but the repository has built it (the file `RealPointMetric.v`: `rp_dist` with the axioms of a metric and `rp_dist_Proper`, independence from the choice of representative); see § 1.8.2.
- Full metric completeness of the space of these classes is not proved; completeness is introduced as a *notion* (§ 1.6), not as a theorem about a concrete space.

**Prepares next.**

- Open balls $B(P,\varepsilon)$ and the notion of “close processes”: material for § 5.2, topology.
- Continuity as the preservation of closeness: material for § 5.3; the groundwork is laid by the lemmas `cauchy_map_lipschitz` and `process_map_cauchy` of this chapter.

### The Metric on Classes: Built

{
The list “not built” refers to *this* chapter and its seven supporting files. The metric on the classes `RealPoint` itself has *been built* in the repository, in a separate file, `RealPointMetric.v`; it is worth naming concretely what it consists of, so that the boundary of the chapter is drawn precisely.

First, the pointwise distance as a named construction—and with values directly in the *reals*, not the rationals: the distance between two points is itself a point (a process),

$$
`rp_dist`\;(a b : `RealPoint`)
  := \;`cauchy_abs` (`cauchy_sub`\;a\;b),
$$

that is, $|a-b|$ as a process. Second, those very two lemmas. The first: the process of distances is Cauchy (`cauchy_abs_is_cauchy`, the sketched estimate of § 1.4.2, now a theorem). The second: `rp_dist` is *compatible* with equivalence—replacing representatives by equivalent ones does not change the distance (`rp_dist_compat` and the instance `rp_dist_Proper`). It is precisely the second lemma that makes the distance *descend* from processes to classes and turns `RealPoint` into a metric space. Beyond that, the four axioms of a metric are proved—non-negativity (`rp_dist_nonneg`), zero on the diagonal (`rp_dist_self_zero`), symmetry (`rp_dist_sym`), the triangle (`rp_dist_triangle`)—and, beyond them, separation (`rp_dist_eq_zero_iff`). So what separates the chapter from a metric on classes is no longer a gap: the metric is built, though in `RealPointMetric.v` rather than in the seven files of *this* chapter. What remains open is only the next layer, the metric *completeness* of the space of classes (§ 1.6).
}

### A Bridge to Multidimensional Analysis

One remark for the future. The file `MetricSpace.v` contains not only the distance on $ℚ$ but also *the $L^\infty$ metric on rational vectors* `QVec`—a distance equal to the largest of the coordinatewise discrepancies (`list_max_dist`), with the four properties of a metric proved for it. In the present chapter this material is not unfolded: the chapter has stayed within one-dimensional distance. But it is worth noting it as a *bridge*: the process metric is not tied to one dimension, and when the volume reaches multidimensional analysis and optimization, the $L^\infty$ distance on `QVec` will be a ready starting point.

### Summary of the Chapter

Chapter 5.1 has laid the first analytic layer of Part V: distance. It traveled the path from the simplest rational $|x-y|$ through the abstract metric frame to process distances—and at every step it kept the boundary between what is proved and what is only sketched. The main turn: the *pointwise* distance between processes is itself a process, not a completed number (and alongside it `process_dist` gives a finite-horizon distance, a different layer); the main caution: completeness is so far a notion, not a theorem. On this foundation Part V will build topology, continuity, and all further analysis.

{*The summary of the chapter comes in three parts. First: what is built. The distance between rational numbers—$|x-y|$ with the four proved axioms of a metric; the abstract metric frame as a parametric `Section`; distance as a process—`metric_cauchy` over `RealProcess`, equivalent to the ordinary Cauchy condition; the finite-horizon observable distance `process_dist`; bridges between `CauchySeq`, `RealProcess`, and `GenProcess`. All seven supporting files are axiom-free.*}

{*Second: what this rests on. Distance takes values in the rational numbers: the process metric does not require a completed “$ℝ$.” The abstract section fixes the basic structure—non-negativity, zero on the diagonal, symmetry, the triangle; strict separation does not enter it as a general hypothesis, and for the rational metric it is proved separately. $\varepsilon$-arguments rely on the Archimedean property of $ℚ$, which makes the refinement of precision computably finite.*}

{*Third: what remains open. The metric on the classes `RealPoint` is already built—outside the seven files of this chapter, in `RealPointMetric.v` (`rp_dist` with the axioms and `rp_dist_Proper`; § 1.8.2). What remain open are *full metric completeness* of the space of these classes (completeness is introduced as a notion, not as a proved theorem) and a reified quotient type as a separate object; the latter ToS deliberately does not build, by $P4$ (Chapter 4.3). The chapter has given the foundation, distance; the topology and continuity that will stand on it are the subject of the following chapters of Part V.*}

---

[^1]: This is the verbatim E/R/R labeling in the header of the file `MetricSpace.v`; here it is only unfolded following the pattern of Part I.
[^2]: These four positions—`close` / `far` / `convergent` / `divergent`—are listed in the `Status` line of the header of `MetricSpace.v`.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/06 P4 as a Filter|Chapter 6. P4 as a Filter—Part IV]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/02 Topology and Compactness|Chapter 2. Topology and Compactness]] →
