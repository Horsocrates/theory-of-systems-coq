---
title: "Chapter 3. Continuity"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/03 Непрерывность.md"
sourceBlob: 635d1064e7cf184a6a37464bd9411929d3acab47
translated: 2026-10-20
status: draft
---

## From Topology to Continuity

### What the Previous Chapters Built

Part V builds the analysis of processes layer by layer. Chapter 5.1 gave *distance*: the metric on the rational numbers, open balls, distance as a process. Chapter 5.2 gave *topology*: open and closed sets, separation, compactness, uniform covers. Everything needed for the next step has been accumulated—and this step is called *continuity*.

A continuous function is a function that *respects closeness*. If two arguments are close, so are the values; a small perturbation of the input gives a small perturbation of the output. The metric gave meaning to the word “close”; topology gave neighborhoods; now we can ask which functions carry the close to the close.

And at once come the two main theorems that continuity makes possible. The intermediate value theorem: a continuous function that changes sign vanishes somewhere. The extreme value theorem: a continuous function on a closed interval attains its maximum. These are two pillars of classical analysis, and both are the subject of the present chapter.

### Two Faces of Continuity

With continuity over $ℚ$ we must agree from the very beginning on a distinction without which the whole chapter would sound imprecise. Continuity comes in *two kinds*, and over the rational numbers they *do not coincide*.

*Pointwise* continuity looks at each point separately. A function $f$ is continuous at a point $x$ if for every required precision $\varepsilon$ there is a neighborhood $\delta$ *of its own* in which the values do not stray from $f(x)$ by more than $\varepsilon$. The size of $\delta$ may depend on the point $x$: in some places the function may be gentle, in others steep.

*Uniform* continuity requires more. It requires that $\delta$ can be chosen *one for the whole interval*, common to all points at once. Not “each point has its own neighborhood,” but “there is a single scale at which the function behaves tamely everywhere.”

Over the real numbers there is a classical theorem, the Cantor–Heine theorem, which says that on a closed interval (on a compact set) these two kinds of continuity *coincide*. A pointwise continuous function on $[a,b]$ is automatically uniformly continuous. Over $ℚ$ this is *not so*. And the reason is the same one that brought down Heine–Borel in § 2.5: the *incompleteness* of $ℚ$. The rational interval is full of holes, and pointwise continuity is not enough to pull all the local $\delta$ together into one global one.

From this follows a key fact about the structure of the chapter. Both main theorems—on the intermediate value and on the extreme value—are formalized with the hypothesis of *uniform* continuity, not pointwise continuity. This is not because the formalization is weak but because over $ℚ$ uniformity is exactly what is needed, and it has to be required *explicitly*, since Cantor–Heine does not hold.

### On Axiom Status: The Technical and the Ontological

As in Chapter 5.2, let us agree on words in advance; otherwise the theorems of this chapter will sound more alarming than they should.

The proofs of the intermediate value theorem and the extreme value theorem *use the axiom* `classic`, an object from the file `ToS_Axioms.v`. But `classic` is a *technical Rocq axiom that implements an ontological law of logic* of ToS, not a foreign crutch or a concession to looseness: it is the Law of Excluded Middle, $L3$, in the form in which Rocq accepts it.

The difference is one of principle. In purely constructive mathematics the appearance of `classic` would be an admission of weakness. In ToS it is not: $L3$ is a law of logic of ToS, accepted at the level of the system itself (Part I). When a proof “uses `classic`,” it does not depart from rigor: it *explicitly takes into account* that it rests on a law of logic of ToS. Therefore, whenever the chapter marks an appeal to $L3$, this is an *honest accounting of the level*, not an alarm signal. Throughout the rest of the chapter, the recurring reference “as agreed in § 3.1” points here.

### The Plan of the Chapter

The chapter goes from the notion to the theorems. First comes continuity as such: its topological face (§ 3.2) and the discussion, central for the chapter, of uniform continuity and the boundary of $ℚ$ (§ 3.3). Then the first great theorem, the intermediate value theorem, through bisection (§ 3.4) and on three levels of typing (§ 3.5). Then the second, the extreme value theorem, through grid refinement (§ 3.6), in two versions of the formalization (§ 3.7). And finally the uniform limit of continuous functions and the summary of the chapter (§ 3.8).

There are nine supporting files, all checked against the repository verbatim. The topological layer of continuity is axiom-free; the intermediate value and extreme value theorems have $L3$ explicitly accounted for.

## Continuity: The Topological Face

### Definition via $\delta$-$\varepsilon$

Let us begin with the simplest face of continuity, the pointwise one. ToS defines the *continuity of a function at a point* as follows: a function $f$ is continuous at a point $x$ if any required precision of the value can be ensured by a sufficient precision of the argument. Formally: for any $\varepsilon$ there is a radius $\delta$ such that every argument $y$ closer than $\delta$ to $x$ gives a value $f(y)$ closer than $\varepsilon$ to $f(x)$. A function is *continuous* if it is continuous at every point. This is the classical $\delta$-$\varepsilon$ definition, carried over to the rational level: argument, point, and radii are rational. In Rocq it is written in the file `Topology.v`, with which the chapter already became acquainted in § 2.2:

```coq
Definition continuous_at (f : Q -> Q) (x : Q) : Prop :=
  forall eps, eps > 0 -> exists delta, delta > 0 /\
    forall y, Qabs (y - x) < delta -> Qabs (f y - f x) < eps.

Definition continuous (f : Q -> Q) : Prop :=
  forall x, continuous_at f x.
```

For working with increments, a second, related form of the same notion is convenient: continuity *on an interval*. It asks about the behavior of $f$ on an interval $[a,b]$ and measures the change through an increment $h$: a small $h$ gives a small change $f(x+h) - f(x)$. In the repository this form is written in `UniformConvergence.v`:

```coq
Definition continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall x : Q, a <= x -> x <= b ->
    forall eps : Q, 0 < eps ->
      exists delta : Q, 0 < delta /\
        forall h : Q, Qabs h < delta ->
          a <= x + h -> x + h <= b ->
          Qabs (f (x + h) - f x) < eps.
```

`continuous_on f a b` is the same pointwise continuity, restricted to an interval and written through the increment. This is the main interval form of the definition of continuity among the supporting files of the chapter; it is precisely this form that is convenient for the theorems on uniform limits, to which the chapter will come in § 3.8.

### The Algebra of Continuous Functions

Continuity is a *stable* property: it survives the basic operations on functions, and so a rich class can be built from a few of the simplest continuous functions. Let us trace this construction; each of its steps is confirmed by a proved lemma of `Topology.v`.

*The simplest functions are continuous.* The identity $x \mapsto x$ is continuous: a small change of the argument is exactly a small change of the value (lemma `identity_continuous`). A constant function is trivially continuous: the value does not change at all (`constant_continuous`). The shift $x \mapsto x + c$ is continuous (`add_const_continuous`). These are the starting bricks.

*Operations preserve continuity.* The sum of two functions continuous at a point is continuous at that point (`continuous_at_sum`); the negation of a continuous function is continuous (`continuous_at_neg`); the composition of continuous functions is continuous (`continuous_at_comp`). Each of these lemmas of `Topology.v` closes the class of continuous functions under one more operation.

Putting the starting bricks together with these operations, we obtain a great deal at once: by addition, negation, shift, and composition, a rich class of continuous functions is built from the identity and the constants. The full claim—that *all* polynomials are continuous—requires one more link: a lemma on the preservation of continuity under multiplication. Among the lemmas of `Topology.v` on which the chapter relies here (`continuous_at_sum`, `continuous_at_neg`, `continuous_at_comp`, and the starting `identity_
continuous`, `constant_continuous`), there is no such link;
closure under multiplication is a standard extension of the algebra of continuous functions, and the chapter leaves it precisely an extension, without ascribing to `Topology.v` more than is proved there. What matters is something else: the foundation, a stable class of continuous functions closed under the basic operations, has been laid, and one can rely on it.

### The Preimage of an Open Set Is Open

Continuity also has a second face, a purely topological one: without $\delta$ and $\varepsilon$, with open sets alone. ToS does not postulate it separately but *derives* it from the $\delta$-$\varepsilon$ definition, showing that the two descriptions of continuity are one.

The reasoning goes as follows. Let $f$ be continuous and $S$ an open set. Take a point $x$ whose image $f(x)$ lies in $S$. Since $S$ is open, there is a margin of free space around $f(x)$: a ball of radius $\varepsilon$ lying entirely in $S$. Since $f$ is continuous at $x$, to this $\varepsilon$ there corresponds a $\delta$: every argument closer than $\delta$ to $x$ gives a value closer than $\varepsilon$ to $f(x)$, that is, a value that still falls into $S$. Hence the whole $\delta$-ball around $x$ is carried by $f$ into $S$: the point $x$ has a margin of free space *in the preimage*. And this is exactly what it means for the preimage of $S$ to be open. Thus topological continuity is derived from $\delta$-$\varepsilon$ continuity:

```coq
Theorem continuous_preserves_open_preimage : forall f S,
  continuous f -> is_open S ->
  is_open (fun x => S (f x)).
```

This statement is a theorem proved in `Topology.v`, confirming the derivation just carried out: the preimage of an open set under a continuous function is open. In classical topology continuity is often *defined* by it: a continuous function is one that does not break openness when preimages are taken. ToS obtains this definition as a consequence of the $\delta$-$\varepsilon$ definition rather than as a postulate, and the two faces of continuity turn out to agree.

Here a direct link with Chapter 5.2 is visible as well. The open set, which there was the central notion of topology, now becomes the *touchstone* of continuity: a continuous function is exactly one that respects the topological structure built by the previous chapter.

And let us note what all this stands on. The topological face of continuity—the $\delta$-$\varepsilon$ definition, the algebra of continuous functions, the derivation of the preimage theorem—has been obtained *constructively*, without appeal to the laws of logic; `Topology.v`, as noted back in § 2.2, uses not a single axiom. Axioms will be needed later, when the chapter turns to the two great theorems of analysis.

### E/R/R Analysis: Continuity as a System

Continuity is a system, and the E/R/R methodology (Part I) applies to it. The analysis unfolds the labeling that already stands in the header of the supporting file, where continuity is named directly: *rule—continuity is a constitution: the preimage of an open set is open*.[^1] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. The caveat about status is the same as in Chapters 5.1–5.2: continuity here is a property of functions $ℚ \to ℚ$, not of maps of quotient classes; “system” is a substantive ontological interpretation, not an object `System` $L$.

*Rules* (the law $L5$). Continuity itself is a *constitution*, in two equivalent forms: the local one ($\delta$-$\varepsilon$) and the topological one (“the preimage of an open set is open”); § 3.2.3 showed that this is one rule written twice. Adjoining it is a concrete layer: the closure of the class of continuous functions under sum, negation, shift, and composition (§ 3.2.2); all of this is constructive, without axioms. But over $ℚ$ the rules of continuity undergo a *forced strengthening*: the pointwise form is *insufficient* for the theorems of analysis, since Cantor–Heine fails over $ℚ$ (§ 3.3.2). Therefore the requirement of *uniformity* enters the rules, and the constructive bridge to it is the Lipschitz property (§ 3.3.3). This is a Rule-level consequence of the incompleteness of $ℚ$, and it explains why both great theorems carry uniform continuity in their hypotheses. Finally, each theorem has its own rule-construction: bisection (the sign at the midpoint $\to$ the choice of a half) and grid refinement.

*Roles—the significance of positions* (the law $L4$). A function plays the role of a *map*, a translation of input into output; continuity endows it with one of the qualitative *positions*: *continuous at a point*, *uniformly continuous*, *Lipschitz*—modes in which the function respects closeness with different strength. In the two great theorems the role is different: the object sought, the root or the maximizer, plays the role of a *Cauchy process in $[a,b]$* converging to the sign change or to the supremum.[^2] Here too belongs the subtle role distinction of § 3.6.3: for the maximum, the role of *value* (the supremum process, Cauchy) is primary, while the role of *position* (argmax) is derivative and fragile.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are the functions $ℚ \to ℚ$ themselves and the points of $ℚ$ on which they are defined. In the processes of the two theorems the bearers are finite at every step: the midpoints of nested intervals (bisection) and the grid nodes (extremum); every snapshot is surveyable, in the spirit of $P4$. A completed “root” or “point of maximum” may be irrational and does not exist as a ready element; only the finite approximations are actual.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| functions $ℚ \to ℚ$, points | bearers | Element |
| map; modes: continuous / uniformly / Lipschitz | role-positions | Role |
| continuity ($\delta$-$\varepsilon$ $\equiv$ preimage of an open set is open) | constitution | Rule (constr.) |
| closure under sum, composition, shift | algebra | Rule (constr.) |
| uniformity as a requirement (Cantor–Heine fails over $ℚ$) | strengthening of the rule | Rule (incompleteness, $L3$) |
| bisection, grid refinement | constructions of the theorems | Rule |
| laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: functions are elements, the modes of continuity are roles, the criterion of continuity is a rule. There is no self-reference: the criterion quantifies over arguments and stands *above* the values of the function—by $L5$, an operation stands above its operands. Continuity is well-formed.

The analysis clarifies two subtleties to which the chapter will come later. The *three levels* of the intermediate value theorem (§ 3.5) are, by $P3$, three intensionally distinct *representations* of one root: three answers to the question “what is a root,” agreeing in content but different in type. And the *argmax* of the extreme value theorem (§ 3.7) is an $L5$-distinguished role-position: the order $L5$ makes the choice of the maximizer unambiguous where there are several candidate values. And the same analysis sets the pattern of Part V: every analytic notion is read as a system with its own E/R/R structure.

## Uniform Continuity and the Boundary of $ℚ$

### The Definition of Uniform Continuity

§ 3.2 gave pointwise continuity. Now we need its *strengthening*, the notion on which the whole second half of the chapter will stand.

Pointwise continuity lets $\delta$ depend on the point: each $x$ has its own neighborhood. For the two great theorems of analysis this is not enough; they need a *single scale*, one $\delta$ fit for the whole interval at once. This requirement is what singles out *uniform* continuity: a function is uniformly continuous on $[a,b]$ if for every required precision $\varepsilon$ one can indicate *one* $\delta$ such that any pair of arguments of the interval less than $\delta$ apart gives values less than $\varepsilon$ apart. In Rocq this is written as follows:

```coq
Definition uniformly_continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall eps : Q, eps > 0 -> exists delta : Q, delta > 0 /\
    forall x y : Q, a <= x <= b -> a <= y <= b ->
      Qabs (x - y) < delta -> Qabs (f x - f y) < eps.
```

The whole difference from the pointwise continuity of § 3.2 lies in the *order of quantifiers*. There, $\delta$ stood *inside* the quantifier over the point: “for each point, its own $\delta$.” Here, $\delta$ is moved *outside*, in front of the quantifier over $x$ and $y$: one $\delta$ for the whole interval. Swap two quantifiers, and a fundamentally different, stronger property results: a single scale at which the function behaves tamely everywhere on $[a,b]$ at once.

One honest word must be said about this notion, about its *status* in our construction. The canonical head file of the theory of continuity now exists: `analysis/Continuity.v`. It brings together the definitions `continuous_on`, `uniformly_continuous_on`, and `Lipschitz_on` (for $f\colonℚ\toℚ$ on an interval $[a,b]$), proves the bridge `lipschitz_uniform` (the Lipschitz property implies uniform continuity) and the passage `uniformly_continuous_pointwise`, and, together with them, elementary algebra (constant, identity, sum)—all without axioms. The honest caveat, however, is twofold. First, *migration*: the existing great theorems—`IVT_ERR.v`, `EVT_ERR.v`, `EVT_idx.v`, `HeineBorelComplete.v`—have *not* yet been moved onto this head file: each still carries its own local, verbatim repeated definition of `uniformly_continuous_on`, and reducing them to the canon has been postponed (so as not to set off a cascade of edits in what has already been proved). Second, the canon contains no reverse passage, from pointwise continuity to uniform continuity, and this is no omission: over $ℚ$ it is false (the Cantor–Heine theorem, to which the chapter turns below). So the head file sets the canon and the Lipschitz path to uniformity, but it will become a unified theory on which *all* theorems of the chapter rely only after the migration.

### Cantor–Heine Fails over Q

Now comes the central fact of the chapter. And it has to be presented as directly as the failure of Heine–Borel was presented in § 2.5.

**Over $ℚ$, pointwise continuity on a closed interval *does not imply* uniform continuity. The classical Cantor–Heine theorem is false over $ℚ$.**

The classical Cantor–Heine theorem asserts that a function pointwise continuous on a closed bounded interval is automatically *uniformly* continuous on it. Over the real numbers this is so. Over the rationals it is not.

The root is the same as that of the failure of Heine–Borel in § 2.5: the *incompleteness* of $ℚ$. The classical proof of Cantor–Heine relies on the compactness of the interval in the full sense: from any cover by local $\delta$-neighborhoods a finite subcover is extracted, and the minimum of the finite collection of $\delta$ gives the required global $\delta$. Over $ℚ$ this move does not go through. The rational interval is not compact in the classical sense (§ 2.5): a cover can “leak” into an irrational gap, and the local $\delta$, shrinking toward the gap, give no positive minimum. Pointwise continuity remains, but there is nothing with which to pull it together into uniform continuity.

This is a *mathematical fact* about $ℚ$, not a defect of the formalization: a direct continuation of what Chapter 5.2 established about compactness. The rational line is full of holes, and the holes obstruct uniformity just as they obstructed the finite subcover.

This fact has a simple, quite tangible face: a concrete example. Take the function

$$
f(x) = \frac{1}{x^2 - 2}
$$

on the rational interval $[1,2] \cap ℚ$. For every rational $x$ the denominator $x^2 - 2$ is nonzero—$\sqrt{2}$ is irrational, and no rational square equals two—so the function is defined and pointwise continuous at every point of the interval. But it is *not* uniformly continuous. Rational points can approach the irrational cut $\sqrt{2}$ arbitrarily closely, and near the cut itself the values of $f$ grow without bound. For such a function there is no single $\delta$ fit for the whole rational interval at once: the closer to $\sqrt{2}$, the smaller the neighborhood has to be taken. This is the concrete face of the incompleteness of $ℚ$: local continuity is present at every point, while global uniformity is absent, because the interval is full of holes and the function makes use of a hole.[^3]

### A Constructive Replacement: The Lipschitz Property

If the bridge “continuity $\Rightarrow$ uniformity” has collapsed over $ℚ$, another path to uniform continuity is needed—one that holds over $ℚ$ without relying on completeness. ToS lays down such a path, and it leads through the *Lipschitz property*.

A function is *Lipschitz* with constant $L$ if the distance between values does not exceed $L$ times the distance between arguments: $|f(x) - f(y)| \le L |x-y|$. Uniform continuity follows from this property by direct calculation. Indeed: let $\varepsilon$ be given; take $\delta = \varepsilon / L$ (for $L > 0$); then for every pair of arguments closer than $\delta$ we have $|f(x) - f(y)| \le L |x-y| < L \cdot \varepsilon/L = \varepsilon$. A single $\delta$, fit for the whole interval at once, is *computed* from $\varepsilon$ and $L$, not picked at random. The degenerate case $L = 0$, a constant function, is simpler still: any $\delta$ will do. This derivation is formalized in `HeineBorelComplete.v` (the chapter met this file in § 2.6) by the theorem:

```coq
Theorem lipschitz_uniform_cont : forall f a b L,
  Lipschitz_on f a b L ->
  uniformly_continuous_on f a b.
```

Here is the meaning of this replacement. Over $ℝ$ the path to uniform continuity went like this: continuity $\Rightarrow$ (by Cantor–Heine) uniformity. Over $ℚ$ the first arrow is broken. But there is a detour: Lipschitz property $\Rightarrow$ uniformity—and this path is constructive; it does not depend on completeness. Where the classical picture uses an implication unprovable over $ℚ$, ToS uses a provable one: the Lipschitz property is a checkable, computable property, and uniform continuity follows from it by direct calculation.

And around this bridge stands the same algebra that surrounded pointwise continuity in § 3.2. The sum, scaling, and composition of uniformly continuous functions are again uniformly continuous, and the identity and constants are uniformly continuous: the class of uniformly continuous functions is just as closed and rich as the class of continuous ones. These closures are confirmed in `HeineBorelComplete.v` by the lemmas `uniform_cont_sum`, `uniform_cont_scale`, `uniform_cont_composition`.

### Why the Theorems of Analysis Require Uniform Continuity

Now it is clear why both main theorems of the chapter—the intermediate value theorem (§ 3.4) and the extreme value theorem (§ 3.6)—are formalized with the hypothesis of precisely *uniform* continuity.

This is a direct consequence of § 3.3.2. Over $ℝ$ one could state these theorems with the hypothesis of pointwise continuity and obtain uniformity along the way, from Cantor–Heine. Over $ℚ$ this cannot be done: Cantor–Heine does not hold. Hence the uniformity that the proofs *really need* (a single $\delta$ is needed for the estimates to work over the whole interval at once) has to be required *explicitly*, that is, put into the hypothesis of the theorem. In the terms of the analysis of § 3.2.4, this is a strengthening of the rule: over $ℚ$ the constitution of continuity requires the uniform form.

And this, by the logic of all of Part V, is precision, not weakness. A theorem honestly stated over $ℚ$ is obliged to carry in its condition exactly what its proof stands on. The hypothesis `uniformly_continuous_on` in the formulations of the IVT and the EVT is an exact indication of the level—here is the condition under which the theorem holds over $ℚ$—and no superfluous precaution. When in § 3.4 and § 3.6 the chapter reads the signatures of the main theorems, this hypothesis will stand there for a reason: it was put there by the incompleteness of $ℚ$.

## The Intermediate Value Theorem: Bisection

### The Idea of the Theorem

The first great theorem of the chapter is the intermediate value theorem. The classical formulation is simple and vivid: if a continuous function $f$ has values of different signs at the endpoints of an interval—$f(a) < 0$ and $f(b) > 0$—then somewhere between $a$ and $b$ it vanishes. A continuous function cannot jump over zero without touching it.

The classical picture says: *there exists a point* $c$ with $f(c) = 0$. ToS, by $P4$, says it differently. A completed point $c$ may not exist: the root may turn out to be irrational, and there is no irrational number in $ℚ$. Therefore ToS builds a *process* rather than a point: an algorithm that, step by step, localizes ever more precisely where the function crosses zero. The root is the process itself, not its unattainable limit. How exactly we build this process is the subject of the next subsection; the construction is fully formalized in the file `IVT_ERR.v` (424 lines, twenty-three proved theorems, not a single open gap).

### The Bisection Algorithm

We build the process that localizes the root by *bisection*, division in half. The idea is simple. The sign change is locked inside the interval $[a,b]$; let us divide the interval in two and see in which half it is locked now. The sign of the function at the midpoint of the interval decides: if $f$ is negative at the midpoint, the sign change has moved into the right half; if it is non-negative, into the left one. We take the half where the sign change remains and repeat. The interval shrinks by half at each step, and the sign change at its endpoints is not lost.

To formalize this, let us describe the *state* of the process—the pair of endpoints of the current interval—and the *step* that takes a state to a state:

```coq
Record BisectionState := mkBisection { bis_left : Q; bis_right : Q }.

Definition bisection_step (f : ContinuousFunction) (s : BisectionState)
  : BisectionState :=
  let mid := (bis_left s + bis_right s) / 2 in
  if Qlt_le_dec (f mid) 0
  then mkBisection mid (bis_right s)
  else mkBisection (bis_left s) mid.
```

This is how `IVT_ERR.v` writes one step of bisection. `mid` is the midpoint; `Qlt_le_dec` checks the sign of $f$ at it; depending on the sign, the new state becomes the right half $[\text{mid}, \text{right}]$ or the left half $[\text{left}, \text{mid}]$, exactly the half in which the sign change has been preserved.

One thing is essential here: `Qlt_le_dec`. This is a *decision procedure*: for rational numbers the question “$f(\text{mid}) < 0$ or $f(\text{mid}) \ge 0$?” is decided by *computation*, in finite time, without any appeal to the Law of Excluded Middle. The choice of a half is constructive here—and this is how the bisection of the IVT differs from the bisection of Bolzano–Weierstrass (§ 2.7), where the choice of an inhabited half was *not* computed and required $L3$.

The bisection step is built; now it has to be repeated and the result assembled into a process. Applying the step $n$ times to the initial interval $[a,b]$ and taking the midpoint of the resulting interval, we obtain the $n$-th approximation of the root. The sequence of these midpoints is the process we seek, the root localizer. In `IVT_ERR.v` the iteration of the step and the process itself are written as follows (`bisection_iter` applies the step $n$ times, `bisection_process` outputs the midpoint):

```coq
Definition bisection_process (f : ContinuousFunction) (a b : Q)
  : RealProcess :=
  fun n => let s := bisection_iter f (mkBisection a b) n in
           (bis_left s + bis_right s) / 2.
```

At step $n$ the process outputs the midpoint of the $n$-th nested interval: a rational approximation of the root, the more precise the larger $n$ is.

### Width and the Cauchy Property

For the sequence of midpoints to be a *meaningful* approximation of the root, the nested intervals must contract to a point; otherwise the “approximation” approximates nothing. Let us make sure that they contract, and establish that the process of midpoints is a Cauchy process.

Each bisection step divides the interval exactly in half; hence after $n$ steps the width of the interval is exactly $(b-a)/2^n$. This is established by the lemma `bisection_width`. Then the Archimedean property of $ℚ$ comes into play: the quantity $(b-a)/2^n$ becomes smaller than any quantity given in advance after a finite number of steps. And since the intervals are nested and their width tends to zero, the midpoints draw together: for every precision there is a step after which all midpoints lie closer together than required, that is, the process of midpoints is a Cauchy process. This derivation is confirmed in `IVT_ERR.v` by the lemmas `bisection_shrinks` and `bisection_is_Cauchy`. The bisection process is a full-fledged Cauchy process in the sense of Chapter 5.1; its rate of convergence is $1/2$ per step.

### The Weak Sign Invariant

For bisection to work, the sign change must be preserved at the endpoints of each nested interval. Let us ask precisely: *which* invariant can we prove here?

One would naturally expect a *strict* invariant: at the endpoints of each interval, $f(\text{left}) < 0$ and $f(\text{right}) > 0$. But the strict invariant is *unprovable* over $ℚ$, and here is why. The midpoint of an interval is a rational number; $f$ is a function $ℚ \to ℚ$. It may well happen that $f(\text{mid})$ turns out to be *exactly equal* to zero: for a rational function this is a possible case, not an exception. If this happens, $f$ vanishes exactly at the new endpoint of the interval, and the strict inequality fails there.

Hence the provable invariant is a *weak* one: $f(\text{left}) \le 0$ and $f(\text{right}) \ge 0$, with non-strict inequalities. And this is quite enough. If at some midpoint $f$ has become exactly zero, so much the better: the root has been found literally; and if not, the weak invariant keeps squeezing the sign change between the endpoints. It is precisely the weak invariant that the theory needs, and it is precisely this invariant that `IVT_ERR.v` proves, under the name `bisection_preserves_signs_weak`; the word *weak* in the name is there for a reason. The weak formulation is an exact accounting of the fact that over $ℚ$ a function can hit zero exactly, not carelessness.

### The Main Theorem

All the parts are assembled: bisection builds nested intervals, their width tends to zero, the process of midpoints is Cauchy, and the weak invariant holds the sign change. Putting them together, we obtain the intermediate value theorem; in `IVT_ERR.v` it is written as follows:

```coq
Theorem IVT_process : forall (f : ContinuousFunction) (a b : Q),
  a < b -> uniformly_continuous_on f a b ->
  f a < 0 -> f b > 0 ->
  exists c : RealProcess, is_Cauchy c /\ in_interval a b c /\
    equiv (apply_to_process f c) (fun _ => 0).
```

Let us read it carefully: there are two points of precision here at once.

*First, the hypothesis.* The condition contains `uniformly_continuous_on`, uniform continuity, not pointwise continuity. This is exactly what § 3.3.4 spoke about: over $ℚ$ Cantor–Heine does not hold, and uniformity—what the proof really needs (a single $\delta$, so that the estimate $|f(\text{mid}) - f(\text{left})|$ works at any step)—has been put into the hypothesis explicitly.

*Second, the conclusion.* The theorem gives not “a point $c$ with $f(c) = 0$” but a process $c$—a Cauchy process lying in $[a,b]$—for which `equiv (apply_to_process f c) (fun _ => 0)`. This means that the process of values $f(c)$ is *equivalent to the zero process*. Not “$f(c)$ is literally zero,” but “the process $f(c)$ is arbitrarily close to zero.” The difference is one of principle and again comes from $P4$: a literal root over $ℚ$ may not exist (it is irrational), but a process whose values under $f$ indistinguishably approach zero *exists* and *has been built*: it is the bisection itself.

And, as agreed in § 3.1, a word about the basis. The proof relies on the Archimedean property of $ℚ$ and, through it, on `classic`, an axiom that comes into the file from `Archimedean_ERR`. As agreed, `classic` is the technical Rocq implementation of $L3$. Appealing to it is an explicit accounting of the level. The choice of a half itself, let us note, is constructive (`Qlt_le_dec`); $L3$ is needed not for the choice but in the Archimedean part of the argument.

## The IVT on Three Levels

### One Fact, Three Heights of Typing

The intermediate value theorem is formalized in ToS *three times*—not out of repetition, but because one and the same mathematical fact can be written at different *heights of typing*. Three files—`IVT_ERR.v`, `ProcessIVT.v`, `IVT_CauchyReal.v`—give three levels. § 3.4 examined the lowest; now come the two upper ones.

### The Level of the Process

On the first level the root was a `RealProcess`: a function $ℕ \to ℚ$, a bare sequence of rational numbers to which the Cauchy property is *attached* by a separate lemma. To raise the result to the level of *processes* in the sense of `ProcessCore`—the apparatus on which all of Part V stands—means to rewrite the theorem in its language. This is what the second level does.

The main work here is to build *compatibility bridges*. The snag is technical: the Cauchy property is defined in two slightly different ways. `Archimedean_ERR`, where the bisection came from, formulates it through the condition $(m > N)$; `ProcessCore` formulates it through $(N \le m)$. The conditions are equivalent—up to a shift of $N$ by one—but formally they are different predicates, and before carrying the theorem over, one has to prove their equivalence. Having proved it, we obtain the bridges: `cauchy_compat` (the Cauchy properties coincide), `interval_compat` (the definitions of “lying in $[a,b]$” coincide), `equiv_compat` (the definitions of equivalence of processes coincide). Along these bridges the intermediate value theorem is rewritten in the types of `ProcessCore` as `process_IVT`, and `ivt_convergence_rate` fixes the rate, $1/2$. All this is the content of the file `ProcessIVT.v` (175 lines).

There are no new mathematical difficulties at this level: bisection and its convergence have already been proved, and here there is only a careful joining of the theorem to the process language of ToS. Nor does this level bring in axioms of its own: it inherits `classic` from `IVT_ERR`, adding nothing to it.

### The Level of the Type: The Root as a CauchySeq

The third level, `IVT_CauchyReal.v` (382 lines), takes a subtler step. On the first two levels the root was a sequence, and the Cauchy property was a separate statement about it. Here the root is presented as an object of type `CauchySeq`, a type into which the Cauchy property is *built in*. It is no longer necessary to carry the proof of the Cauchy property around separately: it has become part of the object itself.

```coq
Theorem ivt_cauchy_real :
  forall (f : ContinuousFunction) (a b : Q),
    a < b -> uniformly_continuous_on f a b ->
    f a < 0 -> f b > 0 ->
    exists c : CauchySeq,
      (forall n : nat, a <= cs_seq c n /\ cs_seq c n <= b) /\
      (forall eps : Q, 0 < eps ->
        exists N : nat, forall n : nat,
          (N <= n)%nat -> Qabs (f (cs_seq c n)) < eps).
```

The root is `c : CauchySeq`: not “a sequence about which it has been proved that it is Cauchy,” but an object whose *type membership* already carries the proof of the Cauchy property.

The lemma essential for this level is `continuous_compose_cauchy`. It asserts that if $f$ is uniformly continuous and $c$ is a Cauchy sequence in $[a,b]$, then the composition $f \circ c$ is again Cauchy. Uniform continuity *preserves* the Cauchy property. And here again one sees why precisely uniform continuity is needed, not pointwise continuity: a common $\delta$ makes it possible to infer the closeness of the terms of $f \circ c$ from the closeness of the terms of $c$ *uniformly*, without picking $\delta$ anew for each point. The main theorem `ivt_cauchy_real` and its corollary `ivt_cauchy_real_equiv` (which expresses the result through `cauchy_equiv` with the constant zero) stand on this lemma.

### What the Three Levels Are For

It is worth saying why one fact is written three times. The point is *intensional precision*, the principle $P3$, not redundancy.

The three levels are three answers to the question “what is a root.” At the level of `IVT_ERR` it is a bare sequence plus a separate certificate of its Cauchy property. At the level of `ProcessIVT` it is a process in the sense of `ProcessCore`, built into the general apparatus of Part V. At the level of `IVT_CauchyReal` it is an object in whose *type* the Cauchy property is already written. The mathematical content—bisection converging to the sign change—is one. But *how the object is given*, *what it is intensionally*, changes from level to level. By $P3$ this means precisely that we have before us three different, though agreeing, representations of one fact. ToS builds a ladder of typing, and the intermediate value theorem is written out on each of its rungs. In the terms of the analysis of § 3.2.4, these are three role-representations of one root, different in type and agreeing in content ($P3$).

## The Extreme Value Theorem: The Grid

### The Idea of the Theorem

The second great theorem of the chapter is the extreme value theorem. The classical formulation: a continuous function on a closed interval attains its maximum on it—there is a point $x^*$ at which $f(x^*)$ is not less than all the other values.

And again ToS reads “attains” by $P4$. A completed point of maximum may not exist: $x^*$ may turn out to be irrational. Therefore the maximum is built as a *process*: a sequence of ever more detailed approximations. But here, unlike in the intermediate value theorem, there turn out to be *two* processes, and they behave differently. This is the crucial point of precision of the section, and § 3.6.3 will return to it separately.

The supporting files of the EVT are three: `EVT_ERR.v` as the historical argmax version, `EVT_idx.v` as the current recommended index version, and the process wrapper `ProcessEVT.v`. In § 3.6 we will explain the general construction, the grid and the process of values; in § 3.7 we will examine why the current main version is precisely `EVT_idx.v`.

### The Grid

The instrument of the extreme value theorem is the *grid*, not bisection. Bisection suited the root: the sign of the function at the midpoint *indicated* which half to take. For the maximum there is no such indicator: the maximum can hide anywhere on the interval. Therefore we seek the maximum differently: we place a finite uniform set of test points on the interval, compute $f$ at all the nodes, take the largest value, and then *refine* the grid by adding nodes. The denser the grid, the more precisely the largest value over the nodes approximates the true maximum.

A grid node is built by a direct formula: the $k$-th of the $n+1$ equally spaced nodes of the interval $[a,b]$ is $a + \frac{k}{n}(b-a)$. In Rocq this is written as follows:

```coq
Definition grid_point (a b : Q) (n k : nat) : Q :=
  a + (inject_Z (Z.of_nat k)) * (b - a) / (inject_Z (Z.of_nat n)).
```

For $k = 0$ this is $a$, for $k = n$ it is $b$, and in between are uniform nodes; `grid_list` collects them into a finite list. Refinement is the growth of $n$: at step $n$ the grid is the denser, the larger $n$ is.

And here it is worth noting $P4$ at work. The process of searching for the maximum unfolds infinitely, but every *snapshot* of it is a finite, surveyable list of nodes, on which $f$ is computed in a finite number of operations. There is no completed infinity; at every step there is an actually finite grid.

### Value versus Position

Now comes the crucial point of precision of the whole section. On the grid the maximum has *two* aspects, and over $ℚ$ they behave *differently*.

The *value* of the maximum is `max_on_grid`, the largest of the values of $f$ over the grid nodes. The *position* of the maximum is `argmax`, the node at which this largest value is attained. As the grid is refined, both would seem bound to converge. But this is not so.

The *process of values*, `sup_process`, converges. The file proves `sup_process_is_Cauchy`: the sequence of largest values over ever denser grids is a Cauchy process.

The *process of positions*, `argmax_process`, is *not bound* to converge. And `EVT_ERR.v` states this directly in a comment. Imagine a constant function: $f(x) = 1$ everywhere. Then the largest value is attained *at every* node of the grid. Without a fixed rule of choice, the “position of the maximum” is not uniquely defined here at all: under different admissible choices it can jump from node to node at each refinement. The process of values meanwhile converges impeccably: it is simply constant and equal to one.

The index version (§ 3.7) introduces exactly such a rule, the $L5$ order of positions, to make the position deterministic at each step. But determinism is not enough either: even with a uniquely chosen position, the process `argmax_process` over $ℚ$ need not be Cauchy. The maximum may approach an irrational point, and then the process of rational approximations of the position does not reduce to a Cauchy process; or the position may jump from one side to the other as the grid is refined. The process of values is free of all these troubles.

The conclusion that the chapter must state directly: over $ℚ$, the extreme value theorem proves the convergence of the *process of values*, not of the process of positions. By $P4$ this is the right reading of “maximum”: the process of the value of the supremum is fundamental; the position is a derivative, more fragile notion that requires additional structure (isolation of the maximum), which in general is absent. In the terms of the analysis of § 3.2.4, we have before us a splitting of the *role*: value and position are two roles of the maximum, and over $ℚ$ only the first is Cauchy-stable.

### The Main Theorem

Putting together the grid, the process of largest values, and its properties, we obtain the extreme value theorem. In `EVT_ERR.v` it is written as follows:

```coq
Theorem EVT_complete : forall f a b,
  a < b -> uniformly_continuous_on f a b ->
  exists (M : RealProcess) (c : RealProcess),
    is_Cauchy M /\
    (forall n, a <= c n <= b) /\
    (forall n, apply_f f c n == M n) /\
    (forall x, a <= x <= b -> process_le (fun _ => f x) M).
```

The theorem gives two processes: $M$, the process of values of the supremum, and $c$, the process of approximate maximizers. It asserts that $M$ is a Cauchy process; that $c$ lies in $[a,b]$; that at each step $f(c)$ coincides with $M$; and that $M$ *dominates* $f$: the value of $f$ at any point of the interval does not exceed $M$ (up to the process $\le$). The hypothesis is again `uniformly_continuous_on`, uniform continuity, for the reason given in § 3.3.4.

And here honesty requires us to note what is *absent* from this formulation compared with what one would like to prove. Looking at § 3.6.3, one would naturally expect the conclusion to contain the Cauchy property for the process of positions $c$ as well. It is not there, and in such a general formulation it should not be: the maximization problem by itself does not guarantee the Cauchy property of the process of positions. With a plateau or several equally good maxima, the choice of position requires an additional rule; without it, the positional process may turn out to jump around. Therefore the formulation had to be *weakened*, leaving the Cauchy property only to the process of values $M$. It is precisely this—the convergence of $M$ and its dominating property—that is the honest content of the extreme value theorem over $ℚ$; and it is precisely so that `EVT_complete` is formulated in the repository (the comment of the file notes this weakening directly). The chapter does not pass off `EVT_complete` as the full classical theorem: it is its repaired, weakened—and therefore *true*—form.

## The EVT: The Argmax Version, the Index Version, the Wrapper

### Two Versions of the Main File

The extreme value theorem is formalized in the repository *twice*, and these two formalizations must be discussed directly, because one of them ran into a difficulty and the other got around it.

The first formalization is `EVT_ERR.v`, the argmax version. Today it is the *historical* version: its header carries the note *“DEPRECATED: Use EVT_idx.v instead”*, and it is not the one recommended for use. The trace of the difficulty for whose sake the version was replaced is visible inside the file as well: one lemma, `max_list_attained`, breaks off with the command `Abort`; it could not be proved in the intended form, and the workaround `max_list_attained_classical` was put to use. We do not hide this `Abort`: it is the very evidence that the argmax version ran into a wall.

The second formalization, `EVT_idx.v`, gets around this wall, and it is also today’s recommended, main version. To understand why the change of version was needed, let us examine what the difficulty consisted of and what its solution is.

### The Index-Based Solution

The difficulty of the argmax version is subtle but telling. It lies in the difference between two equalities of rational numbers. There is equality *by value*, `Qeq`: the numbers $1/2$ and $2/4$ are equal as rationals. And there is *literal*, Leibniz equality: $1/2$ and $2/4$ are different *expressions*, different representations. The grid node `grid_point a b n 0` equals $a$ *by value* (`Qeq`) but not literally: these are different terms. The argmax version, choosing the maximum by values, kept stumbling over this gap: the proofs that the maximum *is attained* got bogged down in reconciling `Qeq` with Leibniz equality.

`EVT_idx.v` gets around this difficulty by a switch of attention—and the device deserves to be named directly: instead of the value of the best node, argmax returns its *number*, its index in the list. Not “which value is the largest,” but “at which place it stands.” In Rocq this is written as follows:

```coq
Definition argmax_idx (f : Q -> Q) (l : list Q) (default : Q) : nat :=
  match l with
  | [] => O
  | x :: xs => find_max_idx_acc f xs 1%nat O (f x)
  end.
```

`find_max_idx_acc` is an accumulator traversal of the list that returns the index of the best node; `max_on_grid` is then defined as $f$ of the node standing at this index. The gain is immediate. The lemma “the maximum on the grid is attained,” `max_on_grid_attained`, becomes *trivial* in the index version: it is proved by the single word `reflexivity`. The attainment of the maximum is *definitional* here—the maximum is, by construction, $f$ of the node at the found index—and there is no longer anywhere to reconcile `Qeq` with Leibniz equality. Indices are natural numbers, and their equality has no subtleties. Thus the switch from value to position removes the difficulty into which the argmax version ran.

### L5 and the Status of argmax

With the transition to indices, a deeper question also becomes clear: what is a “position of the maximum” at all, when the maximum is attained at more than one point? Let us examine it; the answer rests on a law of logic of ToS, and the same answer is recorded in a comment of `EVT_idx.v`.

Imagine a *plateau*: on the grid several nodes give one and the same largest value, $f(x_1) = f(x_2) = f(x_3) = M$. Which of them is the “argmax”? The naive answer is that “the tie has to be broken,” the choice completed by some external rule. It is more precise to put it otherwise. $L5$, the Law of Order of ToS, is at work here. $L5$ constitutes the order of positions; and we *define* the “argmax” through this order, as the *distinguished $L5$-position* attaining the maximum: the position selected by a fixed order of traversing the grid. On a plateau the role of “argmax” is assigned by $L5$ because $L5$ itself sets the order in which the nodes are considered, not as “tie-breaking” by an external rule. There is no tie: the order $L5$ distinguishes a position, and the well-ordering of natural indices makes the choice unambiguous. No external information is added: the structure is taken from the law of order itself.

Let us specify what “distinguished” means—and here one should be attentive when reading the code. In the accumulator `find_max_idx_acc`, nodes are compared through `Qle_bool`, and the best index is updated *on equality* of values. If the grid is enumerated from left to right, one position will be distinguished; if the list implements the reverse order or updates differently on equality, another. What matters, therefore, is the *absence of an arbitrary external choice*, not “the leftmost first” as such: the “argmax” is determined by the order $L5$, by whatever concrete order of enumerating the nodes this $L5$ priority may be implemented. It is precisely the index version that makes the choice deterministic; for full transparency one need only keep in mind which order of traversing the grid this priority embodies.

The result of the section `EVT_STRONG` of the file is the theorem `EVT_strong_process`: the process of values of the supremum is Cauchy, the process of positions lies in $[a,b]$, and at each step the value of the supremum coincides with $f$ of the position. This is the same honest content as in `EVT_complete` (§ 3.6.4): convergence is proved for the process of *values*; as for the process of positions, the comment of `EVT_idx.v` directly repeats that over $ℚ$ it need not be Cauchy and its limit may turn out to be irrational.

### The Process Wrapper

The third file, `ProcessEVT.v` (133 lines), plays the same role as `ProcessIVT.v` does for the intermediate value theorem: a thin wrapper that carries the result over into the process language of `ProcessCore`. Cauchy-compatibility bridges (`evt_cauchy_
compat`), `sup_process_cauchy`, `process_EVT`;
`evt_convergence_rate` fixes the rate, $1/2$.

Here one caveat about consistency matters. `ProcessEVT.v` wraps precisely the layer of `EVT_ERR.v`: it imports the *historical* argmax version, not the new index version `EVT_idx.v`. Therefore `ProcessEVT.v` should be read as a process adaptation of the historical formulation of the extreme value theorem. And for the question of the attainment of the maximum on the grid and for resolving the difficulty of “`Qeq` versus Leibniz equality,” the main file remains `EVT_idx.v`.

And the last point of precision for the section, as agreed in § 3.1. The file `EVT_idx.v` has a peculiarity with respect to axioms: it *imports* `ToS_Axioms` and at the same time *declares* `Axiom classic` *once more* locally, inside the file itself. In substance this is the same $L3$, the Law of Excluded Middle: *by design* both instances of `classic` are one and the same technical Rocq implementation of a law of logic of ToS. But *technically* the file declares $L3$ as a *separate local axiom*, and when reading `Print Assumptions` this dependence should be counted precisely as a local declaration, not automatically as the same object from `ToS_Axioms.v`. The chapter notes this as a peculiarity of the file; it does not affect the status of the proof, since, as agreed in § 3.1, the appeal to $L3$ is an explicit accounting of the level.

## The Uniform Limit, Connections, and the Summary of the Chapter

### The Uniform Limit of Continuous Functions

There remains the last topic of the chapter, and it answers a natural question: is continuity *preserved* under passage to the limit? If a sequence of continuous functions converges to something, will the limit be continuous?

The answer depends on the *kind* of convergence—and here, as already with continuity in § 3.3, we will have to distinguish the pointwise and the uniform. The convergence of a sequence of functions $f_n$ to a function $f$ can be *pointwise*: at each point $x$ separately, the values $f_n(x)$ converge to $f(x)$. And it can be *uniform*: the index $N$ after which $f_n$ is already indistinguishably close to $f$ is one for the whole interval at once. Uniform convergence on $[a,b]$ is written as follows:

```coq
Definition uniform_converges (fn : fun_seq) (f : Q -> Q) (a b : Q)
  : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> forall x : Q, a <= x -> x <= b ->
        Qabs (fn n x - f x) < eps.
```

And here is the same swap of quantifiers that distinguished uniform continuity from pointwise continuity (§ 3.3). In uniform convergence the index $N$ is moved *outside*, in front of the quantifier over the point: after step $N$ all the functions $f_n$ lie closer than $\varepsilon$ to $f$ at all points at once. This, and only this, is enough for continuity to survive the passage to the limit:

```coq
Theorem uniform_limit_continuous_on :
  forall (fn : fun_seq) (f : Q -> Q) (a b : Q),
    uniform_converges fn f a b ->
    (forall n : nat, continuous_on (fn n) a b) ->
    continuous_on f a b.
```

*The uniform limit of continuous functions is continuous.* If all $f_n$ are continuous on $[a,b]$ and converge to $f$ uniformly, then $f$ is continuous as well. The proof is the classical “$\varepsilon/3$” trick: the distance $|f(x+h) - f(x)|$ is split into three parts—from $f$ to a nearby $f_n$, from $f_n(x+h)$ to $f_n(x)$ by the continuity of $f_n$, and back from $f_n$ to $f$—and each part is made less than $\varepsilon/3$. This is a full-fledged substantive theorem about continuity, and it completes the conceptual line of the chapter: continuity is not only defined and furnished with two great theorems but is also stable under uniform passage to the limit.

One honest caveat about boundaries. The file `UniformConvergence.v` is broader than this one theorem: it also contains the interchange of limit and integral, the interchange with the derivative, and Dini’s theorem. But these topics rest on integration and differentiation, an apparatus that Part V builds *later*. Chapter 5.3 takes from `UniformConvergence.v` only what pertains to continuity proper: the definition `continuous_on` and the theorem on the uniform limit. The interchange of the limit with the integral and the derivative is material for one of the following chapters of Part V.

And, as agreed in § 3.1, a word about axiom status. The header of the file `UniformConvergence.v` declares that the file *as a whole* imports the classical layer: `classic` comes into it through adjacent results on monotone convergence and differentiation. The proof of `uniform_limit_continuous_on` itself has the standard $\varepsilon/3$ form. However, without a separate `Print Assumptions` check of precisely this theorem, the chapter does not assert its axiomatic purity, by the audit rule established back in Chapter 4.6: axiom status is established by the `Print
Assumptions` of a *concrete* theorem, not ascribed to it from the file header.
Therefore the chapter uses `uniform_limit_continuous_on` as a working result on uniform limits and leaves the judgment about its axiomatic purity to that check.

### An Adjacent Stub: Maps of Processes

For the map to be complete, one more file is worth mentioning: `ProcessContinuity.v`. Its name promises a theory of continuity, but its content is different, and it is more honest to say so directly. The file is small (36 lines) and speaks not of the continuity of functions $ℚ \to ℚ$ but of *maps of processes*, maps $\texttt{RealProcess} \to \texttt{RealProcess}$. It introduces `process_map_lipschitz` (the Lipschitz property of such a map) and `process_contraction` (contraction), notions that belong to the future line of fixed points, not to the present chapter. Its theorem with the grand name `continuity_foundation`, like the namesake “foundation” theorems of Chapter 5.1, is honestly only a *conjunction of two trivial lemmas* (the identity map is Lipschitz with constant $1$, a constant map with constant $0$). `ProcessContinuity.v` has no direct bearing on the theory of the continuity of functions; the chapter says so directly.

### What Has Been Built and What Is Being Prepared

The summary of the chapter comes as three lists, following the discipline of the honest mode of Part V.

**Built and checked.**

- The topological face of continuity over $ℚ$—the $\delta$-$\varepsilon$ definition (`continuous_at`, `continuous`, `continuous_on`), the algebra of continuous functions, the preimage of an open set is open; constructively, without axioms (`Topology.v`).
- Uniform continuity and the constructive bridge to it: `lipschitz_uniform_cont` (the Lipschitz property implies uniform continuity), with the algebra of uniformly continuous functions.
- The intermediate value theorem on three levels: the $\varepsilon$-version (`IVT_process`), the process wrapper (`process_IVT`), the type upgrade to `CauchySeq` (`ivt_cauchy_real`); the root is a bisection Cauchy process.
- The extreme value theorem in two versions: the historical argmax version `EVT_complete` is kept but marked as deprecated; the current recommended index-based version is `EVT_strong_process`. In both, the process of values of the supremum is Cauchy.
- The uniform limit of continuous functions is continuous (`uniform_limit_continuous_on`).

**What this rests on.**

- The topological face of continuity, on pure construction, without axioms (`Topology.v`).
- The intermediate value and extreme value theorems, on $L3$: `classic` comes into `IVT_ERR` through the Archimedean property, and into `EVT_ERR` and `EVT_idx` directly. This is an explicit accounting of the level, not a flaw: `classic` is the technical Rocq implementation of the Law of Excluded Middle of ToS.

**Not built in this chapter.**

- The Cantor–Heine theorem over $ℚ$: pointwise continuity on a closed interval *does not imply* uniform continuity; this is a mathematical fact, not a gap, and the reason is the incompleteness of $ℚ$.
- Convergence of the process of *positions* of the maximum: over $ℚ$, `argmax_process` need not be Cauchy; only the convergence of the process of *values* is proved.
- Migration of the theorems onto the head file: the canonical head file of the theory of continuity has been built (`analysis/Continuity.v`: the canon `continuous_on`, `uniformly_continuous_on`, `Lipschitz_on` and the Lipschitz bridge), but the existing theorems (IVT, EVT, HeineBorelComplete) have not yet been moved onto it; each carries its own local definition.
- Continuity of functions on the quotient classes `RealPoint`: the material of the chapter lives at the level of functions $ℚ \to ℚ$.

**Prepares next.** Uniform continuity and the Lipschitz property are the working apparatus for the next chapter of Part V, on the derivative; the intermediate value and extreme value theorems are instruments on which the differential calculus will rely; the interchange of the uniform limit with the integral and the derivative (the rest of `Uniform
Convergence.v`) is material for one of the following chapters.

### Summary of the Chapter

Chapter 5.3 has taken continuity from the $\delta$-$\varepsilon$ definition to the two great theorems of analysis. Its main lesson concerns the *two faces of continuity*. Over $ℚ$, pointwise and uniform continuity do not coincide: the Cantor–Heine theorem, which glues them together over $ℝ$, is false over $ℚ$—the same incompleteness that brought down Heine–Borel. Therefore both main theorems, on the intermediate value and on the extreme value, honestly carry precisely uniform continuity in their hypotheses, and both build a *process* rather than a classical “point”: a bisection converging to the sign change, and a refining grid whose values of the supremum form a Cauchy process.

*The summary of the chapter comes in three parts. First: what is built. The topological face of continuity over $ℚ$—the definition, the algebra of continuous functions, the preimage theorem—is built constructively, without axioms, within the file `Topology.v`. Uniform continuity is furnished with a constructive bridge—the Lipschitz property implies uniform continuity—in place of the Cantor–Heine theorem, which is unprovable over $ℚ$. The intermediate value theorem is proved on three levels of typing, the extreme value theorem in two versions; the uniform limit of continuous functions is continuous.*

*Second: what this rests on. The topological face of continuity rests on pure construction. The intermediate value and extreme value theorems rest on $L3$, the Law of Excluded Middle of ToS. The technical Rocq axiom `classic` is an implementation of $L3$; appealing to it is an explicit accounting of the level of a proof, not a departure from rigor.*

*Third: what remains open. The Cantor–Heine theorem is false over $ℚ$: this is a mathematical fact. The process of positions of the maximum over $ℚ$ need not be Cauchy; only the convergence of the process of values is proved. The canonical head file of the theory of continuity has been built (`analysis/Continuity.v`), but the migration of the existing theorems (IVT, EVT) onto it has been postponed for now. The chapter has given continuity and its two theorems; the derivative, which will stand on this basis, is the subject of the next chapter of Part V.*

---

[^1]: The E/R/R labeling in the header of the file `Topology.v`; here it is unfolded following the pattern of Part I.
[^2]: This role labeling comes from the headers of `ProcessIVT.v` and `ProcessEVT.v`.
[^3]: This example is now formally verified as well. For $f(x)=1/(x^2-2)$ on $[1,2]\capℚ$ both sides of the boundary are machine-established: pointwise continuity at every point of the interval (`cantor_heine_continuous`) and the *absence* of uniform continuity (`cantor_heine_not_uniform`); together they mean that the Cantor–Heine theorem is false over $ℚ$ (`cantor_heine_fails_Q`). The points approaching $\sqrt2$ are the rational approximations given by the Pell recurrence $x_k=p_k/q_k$ with the *exact* error $|x_k^2-2|=1/q_k^2$, at which $|f(x_k)|=q_k^2\to\infty$. Machine-checked, 11 Qed, 0 axioms.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/02 Topology and Compactness|Chapter 2. Topology and Compactness]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/04 Derivative|Chapter 4. The Derivative]] →
