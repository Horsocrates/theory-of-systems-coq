---
title: "Chapter 2. Topology and Compactness"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/02 Топология и компактность.md"
sourceBlob: c0a5b607126241b432db7924b82b618b3523b103
translated: 2026-10-20
status: draft
---

## From Metric to Topology

### What the Previous Chapter Built

Chapter 5.1 gave Part V its first analytic notion: distance. There appeared the metric on the rational numbers, the abstract metric space, distance as a process, and—at the very end—a first promise: open balls $B(P,\varepsilon)$ and the notion of “close processes.” The present chapter begins with this promise.

Having distance, we can build *topology*—the science of closeness, neighborhood, and shape. Topology answers questions that the metric only prepares. What does it mean that a set is “open,” that each of its points has a margin of free space around it? What does it mean that two points can be *separated*? What does it mean that a set is “connected,” that from any of its points one can get to any other without leaving the set? And—the central notion of the chapter—what does it mean that a set is *compact*?

### Two Layers of the Chapter: Topology and Compactness

The chapter falls into two layers, and it is more honest to state the difference between them at once, from the very beginning.

The first layer is *topology* proper: open and closed sets, separation, connectedness. Over $ℚ$ this layer is built *fully and constructively*. The supporting files of the topological layer—`Topology.v`, `ProcessTopOpen.v`, `ProcessTop\-
Connected.v`—use not a single axiom. Here ToS obtains topology “for free”: from the rational distance alone, without any additional assumptions.

The second layer is *compactness*: the Heine–Borel and Bolzano–Weierstrass theorems. And here the picture changes. Compactness is the place where the rational numbers *reveal their incompleteness*. Over $ℚ$ the classical Heine–Borel theorem is simply *false* (more on this in § 2.5), and the compactness theorems have either to be repaired or to be proved with the help of the *laws of logic* of ToS. The files of the compactness layer—`HeineBorel_ERR.v`, `BolzanoWeierstrass.v`—rely on $L3$ and, locally, on $L4$.

The chapter honestly keeps this boundary. It does not say “all of topology is built without axioms”: that would be untrue of the compactness layer. It says something more precise: the topological layer is constructive; the compactness layer relies on the laws of logic of ToS, and each such appeal is marked in place.

### On Axiom Status: The Technical and the Ontological

Here we need to agree on words; otherwise the second half of the chapter will sound more alarming than it should.

When the chapter says that a proof “uses the axiom `classic`” or “the axiom `L4_witness`,” it speaks of quite definite objects from the file `ToS_Axioms.v`. These objects are *technical Rocq axioms that implement the ontological laws of logic* of ToS, not foreign crutches or a concession to looseness. The axiom `classic` is $L3$, the Law of Excluded Middle, in the form in which Rocq accepts it. The axiom `L4_witness` is $L4$, the Law of Sufficient Reason.

The difference is one of principle. In purely constructive mathematics, the appearance of `classic` would be an admission of weakness: “we could not construct it here and had to postulate it.” In ToS this is *not so*. $L3$ and $L4$ are laws of logic of ToS, accepted at the level of the system itself (Part I). When a proof “uses `classic`,” it does not depart from rigor: it *explicitly takes into account* that it rests on a law of logic of ToS and is not derived from computational constructivity alone. The technical axioms of Rocq are exactly the bridge by which the ontological laws of logic enter formal verification.

Therefore, whenever the chapter marks an appeal to $L3$ or $L4$, this is an *honest accounting of the level*, not an alarm signal: the given argument rests on a law of logic, and the chapter says on which one. To distinguish “proved constructively” from “proved with support from a law of logic of ToS” is to show the structure of the proof rather than hide it.

### The Plan of the Chapter

The chapter goes from the simple to the difficult. First come open and closed sets over $ℚ$ (§ 2.2) and the process view of an open set as a process of covers (§ 2.3). Then separation: the Hausdorff property of $ℚ$ (§ 2.4). Next comes the central and most demanding section: compactness and the incompleteness of $ℚ$, the Heine–Borel theorem (§ 2.5). Then total boundedness and $\varepsilon$-nets, with a computational example (§ 2.6). Then Bolzano–Weierstrass, honestly examined together with its axiomatic basis (§ 2.7). And finally connectedness, the unification of the three faces of compactness, and the summary of the chapter (§ 2.8).

There are eleven supporting files—six main ones and five auxiliary process wrappers; all have been checked against the repository verbatim. The topological layer is axiom-free; the compactness layer has $L3$ and $L4$ explicitly accounted for.

## Open and Closed Sets over $ℚ${Q}

### The Open Ball and the Open Set

Topology begins with the notion of a *neighborhood*. And the simplest neighborhood can already be built from the material of Chapter 5.1: the *open ball*, the set of all points lying at less than a given radius from the center. We have the distance—that very rational $|x - c|$; the ball is defined by it at once. In Rocq this is written in the file `Topology.v` as follows:

```coq
Definition open_ball (center radius : Q) (x : Q) : Prop :=
  Qabs (x - center) < radius.
```

A point $x$ lies in the ball with center `center` and radius `radius` if the distance from $x$ to the center is strictly less than the radius. Everything is over $ℚ$: center, radius, and point are rational.

From the ball we grow the central notion of topology, the *open set*. We call a set open if each of its points has *a margin of free space*: a ball lying entirely inside the set. Wherever a point is located inside $S$, there is “air” around it—a ball that does not go beyond $S$. In Rocq:

```coq
Definition is_open (S : Q -> Prop) : Prop :=
  forall x, S x -> exists eps, 0 < eps /\
    forall y, open_ball x eps y -> S y.
```

A set $S$ is *open* if each of its points $x$ has a positive radius $\varepsilon$ such that the whole ball $B(x,\varepsilon)$ lies entirely in $S$.

We define a *closed* set through the open one, as the complement of an open set: $S$ is closed if the set of points *outside* $S$ is open. In Rocq this is a direct transcription:

```coq
Definition is_closed (S : Q -> Prop) : Prop :=
  is_open (fun x => ~ S x).
```

And finally, we call a set *bounded* if it fits entirely into some ball around zero.

### Nineteen Lemmas of Topology over Q

On these definitions we build the whole basic apparatus of point-set topology over $ℚ$—and we build it constructively, without once resorting to an axiom. The nineteen lemmas of `Topology.v` confirm every step; let us list the main ones.

*The ball is open.* An open ball is itself an open set: each of its interior points $y$ has a margin of free space—a ball of radius $r - |y-c|$, which by the triangle inequality does not go beyond $B(c,r)$. This is the lemma `open_ball_is_open`.

*The empty and the full sets are open.* Two degenerate but necessary cases: both the empty set and the whole of $ℚ$ are open (`empty_is_open`, `full_is_open`).

{
*The union and the intersection of two open sets are open.* Topology is closed under the two basic operations on sets; for the intersection, the margin of free space is taken as the smaller of the two margins. These are `union_two_open` and `intersection_two_open`.
}

{
*Intervals.* An open interval $(a,b)$ is an open set, and a closed interval $[a,b]$ is a closed one (`interval_open`, `closed_interval_closed`). These two facts support the whole future theory of compactness: it is precisely the *closed* interval that will turn out to be compact.
}

{
*Continuity.* Here we also introduce continuity—at a point (`continuous_at`) and everywhere (`continuous`)—and establish its stability: the identity and constants are continuous, the shift $x \mapsto x+c$ is continuous, and the sum, negation, and composition of continuous functions are continuous. We also prove the lemma that is key for topology, `continuous_preserves_open_preimage`: the preimage of an open set under a continuous map is open. This is the topological *definition* of continuity in an equivalent form; Chapter 5.3 will return to it in detail.
}

### Topology over Q, Not over Classes

One clarification, important for the whole chapter. Everything built in `Topology.v` is topology over the *rational numbers*. An open set here is a predicate `Q -> Prop`, a subset of $ℚ$; continuity is a property of functions $ℚ \to ℚ$.

This is *not* topology on the quotient classes `RealPoint`, those classes of equivalent processes by which Part IV defined the point. In the supporting files of *this* chapter, topology lives at the level of $ℚ$. But the *basis* of the metric topology on classes has already been carried over, in a separate file, `RealPointTopology.v`: it defines the open ball on classes `rp_in_ball` (the center is a point, the radius is rational) and proves its *well-definedness* on classes (`rp_in_ball_well_defined`: membership in the ball does not depend on the choice of representative), as well as `rp_in_ball_centre` (the center lies in its ball). The full theory of open and closed sets on classes, however, has not yet been carried over. The chapter will consistently distinguish the rational level and the level of classes: topology over $ℚ$ is a solid constructive foundation; on classes its metric basis has been built (the ball with well-definedness), while the full topology of classes is a direction of further work.

And let us note the main thing about the topological layer: `Topology.v` has nineteen lemmas and *zero axioms*. Open sets, closed sets, continuity, intervals—ToS obtains this whole apparatus purely constructively, from the rational distance alone. Axioms will appear later, when the chapter comes to compactness.

### E/R/R Analysis: Topology as a System

Topology is a system, and so the E/R/R methodology (Part I) applies to it: analysis into three aspects—Elements, Roles, Rules. Let us carry it out. As with the metric in Chapter 5.1, the analysis imposes nothing from outside; it *unfolds* the labeling that already stands in the header of the supporting file: *elements—points, subsets, balls; roles—the point as position, the ball as neighborhood, the set as region; rules—openness and continuity as constitutions*.[^1] The order of the analysis is ontological, Rules $\to$ Roles $\to$ Elements; cognitively we went the reverse way, from the ball and the open set to the axioms to which they are subject.

The caveat about status is the same as in Chapter 5.1. Topology here lives over the *rational numbers*: an open set is a predicate `Q -> Prop`, and continuity is a property of functions $ℚ \to ℚ$ (§ 2.2.3). In calling this a *system*, we carry out a substantive ontological interpretation; we do not ascribe to the code an object of type `System` $L$. The analysis reads the structure of the file without adding formal content to it.

*Rules—those that hold topology together* (the law $L5$: rules stand above what they organize). And here the analysis clarifies *the main theme of the chapter, the two layers*. The rules of topology are stratified. The *universal layer* is the laws $L1$–$L5$. The *concrete constructive layer* is the two constitutions from the header, *openness* (“each point of a set has a ball inside it”) and *continuity* (“the preimage of an open set is open”), and with them the closure of topology under union and intersection and the facts about intervals—the whole topological apparatus of § 2.2, proved without a single axiom. And then there is the *concrete layer that rests on the laws of logic*: the rules of *compactness*, “a finite subcover exists” and “the process of construction terminates.” As § 2.5 and § 2.7 will show, these rules draw on $L3$ (and Bolzano–Weierstrass on $L4$ as well). The distinction that runs through the whole chapter—between constructive topology and compactness, which reveals the incompleteness of $ℚ$—is, in the terms of the analysis, a *stratification within Rules*: some rules are constructive, while others explicitly take into account a law of logic of ToS.

*Roles—the significance of positions* (the law $L4$: every role is structurally grounded). The header names three roles: the point plays the role of a *position*, the ball that of a *neighborhood*, the set that of a *region*. These roles are not arbitrary: by $L4$, their ground lies in the rules themselves (a ball *is* a neighborhood precisely because it gives a “margin of free space” around its point; a set *is* a region because openness endows each of its points with such a margin). In the process layer (§ 2.3) the roles of *cover* and *refinement* are added to them: finite collections of balls that cover a set, and the passage to finer collections.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are the points of $ℚ$, the subsets `Q -> Prop`, and the open balls. By $L1$ each point is identical to itself. And in the process form of an open set (§ 2.3) the bearers are *finite* rational covers: the “whole” of an open set is potential, but every snapshot of it is finite and surveyable (lemma `p4_cover_finite`)—a direct manifestation of $P4$.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| points of $ℚ$, subsets, balls | bearers | Element |
| point $\to$ position, ball $\to$ neighborhood, set $\to$ region | role positions | Role |
| openness, continuity | constitutions | Rule (constr.) |
| closure under $\cup$/$\cap$, intervals | rules of topology | Rule (constr.) |
| finite subcover, termination | compactness | Rule (rests on $L3$/$L4$) |
| laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: points and balls are elements; position, neighborhood, and region are roles; openness and continuity are rules; no component lays claim to two categories. There is no self-reference: the criterion of openness quantifies over the points of a set and stands *above* them—by $L5$, an operation stands above its operands. Topology is well-formed.

The analysis explains distinctions already drawn in the chapter. The two-layeredness that § 2.1 speaks of as the main lesson turns out to be a stratification of *Rules*: the topological constitutions are constructive, while the compactness rules rest on the laws of logic. The Hausdorff property (§ 2.4) is the rule by which topology *respects the act of distinction*: distinguishable elements turn out to be spatially separable as well. And the “three faces of compactness” (§ 2.8)—Heine–Borel, Noetherianity, termination of a process—are one Rule-level property, read under $P4$ as *the simplest process, one that terminates in a finite number of steps*. And the same analysis sets the pattern: Part V reads every topological notion as a process pattern with its own E/R/R structure.

## The Open Set as a Process of Covers

### The Process View

Up to now an open set has been a *predicate* for us, $S : ℚ \to Prop$. This is a static description: for each point it is said whether it is inside or not. But the whole of ToS has trained us to look differently, and it is natural to rethink the open set *in process terms*.

The reasoning here is the same as the one that turned a number into a process of approximations (Part IV). Under $P4$ an open set cannot be a completed subset of $ℝ$: there is no completed $ℝ$. It can, however, be *presented*: by a process of rational covers by balls, a sequence of ever more detailed finite collections of rational balls. Such a process is a *process representation* of openness: a way of showing how an open set unfolds in finite approximations, level by level. An object that classical mathematics thinks of as ready, ToS sees as an unfolding sequence of finite approximations; we apply this same move to the open set. In Rocq the process layer is gathered in the file `ProcessTopOpen.v`.

### Ball, Cover, Process

We build this view from the bottom up. At the base is the rational ball: `in_ball c r x` means $|x-c| < r$, the same construction as in § 2.2. Its basic properties are the same: the center lies in its ball, and—`in_ball_shrink`—if a point is inside a ball, a smaller ball fits around it (again the triangle inequality).

Above the ball is the open set in process form, `is_open_process`, with the same set of lemmas as in § 2.2, only in process language: the empty and the full sets are open, the ball is open (`ball_is_open`), the union and the intersection of open sets are open, and an open interval is open.

And at the top are the *cover* and the *process of covers* proper, which carry the process idea:

```coq
Definition QBallCover := list (Q * Q).

Definition OpenProcess := nat -> QBallCover.

Definition is_refining (op : OpenProcess) : Prop :=
  forall n x, covered_by_balls (op n) x ->
              covered_by_balls (op (S n)) x.
```

`QBallCover` is a finite list of “center, radius” pairs: a finite collection of rational balls. `OpenProcess` is a function from the level number to such a collection: at each level, its own finite cover. `is_refining` is the property of *refinement*: everything covered at level $n$ stays covered at level $n+1$. A cover with levels loses no points; it only adds them.

It is essential that at each level the cover is *finite*, a list of finite length; this is established by the lemma `p4_cover_finite`. And here $P4$ is directly visible: an open set unfolds as an infinite process, but every *snapshot* of it is a finite, surveyable collection of balls. The “whole” of an open set is potential; the “snapshot” is actually finite.

### What the Process View Gives

Why a process form, if `Topology.v` has already given the open set as a predicate? For the same reason that Part IV gave the number as a process. The predicate $S : ℚ \to Prop$ describes the result but not the *path* to it. The process of covers describes *how* an open set is built: level by level, finite collection of balls after finite collection. For the ontology of ToS this is the essence and no stylistic detail: an open set is a process of its rational exhaustion, not a region given all at once.

Let us be precise, however, about what exactly we have *built* here and what we have not. What is built is *infrastructure*: `QBallCover`, `OpenProcess`, `is_refining`, `covered_by_balls`—and its basic properties are proved. What we have *not* proved is the full equivalence theorem: that to every open predicate $S : ℚ \to Prop$ there corresponds a process of covers exhausting exactly $S$, and conversely. Therefore it is honest to call the process of covers a *process representation* of openness, an infrastructure layer, and not a proved identity between all open predicates and processes of covers. The chapter uses it in just this way: as a way of *presenting* openness by finite approximations, not as a theorem about the coincidence of two descriptions. What has been built in `ProcessTopOpen.v` we present as exactly what it is.

{
And, importantly for the overall picture of the chapter, the process layer, like the topological one, remains *constructive*: `ProcessTopOpen.v`, like `Topology.v`, uses not a single axiom.
}

## Separation: $ℚ$ Is Hausdorff{Separation: Q Is Hausdorff}

### To Distinguish Is to Separate

All of ToS grew out of a single act, the act of distinction. To distinguish two objects is the initial step from which everything else begins. This act has a topological face, and it is called the *Hausdorff property*.

A topological space is *Hausdorff* if any two distinct points can be *separated*, that is, placed in disjoint neighborhoods. To distinguish two points logically (to say that they are not equal) and to distinguish them topologically (to separate them into disjoint balls) are, in a Hausdorff space, one and the same. The Hausdorff property is the statement that logical distinction is *supported* spatially.

### The Theorem hausdorff_Q

Let us establish that $ℚ$ is Hausdorff and trace how this is derived. Given: two distinct rational points $x$ and $y$. Required: to separate them into disjoint balls.

The reasoning is direct. Since $x \neq y$, the distance between them is *positive*; this is a separate fact, the lemma `not_Qeq_pos_dist`: distinct rational numbers have a strictly positive distance. Let us take the radius $e$ equal to half of this distance. If some point $z$ fell into both balls of radius $e$ at once—around $x$ and around $y$—then by the triangle inequality the distance from $x$ to $y$ would be less than $e + e$, that is, less than the distance from $x$ to $y$ itself. This is impossible; hence the balls have no common points, and the points are separated. This is how the theorem `hausdorff_Q` is derived; in `ProcessTopOpen.v` it is written as follows:

```coq
Theorem hausdorff_Q : forall x y : Q,
  ~ (x == y) ->
  exists e : Q, 0 < e /\
    (forall z, Qabs (z - x) < e -> Qabs (z - y) < e -> False).
```

For any two *distinct* rationals $x$ and $y$ there exists a positive radius $e$ such that no point $z$ lies simultaneously in the ball of radius $e$ around $x$ and in the ball of radius $e$ around $y$—exactly what we derived.

### The Hausdorff Property and the Act of Distinction

It is worth dwelling on why this simple theorem matters ontologically.

ToS begins with the act of distinction: $A = \exists$, and to distinguish is to set a boundary. The lemma `not_Qeq_pos_dist` is a literal embodiment of this at the level of rational numbers: if two numbers are *distinguished* (not equal), there is a *gap* between them, a positive distance. A distinction is never “infinitesimal”: either it is there, and then there is a measurable gap, or it is not there at all.

The Hausdorff property builds a topological storey on top of this. A positive gap between points means that a neighborhood can be outlined around each of them, and these neighborhoods will not merge. Logical distinction ($x \neq y$) unfolds into spatial separation (disjoint balls). The Hausdorff property is a guarantee that the topology of $ℚ$ *respects* the original act of distinction: what is distinguished can also be separated. In the terms of the analysis of § 2.2.4, separation is the rule (Rule) by which topology respects the distinguishability of elements.

And, as before, not a single axiom. `hausdorff_Q` and `not_Qeq_pos_dist` are proved purely constructively. ToS builds the whole topological layer—open sets, closed sets, continuity, separation—without appealing to the laws of logic. This changes in the next section, where the chapter comes to compactness.

## Compactness: Where $ℚ$ Reveals Its Incompleteness{Compactness: Where Q Reveals Its Incompleteness}

### A Bold Line

This is the central and most demanding section of the chapter, and it has to begin with a direct thesis.

**The classical Heine–Borel theorem over $ℚ$ is *false*. And this is a mathematical fact, not a defect of the formalization.**

The classical Heine–Borel theorem asserts: every open cover of a closed bounded interval has a finite subcover. Over the real numbers this is true. Over the rationals it is not. The chapter neither hides this break nor passes off the desired as the proved: it shows *where* the boundary runs and *how* ToS works with it.

### The Counterexample

{
Why the classical Heine–Borel theorem is false over $ℚ$ can be seen from a counterexample. The file `HeineBorel_ERR.v` records the general sense of the obstacle—the classical Heine–Borel theorem requires completeness, which $ℚ$ lacks—while the concrete construction is given here as the chapter’s own illustration.
}

Let us take an irrational number $\alpha$ lying inside the interval—say, $\alpha = \sqrt{2}/2$ on the interval $[0,1]$. For each rational point $x$ of the interval, let us set the radius

$$
C(x) = \tfrac{1}{2} |x - \alpha|.
$$

This radius is strictly positive: $x$ is rational and $\alpha$ is irrational, so they cannot coincide. Hence the cover is *valid*: each rational point $x$ is covered at least by its own ball.

But this cover has no finite subcover. Suppose a finite collection of centers $x_1, …, x_k$ is chosen. The quantity

$$
d \;=\; \min_i  |x_i - \alpha|
$$

is strictly positive, as the minimum of a finite collection of positive numbers. The ball around the center $x_i$ has radius $\tfrac12|x_i-\alpha|$ and therefore does not reach closer to $\alpha$ than $\tfrac12|x_i-\alpha| \ge
\tfrac12 d$: every point lying closer to $\alpha$ than $\tfrac12 d$ is covered by *none* of the chosen balls. Rational points in this neighborhood of $\alpha$ exist—by the density of $ℚ$—and none of the finitely many balls covers them. A finite collection of centers does not cover the whole rational interval.[^2]

It is essential to see what exactly breaks compactness. The gap at $\alpha$—an irrational point that is *absent* from $ℚ$ and takes no part in the set being covered—is the very “hole” through which the finiteness of the subcover leaks away. The balls shrink as they approach $\alpha$, and the half radius does not let them close over the gap.

The root lies in one word: *incompleteness*. The classical proof of Heine–Borel relies on completeness: nested intervals converge to a point, and this point *is bound to exist*. Over $ℚ$ it is not bound to exist: nested intervals can converge to an irrational gap. Compactness is exactly the place where $ℚ$ reveals the incompleteness of which Chapter 5.1 spoke as a notion. Here the notion becomes a tangible obstacle.

### The Repair: The Lebesgue Number

We do not leave the broken theorem broken; we *repair* it. The counterexample pointed out what exactly breaks compactness: the radii of the cover can tend to zero at an irrational gap. Hence the repair: to add to the cover a condition that does not admit this pathology and keeps the radii from petering out. Such a condition is the *uniformity* of the cover, or, in classical terms, the existence of a *Lebesgue number*. In Rocq it is written as follows:

```coq
Definition uniform_cover (C : OpenCover) (a b delta : Q) : Prop :=
  delta > 0 /\ forall x : Q, a <= x <= b -> C x >= delta.
```

An ordinary cover (`valid_cover`) only requires that each point have a positive radius—and this, as the counterexample showed, is not enough. `uniform_cover` requires more: there exists a *single* positive $\delta$ that bounds every radius from below. The radii cannot “peter out”: they all have a common lower bound. This is the Lebesgue number: the scale at which the cover works *uniformly* over the whole interval.

With this condition, Heine–Borel is provable again. The argument is bisection: we divide the interval in half, then each half in half again. Since all radii are at least $\delta$, the subdivision can be stopped as soon as the width of a piece becomes less than $\delta$: such a piece is entirely covered by one ball. The Archimedean property of $ℚ$ guarantees that the required fineness is reached in a finite number of steps, and the finite subcover is assembled from a finite number of balls. This derivation is formalized in `HeineBorel_ERR.v` (the bisection descent: `hb_step`, `Qpow2`, `Heine_Borel_by_depth`) and assembled into the theorem:

```coq
Theorem Heine_Borel_uniform : forall (C : OpenCover) (a b delta : Q),
  a < b ->
  uniform_cover C a b delta ->
  exists centers : FiniteSubcover, covers_interval C centers a b.
```

Given a Lebesgue number, a finite subcover *exists*. The theorem `Heine_Borel` is the same statement with the hypothesis of the existence of a Lebesgue number made explicit.

### What Is Proved and What Is Not

{
Let us be precise about what exactly has been established. What is proved is the *uniform* version of Heine–Borel, for covers that possess a Lebesgue number. *Full* classical compactness—“every cover has a finite subcover,” without the uniformity proviso—is *not* proved, and cannot be: the counterexample contradicts it. The chapter does not pass off `Heine_Borel_uniform` as the classical theorem. This is an honest repair: the theorem is restored on the class of covers on which it holds over $ℚ$ at all.
}

### Axiom Status: $L3${L3} in the Bisection

{
And, as agreed in § 2.1, let us honestly mark where our argument rests on a law of logic. The Heine–Borel bisection hinges on one step that is not constructive. This step is the lemma `not_coverable_half`: if an interval is not covered by finitely many balls, then one of its halves is not covered either. The statement is true, but to indicate *which* half is not covered, the Law of Excluded Middle is needed. Therefore `HeineBorel_ERR.v` imports `ToS_Axioms.v`, and this lemma uses `classic`.
}

Let us recall the agreement of § 2.1: `classic` is the technical Rocq implementation of $L3$, the Law of Excluded Middle of ToS. Appealing to it is an *explicit accounting of the level*, not a breach in rigor: the bisection argument of Heine–Borel rests on a law of logic of ToS, and the chapter notes this. The compactness layer, moreover, is *not homogeneous*. Some of its parts are fully constructive—for example, the total boundedness of an interval and the construction of $\varepsilon$-nets, to which the chapter will turn in § 2.6. Others—for example, the bisection arguments about the uncoverable half or the infinitely inhabited half—rest on $L3$. To distinguish “proved constructively” from “proved with support from $L3$” is not pedantry here but an exact description of what each particular theorem stands on. This is precisely the sublayer of *Rules* resting on a law of logic that the analysis of § 2.2.4 singled out.

## Total Boundedness and $\varepsilon$-Nets{Total Boundedness and eps-Nets}

### Another Approach to Compactness

Section 2.5 showed that the classical Heine–Borel theorem breaks down over $ℚ$, and repaired it with the condition of a Lebesgue number. Let us now come from another side: *part* of the same gap can be closed by a different notion, *total boundedness*, and over $ℚ$ this notion behaves much more tamely.

The idea is simple. Instead of speaking of covers by arbitrary balls, let us ask for little: that the whole set can be approximated by a *finite grid* of points with any precision given in advance. Such a grid is called an $\varepsilon$-net, and the property of an interval of having an $\varepsilon$-net for each $\varepsilon$ is called total boundedness. In Rocq (the file `HeineBorelComplete.v`) this is written as follows:

```coq
Definition eps_net (pts : list Q) (a b eps : Q) : Prop :=
  forall x : Q, a <= x <= b ->
    exists p : Q, In p pts /\ Qabs (x - p) < eps.

Definition totally_bounded (a b : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists pts : list Q, eps_net pts a b eps.
```

`eps_net` is a finite list of points `pts` such that every point of the interval lies at a distance less than $\varepsilon$ from some point of the list. `totally_bounded` is the property of an interval of having such a net for *every* $\varepsilon$: however fine the required precision, a finite grid covering everything with that precision can be found.

### The Main Theorem: An Interval Is Totally Bounded

{
Let us establish the main thing: every closed interval is totally bounded. In `HeineBorelComplete.v` this is a theorem:
}

```coq
Theorem totally_bounded_interval : forall a b,
  a <= b -> totally_bounded a b.
```

And, what is important for the ontology of ToS, it is proved *constructively*, by direct construction of the grid. Given $\varepsilon$, we lay out over the interval a uniform rational grid with a step computed from $\varepsilon$ and present it as a finite list of points; every point of the interval turns out to be closer than $\varepsilon$ to some node of the grid. There is no appeal to the laws of logic: the grid is built explicitly (lemma `rational_eps_net`, nodes `grid_points`).

Unlike Heine–Borel, where a genuine difficulty arose over $ℚ$, the total boundedness of an interval is a constructive and unproblematic result. And this is understandable: total boundedness does not require a limit point to *exist*; it requires only that the interval can be *approximated* by a finite grid. And $ℚ$ knows how to approximate finitely without any completeness.

{
On the same foundation we also build a *bridge to uniform continuity*, groundwork for Chapter 5.3. A Lipschitz map is uniformly continuous (`lipschitz_uniform_cont`); this is the constructive replacement for the classical implication “continuity implies uniform continuity,” which is unprovable over $ℚ$. The sum, scaling, and composition of uniformly continuous functions are again uniformly continuous. `HeineBorelComplete.v` supplies this whole apparatus to Chapter 5.3.
}

### A Caveat on Axiom Status

{
An honest caveat is needed here—and it also illustrates a general rule of ToS auditing. The header of the file `HeineBorelComplete.v` declares the status “0 axioms.” But this is the status of the *file according to its header*, not of every theorem in it. Among the lemmas of the file is `mono_bounded_is_cauchy`—“a monotone bounded sequence is Cauchy”—and it *uses* `classic` (through the device `NNPP`, double-negation elimination).
}

{
There is no contradiction with the header; there is a reminder of the rule established back in Chapter 4.6: axiom status is checked for a *concrete theorem*, with the command `Print Assumptions`, not ascribed wholesale to a file. `totally_bounded_interval` and the construction of $\varepsilon$-nets are constructive. But `mono_bounded_is_cauchy` rests on $L3$—and, as agreed in § 2.1, this is an *explicit accounting of the level*: the given lemma stands on the Law of Excluded Middle of ToS, and the audit records this.
}

### A Computational Example: The Grid of an Interval

Total boundedness is a notion that is easy to make *tangible*. This is the third, computational layer of the exposition. Let us take the interval $[0,1]$ and count *how many points* an $\varepsilon$-grid needs for several levels of precision.

The grid is laid out with a step equal to $\varepsilon$; the number of points is the number of steps of length $\varepsilon$ that fit into the unit interval, plus one. Here is the result:

| Precision $\varepsilon$ | Grid step | Points sufficient for $[0,1]$ |
|---|---|---|
| $1/4$ | $1/4$ | $5$ |
| $1/8$ | $1/8$ | $9$ |
| $1/16$ | $1/16$ | $17$ |

{

Let us read the table. To cover $[0,1]$ with precision $1/4$, five points suffice—$0,\ 1/4,\ 1/2,\ 3/4,\ 1$: every point of the interval lies at a distance less than $1/4$ from one of them. With precision $1/8$, nine points. With precision $1/16$, seventeen. The grid is *finite* for every $\varepsilon$, and its size is computed directly: when $\varepsilon$ is halved, the number of points roughly doubles. This is total boundedness at work: a concrete finite table in place of the abstract “a grid exists.” And everything is computable—no completeness, no passage to a limit, only rational arithmetic.
}

One technical caveat. The table above shows the most intuitive grid, with a step of exactly $\varepsilon$. The *formal* proof in `HeineBorelComplete.v` is arranged more robustly: the lemma `rational_eps_net` builds a grid with a *half* step $\varepsilon/2$ to guarantee the strict inequality $|x - p| < \varepsilon$ without provisos about the endpoints. The table here is a pedagogical illustration of the orders of magnitude, not the literal `grid_points` of the proof; the code takes a grid twice as dense and thereby avoids fussing with the boundaries.

## Bolzano–Weierstrass: Compactness through Bisection

### The Second Theorem of Compactness

Heine–Borel speaks of covers. Compactness also has a second face, dual to the first: the Bolzano–Weierstrass theorem, which speaks of *sequences*. Classically it is formulated as the existence of a convergent subsequence for every bounded sequence. The current formalization proves a close, Cauchy-compatible form. In the terms of ToS, where a limit is a process: every bounded sequence of rational numbers has a *cluster point*—a Cauchy process to which terms of the sequence with large indices come arbitrarily close. It is precisely this formulation—through a cluster point, not through an explicitly constructed subsequence $k : ℕ \to ℕ$—that will be proved.

{
To prove this theorem is our next step (its formalization is gathered in `BolzanoWeierstrass.v`). And at once, honestly and as agreed in § 2.1, a word about the basis on which it will stand. Unlike the total boundedness of § 2.6, Bolzano–Weierstrass will not be constructive: its proof rests on *two* laws of logic of ToS, $L3$ and $L4$. The header of `BolzanoWeierstrass.v` does not hide its axiom status and declares it directly: *“Axioms: classic ($L3$), L4_witness ($L4$)”*. The chapter makes this basis the crux of the section rather than a footnote in small print—and § 2.7.2 will show exactly where and why the laws of logic come into play.
}

### Bisection and the Choice of a Half

The proof is a bisection akin to the one that worked in Heine–Borel, but applied to a sequence. We are given an interval $[a,b]$ in which a bounded sequence $s$ lies. We divide the interval in half. In one of the halves—in at least one—lie *infinitely many* terms of the sequence (there are infinitely many terms in all, and only two halves). We choose such a half, divide again, and so on. The result is a process of nested intervals whose width tends to zero; the “point” to which they contract is the cluster point.

{
There is exactly one non-constructive step in this argument, and we point it out directly instead of masking it. The step is the *choice of a half*; in Rocq it is written as follows:
}

```coq
Definition bw_step (s : nat -> Q) (st : BWState) : BWState.
Proof.
  destruct (L3_informative (bw_step_left s st)) as [H | H].
  - exact (mkBW (bw_left st) (bw_mid st)).
  - exact (mkBW (bw_mid st) (bw_right st)).
Defined.
```

To choose whether to go to the left half or to the right, one must *decide* whether the left half contains infinitely many terms. And this, in the general case, cannot be decided constructively: the check “infinitely many” does not terminate in finite time. This is where `L3_
informative` comes in—the informative form of the Law of Excluded Middle: it *settles* that one of the two possibilities holds and makes it possible to split into cases.
The lemma `infinite_pigeonhole`—the infinite version of the pigeonhole principle, “at least one half contains infinitely many”—uses `classic` for the same reason.

By the convention of § 2.1, `L3_informative` and `classic` are technical Rocq implementations of $L3$. The choice of a half rests on the Law of Excluded Middle of ToS. This is the honestly presented structure of the proof, *not* a flaw in it. The Bolzano–Weierstrass bisection is non-constructive *by its very nature*: the “inhabited” half cannot be computed; it can only be *named* by $L3$. ToS accepts $L3$ as a law of logic, and therefore in ToS the theorem is *provable*; but it is provable precisely *with support from a law of logic*, not from pure computation, and the chapter says so directly.

Let us also specify the character of this step. `bw_step` chooses a half by a *classical case analysis* on the proposition “the left half contains infinitely many terms,” via `L3_informative`. This is *not* a full-fledged algorithm for constructing a subsequence by indices, nor a choice of a minimal index. The Bolzano–Weierstrass bisection is a process of constructing nested intervals and a Cauchy cluster point; the non-constructivity is concentrated in exactly one place—in maintaining the status of the “inhabited half” through case analysis—and nowhere else.

### The Main Theorem

The remaining properties of the bisection are constructive and worked out in detail: each step preserves nesting and the “inhabitedness” of the chosen half; the width after $n$ steps does not exceed $(b-a)/2^n$ and, via the Archimedean property (`bw_width_to_zero`), tends to zero; and the left and right endpoints form Cauchy processes. Putting the choice of a half together with these properties, we obtain the main theorem; in `BolzanoWeierstrass.v` it is written as follows:

```coq
Theorem bolzano_weierstrass : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : CauchySeq, is_cluster_point s L.
```

Every bounded sequence in $[a,b]$ has a cluster point, and this point is presented as a `CauchySeq`, a Cauchy process. The predicate `is_cluster_point` is defined in a Cauchy-compatible way: for any precision and any index threshold there is a term of the sequence with a larger index lying closer to the cluster point than required. A dual pair of theorems, `monotone_bounded_cauchy` and `decreasing_bounded_cauchy`, adds that a monotone bounded sequence is itself Cauchy.

### Bisection as a Process

{
It remains to translate the result into the process language of ToS; this wrapper is carried by the file `ProcessBW.v`. We regard the left and right endpoints of the bisection as processes over $ℚ$ (`bw_left_process` and `bw_right_process`) and establish that they are monotone (the left ones increase, the right ones decrease), that both are Cauchy, and that they converge to one limit. The theorem `bw_is_process_construction` assembles this into a single E/R/R picture, and `bw_convergence_rate` fixes the rate, $1/2$: the interval is halved at each step.
}

{
The process wrapper does not change the axiomatic basis: it adds nothing and takes nothing away, carrying over into the language of processes the theorem as it is—proved, with support from $L3$ and $L4$. The header of `ProcessBW.v` records exactly this: *“classic (inherited from BolzanoWeierstrass)”*.
}

Ontologically, the Bolzano–Weierstrass bisection is a pure specimen of a ToS process. The cluster point is not given in advance; it is *built*—step by step, division after division, choice of an inhabited half after choice. The result is a Cauchy process unfolding at the rate $1/2$. What classical mathematics has as a ready “limit point” is a process here; and the only place where the process rests on a law of logic rather than on computation is the honestly named choice of a half.

## Connectedness, Unification, and the Summary of the Chapter

### Connectedness: Topological Connectedness and Process Paths

There remains the last topological notion: *connectedness*. And with it $ℚ$ behaves instructively: the answer depends on which connectedness one asks about.

In the sense of classical *topological* connectedness, $ℚ$ is *not connected*; moreover, it is totally disconnected. Between any two rational numbers lies an irrational gap along which $ℚ$ can be cut in two. Topologically the rational line crumbles into dust; $ℚ$ has no nontrivial connected subsets.

But there is another notion of passage—and here terminological care is needed, or else a conflict with standard topology will arise. If $ℚ$ lacks connectedness as *wholeness*, let us ask about connectedness as *reachability*: can one get from one rational point to another without leaving the set? For this, let us build a rational linear interpolation, a straight parametrization from $a$ to $b$:

```coq
Definition linear_path (a b t : Q) : Q := a + t * (b - a).
```

`linear_path` gives $a$ at the parameter $t=0$, $b$ at $t=1$, and linear interpolation in between. We define a “path in a set” as follows:

```coq
Definition PathIn (S : Q -> Prop) (gamma : Q -> Q) (a b : Q) : Prop :=
  gamma 0 == a /\ gamma 1 == b /\
  forall t, 0 <= t -> t <= 1 -> S (gamma t).
```

And here is an essential caveat, which the chapter makes directly. The definition of `PathIn` contains *no requirement of continuity* of the map `gamma`. A standard topological path is a *continuous* map of a connected interval; it is continuity that guarantees that the image is connected. `PathIn` requires only that the parametrization hit $a$ and $b$ at the endpoints and stay inside $S$ at every rational parameter. This is *not* standard path-connectedness, and we do not pass it off as such. It is *process path-reachability*: a rational parametrization that carries one point to another without leaving the set. In Rocq this layer is gathered in `ProcessTopConnected.v`.

Therefore the chapter does not call $ℚ$ “path-connected” in the topological sense: that would be false. The chapter says something more precise: $ℚ$ is *process-reachable*. What has been established is this: `linear_path` stays inside the interval and is Lipschitz in $t$, and paths can be reversed and concatenated; `interval_path_connected` gives process reachability for a closed interval; the process form `process_path` is a walker moving from $a$ to $b$ that occupies the parameter $t = n/(n+1)$ at step $n$, and `process_path_cauchy` shows that this process is Cauchy and converges to $b$. This whole layer has zero axioms.

The difference between the two notions is ontologically important. Topological connectedness asks about a *completed* continuum without holes, and $ℚ$ does not form one. Process reachability asks about a *process* of passage, and $ℚ$ builds the process of linear interpolation without difficulty. What for classical topology is a shortcoming of $ℚ$ (total disconnectedness) turns out to be inessential for the process ontology of ToS: what matters is the possibility to *pass through*, not static wholeness—and a rational process path does allow one to pass from point to point. In the terms of the E/R/R analysis (§ 2.2.4), reachability is a role (Role): a process path leading from one point to another.

### The Three Faces of Compactness

Let us now bring together the different guises of compactness: in ToS there turn out to be three of them, and they are one. Under $P4$, compactness is the *simplest* case of a process: a process that *terminates*, that is completed in a finite number of steps. This simplest case has three names.

*Heine–Borel*: every (uniform) cover has a finite subcover. *Noetherianity*: every bounded ascending chain stabilizes. *Termination*: the process of construction is completed in a finite number of steps. These are three formulations of one thing; in `ProcessTopCompact.v` their unity is secured by the theorem `p4_compactness_summary`, while `compact_eq_noetherian` and `compact_eq_hb` link them pairwise.

It is worth saying precisely, however, what the *status* of these summary theorems is. `p4_compactness_summary` and its relatives are *conjunctions* of what has already been proved, not new results: they gather together theorems established in `HeineBorel_ERR.v` and in the files on Noetherianity. The same applies to the file `ProcessTopUnified.v`, a summary of all the topological material: it lists five subpatterns of topology (open sets, metric, compactness, connectedness, separation) and places topology eleventh in the series of process patterns of ToS. `ProcessTopUnified.v` is an *overview* file, a summary; the chapter refers to it as a map of ground already covered, not as a source of new proofs. And, as agreed in § 2.1, the headers of `ProcessTopCompact.v` and `ProcessTopUnified.v` honestly note that `classic` is inherited from the Noetherianity layer.

{
The small file `ProcessCompactness.v`, with its theorem `compactness_foundation`, belongs here as well. The name is grand, but, as with `process_space_complete` in Chapter 5.1, in its content it is a *foundation stub*, not a theory of compactness: it records basic facts such as the boundedness of a constant process and the Cauchy property of a constant sequence. The chapter counts it exactly as such and calls things by their proper names.
}

### What Has Been Built and What Is Being Prepared

The summary of the chapter comes as three lists, following the discipline of the honest mode.

**Built and checked.**

- { The topological layer over $ℚ$—open and closed sets, balls, intervals, continuity, the Hausdorff property, process path-reachability; constructively, without axioms (`Topology.v`, `ProcessTopOpen.v`, `ProcessTopConnected.v`).}
- The open set in process form: a process of finite rational covers by balls, with refinement across levels.
- Heine–Borel in the uniform version (`Heine_Borel_ uniform`), for covers with a Lebesgue number; proved by bisection.
- The total boundedness of every interval (`totally_bounded_interval`), constructively, through the explicit construction of $\varepsilon$-grids.
- Bolzano–Weierstrass (`bolzano_weierstrass`) in the `CauchySeq` form: every bounded sequence has a Cauchy cluster point (rather than an explicitly constructed subsequence).

**What this rests on.**

- The topological layer, on pure construction, without the laws of logic.
- The compactness layer, on the laws of logic of ToS: the bisection of Heine–Borel and Bolzano–Weierstrass rests on $L3$ (`classic`, `L3_informative`), and Bolzano–Weierstrass additionally on $L4$ (`L4_witness`). This is an explicit accounting of the level, not a flaw: the technical Rocq axioms implement the ontological laws of logic of ToS.

**Not built in this chapter.**

- The classical Heine–Borel theorem without the uniformity proviso: over $ℚ$ it is *false*, and this is a mathematical fact, not a gap.
- { The *full* topology of open sets and compactness on the quotient classes `RealPoint` are not built as a separate structure; the material of this chapter lives at the level of $ℚ$ and of processes over $ℚ$. (The basis of the metric topology on classes—the open ball `rp_in_ball` with well-definedness—is built separately, in `RealPointTopology.v`; see § 2.2.3.)}

**Prepares next.** Uniform continuity, the Lipschitz apparatus, and $\varepsilon$-nets are groundwork for Chapter 5.3 on continuity; the compactness of an interval is the instrument on which the intermediate value and extreme value theorems will stand.

### Summary of the Chapter

Chapter 5.2 has taken the topology of processes from the open ball to the cluster point. Its main lesson concerns the *two layers*. Topology as such—openness, closedness, separation, connectedness—is given to ToS for free, purely constructively, from the rational distance alone. Compactness is given differently: here $ℚ$ reveals its incompleteness, the classical Heine–Borel theorem breaks down, and the theorems are restored either by repair (the Lebesgue number) or by support from the laws of logic of ToS. And this support is an honestly presented structure, not a weakness: $L3$ and $L4$ are laws of logic of ToS, and the audit marks the appeal to them as an accounting of the level, not as a breach.

{*The summary of the chapter comes in three parts. First: what is built. The topological layer over $ℚ$—open and closed sets, balls, intervals, continuity, the Hausdorff property, process path-reachability—is built constructively, without a single axiom. The open set has received a process form: a process of finite rational covers by balls. The uniform version of Heine–Borel, the total boundedness of every interval, and the Bolzano–Weierstrass theorem are proved.*}

{*Second: what this rests on. The topological layer rests on pure construction. The compactness layer rests on the laws of logic of ToS: the bisection of Heine–Borel and Bolzano–Weierstrass rests on $L3$, and Bolzano–Weierstrass additionally on $L4$. The technical Rocq axioms `classic` and `L4_witness` are implementations of the ontological laws of logic of ToS; appealing to them is an explicit accounting of the level of a proof, not a departure from rigor.*}

{*Third: what remains open. The classical Heine–Borel theorem without the uniformity proviso is false over $ℚ$: this is a mathematical fact. On the quotient classes `RealPoint` the *basis* of the metric topology has been built—the open ball `rp_in_ball` with well-definedness (`RealPointTopology.v`, § 2.2.3); the full theory of open sets and compactness on classes, however, has not been built as a separate structure. The chapter has given the topology of processes and two compactness theorems; continuity, which will stand on this basis, is the subject of the next chapter of Part V.*}

---

[^1]: The verbatim E/R/R labeling in the header of the file `Topology.v`; here it is unfolded following the pattern of Part I.
[^2]: This concrete construction is now machine-checked as well—as a *standalone* 0-axiom theorem, not only as the general sense of the obstacle. For $[1,2]\capℚ$ an explicit open cover $U_k=\{x : |x^2-2| > 1/(k{+}1)\}$ is given: it covers the whole rational interval (`covers`, since $x^2\neq 2$) but has no finite subcover (`no_finite_subcover`)—at the cut $\sqrt2$ the quantity $|x^2-2|$ decreases to zero faster than any finite threshold. Together they give `Q_interval_not_compact`; the witness is provided by Pell approximations of $\sqrt2$. Machine-checked, 5 Qed, 0 axioms.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/01 Metric on Processes|Chapter 1. Metric on Processes]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/03 Continuity|Chapter 3. Continuity]] →
