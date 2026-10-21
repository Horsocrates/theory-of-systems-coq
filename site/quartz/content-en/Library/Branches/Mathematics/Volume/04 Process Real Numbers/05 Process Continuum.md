---
title: "Chapter 5. The Process Continuum"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/04 Процессные действительные числа/05 Процессный континуум.md"
sourceBlob: a85e69621c14b191f58affb1e3e3e8dc2f865cfb
translated: 2026-10-20
status: draft
---

## From Quantity to Structure

### What Chapter 4.4 Left Behind

The previous chapter carried the process reading of Cantor’s theorem
through to the end. Uncountability turned out to be a statement about
processes, not a property of a completed set—there is no such set in
the $P4$-ontology: no regular enumeration of Cauchy processes covers all
the process classes of the unit interval. For every such enumeration a
diagonal process is built that did not enter the numbering.

And at the very end Chapter 4.4 left a question—open, deliberately not
prejudging the answer. The rational points are *countable*: a process of
enumeration exists for them. The process classes of the interval escape
every regular enumeration. There is some difference between the former
and the latter. But *what* is it? How exactly do the process classes
differ from the countable rational points—if one speaks in a language
other than that of completed cardinalities?

### The Temptation of Cardinality and Why It Does Not Fit

Classical mathematics answers this question instantly and habitually:
the difference is in *cardinality*. The rationals are “countably many”;
the points of the interval are “uncountably many”; and the second is
strictly larger than the first. And once this is so, the next classical
question arises, the famous *continuum hypothesis*: is there a
cardinality *strictly between* the countable one and the cardinality of
the continuum? Is there a collection of points that is no longer
countable but still “smaller” than the whole interval?

Under $P4$ this line of reasoning is unavailable from the very first
step. “Cardinality” is a characteristic of a completed set: how many
elements it has, taken all at once, as a ready collection. And $P4$ does
not admit completed sets of points (Chapters 4.1–4.3). To ask “what is
the cardinality of the continuum” or “is there an intermediate
cardinality” is already to accept what has been rejected: that the
continuum *is* a ready set with a definite number of elements. Under
$P4$ the question of an intermediate cardinality does not receive a
false answer—it loses its subject altogether. In the E/R/R analysis
(§ 5.7.5) the continuum will turn out to be a structural *type*—a role,
not an object—rather than a cardinality.

### The Transition to the Question of Structure

But losing the subject does not mean that there is nothing left to ask.
Under $P4$ the question is reformulated. Not “how many elements are in
the collection” but “how the collection is *arranged*.” Not a measure of
magnitude, but a *type of structure*. Instead of “what is the
cardinality”—“what kind of collection of processes is this: can it be
traversed by an enumeration, or does it branch so that a traversal is
impossible?”

This shift—from quantity to structure—is what the present chapter is
about. It will show that closed collections of processes have exactly
*two* structural types, and that there is no intermediate type between
them. This statement is the process theorem about the continuum; and,
as will be seen, it is a proved *dichotomy*, not a question about
cardinality.

### The Plan of the Chapter

To state and justify this dichotomy, the chapter will need to change its
working model. Chapters 4.2–4.4 worked with Cauchy processes over
$ℚ$—a model close to the customary number line. The present chapter
passes to *binary* processes—the Cantor space $2^ℕ$. Why the change of
model is needed and what justifies it is the subject of § 5.2. Then
come the diagonal argument in the new model, which turns out to be
simpler than the former one (§ 5.3); the apparatus of trees and closed
collections (§ 5.4); perfect subtrees (§ 5.5); and, as the culmination,
the Cantor–Bendixson dichotomy itself (§ 5.6) and its reading in the
role of the process version of the continuum question (§ 5.7). The
concluding section sums up not only the chapter but the whole of
Part IV (§ 5.8).

The chapter, like the previous ones, is checked against the Rocq
formalization line by line. This time there are three supporting files,
and they form an ascending line. `ProcessTypes.v` introduces the types
of binary processes, trees, and collections. `ProcessDiagonal.v` builds
the diagonal argument on them. `ProcessContinuumHypothesis.v` proves
the central theorem—the structural dichotomy. And where the
formalization states conditions—the closedness of the collection, the
reliance on the laws of logic—the chapter will state them along with it.

## Another Model: Binary Processes

### What the Change of Model Is For

Chapters 4.2–4.4 built the real number as a Cauchy process over $ℚ$: a
function from step numbers to rational approximations,
`RealProcess` ${}={}$ `nat -> Q`. This model is close to the customary
number line and is good when one needs to speak of *magnitudes*—of the
number to which a process converges, how fast, in what interval it
lies.

But the present chapter asks about the *structure* of collections, not
about magnitudes. And for a conversation about structure the Cauchy
model is inconvenient. To see the structure of a collection of
processes—its branching, its capacity or incapacity to be
traversed—one needs the apparatus of *trees*: branching schemes along
which a process lays its path. Over Cauchy processes such an apparatus
is built with difficulty: a rational approximation is not a “fork”; no
branching is visible in it.

Therefore the chapter passes to another model—simpler and directly
suited to a conversation about structure. To *binary* processes.

### The Binary Process

A binary process is a process that at each step yields one of two
values—“yes” or “no,” $1$ or $0$, `true` or `false`—rather than a
rational approximation. In `ProcessTypes.v` the definition is as short
as can be:

```coq
Definition BinProcess := nat -> bool.
```

A function from step numbers to Boolean values. At step $0$ the process
says “yes” or “no,” at step $1$ again one of the two, and so on. A
binary process is an infinite sequence of binary choices.

The collection of all binary processes—all functions
`nat -> bool`—is called the *Cantor space* and is denoted $2^ℕ$. This is
a classical object, and it is on it that the present chapter will work.

As before with `RealProcess` (Chapter 4.2), a $P4$ reservation is needed
here. `nat -> bool` is a formal *type* of the Rocq language, not an
ontologically primary completed collection of all binary sequences. ToS
reads it as a type of *process rules*, not as a ready set taken all at
once: a binary process is a rule that answers every finite request—a
step number $n$—with the value `true` or `false`. “All binary processes”
is a manner of speaking about a type of rules, not about a completed
infinite collection; and when below the chapter asks whether this or
that collection of such processes is enumerable, it will be asking
precisely about rules and their traversal, not about ready sets.

### The Binary Model Is Not the Interval

Here an important reservation must be made at once, so that no false
identification arises. The Cantor space $2^ℕ$ is *not* the interval
$[0,1]$ and not the model with which Chapters 4.2–4.4 worked. There is,
of course, a connection between them: an infinite sequence of zeros and
ones can be read as the binary expansion of a number from $[0,1]$, and
classically the Cantor space is closely intertwined with the continuum.
This connection is now formalized as well—in one direction: the file
`ProcessBinReal.v` builds the translation `bin_to_real`, which assigns
to every binary process a point of the interval (the partial sums
$\sum_k \mathrm{bit}_k/2^{k+1}$, lying in $[0,1]$). But there is no
*identity*, and this is visible right in the translation: the binary
expansion is ambiguous—$0{,}0111…$ and $0{,}1000…$ define one
point—and the proved lemma `bin_ones_equiv_one`
($0{,}111\ldots_2 = 1$ as an equality of points) serves as the model
case. Because of this ambiguity $2^ℕ$ and $[0,1]$ are arranged
differently; the translation is not one-to-one, and the Cantor space,
strictly speaking, is not the interval.

For the present chapter this is a convenience, not a hindrance. The
chapter is concerned with *structure*, and $2^ℕ$ is a cleaner
structural model than $[0,1]$: it has no rational approximations, no
edge complications with double representations *inside* the argument
(each step is simply `true` or `false`), and the branching is directly
visible. The binary model is a separate branch of the process
formalization of the continuum: a structural double of the Cauchy model
on which the theorem about structure is proved more cleanly, not a
replacement for it. Chapter 4.4 worked in the Cauchy model on the
interval; Chapter 4.5 works in the Cantor model—and this is a deliberate,
stated transition.

### Equality of Binary Processes

When should two binary processes be considered *one*? Here one more
separation is needed—from the notion of equivalence of the previous
chapters.

In `ProcessTypes.v` the equality of binary processes is `bp_eq`:

```coq
Definition bp_eq (p q : BinProcess) : Prop := forall n, p n = q n.
```

Two binary processes are equal if they coincide *at every step*—in all
coordinates. This is *pointwise* equality.

And here it is important not to confuse things. In Chapters 4.3–4.4
processes were compared *not* pointwise. There the relation
`process_equiv` linked Cauchy processes with a *common limit*: two
processes could diverge at every step, yield different approximations,
and still be equivalent if they converged to one number. The point there
was a class under such a relation of “the same limit.”

In the binary model everything is different. `bp_eq` is precisely
pointwise coincidence, not “the same limit.” And what is considered here
is the binary processes themselves as sequences—not classes by the
limit. This is a deliberate choice of model: the previous chapters built
the point as a class; this chapter works with process-sequences
directly. A collection of binary processes—`BinCollection`—is simply a
collection of such sequences:

```coq
Definition BinCollection := BinProcess -> Prop.
```

And the *enumerability* of a collection is the existence of a process
that traverses it:

```coq
Definition is_enumerable (C : BinCollection) : Prop :=
  exists f : nat -> BinProcess,
    forall p, C p -> exists n, bp_eq (f n) p.
```

A collection $C$ is enumerable if there is a function $f$ from indices
to binary processes covering every member of $C$: for any $p \in C$
there is an index $n$ with `bp_eq` $(f n)\;p$. Enumerability is exactly
“the collection can be traversed by a countable list.” The whole chapter
will be built around this notion—enumerable or not.

## Uncountability Again—but Simpler

### The Diagonal for Binary Processes

The first thing worth doing in the new model is to make sure that
Cantor’s theorem still holds in it: binary processes are also
uncountably many; no enumeration covers them. This is needed both in
itself and as a run-up to the main result of the chapter. And here a
pleasant discovery is made: in the binary model the diagonal argument
turns out to be *much simpler* than the trisection construction of
Chapter 4.4.

The basis is two short operations from `ProcessDiagonal.v`. The first is
the *flip*, Boolean negation:

```coq
Definition flip (b : bool) : bool :=
  match b with true => false | false => true end.
```

`flip` changes `true` into `false` and back. The second is the *diagonal
process* itself:

```coq
Definition diagonal (f : nat -> BinProcess) : BinProcess :=
  fun n => flip (f n n).
```

From an enumeration $f$ a binary process is built that at step $n$
yields the *flipped* $n$-th value of the $n$-th process of the
enumeration. This is Cantor’s classical diagonal in its pure form: we go
along the diagonal of the table “process number $\times$ step number”
and flip everywhere.

### Why There Are No Edge Difficulties Here

It is worth pausing on the contrast with Chapter 4.4. There the diagonal
process had to be built by trisection—by dividing an interval into three
parts—and all because of the *edge difficulty*: the position of an
enumerated Cauchy process is known only approximately, the confidence
interval may straddle a boundary, and a simple “go the other way” does
not work. Regularity, the synchronization of parameters, and the free
third were needed.

In the binary model none of this is needed, and the reason is simple.
The value of a binary process at step $n$ is simply `true` or `false`:
one of two *exact* options, not a rational approximation surrounded by
uncertainty. To “step away” from it is simply `flip`: to take the other
option. No approximation, no confidence interval, no boundary that could
be straddled. Nor is there an analogue of the problem $0{,}999… = 1$—the
duality of representation that hindered the digit argument in
Chapter 4.3: the coordinate of a binary process is unambiguous. `flip`
*guarantees* a non-coincidence in one coordinate—and this is enough.

### The Diagonal Differs from Every Process

The key property of the diagonal is the lemma `diagonal_differs`:

```coq
Lemma diagonal_differs : forall f n,
  ~ bp_eq (diagonal f) (f n).
```

The diagonal process is not equal (by `bp_eq`) to any member of the
enumeration. The proof fits into one thought: if `diagonal` $f$
coincided with $f n$ at every step, it would coincide at step $n$ too;
but at step $n$ the diagonal by construction yields `flip` $(f n n)$—the
flipped value—and the flipped value is not equal to the original
(`flip_neq`). A contradiction.

And here is what is essential. This lemma is proved *without any
axioms*. The file checks this by machine with the command `Print Assumptions`, and for `diagonal_differs` it shows: not a single
axiom; the proof is closed. This is a sharp and instructive contrast
with Chapter 4.4: there the trisection diagonal rested on classical
logic ($L3$). Here we have a pure construction: `flip` is computed, the
non-coincidence is checked, and no law of excluded middle is required.
The binary diagonal is *constructive* in the full sense.

### Cantor’s Theorem in the Binary Model

Uncountability follows immediately from `diagonal_differs`.
`ProcessDiagonal.v` formulates it as follows:

```coq
Theorem cantor_for_processes :
  forall f : nat -> BinProcess,
  exists g, forall n, ~ bp_eq g (f n).
```

For every enumeration $f$ there exists a binary process $g$ not equal to
any $f n$—and this $g$ is simply `diagonal` $f$. The file also presents
the same result as a direct negation of the enumerability of the whole
space:

```coq
Theorem binary_processes_not_enumerable :
  ~ exists f : nat -> BinProcess,
      forall p, exists n, bp_eq (f n) p.
```

No function $f$ from indices to binary processes covers them all: the
diagonal always escapes.

{
Let us state exactly what this theorem is *not*. It is *not* the same
theorem as `unit_interval_uncountable_trisect_v2` of Chapter 4.4. That
one spoke of Cauchy processes in the interval $[0,1]$; this one speaks
of binary processes in the Cantor space $2^ℕ$. Two different models—two
different Cantor theorems, even if about “one and the same thing” in
the informal sense. The binary one is simpler and more constructive; and
it clears the ground for the main result. Uncountability is
established; now the question is not “how many” processes there are,
but *how* their collections *are arranged*.
}

## Trees and Closed Collections

### The Tree as a Decidable Predicate

To speak of the *structure* of collections of binary processes, the
apparatus of trees is needed. A binary process lays its path through
forks: at each step—left (`false`) or right (`true`). A finite segment
of such a path is a finite list of Boolean values; and a *tree* is an
indication of which finite segments are admissible.

In `ProcessTypes.v` a tree is defined as follows:

```coq
Definition PrunedTree := list bool -> bool.
```

A tree is a function from finite binary strings to Boolean values: for
each string it says `true` (the string is a node of the tree) or `false`
(it is not a node). It is essential that the value here is `bool`, not
Prop. This is a *decidable* predicate: the membership of a string in the
tree is a finite operation that terminates with a definite answer. Such
is the $P4$ refactoring: membership of a node in a tree must be
*checked* in a finite number of steps, not “established” as a logical
property. And indeed the file proves decidability directly—the lemmas
`tree_mem_dec`, `is_splitting_dec`, and others—and proves it *without
recourse to classical logic*, by a simple case analysis on Boolean
values.

### What Is Required of a Tree

Not every function `list bool -> bool` is a tree. The condition “to be a
tree” is given by the predicate `is_tree`:

```coq
Definition is_tree (T : PrunedTree) : Prop :=
  T [] = true /\
  forall sigma, T sigma = true -> T (removelast sigma) = true.
```

Two requirements. First: the empty string—the *root*—is a node
($T [ ] = `true`$). Second: *prefix-closedness*—if a string is a node,
then the string without its last element (`removelast`) is a node too.
In other words: every node is reachable from the root; the tree has no
pieces “hanging in the air.”

Here precision is needed, so as not to read the definition as stronger
than it is. The type is called `PrunedTree`—a “pruned tree”—but
`is_tree` does *not* require that every node have at least one
child—that is, it does not require the absence of “dead ends.”
“Pruned” here is the name of the type, not a proved mathematical
property. The condition `is_tree` consists of exactly two points: the
root and prefix-closedness, and nothing beyond. Branching properties,
when they are needed, are given *separately*—through the predicate
`is_perfect` and the lemmas connected with it (§ 5.5).

### Paths and Closed Collections

An infinite path through a tree is a binary process every finite initial
segment of which is a node of the tree. In the file this is the
predicate `is_path`: a process $p$ is a path of a tree $T$ if for every
$n$ the initial segment of $p$ of length $n$ belongs to $T$.

Now the main notion of the section. A collection of binary processes is
called *closed* if it is exactly the set of all paths of some tree:

```coq
Definition is_closed (C : BinCollection) : Prop :=
  exists T : PrunedTree,
    is_tree T /\ forall p, C p <-> is_path T p.
```

$C$ is closed if there exists a tree $T$ such that membership in $C$ is
equivalent to “being a path of $T$.” A closed collection is exactly a
collection given by a tree.

The word “closed” is not chosen by chance. Classically, the collections
of paths of trees are exactly the closed subsets of the Cantor space;
and the phrase “a closed collection contains all its limit paths” is a
correct topological reading. But a reservation is needed here about
what is *built in the code* and what is only an interpretation. The
supporting files define *neither* a general topology, nor limits, nor a
closure operation. Closedness is given *by trees*—through the
equivalence of “being in $C$” and “being a path of a tree”—and for the
Cantor space this form is equivalent to the topological one. So
“contains its limit paths” is a *topological reading* of the tree
notation, a way of explaining it, not a separate definition of the
formalization. The chapter uses the word “closed” in its exact, tree
sense: a collection is the set of paths of a tree.

And it is to closed collections—not to arbitrary ones—that the main
theorem will apply. This is the first of its safeguards, and from here
on the chapter will keep it constantly in view.

## Perfect Subtrees

### The Splitting Node

The dichotomy toward which the chapter is moving will oppose two
structural types of collections. One type is the enumerable ones,
traversable by a countable list. The other is those that cannot be
traversed; and to describe it, the notion of a *perfect* tree is needed.
It begins with the notion of a splitting node.

A node of a tree—a finite string—can have continuations. To the left, if
the string with `false` appended is also a node (`has_left`); to the
right, if the string with `true` is a node (`has_right`). A node is
called *splitting* if it has *both* continuations:

```coq
Definition is_splitting (T : PrunedTree) (sigma : list bool) : Prop :=
  has_left T sigma /\ has_right T sigma.
```

At a splitting node the path *forks in two*: one can go either way, and
both continuations remain in the tree. A splitting node is a place of
genuine choice.

### The Perfect Tree

A tree is called *perfect* if branching in it does not run dry—if from
every node one can reach a splitting one:

```coq
Definition is_perfect (T : PrunedTree) : Prop :=
  is_tree T /\
  forall sigma, T sigma = true ->
    exists tau, T (sigma ++ tau) = true /\
                is_splitting T (sigma ++ tau).
```

From any node $\sigma$ there is a continuation $\tau$ leading to a
splitting node $\sigma \mathbin{+\!\!+} \tau$. In a perfect tree,
wherever one goes, there is *always* a new fork ahead. Branching resumes
without end.

A collection *contains a perfect subset* if some perfect tree is
embedded in it entirely by its paths. The definition
`has_perfect_subset` says exactly this: there exists a tree
structure—with a root, prefix-closed, perfect (every node extends to a
splitting one)—all of whose paths lie in the collection.

### Two Levels: The Decidable Tree and the Logical Witness

Here is an important architectural subtlety, which the chapter is bound
to name directly. The trees of *closed collections* (§ 5.4) are given
*decidably*: the type `PrunedTree` is `list bool ->
bool`, and the membership of a node is a finite computable check. But the perfect
subtree that the main theorem *extracts* is given differently. In the
definition `has_perfect_subset` the witness is a structure

```coq
mem : list bool -> Prop
```

with values in Prop, not in `bool`. This is a *logical* predicate, not
necessarily a computable one.

The difference is not accidental, and it is a deliberate boundary, not
an oversight of the formalization. The original tree of a closed
collection is decidable: for every string it is known in finite time
whether it is a node or not. But the perfect subtree obtained by the
Cantor–Bendixson theorem—its *kernel*—can be given only as a logical
property: “the string belongs to the kernel” is a statement for which
there may be no computable check. Therefore the chapter, speaking of
$P4$-decidability, keeps the two levels apart: membership in the
original tree is a finite check (`bool`); membership in the perfect
kernel is a logical property (Prop). To say that the *whole*
construction of the perfect kernel is decidable would be wrong; what is
decidable is the *original* tree, while the kernel is a predicate over
Prop.

### What “Perfect” Means in Substance

Behind the formal definition stands a clear image. A perfect subtree is
a *cluster* of processes that branches again and again and nowhere
degenerates into separate, isolated points. In it, wherever one moves,
the path ahead will fork again; the choice of branches is never
exhausted.

One wants to say: in a perfect subtree there are “continuum-many”
processes. And this is the right word—but it must be understood
correctly, otherwise it will bring us back to the language of
cardinalities that the chapter has declined. “Continuum-many” here
does *not* mean a cardinality—a ready number of elements of a completed
collection. It means a structural property: *inexhaustible branching*.
After every node there is a continuation to a new fork, and the process
of choosing branches does not end. The perfect subtree is the process
analogue of the continuum character: an inexhaustible branching of
structure, not a cardinality as a ready magnitude. It is in this
sense—structural, not quantitative—that the perfect subset will be the
second pole of the dichotomy.

## The Cantor–Bendixson Dichotomy{The Cantor-Bendixson Dichotomy}

### The Main Theorem

The whole apparatus is assembled—binary processes, trees, closedness,
branching, perfection—and the central theorem of the chapter can be
stated. In `ProcessContinuumHypothesis.v` it is written as follows:

```coq
Theorem process_continuum_hypothesis :
  forall C : BinCollection,
    is_closed C ->
    is_enumerable C \/ has_perfect_subset C.
```

Let us read it word for word. For every collection of binary processes
$C$, *if it is closed*, one of two things holds: either $C$ is
enumerable, or $C$ contains a perfect subset. The conjunction “either …
or” here is a proved *dichotomy*: one of the two possibilities
necessarily holds.

Let us note at once both conditions—the safeguards of the theorem.
First, $C$ must be *closed*: the theorem speaks of collections given by
a tree (§ 5.4), not of arbitrary `BinCollection`. Second, everything
takes place in the *binary* model—in the Cantor space (§ 5.2), not in
the Cauchy model of the interval. Within these limits the dichotomy is
complete.

### The Conceptual Core of the Proof

The proof of the theorem is technically long, but its *idea* is one,
and it is remarkably clear. It is the idea that is worth setting out,
without retelling the calculations.

The question of the dichotomy is why there is nothing *third*, nothing
intermediate, between “enumerable” and “contains a perfect subset.” The
answer rests on a single alternative concerning *branching*.

Take a closed collection and its tree. Let us ask: does genuine
branching—splitting into *both* children, leading in both directions to
new splittings—resume in the tree without end?

*If yes*—branching resumes infinitely—then a perfect subtree sits in the
tree: that same inexhaustible cluster of forks from § 5.5. The
collection contains a perfect subset. This is the second pole of the
dichotomy.

*If no*—if repeated branching runs dry at some moment—then the
following happens. Since there is no node that splits both ways with a
continuation, the part of the tree essential for non-enumerability can
no longer be held up by two branching directions and, for the purposes
of classifying paths, *reduces to a main chain with countably
classifiable deviations*. One can single out one *main chain*—a single
“main-line” path (in the file it is built by the direction-choice
function `pick_dir`). And then every path of the tree is arranged
simply: it either *follows* this main chain to the end, or *deviates*
from it—and the deviation has a *first* step at which the path left the
main line. There is at most one path that follows the main chain. And
the deviating paths are classified *by the index of the first
deviation*: for each index its own class, and each such class is
enumerable. There are countably many classes in all (one per step
number), and a countable union of enumerable collections is enumerable.
Hence the whole collection is enumerable too. This is the first pole of
the dichotomy.

That is the whole core: *either branching resumes without end—and then
there is a perfect subset; or there is not enough branching—and then the
tree is a chain with countable deviations, and the collection is
enumerable*. The intermediate simply has nowhere to fit: resumable
branching either suffices for a perfect subtree or it does not—and then
the structure collapses into the countable regime. In the formalization
this fork is carried by two lemmas: `no_split_implies_enum` (no
resumable branching $\Rightarrow$ enumerable) and
`perf_subtree_has_splitting` (a perfect subtree always branches
somewhere).

### Both Poles Are Inhabited

The dichotomy would be empty if one of its outcomes were impossible. The
file checks that both outcomes are *real* by two limiting cases. The
empty collection is closed and enumerable (`empty_closed_enum`)—this is
the pole of enumerability. And the whole collection of binary processes
has a perfect subset (`full_has_perfect`)—the pole of perfection. Both
sides of the dichotomy are inhabited: neither “enumerable” nor
“contains a perfect subset” stands empty.

### The Names of the Theorem

{
The file gives the central result a second name as well—
`no_intermediate_process_type`—proving it by a verbatim repetition of
the first. The name is chosen to be telling: it stresses the essence—there
is no intermediate *type*. A closed collection of binary processes falls
into one of two structural alternatives: it is enumerable or it
contains a perfect subset. What matters most for the present chapter is
the absence of an *intermediate* case: if a closed collection is not
enumerable, it already contains a perfect subset. This is exactly what
the third formulation of the theorem, `PCH_structural_dichotomy`,
carries: a closed and *non*-enumerable collection necessarily contains a
perfect subset—the same dichotomy, read as an implication. (That the
two alternatives are, in addition, *mutually exclusive*—an enumerable
closed collection would not contain a perfect subset—is mathematically
to be expected for the Cantor space, but no separate lemma on
incompatibility is singled out in the supporting file; the chapter
therefore speaks of the absence of an intermediate case without
asserting formal mutual exclusivity as proved.)
}

## The Process Reading of the Continuum Hypothesis

### The Name and Its Danger

In the file the central theorem is named
`process_continuum_hypothesis`—“the process continuum hypothesis.” The
name is expressive, and it requires careful analysis; otherwise it will
be read as far stronger than the theorem is.

Let us say at once and plainly: this theorem does *not* settle the
classical continuum hypothesis. It neither proves nor refutes it. The
classical continuum hypothesis is a statement of set theory: there is no
cardinality *strictly between* the cardinality of a countable set and
the cardinality of the continuum. This is a question about
*cardinalities*—about the sizes of completed infinite sets.
`process_continuum_hypothesis` formally *has no bearing* on this
question: it is not about cardinalities and not about completed sets.

### What the Theorem Really Is

What, then, is it? Formally, `process_continuum_hypothesis` is the
process version of the classical *Cantor–Bendixson* theorem, also known
as the perfect set theorem (perfect set dichotomy). The classical
Cantor–Bendixson theorem says: every closed subset of a suitable space
is either countable or contains a perfect subset. This is a structural
theorem about closed sets, and, unlike the continuum hypothesis, it is
provable by ordinary means.

{
The process version is exactly what was analyzed in § 5.6: every
*closed* collection of binary processes is either enumerable or contains
a perfect subset. This is a structural dichotomy, not a statement about
cardinality. The name given in the file, `no_intermediate_process_type`,
names the essence more exactly than the title one: there is no
intermediate *structural type*.
}

### How the Dichotomy Takes the Place of the Continuum Question

Where, then, does the name “continuum hypothesis” come from—and in what
sense is it justified? In this one. The classical continuum hypothesis
asked: is there an *intermediate* rung between the countable and the
continuum? Under $P4$ this question, as § 5.1 showed, loses its
original subject—there are no cardinalities. But it has a process
*heir*. The question is translated from cardinalities to structural
*types*: is there an intermediate *type* of closed collection—between
one traversable by a countable list and one that branches
inexhaustibly?

And to this reformulated question the theorem gives an answer—a
*negative* and proved one. A closed collection of binary processes is
either “of the enumerable type” (traversable by a countable list) or “of
the continuum type” (it contains a perfect subset).
There is no intermediate structural type. The Cantor–Bendixson
dichotomy *takes the place* where classically the question of an
intermediate cardinality stood: the same interest—whether there is
something between the countable and the continuum—but posed
structurally and given a rigorous answer.

Let us stress the boundary once more, so that it stands firm. This is
*not* a resolution of the classical continuum hypothesis, nor a claim to
one. It is a *different* theorem—the Cantor–Bendixson theorem—which
under $P4$ *takes the place* of the classical continuum question, having
translated it from the language of cardinalities into the language of
structural types. “The process continuum hypothesis” is a name given by
this role, not by identity with the classical statement.

### Why This Is the Process Continuum

Now one can say what the “process continuum”—the notion placed in the
title of the chapter—is. It is neither a completed uncountable set nor a
cardinality. The process continuum is a structural *state of affairs*:
that among closed collections of binary processes there are exactly two
types, and one of them—the inexhaustibly branching one, continuum-like
in the structural sense of § 5.5—is the process form of the continuum
character. Under $P4$ “continuum” is the name of a *structural type*,
not of an object: the type of collections whose branching cannot be
exhausted by any enumeration. The dichotomy of § 5.6 says that this
type exists, that it is separated from the countable one, and that
there is nothing intermediate between them. This is the process
continuum—a proved structural fork, not a thing.

### E/R/R Analysis: The Process Continuum as a System

{
Let us secure what has been read by an E/R/R analysis (Part I). The
header of the supporting file gives the labeling directly:
*elements—binary processes (the Cantor space $2^ℕ$); roles—closed
collections, perfect subtrees, paths; rules—the continuum-hypothesis
dichotomy, Cantor–Bendixson*.[^1] We conduct the analysis in the
ontological order Rules $\to$ Roles $\to$ Elements. A reservation about
status: the dichotomy is proved in the *binary* model $2^ℕ$, separate
from the Cauchy model of Chapters 4.2–4.4 (§ 5.8); the “system” is a
substantive interpretation over the type `BinProcess`, read
operationally.}

{
*Rules* (the laws $L3$, $L4$).
The constitution is the Cantor–Bendixson dichotomy itself
(`process_continuum_hypothesis`): every closed collection is either
enumerable or contains a perfect subset, and there is no intermediate
structural type (`no_intermediate_process_type`). Added to it are the
decidable tree (`PrunedTree`, a predicate over finite prefixes) and the
countable union of enumerable classes (`countable_union_enum`). The
logical means are exactly two axioms: $L3$ (`classic`) and $L4$
(`L4_witness`; the latter extracts the enumerator of a class—work
*resembling* choice, but at the level of witnesses, not the
set-theoretic axiom of choice, § 5.8).

*Roles—the significance of positions* (the law $L4$). The roles are the
*two structural types* of a closed collection: the *enumerable* one
(traversable by a countable list) and the *continuum* one (containing a
perfect subtree—an inexhaustibly branching one). The perfect subtree
plays the role of the “continuum kernel,” the paths the role of the
elements of the collection. And “continuum” here is the role of a
*structural type*, not the name of an object: the type of collections
whose branching cannot be exhausted by an enumeration.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The
elements are binary processes, `BinProcess := nat -> bool` (the Cantor
space $2^ℕ$). By $L1$ each is identical to itself. By $P4$ this is a
*type* of process rules (a rule answers a finite request $n$ with the
value `true`/`false`), not a completed set; there is no completed
uncountable object at the level of elements (§ 5.2).}

 Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| the CB dichotomy; no intermediate type | constitution (fork) | Rule |
| decidable tree; countable union ($L4$) | closedness, numbering | Rule |
| two types: enumerable / continuum | roles (structural types) | Role |
| perfect subtree; paths | kernel and what is borne | Role |
| binary processes (`nat -> bool`, $2^ℕ$) | bearers (type, $P4$) | Element |
| laws $L1$–$L5$ (here $L3$, $L4$) | universal layer | Rule (univ.) |

{
*Well-formedness.* The labeling is unambiguous: binary processes are the
elements, the two types and the perfect kernel are the roles, the
dichotomy and the tree are the rules. $P1$ is observed: a collection is
a collection of *processes*, and the tree is a decidable predicate over
finite prefixes; there is no self-membership. And here the analysis
turns into *diagnostics*—completing the process line. The “continuum
hypothesis” in the name of the theorem is dangerous (§ 5.7.1): to take
it for a *resolution* of the cardinality CH or for an *uncountable set*
is the same confusion of categories that lies at the root of the whole
volume ($P4$, Chapter 4.1): a *structure* (a rule-fork) is read as an
*object*. In the correct labeling the “process continuum” is a
*role*-type—a proved structural fork—not a thing and not a cardinality.
Honest boundaries: the mutual exclusivity of the two types is not
singled out as a separate lemma (the chapter speaks of the *absence of
an intermediate* case, not of proved incompatibility); the perfect
kernel is a logical witness (Prop), not a decidable tree; the model
$2^ℕ$ is kept separate from the Cauchy model.}

 What the analysis yields. The continuum, read by E/R/R, is the last of
the process recastings: infinity became a process (Chapter 4.1), the
number a process (4.2), the point a class (4.3), uncountability a rule
about processes (4.4), and the continuum a structural *type*, a fork
between the countable and the inexhaustibly branching. Each time an
*object* of the classical picture turns out to be a *role* or a *rule*
of the process picture.

## What Is Proved and What It Rests On. Summary of Part IV

### What Is Proved

Let us gather the result of the chapter exactly. A *structural
dichotomy* is proved: every closed collection of binary processes is
either enumerable or contains a perfect subset. Among closed collections
there are exactly two structural types—the countable and the continuum
type—and there is no intermediate type. This is the process version of
the Cantor–Bendixson theorem; under $P4$ it takes the place of the
classical continuum question, translating it from the language of
cardinalities into the language of structural types.

The dichotomy is established in the *binary* model—the Cantor space
$2^ℕ$—separate from the Cauchy model of Chapters 4.2–4.4. This is a
deliberate separation: the Cauchy model is closer to the number line and
good for a conversation about magnitudes; the binary model is cleaner
for a conversation about structure. Two models—two branches of the
process formalization of the continuum—and the chapter worked in the
second.

### What It Rests On

Let us name the logical means. The central theorem in
`ProcessContinuumHypothesis.v` rests on *two* axioms—both times these
are laws of the logic of ToS. The first is $L3$, classical logic (the
axiom `classic`). The second is $L4$, the law of sufficient reason (in
the file, `L4_witness`).

It is worth saying *where* $L4$ appears, because the place is
instructive. At one point the proof takes a *countable union* of
enumerable collections—when the paths that deviated from the main chain
are gathered into one class over all the indices of the first deviation
(§ 5.6). For such a union to remain enumerable, two things are needed.
The first is the Cantor pairing of natural numbers from the standard
library: a technical function that assigns one index to a pair $(a,b)$
one-to-one; it makes it possible to number “the class index plus the index
within the class” by a single number. This is a *computational device*,
not “the cardinality of the continuum”—simply a way of reducing a double
numbering to a single one. The second is $L4$, `L4_witness`: for each
class it *extracts* a concrete enumerator. This is where the law of
sufficient reason is at work: every enumerable class *has* a ground—a
witness of its enumerability—and $L4$ makes it possible to take this
witness.

{
And—just as important—let us name what the proof does *not* contain.
There is no *axiom of choice* as a separate set-theoretic axiom—an act
of choice over a completed family of sets. This, however, must be stated
exactly. `L4_witness` in `countable_union_enum` performs work
*resembling* choice, but at the level of witnesses: from the proof of
the enumerability of each class it extracts a concrete enumerator. The
correct formulation is therefore this: the proof does not use a separate
set-theoretic axiom of choice over completed families of sets, but it
does use $L4$-witnessing as an internal law of ToS. This is the law of
sufficient reason at work, not set-theoretic choice—and it is more
honest to name it than to pass over it in silence.
}

Nor is there *completed infinity* as a ready object: the proof does not
use a ZFC-like axiom of infinity. Here, too, a reservation is needed, so
that no false impression arises. Of course, the inductive type `nat` and
the function types—`nat ->
bool`, `BinCollection`—are used in the proof: these are types of the
Rocq language, and their $P4$ reading is processual and type-based, not
a reading as completed sets (§ 5.2). What is not used is precisely the
*set-theoretic axiom* of completed infinity—the postulate of a ready
infinite set as an actual object. The file checks this by machine—with
the command `Print Assumptions`, which for a specified theorem outputs
the list of axioms it depends on; the list contains $L3$ and $L4$, and
neither choice nor the axiom of infinity. (As in Chapter 4.4, let us
state: `Print Assumptions` checks the dependencies *of the specified
theorem*; it does not “scan the file.”) The two auxiliary files stand
even lighter: `ProcessTypes.v` and `ProcessDiagonal.v` each appeal to
$L3$ in only one lemma—and the key `diagonal_differs` (§ 5.3) uses no
axioms at all. The decidability lemmas for trees are proved without
recourse to classical logic; the file `ProcessTypes.v` itself, however,
imports the module of the laws of ToS, and one of its
lemmas—`not_enum_union`, which analyzes the non-enumerability of a
union—uses $L3$. So one must speak exactly: the *decidability of trees*
is without axioms; the file as a whole, with one.

### Summary of the Chapter. Transition to Chapter 4.6

This chapter has completed the process line of the continuum: everything
that was classically called an uncountable set of points or a measure of
cardinality has appeared as a structural dichotomy of closed collections
of binary processes. With this the last of the five recastings of
Part IV has been carried out—infinity, number, point, uncountability,
continuum.

But Part IV does not yet close with this chapter. It remains to draw up
the *balance* of the whole part: what $P4$ has *cut off* over five
chapters, what it has *kept*, with what *strength* each result is tied
to the starting points, and what has remained open. This balance—and
the overall summary of Part IV—is drawn up by the concluding
Chapter 4.6, which reads $P4$ no longer only as the ontological
principle of processes but also as a *filter* of the admissible strength
of a statement. The process continuum itself, at which the present
chapter has arrived, can now be summed up in three points.

{*The summary of the chapter comes in three parts. First: what is proved.
Every closed collection of binary processes is either enumerable or
contains a perfect subset; there is no intermediate structural type.
This is the process version of the Cantor–Bendixson theorem—a structural
dichotomy that under $P4$ takes the place of the continuum question, not
a statement about cardinality and not a resolution of the classical
continuum hypothesis. The process continuum is a proved fork between the
countable and the inexhaustibly branching structural types, not an
object.*}

{*Second: what it rests on. The dichotomy is proved in the binary
model—the Cantor space $2^ℕ$, separate from the Cauchy model of
Chapters 4.2–4.4—on three supporting files. The central theorem rests on
two axioms—the laws of logic $L3$ and $L4$ ($L4$ for the countable
union of enumerable classes). A separate set-theoretic axiom of choice
and an axiom of completed infinity are *not* used.*}

{*Third: what remains open. The theorem applies to *closed*
collections—those given by a tree; it does not cover arbitrary
collections. The perfect subtree is extracted as a logical witness (a
predicate over Prop), not as a decidable tree—the original tree of the
collection is $P4$-decidable, but the Cantor–Bendixson kernel is not.
The relation between the two models is now established *partially*: the
file `ProcessBinReal.v` builds a direct translation
`bin_to_real` $\colon 2^ℕ \to [0,1]$
(`bin_to_real_in_interval`, `bin_to_real_is_Cauchy`—the latter rests on
$L3$) and proves the model identification `bin_ones_equiv_one`
($0{,}111\ldots_2 = 1$). What remains open is the *full* translation—the
inverse map $[0,1] \to 2^ℕ$, the general ambiguity of representation,
and the transfer of the Cantor–Bendixson dichotomy itself to the Cauchy
model; the connection of the two branches in full awaits a separate
investigation.*}

---

[^1]: The E/R/R labeling in the header of the file `ProcessContinuumHypothesis.v`; here it is unfolded on the model of Part I.

---

Part: [[04 Process Real Numbers|Part IV. Process Real Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/04 Uncountability of Processes|Chapter 4. The Uncountability of Processes]] · [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/06 P4 as a Filter|Chapter 6. P4 as a Filter]] →
