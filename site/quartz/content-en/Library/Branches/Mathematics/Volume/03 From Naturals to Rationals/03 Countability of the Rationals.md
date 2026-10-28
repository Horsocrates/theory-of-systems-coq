---
title: "Chapter 3. The Countability of the Rational Numbers"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/03 От натуральных к рациональным/03 Счётность рациональных чисел.md"
sourceBlob: fd03382f10b4cb228cd1113d69942f42f303cd70
translated: 2026-10-20
status: draft
---

## What Countability Means in the Theory of Systems

### The Question Left by the Previous Chapter

Chapter III.2 built the rational numbers—a coordinate marking with a commensurable step—and at the end it left a question that it had only indicated. The rational numbers are positions of a commensurable marking, and this marking is not completed: after every position reached there is a next one; every interval is divisible still more finely. Can one then speak of the rational numbers as a *list*—enumerate them one after another so that every one is reached?

This question—about the *countability* of the rational numbers—is the subject of the present chapter. But before answering it, we must agree on what the word “countability” means in ToS at all. Standard mathematics and ToS understand it differently, and the difference is not verbal.

### Countability in the Standard Exposition

The standard definition is as follows. A set $X$ is called *countable* if there exists a bijection $f \colon ℕ \to X$—a one-to-one correspondence between the natural numbers and the elements of $X$. A set is countable if such a function *exists*.

In this definition two things are taken as self-evident. The first: $ℕ$ and $X$ are taken as *ready sets*—completed collections lying at hand, between which a correspondence is established. The second: countability is the *existence* of a function—a fact that the function is there in principle, regardless of whether it has been presented.

For standard mathematics both assumptions are habitual and work. And it is worth saying directly at once: ToS does *not* declare the standard definition inapplicable. The property of countability itself can perfectly well be expressed formally too—as a statement about the injectivity and surjectivity of some function; it is in precisely this form that it is proved in Rocq, and ToS uses this proof. The difference between ToS and the standard exposition lies not in the standard notion’s being inapplicable but in the *methodological form* that ToS requires of countability. As Part II already showed, ToS does not take infinite collections as ready (the principle $P4$): the natural number series is a potentially continuable series, not a completed set; and the rational numbers, as Chapter III.2 showed, are a potential marking, not a completed set. Therefore ToS requires of countability not merely a *statement of the existence* of a correspondence but a stronger form: an *explicit traversal* that can be computed, traced step by step, and inverted. Not “the function is there in principle,” but “here is the procedure, and it works.” Countability in ToS is read operationally—and the chapter goes on to build this operational form.

### Countability as a Traversal Procedure

ToS redefines countability operationally.

*A collection is countable if there exists a constructive procedure that, for every natural number $n$, builds the $n$-th element of the traversal, and an inverse procedure that, for every element, finds its index.*

This is a *working possibility*, not a “fact about a set.” Countability in this sense means: one can start the traversal, and the traversal will reach any element in a finite number of steps. Not “a bijection between two ready collections exists,” but “there is a procedure, and it works”: an index is presented—the procedure builds the element; an element is presented—the procedure finds the index.

It is worth stipulating that this is a *strengthened* form of countability. Ordinary countability in standard mathematics can be given in different ways—by a surjection $ℕ \to X$, an injection $X \to ℕ$, a bijection, or an enumeration—and not every one of these forms requires being able to *effectively find the index* of a presented element. The requirement of an inverse procedure—“from an element, find its index”—is stronger than the minimal one: it is effective indexing with computable inversion. In this chapter ToS takes precisely the strong, operational form: not only the procedure $n \mapsto x_n$ but also its inverse. This is a working strengthening, and it is chosen for a reason: for the rational numbers such a strengthened form, as the chapter will show, is available—the traversal of the Calkin–Wilf tree is invertible, and the inverse pass is also built explicitly.

The difference from the standard definition lies in what is being spoken of, not in rigor. The standard definition speaks of a *correspondence between sets*; the operational one, of a *procedure* that can be started and traced. The standard one asks “does a function exist”; the operational one, “is there a traversal, and does it reach.” For a collection that is a potential marking rather than a completed set, only the second is meaningful: one cannot establish a correspondence with what has not been gathered into a ready whole—but one can set a procedure that traverses this potential.

### What Remains to Be Shown

The countability of the rational numbers thus means the presence of a *working traversal procedure*—one by which every rational number is reachable in a finite number of steps and which assigns an index to every rational number—not the existence of a bijection with a ready set.

The present chapter will present such a procedure. Instead of referring to an existence theorem, it will build the traversal explicitly—trace its arrangement and show that it reaches every rational number. First, however, we must say why an explicit construction is necessary here and a reference to existence is not enough. This is how the chapter continues.

## What an Explicit Bijection Is Needed For

### The Standard Proof of Countability

Standard mathematics proves that the rational numbers are countable, and proves it briefly. The argument runs as follows. Every rational number is a pair—a numerator and a denominator—that is, the rational numbers are a subset of the product of the integers by the nonzero integers. The product of two countable collections is countable—this is a well-known theorem. Hence its subset is countable as well. Therefore the rational numbers are countable.

The proof is correct, and within standard mathematics there is nothing to object to in it. It is only worth noting by what exactly it proves countability. It proves it *through general theorems*: it refers to the theorem on the countability of products and subsets, which in turn refers to its own grounds, and in the end it is asserted that a bijection between the natural and the rational numbers *exists*. Such a route is correct—but it hides the very *mechanism* of the traversal: what the bijection is, how it is arranged, what it gives on the input $n = 5$ or $n = 100$—none of this is directly visible from a proof through general theorems. One should not, however, fall into caricature: standard mathematics is *not* limited to this abstract route—textbook proofs often give an explicit diagonal enumeration of pairs, as well as traversals of trees such as the Calkin–Wilf or the Stern–Brocot tree. ToS does not reproach the standard approach for a lack of rigor. It merely *chooses*, of the two possible routes, the explicit one rather than the abstract one: to build a concrete enumeration function and its inverse pass, rather than to refer to the theorem on the countability of products.

### Why This Is Not Enough for the Theory of Systems

For ToS such a proof is unsatisfactory—and unsatisfactory in substance, not in rigor.

Countability in ToS (§ 3.1) is the presence of a *working traversal procedure*, not the existence of a bijection. To say “a bijection exists” is to answer a different question. The operational understanding of countability asks: *is there a traversal, and does it reach every element*? The answer “a function carrying out the traversal exists in principle” does not close this question: the existence of a function and the presence of a procedure that can be started and traced are not one and the same.

To refer to an existence theorem is to make a move that ToS everywhere marks specially: to pass from the question “how to build it” to the question “is there one, by a theorem.” ToS does not rule out such a move in standard mathematics, but it is not itself content with it: for ToS, *to exist* is to be built, actualized by a concrete act, not to be derivable from a theorem as an abstract possibility. Countability proved by reference to existence remains a statement that a traversal *could be*; countability in the sense of ToS requires that the traversal *be* presented.

### An Explicit Procedure Is Required

Hence what the present chapter must do. Not refer to a theorem but *present* a traversal: set a concrete procedure that can be computed, traced step by step, and checked to reach every rational number.

And such a procedure exists. It is called the *Calkin–Wilf enumeration*, and it is arranged so that it builds a rational number from every index and the index from every rational number, and builds them *computably*: every step is a concrete action that can be performed and checked. ToS formalizes this enumeration completely—and formalizes it, importantly, *constructively*: without references to abstract existence theorems, by construction alone.

*The standard proof of the countability of the rational numbers refers to existence theorems: a bijection between the natural and the rational numbers exists. ToS is not content with this: for it, countability is the presence of a working traversal procedure, not the existence of a function. Therefore the chapter does not refer to a theorem but presents the traversal explicitly—a concrete, computable procedure that builds a rational number from an index and an index from a rational number. This procedure is the Calkin–Wilf enumeration.*

### Toward the Construction of the Enumeration

The Calkin–Wilf enumeration rests on one elegant structure—a tree in which the rational numbers are placed so that its traversal becomes direct and visual. The chapter begins the construction with this tree.

## The Calkin–Wilf Tree

### The Positive Rational Numbers as Pairs

The construction of the traversal begins with the positive rational numbers—with the positions of the commensurable marking on one side of the reference point. It is on them that the traversal will be set; its extension to all the rational numbers, together with zero and the negative side, is added afterward and simply (§ 3.5).

A positive rational number is taken here via a *pair* of natural numbers—a numerator and a denominator.[^1] In Rocq this is written as follows:

```coq
Definition QPos := (positive * positive)%type.
```

The type `QPos` is the type of *all* positive pairs $(a, b)$: the first component is the numerator, the second the denominator. Two reservations are needed here. The first concerns the type `positive`. In the standard library of Rocq, `positive` is a separate *technical* type of positive natural values in binary notation; it is not identical to the type `nat` with the condition $n > 0$, and it is not the primary series $ℕ$, beginning with one, of which Part II spoke. Its role in this chapter is simple and purely auxiliary: it guarantees that the numerator and the denominator are positive, and in particular that the denominator is not zero. The second reservation concerns the relation between pairs and rational *values*. The type `QPos` contains all pairs, including reducible ones: $(2, 4)$ and $(1, 2)$ are different elements of `QPos`. But the Calkin–Wilf tree, as the chapter will show, enumerates precisely those pairs in which the numerator and the denominator are *coprime*; these irreducible pairs serve as the *canonical representatives* of the positive rational numbers. Taking a positive rational number via a pair is convenient in that it removes from the very start any concern about the sign and about zero: a pair of `positive` admits neither, by the arrangement of the type.

### The Root and Two Children

The Calkin–Wilf tree places the positive rational numbers at its nodes so that each one enters the tree *exactly once*. It is arranged by three rules.

The *root* of the tree is the fraction $1/1$:

```coq
Definition cw_root : QPos := (1, 1).
```

The *left child* of a node $a/b$ is the fraction $a/(a+b)$; the *right child* is the fraction $(a+b)/b$:

```coq
Definition cw_left  (ab : QPos) : QPos :=
  let (a, b) := ab in (a, a + b).
Definition cw_right (ab : QPos) : QPos :=
  let (a, b) := ab in (a + b, b).
```

From the root $1/1$, to the left lies $1/2$, to the right $2/1$. From $1/2$, to the left $1/3$, to the right $3/2$. From $2/1$, to the left $2/3$, to the right $3/1$. And so on without end: every node gives two children; the tree branches infinitely.

### Three Properties of the Tree

The Calkin–Wilf tree is not an arbitrary layout of fractions at nodes but a structure with three properties, and all its strength lies in these properties.

*The first: every positive rational number stands in the tree, and stands there exactly once.* Precision is needed here about what is to count as “the same” number. If a rational number is understood as a *value*, then each positive rational value appears in the tree exactly once—no omissions, no repetitions. If, however, a fraction is understood as a *raw pair* of a numerator and a denominator, then the tree enumerates only the *irreducible* pairs, not all pairs: a reducible notation like $2/4$ does not appear in the tree—it is already represented by the node $1/2$. In other words, the tree traverses the irreducible pairs as canonical representatives, and in this sense each positive rational value is reached once.

*The second: every fraction in the tree is irreducible.* In each node the numerator and the denominator are coprime—they have no common divisor greater than one. The tree does not generate $2/4$ or $3/6$; it generates $1/2$ at once, in irreducible form. This property is not brought in by a check but follows from the arrangement of the tree: the root $1/1$ is irreducible, and both rules—the left child and the right—preserve irreducibility. ToS proves this formally—by a theorem that the greatest common divisor of the numerator and the denominator in each node equals one.[^2]

*The third: the tree is binary.* Every node has exactly two children—left and right. This is what makes the tree suitable for traversal: the path to any node is a finite sequence of choices “left or right,” and such a sequence, as the next section will show, can be recorded by a number.

*The Calkin–Wilf tree places the positive rational numbers at its nodes: the root is $1/1$, the left child of a node $a/b$ is $a/(a+b)$, the right one is $(a+b)/b$. The tree has three properties: every positive rational number stands in it exactly once; every fraction in it is irreducible (which ToS proves formally); the tree is binary—every node has two children. It is these properties that make the tree the basis of the traversal of the rational numbers.*

### From the Tree to the Traversal

The tree has been built, and its three properties named. But the tree by itself is not yet a traversal: it places the rational numbers at nodes, but it does not line them up in a sequence numbered by the natural numbers. To obtain a traversal—a procedure that gives the $n$-th rational number from the index $n$—one must go through the nodes of the tree in some order. How this order is set and how it connects the natural numbers with the nodes is examined in the next section.

## The Traversal of the Tree: Navigation by a Binary Path

### The Path to a Node Is a Sequence of Choices

The Calkin–Wilf tree places the positive rational numbers at nodes (§ 3.3). To obtain a traversal from it, the nodes must be connected with the natural numbers—so that a node is found for every index, and an index for every node. One simple observation about the arrangement of the tree makes this possible.

To every node of the tree there leads a *unique path* from the root. The tree is binary: from every node there are two exits—left and right. Hence the path from the root to any node is a finite sequence of choices: left, right, left again, and so on to the required node. The root is the empty path, a sequence of zero choices. Its left child is a sequence of one choice, “left”; its right child, of one choice, “right.” And so on: to every node corresponds its own sequence of choices, belonging to it alone, and to every finite sequence of choices corresponds its own node.

### A Sequence of Choices Is Recorded by a Number

A finite sequence of choices “left or right” can be recorded by a *number*—and this is the key to the whole traversal.

A natural number in binary notation is nothing other than a finite sequence of binary digits. ToS uses this directly. The path to a node is encoded by a natural number according to three rules: the number $1$ is the path to the *root*; if a number $p$ encodes the path to some node, then the number written as $p$ with an appended binary zero encodes the path to its *left* child, and $p$ with an appended binary one, the path to its *right* child. In Rocq, where a natural number of type `positive` is itself built from binary constructors, this is written directly:

```coq
Fixpoint cw_node (p : positive) : QPos :=
  match p with
  | xH    => cw_root            (* 1 = root *)
  | xO p' => cw_left  (cw_node p')   (* left child *)
  | xI p' => cw_right (cw_node p')   (* right child *)
  end.
```

The function `cw_node` reads a number as a path and goes through the tree from the root to the required node.[^3] The constructor `xH`—one—gives the root. The constructors `xO` and `xI` intuitively correspond to adding one more binary step to an already given path—a passage to the left or to the right child: `xO` leads to the left child of the node to which the rest of the path leads, `xI` to the right one. The technical details of the order of bits in the inductive representation of the type `positive` do not matter here; one thing matters: each of the two constructors unambiguously encodes the next passage through the tree. Thus every number of type `positive` is read as a route through the tree, and to every route corresponds a node—a positive rational number.

### The Enumeration

It remains to connect with the nodes the *natural numbers* of the traversal—$0, 1, 2, 3, …$—rather than numbers of type `positive`, so that the traversal starts from zero, as befits an enumeration. This is done by a shift by one:

```coq
Definition enum_QPos (n : nat) : QPos :=
  cw_node (Pos.of_nat (S n)).
```

The enumeration `enum_QPos` takes a natural number $n$, adds one to it, and reads the result as a path through the tree. The shift by one is needed because paths are numbered from one (path $1$ is the root), while the traversal is numbered from zero.

Let us trace its first steps. Index $0$: path $1$, the root—the fraction $1/1$. Index $1$: path $2$, which is a binary zero appended to one—the left child of the root, the fraction $1/2$. Index $2$: path $3$, a binary one appended to one—the right child of the root, $2/1$. Index $3$: path $4$—the left child of the node with path $2$, that is, the left child of the fraction $1/2$—$1/3$. Index $4$: path $5$—the right child of the fraction $1/2$—$3/2$. The traversal lines up the positive rational numbers in a sequence:

$$
\tfrac{1}{1}, \;\; \tfrac{1}{2}, \;\; \tfrac{2}{1}, \;\;
\tfrac{1}{3}, \;\; \tfrac{3}{2}, \;\; \tfrac{2}{3}, \;\;
\tfrac{3}{1}, \;\; …
$$

This is the Calkin–Wilf enumeration: a procedure that, from every index $n$, builds the $n$-th positive rational number, and builds it *computably*—every step is a concrete action: add one, read the binary digits, go through the tree.

*The path from the root of the tree to any node is a finite sequence of choices “left or right,” and such a sequence is recorded by a natural number in binary form: one is the root, an appended binary zero is the left child, an appended one is the right child. The function `cw_node` reads a number as a path and finds the node; the enumeration `enum_QPos` shifts the numbering to zero and builds a positive rational number from the index $n$. The first terms of the traversal are $1/1, 1/2, 2/1, 1/3, 3/2, …$. This is a computable procedure: every step is a concrete action.*

### What Is Missing for a Bijection

Half the work is done: there is a procedure that builds a rational number from an index. But countability in the sense of ToS (§ 3.1) also requires the converse—a procedure that finds the index of a rational number—and requires a proof that the two procedures exactly invert each other. With this—the inverse procedure and the proof of the bijection—the chapter is occupied next.

## The Inverse Procedure and the Bijection

### From a Fraction to Its Index

The enumeration builds a fraction from an index (§ 3.4). Countability in the sense of ToS also requires the converse: from a fraction, its index. This inverse procedure is arranged as transparently as the direct one, and it rests on the same connection of a node with a path.

A positive rational number $a/b$ is given. To find its index is to trace the path from its node *back* to the root. This is done according to the arrangement of the tree. If $a = b$, the fraction is $1/1$—the root itself; the path is empty. If $a < b$, the fraction is the *left* child of some node: the left child of a node $c/d$ is $c/(c+d)$, so the parent node is recovered as $a/(b-a)$. If $a > b$, the fraction is a *right* child, and the parent is $(a-b)/b$. Repeating this step, we climb from a node to its parent, from the parent to its parent, and so on to the root, recording along the way whether each node was a left or a right child. In Rocq this is written as follows:

```coq
Fixpoint path_to_node_fuel (fuel : nat) (a b : positive)
  : positive :=
  match fuel with
  | O => xH
  | S fuel' =>
      if (a =? b) then xH
      else if (a <? b)
           then xO (path_to_node_fuel fuel' a (b - a))
           else xI (path_to_node_fuel fuel' (a - b) b)
  end.
```

The climb to the root is always finite—the number of steps is bounded by the sum of the numerator and the denominator—and this sum is passed as the first argument.[^4] The path traversed, read as a number, is what is sought; subtracting one from it gives the index in the traversal:

```coq
Definition index_of_QPos (ab : QPos) : nat :=
  Pos.to_nat (path_to_node ab) - 1.
```

### The Two Procedures Invert Each Other

There are, then, two procedures: the direct one—from index to fraction—and the inverse one—from fraction to index. For them together to make up a bijection, they must *exactly invert* each other: passing from an index to a fraction and back, one returns to the same index; passing from a fraction to an index and back, one returns to the same fraction.

ToS proves both—by two round-trip theorems. The first: for every path laid through the tree, the inverse procedure recovers exactly this path. The second: for every irreducible fraction taken to an index and back, exactly this fraction is recovered.[^5] The condition of irreducibility in the second theorem is essential: the inverse procedure recovers a fraction correctly only for irreducible fractions—but the tree, as § 3.3 showed, contains no others, so the condition is satisfied for every one of its nodes.

### The Main Theorem

Hence the main theorem of the chapter: the enumeration of the positive rational numbers is a bijection.

```coq
Theorem Q_positive_countable :
  (forall n m, enum_QPos n = enum_QPos m -> n = m) /\
  (forall a b, Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
     exists n, enum_QPos n = (a, b)).
```

The theorem asserts two things about the enumeration. The first half: it is *injective*—different indices correspond to different fractions; the traversal does not repeat itself. The second: it is *surjective*—every irreducible fraction is reached by the traversal; none is omitted. Injectivity and surjectivity together mean that the enumeration is a one-to-one correspondence between the natural numbers and the positive rationals. The countability of the positive rational numbers has been proved—and proved by presenting a working traversal, not by reference to existence.

One thing must be said specially about this proof. It is *fully constructive*: it is carried out by construction alone, without a single reference to abstract principles of existence. In particular, it does not use the Law of Excluded Middle—in any form. For ToS this is essential: countability here is not only *asserted* but also *built*—and this construction is a full-fledged proof that the statement is true. A constructive proof is no less a proof than any other: a procedure has been presented every step of which can be computed and checked, and it has been proved—rigorously—that this procedure traverses all the positive rational numbers, omitting nothing and repeating nothing. That the statement of countability is true is secured by the very traversal presented and by the proofs of its properties; “built” is not opposed here to “proved” but is the way in which ToS proves.

### All the Rational Numbers

What has been proved—and proved *formally*, by the theorem `Q_positive_countable`—concerns the *positive* rational numbers in irreducible representation. The extension of the traversal to *all* rational numbers—together with zero and the negative side—is now also secured by theorems: both the direct pass (a surjection) and the inverse one (from a rational, its index), and with them the complete bijection $ℕ \leftrightarrow ℚ$. The chapter gives the formula of the traversal and points to the theorems that close it.

The negative rational numbers are the same positive positions taken on the other side of the reference point (Chapter III.2, § 2.7); zero is the reference point itself. The traversal of all rational numbers is obtained from the traversal of the positive ones as follows. Zero is given the index $0$; then the indices alternate—odd ones carry the positive copy of the traversal, even ones (except zero) the negative one. In explicit notation, if $\operatorname{enum}_{ℚ^+}$ is the traversal of the positive rationals built above, the complete traversal $E \colon ℕ \to ℚ$ is given as follows:

$$
E(0) = 0, \quad
E(2n+1) = +\operatorname{enum}_{ℚ^+}(n), \quad
E(2n+2) = -\operatorname{enum}_{ℚ^+}(n).
$$

Every rational number—positive, negative, or zero—receives its own index in this alternation, and to every index corresponds exactly one rational number.

Here one must be exact about the status of this step—and it is now *closed*. In the file `Countability_Q.v` the formula given above is implemented literally: the function `enum_Q` sets $\operatorname{enum}_ℚ(0)=0$, assigns the positive copy of the traversal to an odd index, and the negative one to an even index (except zero). An *inverse* function `index_of_Q` is built for it: for an arbitrary rational—through reduction to irreducible form and the inverse pass for the positive ones—it finds its index, handling zero, plus, and minus. Both have been proved mutually inverse—by the theorems `enum_Q_index_id` ($\texttt{enum\_Q} (\texttt{index\_of\_Q} q) \mathrel{==} q$) and `index_of_Q_enum_id` ($\texttt{index\_of\_Q} (\texttt{enum\_Q} n) = n$)—and the theorem `Q_bijection` connects them:

`(forall n, index_of_Q (enum_Q n) = n)  /\ (forall q, enum_Q (index_of_Q q) == q)`.

This is a *complete bijection $ℕ \leftrightarrow ℚ$ with computable inversion*—now not only for the positive rationals but for the whole of $ℚ$, constructively and *without a single axiom* (`Print Assumptions
Q_bijection`: “Closed under the global context”).

One precision of formulation remains—not a limitation but the right measure. The bijection connects $ℕ$ with $ℚ$ *taken up to* `Qeq`: the inverse pass goes through the reduction `Qred`, so that $2/4$ and $1/2$ receive one index. It cannot be otherwise—on raw notations of fractions there is no bijection, for $2/4$ and $1/2$ are different notations of one number (§ 2.5). Hence `index_of_Q_enum_id` is exact on $ℕ$ (equality of indices), while `enum_Q_index_id` holds up to `Qeq` on $ℚ$; together this is precisely a bijection of rational *values*.

*The inverse procedure `path_to_node` traces, from a fraction, the path from its node to the root and finds the index. Two round-trip theorems prove that the direct and the inverse procedures exactly invert each other. The main theorem `Q_positive_countable` asserts that the enumeration is injective and surjective—that is, it is a bijection for the *positive* rational numbers. The proof is fully constructive, without the Law of Excluded Middle: countability is not merely asserted but built—and the construction is the way of proving it. The traversal of all rational numbers—with zero and the negative side—is implemented by the function `enum_Q` according to the formula $E(0)=0$, $E(2n+1)=+\operatorname{enum}(n)$, $E(2n+2)=-\operatorname{enum}(n)$; the inverse pass `index_of_Q` is built for it, and the theorem `Q_bijection` proves that they are mutually inverse—a complete bijection $ℕ \leftrightarrow ℚ$ (up to `Qeq`, 0 axioms) now for the whole of $ℚ$.*

### What Has Been Proved

The countability of the rational numbers has been proved—by building an explicit, computable, constructively grounded traversal. It remains to understand what this result means ontologically: what the rational numbers turn out to be, given that they can be traversed in this way. The chapter turns to this in the next section.

## What Countability Means Ontologically

### The Rational Numbers Are Reachable by a Traversal

The countability of the rational numbers has been proved by building a traversal (§ 3.5). It is now worth saying what this result means in substance—what the rational numbers turn out to be, given that they can be traversed in this way.

First of all, what countability does *not* mean. It does not mean that all the rational numbers are gathered into a ready, completed collection that the traversal “counts over.” Chapter III.2 showed: the rational numbers are a potential marking, not a completed set, and Chapter III.3 does not revoke this. The traversal does not gather the rational numbers into a ready whole; it *reaches* them.

And here is what countability means positively. The rational numbers are *reachable by a traversal*—they can be represented as a potentially continuable list given by a traversal procedure, not as a ready, completed list lying at hand. Every individual rational number is reachable: start the traversal—and in a finite number of steps it will reach this number, name its index, build its fraction. There is no need to hold an infinite collection at hand; a procedure that reaches every member of it is enough. Countability is a property of this procedure—of its reaching—not a property of a gathered set.

### Ordinary Infinity

From countability it also follows what the infinity of the rational numbers is like.

The natural number series is potentially infinite: after every number there is a next one ($P4$, Part II). The rational numbers, at first glance, are arranged more richly: they not only stretch out to the sides, like the natural number series, but also condense—between any two of them lies one more (Chapter III.2). It may seem that this double inexhaustibility—both into the distance and into depth—means there are “more” rational numbers than natural ones, that their infinity somehow exceeds the infinity of the series.

Countability shows that this is not so. Since there is a traversal putting the natural numbers and the rational ones into one-to-one correspondence, every rational position has a finite index in the traversal and is reached in a finite number of steps. The denseness of the marking does not make the rational numbers less reachable: between two positions lies one more—but it too receives its finite index, and the traversal reaches it. The rational numbers are an *ordinary* infinity—the same as that of the natural number series: potential, reachable, enumerable. ToS does not describe this in the language of a “greater” or “lesser” infinity, the language of comparing sizes: it is precisely this language that ToS rethinks. The exact statement is simpler and stronger—denseness does not take the rational numbers beyond the bounds of what a traversal reaches; every one of them is enumerable and has a finite index. The rational numbers have no infinity that would exceed the infinity of the series.

This is an important result for ToS, and it is important in that it outlines a boundary. Everything the chapter has gone through so far—the natural numbers, the integers, the rationals—fits into one kind of infinity: potential and enumerable. Whether there is an infinity of another kind—and where the boundary of the enumerable runs—is a question that the rational numbers do not yet pose; it will arise later.

### Countability and the Mode of Consideration

It is worth connecting what has been said with how ToS speaks of infinite collections in general.

Part II established: “the set of all natural numbers” is not a completed object lying ready; it is a list, a scheme of construction, taken in abstraction from order and time. The same holds for the rational numbers. “The field of all rational numbers” is not a gathered whole; to speak of the rational numbers as a whole is to take them in a special *mode of consideration*—to abstract from the fact that the marking is not completed and to consider the list of its positions as if it were given all at once.

Countability clarifies what this mode rests on and why it is legitimate. To take an uncompleted list “as a whole” is permissible exactly insofar as there is a procedure reaching every one of its members. Countability is precisely the presence of such a procedure. It does not turn the potential into the completed—the rational numbers do not become a ready collection through it—but it justifies the mode in which they are spoken of as a whole: behind this “whole” stands a working traversal, not a gathered infinity. Countability is the operational ground of the mode of consideration in which a potential marking is spoken of as a list.

*Countability does not gather the rational numbers into a completed collection—it means that every rational number is processually reachable: the traversal reaches it in a finite number of steps. It follows from countability that the rational numbers are an ordinary infinity—the same as that of the natural number series: the denseness of the marking does not make their infinity greater. And countability justifies the mode in which an uncompleted marking is spoken of as a list: behind this list stands a working traversal, not a gathered infinity.*

### Toward the Next Distinction

The rational numbers have turned out to be enumerable—an ordinary, reachable infinity. But the chapter has also noted a boundary: the question of whether every infinity is like this has not yet been posed. The approach to it lies in one distinction that the Calkin–Wilf enumeration makes visible: the distinction between *data* and *behavior*. The chapter continues with it.

## Data and Behavior

### Why the Rational Numbers Could Be Traversed

The chapter has traversed the rational numbers—it has presented a procedure reaching every one of them. It is worth asking *why* this succeeded—what exactly in the arrangement of a rational number made the traversal possible. The answer to this question outlines the boundary of the enumerable and leads up to what lies beyond it.

A rational number can be traversed because it is a *finite amount of data*. The whole rational number is given without remainder by a pair of natural numbers—a numerator and a denominator (§ 3.3). This pair is finite: the numerator is a concrete natural number, the denominator is a concrete natural number, and that is all. To write down a rational number is to write down two numbers—an expression of finite length that can be written out completely and held before one in its entirety.

This is the condition of traversability—but it must be named exactly, or else it will sound stronger than is true. Not every “collection of finite data” is enumerable: if “data” could be finite objects over an uncountable stock—say, one-element lists whose single element is taken from an uncountable collection—then the collection of such finite data would be uncountable too. Finiteness of the *amount* of data does not by itself give enumerability. The exact condition is different: every collection of *finite expressions over a countable alphabet* is enumerable—finite records composed from a countable stock of signs or from a finite set of constructors. *Such* collections can always be traversed: they can be ordered by length and by signs and gone through in sequence, as the chapter went through the pairs of fractions along the tree. The rational numbers are precisely such: the canonical record of a rational number is a finite pair of natural numbers, a finite expression over a countable stock. The enumerability of the rational numbers is a particular case of this general fact: *a collection of finite expressions of a countable type can be traversed*.

### A Process Is Infinite Behavior

But not everything mathematics speaks of is a finite amount of data. There are objects of another kind—and ToS will meet them in the next Part.

Let us take a *process*—say, an infinite sequence of rational approximations refining some magnitude step by step. Precision is needed here, or else what is said will come into contradiction with the fact that a process often *can* be given finitely. Three things must be distinguished. An *individual computable* process may well have a finite description—a finite rule, a program: “at step $n$ output such-and-such a fraction.” But a process as *behavior* is not identical to this finite record: it unfolds as an infinite sequence of answers—$0$, $1$, $2$, and so on without end—and its whole course, its whole graph, is an infinite object. And, finally, a process as an *arbitrary function* $ℕ \to ℚ$ need not have a finite description at all: computable processes are only a part of all functions $ℕ \to ℚ$.

It is here that this difference—between *data* and *behavior*—runs. Data are something recorded, finite, present in their entirety. Behavior is a way of answering unfolded over the whole infinity of steps; an individual computable behavior is given by a finite rule, but behavior itself, as an infinite sequence of answers, is not *exhausted* by a finite record. And the decisive point: whereas the *collection* of finite expressions—finite programs—is enumerable on a par with other finite data, the *collection of all functions* $ℕ \to ℚ$ does *not* reduce to the collection of finite programs: there are more functions than finite rules, and not every one is given by a rule. A rational number is data. A process is behavior; and the collection of all processes-as-functions is not the same as the enumerable collection of finite data.

### The Boundary of the Enumerable

Here is the boundary toward which the chapter has been leading, and here too is the groundwork for what unfolds beyond the rational numbers.

Collections of finite expressions of a countable type are enumerable—the chapter has shown and explained this: their members are finite records over a countable stock, and such records can be traversed. The natural numbers, the integers, the rationals—all are finite data, and all are enumerable (§ 3.6). But the collection of *all processes*—all functions answering with a rational number at every step—is arranged differently. An individual computable process is given by a finite program, and programs, as finite expressions, are enumerable; but the collection of *all* functions $ℕ \to ℚ$ does not reduce to the collection of finite programs, and the grounds on which finite data are enumerable cannot be applied to it. Whether the collection of all processes is enumerable the present chapter does not decide; it only notes that this question is a *different* one and that there are no grounds here for an affirmative answer.[^6]

With this the boundary is outlined. On one side of it are finite data: the natural, integer, and rational numbers, an ordinary enumerable infinity. On the other, infinite behavior—processes; and their infinity may be of another kind. Part IV will take up precisely this other side: it will build processes as an object in their own right and examine whether they are enumerable. The present chapter only names the boundary without crossing it. In E/R/R terms, this is the boundary between finite *data* (the rational is an element) and infinite *behavior* (a process); see the analysis in § 3.8.3.

*The rational numbers could be traversed because each of them is a finite amount of data—a pair of natural numbers, an expression of finite length. Every collection of finite expressions over a countable alphabet or a finite set of constructors is enumerable; the rational numbers are precisely such. A process—a rule answering with a rational number at every step without end—is given by a finite program as an individual computable behavior, but the collection of all functions $ℕ \to ℚ$ does not reduce to the collection of finite programs. Here the boundary runs: finite data (the natural, integer, and rational numbers) are enumerable; whether the collection of all processes is enumerable is a question for Part IV.*

### Toward the Chapter’s Summary

The chapter has gone through the countability of the rational numbers—from the operational meaning of countability to the explicit traversal and to its ontological significance—and has outlined the boundary beyond which processes lie. It remains to bring together what has been covered and to outline the transition to the next chapter. With this the chapter concludes.

## Summary. The Transition to the Anomalies of the Rational Numbers

### What the Chapter Has Covered

The chapter has gone through the countability of the rational numbers.

It began by refining countability itself. The standard understanding—the existence of a bijection—can be reproduced formally too, as a statement about the injectivity and surjectivity of a function; ToS uses this but requires a stronger, operational form: an explicit traversal that can be computed, traced, and inverted, not a statement about the existence of a correspondence (§ 3.1). From this followed the requirement: to present the traversal explicitly, not to refer to an existence theorem (§ 3.2). And the chapter presented it—via the Calkin–Wilf tree, which places every positive rational number at a unique node and every fraction in irreducible form (§ 3.3); via navigation by a binary path, which connects the nodes with the natural numbers (§ 3.4); via the inverse procedure and the proof that the direct and the inverse traversal exactly invert each other—a fully constructive proof, without the Law of Excluded Middle (§ 3.5). Then the chapter showed what countability means ontologically: the rational numbers are a processually reachable list, an ordinary enumerable infinity—the same as that of the natural number series (§ 3.6). And it outlined the boundary: finite data are enumerable, while processes—infinite behavior—lie on the other side (§ 3.7).

### The Rational Numbers Are Enumerable

The outcome of the chapter comes down to one thing. The rational numbers are *enumerable*—and enumerable in fact, not by an existence theorem: there is a traversal that reaches every one of them in a finite number of steps, and this traversal has been built, written out, and constructively grounded.

With this the passage through the rational numbers as a number system is completed. Part III built them as a coordinate marking with a commensurable step (Chapter III.2), showed why in the standard algebraic shell they form a field (ibid.), and showed their enumerability (the present chapter). The rational numbers are an ordered, dense, countable field: between any two of them lies one more, and at the same time all of them fit into a single traversal that reaches each one.

### E/R/R Analysis: Countability as an Operational Traversal

The countability gone through is worth analyzing by E/R/R (Part I): the analysis secures how the *operational* countability of ToS is richer than the existence of a bijection. The supporting file is `Countability_Q.v` (776 lines, *without a single axiom*, not even the Law of Excluded Middle): the Calkin–Wilf tree, the enumeration `enum_QPos` and its inverse `index_of_QPos`, the theorem `Q_positive_countable`; and for the whole of $ℚ$, the function `enum_Q`, its inverse `index_of_Q`, and the theorem `Q_bijection`. The reservation about status has now been lifted: for the whole of $ℚ$ a *complete* bijection $ℕ \leftrightarrow ℚ$ with computable inversion has been proved—two round-trip theorems, `enum_Q_index_id` and `index_of_Q_enum_id`, 0 axioms—with the single precision that $ℚ$ is taken up to `Qeq` ($2/4$ and $1/2$ receive one index); otherwise there could be no bijection at all. We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements.

*Rules* (the law $L5$). The constitution is the construction of the tree: the root and the two branching rules (`cw_left`/`cw_right`), § 3.3. To it is added navigation: binary path $\leftrightarrow$ node, node $\leftrightarrow$ index (§ 3.4), and the *invertibility* of the direct and the inverse traversal (`enum_injective` and `enum_surjective` give `Q_positive_countable`, § 3.5). And the rule of canonicity: irreducibility (`enum_coprime`)—every rational *value* occurs exactly once; $2/4$ does not appear separately from $1/2$ (§ 3.3). By $P4$, the traversal is a *process*: it reaches every rational in a *finite* number of steps, rather than presenting a completed list.

*Roles—the significance of positions* (the law $L4$). The role that the traversal assigns to each rational is its *index*: a place in the enumeration, returned by the function `index_of_QPos`. A node of the tree plays the role of a *rational value* (an irreducible representative), the binary path the role of an *address*. Countability here is not a property of a “collection” but a *role-index* assigned to each element by the procedure.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are the nodes of the tree (pairs `QPos`, whose representatives are the irreducible ones) and the natural indices. By $L1$, every node is identical with itself. By $P4$, every rational is a *finite* object—a numerator/denominator pair, an expression of finite length—and can therefore be traversed; “all the rationals,” meanwhile, are a potential traversal, not a ready collection.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| tree: root + `cw_left`/`cw_right` | the constitution of the traversal | Rule |
| navigation $\leftrightarrow$ index; invertibility | the bijection `nat` $\leftrightarrow$ `QPos` | Rule |
| irreducibility (`enum_coprime`) | each value once | Rule |
| index in the traversal (`index_of_QPos`) | the role of the rational | Role |
| node-pairs / irreducible representatives | bearers (finite, $P4$) | Element |
| laws $L1$–$L5$ (here $L5$) | the universal layer | Rule (univ.) |

*Well-formedness.* The traversal is formed correctly: it is *bijective* (the direct and the inverse invert each other—proved) and *canonical* by irreducibility—no value is counted twice (there is no $2/4$ next to $1/2$). And here the analysis turns into a *diagnosis*, a twofold one. The first: ToS reads countability as a *rule*-traversal—a procedure that can be computed, traced, and inverted—not as the bare *existence* of a correspondence; the operational form is strictly stronger (§ 3.1). The second, and the main one for what follows: *data* and *behavior* must not be mixed. A rational is finite data (a pair, an element), and is therefore enumerable; a process of approximation is infinite behavior (a function $ℕ\toℚ$), and it does not reduce to the collection of finite programs (§ 3.7). To count processes in the same way as points is a confusion of categories: element-data and role-behavior are different levels.

What the analysis yields. Countability appears not as a property of a ready set but as a *rule*: a traversal that gives every rational a finite index. This closes the arc of number-positions of Part III—natural, integer, rational—all are finite data that can be laid out in a traversal. And by the same token the analysis sets the threshold of Part IV: *data* are enumerable; *behavior* is an open question. The processes of approximation that do not terminate at a rational position (§ 3.8.4) are precisely that behavior; whether *they* are enumerable Part IV will examine (the uncountability of processes).

### What the Rational Numbers Lack

And yet the number series does not end with the rational numbers. There is something in them that on closer examination turns out to be a *shortfall*—and this shortfall will reveal itself not as a flaw but as a pointer to the next step.

The rational numbers are dense: between any two lies a third; the marking condenses without limit. It would seem that such a marking leaves no gaps—wherever one points, there is a rational position. But this is not so. On the commensurable marking there arise *processes of approximation*—sequences of rational positions that describe some magnitude ever more precisely, whose rational stages become arbitrarily close to one another—but that do not *terminate* at any rational position and do not stabilize at any rational number. The chapter does not speak here of “points that are not there” as of ready points of some completed line: ToS will read these objects first of all as *processes*, not as points given in advance. It is precisely such processes that in standard mathematics lead to the irrational numbers. The dense and countable field of rational numbers, for all the density of its marking, leaves room for such non-terminating processes of approximation—and in this sense commensurable marking is not self-sufficient.

To examine these processes—these anomalies of the rational numbers—is to take the next step. They will show what commensurable marking lacks, and thereby indicate what unfolds beyond the rational numbers.

### The Transition to the Next Chapter

The rational numbers have been built, shown to be a field in the standard algebraic shell, and shown to be enumerable. The next chapter will look closely at their anomalies—at those processes of approximation that the rational numbers describe ever more precisely but that do not terminate at any rational position. Chapter III.4 is devoted to the anomalies of the rational numbers.

---

[^1]: Here and below, the formal constructions of this chapter—the type of pairs, the tree, the traversal functions, the theorems—are given according to the file `Countability_Q.v` of the ToS Rocq repository. The names of repository files are given for reference.
[^2]: The preservation of irreducibility is proved in the file `Countability_Q.v`: lemmas about the left and the right child (the greatest common divisor is preserved under each of the two rules) and the theorem `cw_node_coprime`—that in every node of the tree the numerator and the denominator are coprime.
[^3]: The function `cw_node` and the enumeration `enum_QPos` are defined in the file `Countability_Q.v` of the ToS Rocq repository.
[^4]: The functions `path_to_node` and `index_of_QPos`, as well as the theorems of this section, are defined and proved in the file `Countability_Q.v` of the ToS Rocq repository. The first argument `fuel` is a technical device of Rocq: it carries a number of steps known to be sufficient, so that the recursion is explicitly finite. `fuel` does *not* mean that the procedure requires an external, unchecked bound: it is a standard way of making the recursion structural for Rocq’s checking system, and it is then *proved* by a theorem that the chosen fuel is always sufficient—that the result does not depend on how many extra steps are allotted beyond those needed.
[^5]: The round-trip theorems—`path_cw_node_roundtrip` and `cw_node_path_roundtrip`—are proved in the file `Countability_Q.v`.
[^6]: This contrast is already outlined in the comments to the file `Countability_Q.v`: rational points are enumerable as finite objects—pairs of a numerator and a denominator—whereas rational processes (sequences of approximations) have a different status and require separate analysis. The file notes directly that the collection of functions $ℕ \to ℚ$ is not enumerated in this way.

---

Part: [[03 From Naturals to Rationals|Part III. From Naturals to Rationals]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/03 From Naturals to Rationals/02 Rational Numbers|Chapter 2. Rational Numbers]] · [[Library/Branches/Mathematics/Volume/03 From Naturals to Rationals/04 From Position to Process|Chapter 4. From Position to Process]] →
