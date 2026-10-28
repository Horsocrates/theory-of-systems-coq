---
title: "Chapter 2. RealProcess as a Type"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/04 Процессные действительные числа/02 RealProcess как тип.md"
sourceBlob: 769ce17c1998403d152d2ae8f7132ebd0cadcb42
translated: 2026-10-20
status: draft
---

## From Principle to Type

### What Chapter 4.1 Has Left Us

The previous chapter brought to full clarity the principle $P4$—the principle of Finite Actuality: every system is finite at any moment, and infinity is a property of process, not of object. The chapter showed where $P4$ comes from, what it makes superfluous in standard mathematics and with what it is incompatible, and ended with a thesis: a real number cannot originally be a ready point—originally it is a *process*, a sequence of rational approximations unfolding according to a rule.

But to *name* a process and to *build* it as a full-fledged object of formalization are different things. Chapter 4.1 named it; the present chapter builds it. Its task is to give the process the definition of a *type*: an object of the Rocq formalization just as definite as the inductive type of the natural numbers or the type of the rationals. Until this definition exists, all talk of a “process real number” remains a promise; Chapter 4.2 fulfills the promise.

### Why a Type of Functions

Chapter 4.1 has already let slip what this definition will be: a process is a function from the natural numbers to the rationals. Before unfolding the construction in full rigor, it is worth understanding why the type is arranged precisely so and why in this arrangement it is *not arbitrary*.

A process needs to answer a single kind of request: “what is the approximation at step $n$?” The request is given by a natural number—the number of the step; the answer is a rational number—the approximation. An object that gives an output-approximation for every input-number is a *function* from numbers to approximations. ToS already has the natural numbers—the inductive type, the scheme of counting from Part II; ToS already has the rational numbers—finite records, the fractions of Part III. The process requires no new source material: it is a function between two types already built.

This is what makes the choice of type inevitable rather than arbitrary. One could imagine a process in some other way—as an infinite list, as a stream, as a pair of a rule and a state. But every such representation either reduces to a function “step number $\mapsto$ approximation” or smuggles in a completed infinity (an infinite list as a ready object), which $P4$ precisely does not admit. A function from numbers to approximations is the least that suffices and the most that $P4$ allows. The type of the process is read off from the principle, not assigned alongside it.

### The Plan of the Chapter

What follows builds this type step by step and analyzes its apparatus. First, the bare process as a type of functions and its observation by finite prefixes (§ 2.2). Then the condition that selects, from all processes, those fit to be real numbers: the Cauchy property (§ 2.3). Then the arithmetic of processes and the theorems that it does not lead outside the selected class (§ 2.4). Then the type of a real number proper, in which the bearer and the proof are brought together, and an honest account of the fact that the Rocq formalization of ToS gives this type not in one but in several related designs (§ 2.5). Then the relation by which different processes define one and the same number (§ 2.6), and the structural criteria of convergence (§ 2.7). Finally, the summary and the bridge to Chapter 4.3 (§ 2.8).

The chapter, like the previous ones, is checked against the Rocq formalization line by line. And here we will have to be especially attentive: “the process as a type” is represented in the ToS repository not by one construction but by a family of related ones, and the chapter will honestly show this family without passing it off as one single type. This continues the same line of precision that Chapter 4.1 pursued.

## The Bare Process as a Type of Functions

### The Definition of `RealProcess`

In the ToS Rocq repository the basic process type is defined in the file `ProcessCore.v` and bears the name `RealProcess`.[^1]
The definition is extremely short:

```coq
Definition RealProcess := nat -> Q.
```

A process is a function from the natural numbers to the rationals. A term of type `RealProcess` is a rule that assigns a rational approximation to every step number $n$. There is nothing in the definition beyond this: no convergence condition, no limit, no structure—a bare function.

Let us call such an object a *bare process*—bare in the sense that no conditions have yet been imposed on it. A bare process can behave in any way: approach some value, oscillate without limit, run off. The type `RealProcess` accommodates them all. It is important to grasp this at once: `RealProcess` is *wider* than the class of real numbers. Not every bare process is a number; which processes are numbers will be established in § 2.3. For now `RealProcess` is the general carrier type, the space within which the numbers are yet to be singled out.

The simplest inhabitant of this space is the *constant process*:

```coq
Definition const_process (q : Q) : RealProcess := fun _ => q.
```

At every step it outputs one and the same rational number $q$. This is a process that “has already arrived”: its approximations are not refined, because there is nothing to refine. The constant process will serve as a touchstone in all further constructions—the simplest case on which every definition is tested.

### `RealProcess` Is a Type of Total Functions

Chapter 4.1, in § 1.8, already made a caveat that needs to be unfolded here. Technically, `nat -> Q` is, in Rocq, a type of *total* functions: a term of this type is defined on *every* $n$, not only on the numbers that have already been requested. It would be inaccurate to say that there is “nothing completed” in `RealProcess`.

The distinction here is the same as the one drawn in § 1.4 for the type `nat`. Formally, the type `RealProcess` *exists*, and a term of this type is a legitimate Rocq object over which one can quantify. ToS does not deny this formal fact. ToS reads a term of type `RealProcess` *operationally*—as a rule that computes a rational answer for a presented number $n$. Under this reading a process is a scheme unfolding on request, not an infinite table of values gathered into one. There is no completed infinity as a set-theoretic object—a ready infinite set of pairs “number, value”—in this reading; but in the formal language of Rocq `RealProcess` is precisely a function type. The chapter holds both levels: the formal (a function type) and the ontological (an operational rule)—and does not substitute one for the other.

The technical side is also worth noting. In Rocq, the notation `nat -> Q` is a function type built *on top of* two already existing types—`nat` and `Q`—and taking them as its domain and codomain. The definition of `RealProcess` does not create either the natural or the rational numbers anew; it *uses* them. This agrees with the ontological derivation of § 2.1.2—the process requires no new source material—but it is important to see where the boundary runs: the ontological derivation explains *why* the type is as it is, while formally `nat` and `Q` are ready types of the Rocq language, built in the previous parts of the volume, and Chapter 4.2 does not re-justify them but applies them.

### Observing a Process: Prefixes

If a process is read operationally—as a rule answering requests—it is natural to ask: what do we actually *observe* when we have a process in hand? The Rocq formalization gives the answer in the file `ProcessGeneral.v`, and this answer is *finite
prefixes*.[^2]
The file introduces the universal process type `GenProcess A := nat -> A`—a process over any type $A$, which for $A = ℚ$ coincides in essence with `RealProcess`—and two operations of observation:

```coq
Definition observe {A : Type} (p : GenProcess A) (n : nat) : A := p n.

Fixpoint prefix {A : Type} (p : GenProcess A) (n : nat) : list A :=
  match n with
  | O => []
  | S k => prefix p k ++ [p k]
  end.
```

The operation `observe` reads the value at one step. The operation `prefix` gathers the first $n$ values of a process into a finite list. And this—`prefix`—is $P4$ in action, written as a function. Whatever we take from a process, we take a *finite prefix*: a list of length $n$, gathered in $n$ steps. The file proves exactly this: the lemma `prefix_length` establishes that a prefix of length $n$ has exactly $n$ elements, and the lemma `prefix_nth` that the $k$-th element of the prefix is exactly $p(k)$. A process is never presented whole; it is presented in prefixes, and every prefix is finite. This is the Finite Actuality of § 1.1 become an operation: at any moment of observation what is present is a finite list, and only the never-completed process of generating such lists is infinite.

## The Cauchy Condition: Selecting Numbers from Processes

### What the Selection Is For

The type `RealProcess` accommodates all bare processes—convergent, divergent, and oscillating without limit. If a real number is a process, then which of them? Clearly not just any. A process that outputs $0, 1, 0, 1, 0, 1, …$ approaches nothing: it forever rushes between two values. It cannot be called a real number—it does not *refine* any number, it simply lists two. For a process to define a number, its approximations must *converge*—over time come ever closer to one another.

So the type `RealProcess` must be narrowed. A real number is not any bare process but a process that has passed a *selection*: one that satisfies a condition of convergence. ToS, following the classical tradition and the operational spirit of Chapter III.4, formulates this condition as the *Cauchy property*.

### The Definition of the Cauchy Property

The Cauchy property does not speak of a limit. This is essential: a limit would be a ready number toward which the process is going—and if it is precisely the number that we are building, referring to a ready limit would mean reasoning in a circle. The Cauchy property speaks only of *the process itself*: of the fact that its approximations become arbitrarily close *to one another*.

The Rocq formalization writes this as follows. A process is Cauchy if for every positive precision $\varepsilon$ one can point out a step number $N$ such that any two approximations with numbers not less than $N$ are less than $\varepsilon$ apart. In the file `CauchyReal.v` (discussed in detail in § 2.5) this is the predicate `is_cauchy`:

```coq
Definition is_cauchy (a : nat -> Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat -> Qabs (a m - a n) < eps.
```

Let us read this operationally. “For every precision $\varepsilon$”—however small a discrepancy we name; “one can point out $N$”—there is a cutoff; “any $m, n \ge N$”—from this cutoff on, all approximations; “$|a_m - a_n| < \varepsilon$”—differ by less than the named precision. In other words: demand any tightness you like, and the process will sooner or later enter it and never leave it again. The definition does not mention a limit; it is entirely about the internal behavior of the process. It is an operational, $P4$-compatible condition: it is checked by finite requests and needs no completed object.

### A Number as a Selected Process

Now we can say precisely what a process real number is in a first approximation: it is a bare process that has passed selection by the Cauchy property. The process $0, 1, 0, 1, …$ does not pass the selection—for a tightness smaller than one no cutoff $N$ can be found, and the approximations forever differ by one.

The processes of rational approximations to $\sqrt{2}$ analyzed in Chapter III.4—the Newton process and the process of convergents of the continued fraction—serve as *motivating examples* of such candidates for numbers. Here, however, precision is needed about what has been proved in the repository about these processes. In the formalization of Chapter III.4, their first steps have been checked, the difference between the two processes has been established, and the quality of approximation has been compared at a concrete step. A full proof that the Newton or the continued-fraction process in particular is a Cauchy process—that is, a separate theorem of the form `is_Cauchy` with an estimate of the rate of convergence—is not presented in the checked fragment and requires a formulation of its own. Chapter III.4 supports the idea that different processes lead to one number; the full check of their convergence in Cauchy form is the subject of a separate theorem. What is said here about $\sqrt{2}$ should be read in this exact sense: $\sqrt{2}$ is an exemplary and vivid candidate for the role of a process number, but precisely as a candidate.

Here, however, we must be precise on one point, and this is the first case where the multiplicity of process constructions in the repository makes itself felt (on which see § 2.5). The Cauchy property in ToS is formalized by *two* predicates in two files. In `CauchyReal.v`, the predicate `is_cauchy`, given above. In `ProcessCore.v`, the predicate `is_Cauchy` (with a capital letter), imposed on `RealProcess`. In meaning this is one and the same condition; formally these are *two different predicates* in two different files, and the chapter will not pretend that they are one. The file `ProcessGeneral.v` builds a bridge between them—§ 2.5 will return to it. For now let us remember the substance: *a number is a process that has passed selection by the Cauchy property*—and which of the two predicates records the selection depends on which of the process lines of the repository we are working in. In the E/R/R analysis (§ 2.8.2) the Cauchy property is the rule of selection that singles out representatives of a number from the bearer-processes.

## The Arithmetic of Processes

### The Operations Are Pointwise

Arithmetic operations are needed on numbers. If a process real number is a process, then the operations, too, will have to be carried out on processes—and we must say what that means. The Rocq formalization answers in the file `ProcessArithmetic.v`, and the answer is simple: operations on processes are *pointwise*.[^3]
In the current process core the additive operations and scaling by a rational constant are formalized: addition, the opposite process, subtraction, and multiplication by a rational number. To add two processes is to add their approximations at each step separately:

```coq
Definition process_add (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n + R2 n.

Definition process_neg (R : RealProcess) : RealProcess :=
  fun n => - (R n).

Definition process_sub (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n - R2 n.

Definition process_scale (c : Q) (R : RealProcess) : RealProcess :=
  fun n => c * R n.
```

The sum of the processes $R_1$ and $R_2$ at step $n$ is the sum of the rational numbers $R_1(n)$ and $R_2(n)$; the opposite process changes sign at each step; subtraction and multiplication by a rational constant work likewise, pointwise. The definitions do not go beyond rational arithmetic: at each separate step it is *rational* numbers, finite records, that are added and multiplied. There is nothing infinite in these definitions—there is only a rule that applies the pointwise rational operation at every step on request. The arithmetic of processes inherits the $P4$ arrangement of the process: it too is a scheme, not a completed object.

It is worth noting the boundary of this apparatus at once. The listed operations are the additive ones (addition, negation, subtraction) and scaling by a *rational* constant. A full *multiplication* of two arbitrary process numbers—the operation $R_1, R_2 \mapsto (n
\mapsto R_1(n)\cdot R_2(n))$ with a proof that it preserves the Cauchy property—is not among the operations of `ProcessArithmetic.v`, and the present chapter neither builds nor uses it. Multiplication itself, however, has been built in the repository—in a separate file: `process_mul` with the Cauchy-preservation lemma `mul_preserves_Cauchy` (`CauchyProcessBridge.v`), and, on the packaged line, `cauchy_mul` with the field laws (`RealField.v`). It is indeed more complicated than addition (the estimate of a product involves the boundedness of the factors) and belongs to the construction of the *field*—Chapter 4.3 turns to it (§ 3.6). Here the subject is the type of number and its additive arithmetic; this chapter does not use multiplication, but multiplication is no longer an open direction.

### The Operations Preserve the Cauchy Property

The pointwise definition of the operations does not in itself guarantee anything yet. A legitimate question arises: if $R_1$ and $R_2$ are numbers—that is, they have passed the selection of § 2.3 and satisfy the Cauchy property—will their sum again be a number? In other words: does arithmetic lead outside the selected class? If it did, the real numbers would not be closed under addition, and the whole construction would lose its meaning.

`ProcessArithmetic.v` proves that it does not. The file contains four preservation theorems:

```coq
Theorem add_preserves_Cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 -> is_Cauchy (process_add R1 R2).
Theorem neg_preserves_Cauchy : forall R,
  is_Cauchy R -> is_Cauchy (process_neg R).
Theorem sub_preserves_Cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 -> is_Cauchy (process_sub R1 R2).
Theorem scale_preserves_Cauchy : forall c R,
  is_Cauchy R -> is_Cauchy (process_scale c R).
```

Each asserts one thing: an operation applied to Cauchy processes yields a Cauchy process again. The proofs are classical $\varepsilon$-arguments: for the sum to fit within the precision $\varepsilon$, it suffices for each summand to fit within $\varepsilon/2$, and the triangle inequality for the absolute value of rationals completes the matter. What is essential is not the arrangement of the proofs but their result: *the selected class is closed under arithmetic*. Adding, subtracting, and scaling real numbers, we again obtain real numbers—we do not fall out of the class that the selection of § 2.3 singled out.

### The Connection with $P4$ of Chapter 4.1

It is worth noticing that these preservation theorems echo what we met in Chapter 4.1. There the predicate `P4_formalized` from `ProcessFourPrinciples.v` was a conjunction of three statements: a Cauchy process exists; a certain operation on Cauchy processes preserves the Cauchy property; the sum of Cauchy processes is a Cauchy process. The third conjunct of `P4_formalized` is exactly the theorem of closure under addition, analogous to `add_preserves_Cauchy` given here.

The second conjunct requires a caveat, and an important one. In `P4_formalized` it is written through `process_product` and `process_fst`: the preservation of the Cauchy property under the first projection of the *product* of processes. The word *product* here refers to the product of processes in the structural, categorical sense—to forming a pair of processes and its projections—and *not* to the arithmetic multiplication of two real numbers $R_1(n)\cdot R_2(n)$. The chapter does not mix these two things. The arithmetic closure that the present chapter actually uses and that `ProcessArithmetic.v` provides is closure under addition, subtraction, negation, and rational scaling (§ 2.4.2); arithmetic multiplication of two processes is not among it, as noted in § 2.4.1.

The connection with Chapter 4.1 is therefore substantive but not literal. Chapter 4.1 spoke of `P4_formalized` as the *formal trace* of the principle $P4$—a machine-checkable core recording that Cauchy processes exist and are closed under *certain* operations. The present section shows additive closure up close, at the level of individual theorems of `ProcessArithmetic.v`. What in Chapter 4.1 was compressed into a single predicate-trace is unfolded here into a working additive arithmetic. The process real number does not merely *exist* as a type—one *computes* with it: additive operations are defined, and they do not destroy its numerical nature. In the terms of § 2.8.2 these are rule-operations (Rules) that preserve the role “number”: the selected class is closed.

## The Type of a Real Number

### Bearer and Witness in One Object

Until now a real number has been described in two moves: a bare process (the type `RealProcess`, § 2.2) *plus* a condition of selection (the Cauchy property, § 2.3). A number was a process *and* a proof that the process had passed the selection—but these two things lay apart: the process in one place, its Cauchy property in another.

A full-fledged *type* of a real number brings them together into one object. In Rocq this is done by a record—a structure with fields. The file `CauchyReal.v` introduces the type `CauchySeq`:[^4]

```coq
Record CauchySeq := mkCauchy {
  cs_seq :> nat -> Q;
  cs_cauchy : is_cauchy cs_seq
}.
```

A term of type `CauchySeq` is a *pair*: the first field, `cs_seq`, is the process itself, a function from numbers to rationals; the second field, `cs_cauchy`, is a proof that this process satisfies the Cauchy property. The constructor `mkCauchy` assembles the object from these two components: the bearer and the witness of selection together.

Here we must say at once precisely what `CauchySeq` *is* and what it is not, because the temptation to call it directly “the type of real numbers” is great, and this would be inaccurate. `CauchySeq` is the type of process *representatives* of real numbers. A term of type `CauchySeq` is a process of rational approximations together with a proof that it is a Cauchy sequence; it is a *candidate that has passed selection*, a legitimate representative of some real number. But strictly speaking, `CauchySeq` is not yet the *number* proper. The number arises at the next step—as an *equivalence class* of such representatives under the relation `cauchy_equiv` (on which see § 2.6); this step, quotienting, will be taken by Chapter 4.3. The difference is essential, and the chapter will hold to it: `RealProcess` (§ 2.2) is the bare candidate process; `CauchySeq` is the representative process, a candidate that has passed selection; the number proper is a class of equivalent representatives.

With this caveat it is clear how `CauchySeq` differs from `RealProcess`. The type `RealProcess` was *wider*: it also accommodated divergent processes, which define no number. The type `CauchySeq` cannot accommodate a divergent process: to build a term of type `CauchySeq` with a given bearer, one must present the second field—a proof `is_cauchy` for this bearer; and for a process whose Cauchy property has been *refuted*, no such proof can be presented. Therefore the population of the type `CauchySeq` is exactly the Cauchy processes, that is, the admissible representatives of real numbers, and nothing beyond. The selection of § 2.3 is here not a separate step but part of the arrangement of the type.

A small but important detail of the record is the colon with an arrow in `cs_seq :> nat -> Q`. This is a *coercion*: Rocq allows a term of type `CauchySeq` to be applied directly as a function, automatically taking its first field. If $a$ is a `CauchySeq`, then $a (n)$ means `cs_seq` $a (n)$—the approximation of the representative $a$ at step $n$. The representative can be queried as a process without extracting the bearer by hand. The type remembers that the process representative of a number is *still a process*, only a process with a guarantee.

### The Constructive Completion of the Rational Numbers

It is worth calling the thing by its classical name. What `CauchyReal.v` builds is the Cauchy *completion* of the field of rational numbers: the standard construction by which mathematics obtains the real numbers from the rationals. The rational numbers are incomplete—they have “holes” like $\sqrt{2}$, sequences of approximations that have nowhere to converge *within* $ℚ$. The completion plugs the holes by declaring the convergent sequence of rational approximations itself to be a real number.

The distinctive feature of ToS lies not in the construction itself but in its reading. The classical exposition says: a real number *is* an equivalence class of Cauchy sequences—a ready object of the quotient set. ToS reads the same construction *processually*: `CauchySeq` is not a point of a ready continuum but a *process with a guarantee of convergence*. The header of the file calls this a “constructive completion”: constructive because every representative is presented explicitly, by its process and its proof, without appeal to completed infinity. The same classical construction, read in the spirit of $P4$.

Precision is needed, however, about what has already been *built* in the file. The words about “an equivalence class of Cauchy sequences” are for now a classical mathematical *reading*, not a ready Rocq object. The file `CauchyReal.v` builds the type of representatives `CauchySeq` and the relation `cauchy_equiv`; it does *not* build a quotient type—a type in which equivalent processes would literally become one term. The real number as an equivalence class is, then, the task of the *next* step, not a construction already realized in this file. Chapter 4.2 gives the representatives and the relation; the transformation of representatives into numbers—quotienting—will be carried out by Chapter 4.3.

### Three Lines of the Process in the Repository

Now the chapter must say directly what it has hinted at several times. “The process as a type” is represented in the Rocq formalization of ToS not by one construction but by *three* related ones, and a reader who opens the repository will meet all three. Honesty requires naming them and showing how they relate.

*The first line* is `RealProcess := nat -> Q` from `ProcessCore.v` (§ 2.2). The bare process: a function without a built-in proof. The arithmetic of `ProcessArithmetic.v` (§ 2.4) and the formal trace of $P4$ from `ProcessFourPrinciples.v` (Chapter 4.1) stand on it. The Cauchy property here is a separate predicate `is_Cauchy`, imposed *from outside*.

*The second line* is `CauchySeq` from `CauchyReal.v` (§ 2.5.1). A process with a *built-in* Cauchy proof; the type of process representatives of a real number. Its own arithmetic (`cauchy_add` and the rest, § 2.6), its own equivalence relation, its own algebraic laws. This line grew up independently in the repository: `CauchyReal.v` does not even import `ProcessCore.v`.

*The third line* is `GenProcess A := nat -> A` from `ProcessGeneral.v` (§ 2.2.3). A universal process over an *arbitrary* type $A$. It is not a competitor of the first two but a *frame* over them: both `RealProcess` and the bearer of `CauchySeq` are special cases of `GenProcess` with $A = ℚ$. The header of the file says directly that `GenProcess A` is the universal process type and that concrete processes are its special cases.

The three lines are conveniently gathered into a table—all the more so since their Cauchy predicates bear similar, easily confused names:

| **File** | **Type** | **Cauchy predicate** | **Status** |
|---|---|---|---|
| `ProcessCore.v` | `RealProcess`, i.e., `nat -> Q` | `is_Cauchy` | Bare process ${}+{}$ external selection |
| `CauchyReal.v` | `CauchySeq` | `is_cauchy` | Process ${}+{}$ built-in proof |
| `ProcessGeneral.v` | `GenProcess A`, i.e., `nat -> A` | `is_cauchy_gen` | General metric frame |

Let us also note the arrangement of the repository: `CauchyReal.v` and `ProcessGeneral.v` lie in the top-level directory `src/`, while `ProcessCore.v` lies in `src/process/`. This is a historical placement of the files; conceptually all three belong to one process layer.

### How the Three Lines Relate

`ProcessGeneral.v` does not leave the relation of the three lines to guesswork—it partly proves it. The file introduces the rational metric `Qdist` $x y := |x - y|$ and a general Cauchy property `is_cauchy_gen` relative to an arbitrary metric, and then proves the lemma `cauchy_Q_equiv`:

```coq
Lemma cauchy_Q_equiv : forall (a : nat -> Q),
  is_cauchy a <-> is_cauchy_gen Qdist a.
```

The left-hand side is the predicate `is_cauchy` from `CauchyReal.v`; the right-hand side is the general Cauchy property with the metric `Qdist`. The lemma establishes their equivalence: *the Cauchy property of the second line is a special case of the general Cauchy property of the third*. The next lemma, `cauchy_seq_is_gen_process`, completes the picture: every `CauchySeq` is a `GenProcess` $ℚ$ satisfying the general Cauchy property.

It is worth tracing the connection of the lines to the end. `ProcessGeneral.v` connects the second and third lines—the predicate `is_cauchy` with `is_cauchy_gen`. The first line is now connected with the second by a separate file, `CauchyProcessBridge.v`: the predicates `is_Cauchy` (from `ProcessCore.v`, the first line) and `is_cauchy` (from `CauchyReal.v`, the second) formalize one and the same $\varepsilon$-$N$ condition and turned out to *coincide literally*—so the bridge lemma `is_Cauchy_iff_is_cauchy` ($\texttt{is\_Cauchy} R \leftrightarrow \texttt{is\_cauchy} R$ for every $R$) is proved by a simple unfolding of the definitions. The lemma `process_equiv_iff_cauchy_equiv` connects the equivalence *relations* of the two lines as well, and the function `to_CauchySeq` translates a process of the first line into a representative of the second.

This lifts the earlier caveat: the *direction of synchronization* that the chapter used to name here has been *carried through*. The bridge lemma “for every $R$, `is_Cauchy` $R$ holds if and only if `is_cauchy` $R$ holds” has been built (`is_Cauchy_iff_is_cauchy`), and with the full coincidence of the definitions its proof reduced to unfolding. Operations are carried over by the same bridge: the multiplication of the second line, `cauchy_mul`, yields the multiplication of the first, `process_mul`—with Cauchy preservation and compatibility (`CauchyProcessBridge.v`). So the first and second lines are not “related but formally separate” but *machine-linked*: a passage between them is now a reference to something proved, not only a substantive gesture. The difference that remains is *ontological*, not formal—these are two records of one $\varepsilon$-$N$ condition, and the bridge identifies precisely the records.

### Which Line the Chapter Takes as the Main One

Since there are three lines, we must say on which of them the rest of Part IV stands. The chapter makes a choice and names it explicitly.

As the main type for building the process real number the chapter takes `CauchySeq`—the second line. The reason is simple: it is precisely `CauchySeq` that is a ready type of *representatives*, equipped with all the necessary apparatus. In it the Cauchy proof is built into the object, not attached from outside; its population is exactly the Cauchy processes, the admissible representatives of numbers; for it the equivalence relation with all the necessary properties and the algebraic laws have already been proved (§ 2.6). When Chapter 4.3 builds the number as an equivalence class, and Chapter 4.4 proves uncountability, it is most convenient to rely on a type of representatives that already carries its guarantee inside.

At the same time `RealProcess` is not discarded. It remains in the exposition as the *bare process*—the process *before* the Cauchy condition is imposed, that same wide space of § 2.2 within which representatives are singled out by selection. The difference of the lines now receives a clear meaning, and it is worth naming it in final form: `RealProcess` is the bare candidate process; `CauchySeq` is the *representative* process, a candidate that has passed selection; the *number* proper is a class of equivalent representatives, and Chapter 4.3 builds it. And `GenProcess` remains the universal frame, a reminder that both are special cases of one idea of a process over a type. The chapter does not merge the three lines into one artificially—it assigns them to roles: frame, candidate, representative—and leaves the number to the next chapter.

## When Two Processes Define One Number

### Different Processes, One Number

Chapter III.4 has already noted—and Chapter 4.1 repeated—that one real number has *many* processes. Not one process of rational approximations leads to $\sqrt{2}$, but different ones: one can approximate $\sqrt{2}$ by decimal fractions, by the convergents of the continued fraction, by Newton iterations. These are different processes—different functions from numbers to rationals, giving different approximations at the same steps. But the number they define is *one*.

So the type `CauchySeq` distinguishes more objects than there are real numbers: to one number there corresponds a whole family of terms of type `CauchySeq`. This is the reason why § 2.5 called `CauchySeq` a type of *representatives* rather than of the numbers themselves: one number has many representatives. To pass from representatives to numbers, we must *identify* the processes that define the same thing. We need a relation: “the process $a$ and the process $b$ define one number.”

### The Equivalence Relation on Processes

When do two Cauchy processes define one number? When their approximations draw together without limit over time—differ by less than any prescribed precision. This is the same $\varepsilon$-$N$ argument as in the Cauchy property, only now applied to a *pair* of processes. `CauchyReal.v` introduces it as the predicate `cauchy_equiv`:

```coq
Definition cauchy_equiv (a b : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (cs_seq a n - cs_seq b n) < eps.
```

The processes $a$ and $b$ are equivalent if for every precision $\varepsilon$ there is a cutoff $N$ from which on their approximations differ by less than $\varepsilon$. The file introduces a sign for this relation—$a \mathbin{\sim\mkern-3mu\sim} b$ (in the notation of the repository,
`a ~~ b`).

For such a relation to be fit for identifying numbers, it must be an *equivalence relation*—reflexive, symmetric, transitive. `CauchyReal.v` proves exactly this, with three separate lemmas: `cauchy_equiv_refl` (every process is equivalent to itself), `cauchy_equiv_sym` (if $a$ is equivalent to $b$, then $b$ is equivalent to $a$), `cauchy_equiv_trans` (if $a$ is equivalent to $b$, and $b$ to $c$, then $a$ is equivalent to $c$). The three properties are proved; `cauchy_equiv` is a full-fledged equivalence relation on the type `CauchySeq`.

### Arithmetic Respects Equivalence

An equivalence relation alone is not enough—it must also be *compatible* with arithmetic. If a number can be given by different processes, then the result of addition must not depend on which process-representatives we took. Adding $a$ to $b$, and adding a process $a'$ equivalent to $a$ to a process $b'$ equivalent to $b$, we must obtain equivalent results—otherwise addition would be an operation not on *numbers* but only on processes.

`CauchyReal.v` proves this as well. The file defines the arithmetic of the second line—`cauchy_add`, `cauchy_neg`, `cauchy_sub`, `cauchy_const`—where each operation is a `mkCauchy`: it builds a new `CauchySeq`, immediately equipping the result with a proof that it is again Cauchy (this is the same closure as in § 2.4, but carried out within the second line). And then come the key compatibility lemmas:

```coq
Lemma cauchy_add_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_add a b ~~ cauchy_add a' b'.
Lemma cauchy_neg_compat : forall a a' : CauchySeq,
  a ~~ a' -> cauchy_neg a ~~ cauchy_neg a'.
```

The lemma `cauchy_add_compat` says: replacing the summands by equivalent ones gives an equivalent sum; `cauchy_neg_compat` says the same for the change of sign. Arithmetic *respects* the equivalence relation. This means that the operations are well defined not only on processes but also on *numbers*—on classes of equivalent processes: the result does not depend on the choice of representative.

### What This Prepares for Chapter 4.3

What has been assembled in this section is a direct bridge to the next chapter. `CauchySeq` gives the processes; `cauchy_equiv` says which of them define one number; reflexivity, symmetry, and transitivity make this relation a genuine equivalence; the compatibility lemmas ensure that arithmetic survives the passage to classes. Everything is ready for the step that Chapter 4.3 will take: to declare a *real number* an equivalence class of processes, and a *point* not an original object but precisely such a class, a mode of consideration into which the operator passes when abstracting from the differences between processes with a common limit. The present chapter has built the type and equipped it with a relation; Chapter 4.3 will carry out the quotienting.

## Structural Criteria of Convergence

### What Sufficient Conditions Are For

The Cauchy property of § 2.3 is a definition: it says *what it means* to be a convergent process. But checking it directly by the definition—searching for a cutoff $N$ for every precision $\varepsilon$—is not always convenient. Often a process is arranged so that its convergence is visible from its *structure*, without running through $\varepsilon$. Mathematics therefore needs *sufficient conditions* for the Cauchy property: structural criteria from which the Cauchy property follows. The Rocq formalization of ToS provides such criteria, and the present section gathers the main ones.

### Monotonicity and Boundedness

The first and most important criterion is classical. A process is called *monotonically increasing* if each next approximation is not less than the previous one, and *monotonically decreasing* if it is not greater. `ProcessArithmetic.v` introduces both notions:

```coq
Definition monotone_increasing (R : RealProcess) : Prop :=
  forall n, R n <= R (S n).
Definition monotone_decreasing (R : RealProcess) : Prop :=
  forall n, R (S n) <= R n.
```

And it proves a criterion of convergence—the theorem
`monotone_bounded_Cauchy`:

```coq
Lemma monotone_bounded_Cauchy : forall R ub,
  monotone_increasing R -> (forall n, R n <= ub) -> is_Cauchy R.
```

A monotonically increasing process bounded above by some bound $ub$ is a Cauchy process. The dual theorem, `decreasing_bounded_Cauchy`, asserts the same for a monotonically decreasing process bounded below. In substance this is a familiar principle: a sequence that grows all the time but cannot get over a ceiling must converge—it simply has nowhere to go except to cluster at some value. The criterion is powerful: it reduces the check of convergence to two structural facts—monotonicity and boundedness—neither of which requires running through $\varepsilon$.

The proof in the file relies on the *Archimedean property* of the rational numbers—the lemma `q_archimedean`: for any bound $d$ and any positive quantity $\varepsilon$ there is a natural number $K$ for which $K\varepsilon$ exceeds $d$. This is an important technical support: it is precisely the Archimedean property that keeps a monotone bounded process from “hanging” before it comes to cluster. `ProcessArithmetic.v` does not postulate the Archimedean property but proves it—through integer division.

A caveat on logical status is needed here, and the chapter makes it. Unlike the basic file `CauchyReal.v`, the proof of `monotone_bounded_Cauchy` in `ProcessArithmetic.v` uses *classical logic*: the code applies case analysis through `classic` (the file imports `Classical`). For ToS this is not a new external axiom—`classic` is the already accepted law $L3$ (Chapter 4.1, § 1.2.4)—but the status of this proof should be distinguished from fully constructive lemmas. `CauchyReal.v`, with its basic construction `CauchySeq`, the relation `cauchy_equiv`, and additive arithmetic, manages without `classic` altogether; the structural criterion `monotone_bounded_Cauchy`, by contrast, relies on $L3$. The chapter notes this so as not to pass off a classical criterion as constructive in the same sense in which the basic construction of the type is constructive.

### Geometric Rate: The Process Gap

The second criterion is of another nature and is connected with the *rate* of convergence. The file `ProcessBounds.v` introduces a structure that can be called a *process gap*.[^5]
This is the record `has_process_mass_gap` with three conditions: the process has a stable positive lower bound; its approximations converge at a *geometric* rate—the discrepancy decreases as a power of some number less than one; and the process decreases monotonically.

The name `mass_gap` should be read as a *technical term* of the process formalization—the presence of a positive lower gap and a geometric estimate of the rate. It is not a statement about a physical mass gap in the sense of quantum field theory; the caveat is not superfluous, since the ToS repository also contains files of physical content, and the reader might connect the names. Here `mass_gap` is a purely structural notion of convergence.

The main theorem of the file is `pmg_implies_cauchy`: a process with such a gap is a Cauchy process. A geometric rate is a very strong structural condition: if the discrepancy of the approximations decreases as $r^n$ with $r < 1$, convergence is not merely guaranteed, it is fast. But this condition is *sufficient, not necessary*: the process gap is not a criterion of convergence in general but only one of the paths to it. There exist Cauchy processes that have neither a positive lower bound nor a geometric rate—and the file shows this directly: the theorems `pathological_no_pmg` and `vanishing_no_pmg` establish that the zero process and a process decreasing to zero have no such gap. The gap condition is substantive: it holds for some convergent processes, not for all. The chapter cites it as *one of* the structural criteria for the Cauchy property—not as universal as monotonicity with boundedness, and not as the main one.

### Completeness: A Process Is Approximated by Rationals

The third topic is not a criterion for the Cauchy property but a *consequence* of it, and this topic concerns completeness. `CauchyReal.v` proves the theorem `cauchy_rational_approx`: every Cauchy process, at sufficiently distant steps, is approximated arbitrarily closely by a *rational* number—one of its own approximations. And the theorem `cauchy_complete_self`: a Cauchy process converges “to itself”: its tail fits within any prescribed precision around any sufficiently distant approximation.

Precision is needed here about what exactly is proved. These two theorems fix the *basic form* of the completeness of the construction: each `CauchySeq` itself provides rational approximations and converges to itself as a process object. This is *not yet* the full metatheorem of metric completeness—not the statement “every Cauchy sequence of process real numbers has a process real number as its limit.” Such a theorem would require a separate formulation: sequences of real numbers, their limits, and a proof that the limit is again a real number. `cauchy_rational_approx` and `cauchy_complete_self` are not equal to it; the full metric completeness of the space of classes of `CauchySeq` is a separate task, going beyond Chapter 4.2. In substance, however, what has been said suffices for the main point: the rational numbers are incomplete ($\sqrt{2}$ “does not fit” in them), while the process construction removes this incompleteness at the basic level—every Cauchy process has something to converge to: itself. And this basic result is proved without completed infinity: `CauchyReal.v` at its base carries zero axioms; the construction is constructive over $ℚ$.

## The Type Has Been Built

### What Has Been Done

The chapter began with the promise of Chapter 4.1: a real number is a process, and the process must be given the definition of a type. The promise has been kept. The type has been built—and built step by step, each step of which was necessary.

First, the bare process: the type `RealProcess` as a function from step numbers to rational approximations, observed by finite prefixes (§ 2.2). Then the realization that the bare process is too wide: the type `RealProcess` also accommodates divergent processes, which define no number, and therefore a selection is needed—the Cauchy property, the $\varepsilon$-$N$ condition on the internal drawing together of the approximations (§ 2.3). Then arithmetic: pointwise additive operations and theorems that they survive the selection—the selected class is closed under addition, subtraction, and scaling (§ 2.4). Then the type of process representatives of a real number, `CauchySeq`: a record that brings a process and a proof of its convergence into one object, so that the population of the type is exactly the Cauchy processes, the admissible representatives of numbers (§ 2.5). Then the equivalence relation, saying when two processes define one number, with proved reflexivity, symmetry, transitivity, and compatibility with arithmetic (§ 2.6). Finally, the structural criteria that make it possible to establish convergence without running through $\varepsilon$ (§ 2.7).

The chapter also honestly showed that “the type of the process” exists in the ToS repository in three related designs—the bare `RealProcess`, the guarantee-equipped `CauchySeq`, and the universal frame `GenProcess`—and assigned them to roles: candidate, representative, frame. As the main type for building the process real number throughout the rest of Part IV, the chapter adopted `CauchySeq`—with the clear caveat that the *number* proper is a class of equivalent representatives, and that the step to it will be taken by Chapter 4.3.

### E/R/R Analysis: The Process Number as a System

The layers just listed fit together into a system—the process real number—and this system has an E/R/R arrangement (Part I). Let us gather its analysis; it only *names* in E/R/R terms what the chapter has already built. The headers of the supporting files give the labeling directly: `ProcessCore.v` declares the rule *every object is a finite process at each stage* ($P4$); `ProcessArithmetic.v`, *every operation preserves the Cauchy property*.[^6] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. A caveat on status: “system” is a substantive interpretation; we are dealing with processes and representatives over $ℚ$, while the *number* proper as a class has not yet been built—Chapter 4.3 provides it.

*Rules* (the law $L5$). The constitution is the principle $P4$: a number is not a completed point but a *process* of rational approximations, finite at every stage; from it follows the very arrangement of the bearer—the function `nat -> Q` (§ 2.2). Adjoining the constitution is a concrete layer of rules: the *Cauchy property* as the rule of selection (what is fit to be a number, § 2.3); pointwise arithmetic, *closed* with respect to the Cauchy property (§ 2.4); the *equivalence* relation with its compatibility with arithmetic—the rule “when two processes define one number” (§ 2.6); the structural criteria of convergence (§ 2.7). The honest boundary: the criterion `monotone_bounded_Cauchy` relies on $L3$ (not on pure construction). A full multiplication of two processes is not among the rules of *this* chapter—but it has been built in the repository (`process_mul`, `cauchy_mul`; § 2.4.3 and Chapter 4.3).

*Roles—the significance of positions* (the law $L4$). Here is the central distinction of the whole chapter, read as role statuses. One and the same bearer-process passes through three roles: the *bare candidate* (`RealProcess`—a process before selection), the *representative* that has passed selection by the Cauchy property (`CauchySeq`—a process with a built-in guarantee), and finally the *number*—a class of equivalent representatives. By $L4$, each status is grounded in its own rule: Cauchy selection makes a process a representative, equivalence gathers representatives into a number. This progression of roles—candidate $\to$ representative $\to$ number—is the backbone of the chapter.

*Elements—the bearers* (the law $L1$ and the principle
$P4$). The elements are the rational approximations $a(n)$ at each step; the bearer itself is a process `nat -> Q`, the simplest being the constant `const_process`. By $L1$, each approximation is identical to itself. By $P4$, the bearer is finite at any level: a process is observed in *prefixes*—finite lists of length $n$ (§ 2.2.3)—and is never presented whole.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| approximations $a(n)$; the process `nat -> Q` | bearers (finite, $P4$) | Element |
| statuses: candidate $\to$ representative $\to$ number | role positions | Role |
| $P4$: an object is a finite process at a stage | constitution | Rule |
| the Cauchy property | rule of selection | Rule (concr.) |
| pointwise arithmetic (preserves the Cauchy property) | rules of operations | Rule (concr.) |
| equivalence ${}+{}$ compatibility | the rule “the same number” | Rule (concr.) |
| laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: the approximations and the process are elements, the statuses candidate/representative/number are roles, $P4$ with the Cauchy property and arithmetic are rules. There is no self-reference. Two honest caveats. First, the role “number” is *not yet realized* at the level of this chapter: the bearer and the representatives have been built, while the number as a class is built by Chapter 4.3—so the system here is well-formed *at the level of representatives*. Second, the “inevitability” of the type (§ 2.8.3 below) is a substantive thesis, not a Rocq theorem about the uniqueness of the construction.

 This analysis is the E/R/R foundation of the whole of Part IV. It shows that `RealProcess`, `CauchySeq`, and the number are not three competing definitions but three *role statuses* of one bearer, connected by a rule of selection (Cauchy) and a rule of identification (equivalence); and that $P4$ is the constitution by which a number is a process at all, not a point. Both the quotienting of Chapter 4.3 (the number as a class) and the whole analysis of Part V will stand on this type: metric, continuity, derivative, and integral work over process numbers read in exactly this way.

### The Type Is Not Arbitrary

In conclusion it is worth returning to the thesis of § 2.1: the type of the process real number is *not arbitrary*. Now this can be seen in full. Each of its layers is forced.

A function from numbers to rationals is forced: a process must answer the request “the approximation at step $n$,” and an object that assigns an approximation to a number is precisely such a function; it requires nothing new beyond the already built $ℕ$ and $ℚ$. The Cauchy condition is forced: without selection the type would accommodate divergent processes that define no numbers. Bringing the bearer and the witness together into the record `CauchySeq` is forced: only so does the population of the type coincide with the admissible representatives of numbers and with nothing beyond. The equivalence relation is forced: without it one number would correspond to a family of unidentified representatives. Each layer is an answer to a definite necessity, not a free choice of the constructor.

Here, however, a precise caveat is needed about what this “inevitability” *is* and what it is not. Rocq confirms the *correctness* of the chosen definitions and proofs: that the type `CauchySeq` has been built without contradictions, and that the theorems about it are proved. Rocq does *not* prove the *uniqueness* of this construction among all possible formalizations of the real number. Mathematics knows other paths too—Dedekind cuts, located real numbers, interval representations; ToS chooses the process path for the substantive reasons set out in Chapter 4.1 and in § 2.1, not because the other paths are formally excluded. Therefore “the type is not arbitrary” and “the type is structurally inevitable” are a *philosophical-methodological* conclusion of the chapter: each layer of `CauchySeq` is forced by the task “to build number as a process in the spirit of $P4$.” This is not a Rocq theorem and not a statement about the uniqueness of the construction in general. The chapter puts forward a strong substantive thesis and at once outlines its boundaries—exactly as Chapter 4.1 did with the formal trace of $P4$.

### The Bridge to Chapter 4.3

The type has been built—but one thing has not been carried through to the end, and Chapter 4.2 leaves it to Chapter 4.3 deliberately. The type `CauchySeq` distinguishes more objects than there are real numbers: to one number there corresponds a whole class of equivalent processes (§ 2.6). The relation identifying them has been built and equipped with all the necessary properties—but the *quotienting* by it, the passage from processes to their classes, has not yet been carried out.

This passage is the subject of Chapter 4.3. It will declare a real number an equivalence class of processes and analyze what becomes a *point* under such a view: the point will turn out to be not an original object but precisely a class—a mode of consideration into which the operator passes when abstracting from the differences between processes with a common limit. There, too, the famous equality of zero point nine repeating and one will receive its analysis. In the terms of the present chapter it will appear as follows: the process of decimal approximations $0{,}9;\ 0{,}99;\ 0{,}999;\ …$ and the constant process `cauchy_const 1` are two *different* representatives, but one equivalence class, and hence one number. The exact form that Chapter 4.3 has to present is the definition of a concrete representative for $0{,}999…$, a constant representative for one, and a proof of their equivalence by `cauchy_equiv`: schematically,

```coq
Definition nine_process : CauchySeq := (* 0.9, 0.99, 0.999, ... *)
Definition one_process  : CauchySeq := cauchy_const 1.
Theorem nine_equiv_one : nine_process ~~ one_process.
```

The equality $0{,}999… = 1$ will thus turn out to be not a paradox but a simple consequence of the fact that the two representatives fell into one class. The present chapter has built the type of representatives and the relation `cauchy_equiv`; Chapter 4.3 will carry out the quotienting and analyze this example on it. Chapter 4.4 will then prove the uncountability of processes, Chapter 4.5 will reformulate the question of the continuum, and Chapter 4.6 will close the part.

The present chapter has given Part IV its main building material—the type of process representatives of a real number. Everything that follows works with this type.

*A process representative of a real number is a process of rational approximations that has passed selection by the Cauchy property, taken as an object of a single type. The Rocq formalization of ToS gives this type in three related designs: the bare process `RealProcess`
${}={}$ `nat -> Q` with the external predicate `is_Cauchy`; the type `CauchySeq` equipped with a built-in proof of convergence
${}={}$ `mkCauchy { cs_seq; cs_cauchy }`; and the universal frame `GenProcess A` ${}={}$ `nat -> A`. These designs are connected (the lemma `cauchy_Q_equiv` reduces the Cauchy property of the second line to the general case of the third), but the first and second lines are not machine-identified as a single term; the chapter assigns the three lines to roles—candidate, representative, frame—and adopts `CauchySeq` as the main type for building the number in Part IV. What is essential: `CauchySeq` is a type of *representatives*, while the *number* proper is a class of equivalent representatives; the quotienting will be carried out by Chapter 4.3. Over the type a pointwise additive arithmetic is defined—addition, subtraction, negation, rational scaling—and it is proved that it preserves the Cauchy property; *this* chapter does not build a full multiplication of two processes (it has been built separately: `process_mul`, `cauchy_mul`). An
equivalence relation `cauchy_equiv` has been introduced with proved reflexivity, symmetry, transitivity, and compatibility with arithmetic—different processes can be representatives of one number. Convergence is established not only by the definition but also by structural criteria—monotonicity with boundedness, a geometric rate. The basic construction `CauchySeq`, the relation `cauchy_equiv`, and the additive arithmetic in `CauchyReal.v` carry zero axioms and zero incomplete proofs; certain structural criteria—for example, monotonicity with boundedness—use the classical logic of $L3$, which is noted specially. The type is not arbitrary: each of its layers is forced by the task of building number as a process in the spirit of $P4$—this is a substantive thesis of the chapter, not a Rocq theorem and not a statement about the uniqueness of the construction among all formalizations of the real number. The real number as an equivalence class of representatives, and the point as such a class, are built by Chapter 4.3.*

---

[^1]: `ProcessCore.v` of the ToS Rocq repository (directory `src/process/`). The file is declared in the repository as the single source of the basic process definitions. The names `RealProcess`, `is_Cauchy`, `const_process`, and `process_equiv` used below come from it.
[^2]: `ProcessGeneral.v` of the ToS Rocq repository (directory `src/`), 16 proved statements, 0 `Admitted`, 0 axioms. The file builds a general theory of the process over an arbitrary type; on it in more detail, see § 2.5.
[^3]: `ProcessArithmetic.v` of the ToS Rocq repository (directory `src/process/`), 13 proved statements, 0 `Admitted`. The file works with the type `RealProcess` from `ProcessCore.v`. On the status of axioms, see the caveat in § 2.7.2.
[^4]: `CauchyReal.v` of the ToS Rocq repository (directory `src/`), 18 proved statements, 0 `Admitted`, 0 axioms. The header of the file: “Cauchy reals: constructive completion of $ℚ$”—the constructive completion of the rational numbers.
[^5]: `ProcessBounds.v` of the ToS Rocq repository (directory `src/process/`), 11 proved statements, 0 `Admitted`, 0 axioms. In the code the structure is called `has_process_mass_gap`; the name “process gap” used in the text conveys the meaning—the presence of a stable positive lower bound.
[^6]: The E/R/R labeling in the headers of `ProcessCore.v` and `ProcessArithmetic.v`; here it is unfolded on the model of Part I.

---

Part: [[04 Process Real Numbers|Part IV. Process Real Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/01 P4 Infinity as Process|Chapter 1. P4: Infinity as Process]] · [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/03 Point as Equivalence Class of Processes|Chapter 3. The Point as an Equivalence Class of Processes]] →
