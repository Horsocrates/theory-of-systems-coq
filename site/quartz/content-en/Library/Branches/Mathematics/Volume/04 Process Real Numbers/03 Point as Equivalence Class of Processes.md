---
title: "Chapter 3. The Point as an Equivalence Class of Processes"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/04 Процессные действительные числа/03 Точка как класс эквивалентности процессов.md"
sourceBlob: 51967569b1a4fdbc17777a61b698d4bcf8d14fe2
translated: 2026-10-20
status: draft
---

## From Representatives to Number

### What Chapter 4.2 Has Left Us

The previous chapter built the type of the process representative of a real number. It went along the path step by step: the bare process `RealProcess` as a function from step numbers to rational approximations; selection by the Cauchy property, which cuts off divergent processes; the type `CauchySeq`, which brings a process and a proof of its convergence into one object; additive arithmetic, which does not lead outside the selected class; and finally the equivalence relation `cauchy_equiv`, which says when two processes define one and the same number.

And at the last step Chapter 4.2 made an important caveat, for the sake of which the present chapter was written. The type `CauchySeq` is a type of *representatives* of a real number, not of the numbers themselves. One number has *many* representatives: decimal approximations, the convergents of the continued fraction, and Newton iterations all lead to $\sqrt{2}$—different processes, different terms of type `CauchySeq`—yet the number they define is one. Chapter 4.2 built the representatives and equipped them with the relation “to define one number”; but the *number proper*—what is obtained when we stop distinguishing equivalent representatives—it deliberately left to the next chapter.

### The Unfinished Step: Quotienting

The step to be taken is called *quotienting* in mathematics. Given: a type of representatives and an equivalence relation on it. Required: to pass from the representatives to their *classes*—to unite into one object all the representatives that the relation does not distinguish. The equivalence class will be what we call a *number*; and together with the number, a *point*.

Chapter 4.2 prepared everything necessary for this step. The relation `cauchy_equiv` has been proved reflexive, symmetric, and transitive—that is, it is a full-fledged equivalence relation, by which quotienting is *legitimate*. The additive arithmetic has been proved compatible with this relation—so the operations will survive the passage to classes. All that is missing is the passage itself: the declaration that a real number *is* an equivalence class, and an analysis of what happens to the notion of a point under such a declaration.

### The Plan of the Chapter

The present chapter takes this step—and takes it not as a purely technical operation but as an ontological turn. If a number is a class of processes, then the *point*—the point of the real line, the familiar atom of continuous magnitude—ceases to be an original object. It turns out to be *derived*: a class of equivalent processes, a mode of consideration into which the operator passes when abstracting from the differences between processes with a common limit.

What follows proceeds thus. First, why the point cannot be primary at all in the $P4$ ontology (§ 3.2). Then the relation “to define one number” and its proved properties (§ 3.3), and right after it what Chapter 4.2 outlined and what needs to be unfolded here: the two representations of the process, `CauchySeq` and `RealProcess`, are formally connected by a bridge (§ 3.3.1). Then the equivalence class as a point (§ 3.4) and the point as a mode, not an object (§ 3.5). Then what happens to arithmetic and order in the passage to classes (§ 3.6). Then the culmination—the analysis of the equality of zero point nine repeating and one (§ 3.7). Finally, the summary and the bridge to Chapter 4.4
(§ 3.8).

The chapter, like the previous ones, is checked against the Rocq formalization line by line, and here we will have to be especially precise on one point—the distinction between a *setoid* and a *quotient type*. The setoid—a type of representatives together with an equivalence relation on it—is now formalized in the ToS repository: the file `RealPointSetoid.v` registers `cauchy_equiv` as an `Equivalence`, names the carrier `RealPoint := CauchySeq`, and proves that the operations are morphisms (`Proper`) respecting the equivalence. The *quotient type* itself—a new type in which equivalent processes would literally become one term—has not been built as a separate object, and *deliberately* so: it would reify a mode into a thing and would require axioms (§ 3.4.3). The chapter does not pass one off as the other: it conducts “the point as a class” on the formalized setoid, and honestly leaves aside the reification into a quotient type as a path that ToS declines by
$P4$. This continues the same line of precision that Chapters 4.1 and 4.2 pursued.

## Why the Point Cannot Be Primary

### The Familiar Picture: The Point as an Atom of the Line

In the familiar mathematical picture the point is primary. The real line is thought of as a collection of points already gathered into one; the point is its indivisible atom, a ready object that simply *is*. The number $\sqrt{2}$, on this view, is a definite point occupying its place on the line between $1{,}41$ and $1{,}42$; the processes of rational approximation only *point* to it, edging toward a ready place that existed before any approximation.

This picture is so familiar that it seems the only one possible. But it carries within itself exactly the assumption that the principle $P4$ rejects. The collection of all the points of the line is a completed infinity: an uncountable set of atoms gathered into a ready object. The point as an atom of this collection is an element of a completed whole. To accept the point as primary is to accept the completed line as primary; and Chapter 4.1 showed that there is no completed line in the $P4$ ontology.

### What There Is Not and What There Is

Let us say directly and positively what there is and what there is not. A completed real line—a ready uncountable collection of point-atoms—does not exist: it is a completed infinity, and $P4$ excludes it. Ready points existing *before* any process and *independently* of it do not exist either: the point-atom is an element of that very completed collection.

This does not mean, however, that a symbol or type called $ℝ$ cannot be introduced in the metalanguage. It can be introduced—mathematics does exactly that. $P4$ rules out not the symbol but a certain *reading* of it: $ℝ$ must not be read as a primary completed collection of points existing by itself. In ToS such a symbol must be *recovered*—it must receive meaning as a mode of working with processes, not as a ready given. The distinction is the same as the one Chapter 4.1 drew for the type `nat` and Chapter 4.2 for `RealProcess`: the formal object of the language exists, but it is read operationally, not as a completed actual infinity.

What there is, is processes. Chapter 4.2 built them as full-fledged objects: the type `CauchySeq`, a process of rational approximations with a proof of convergence. The process is *primary* in the sense in which the point cannot be primary: it is presented explicitly, by its rule and its witness, without requiring a completed collection. The process is what $P4$ mathematics *begins* with.

So the order of construction is the reverse of the familiar one. Not “there is a line of points, and processes converge to the points,” but “there are processes, and the point must be *built* from them.” The point does not come before the process; the point comes *after* the process, as the result of some operation on processes. Which operation exactly, the following sections will show; but it is already clear that the point cannot be posited *before* the processes—it can only be *obtained* *from* them.

### The Point as a Recoverable Mode

Here it is important not to fall into the opposite extreme. To say “there are no ready points” is not to say that the notion of a point is meaningless or that it must be abandoned. Chapter 4.1, in § 1.8, already outlined the right formulation: the point is not abolished—it is *recovered later*, as a derived mode. Chapter 4.2, in § 2.8, repeated this, pointing to quotienting as the mechanism of recovery.

The point, then, is a legitimate notion, but *not in the place* where we are used to seeing it. It is not a foundation but a superstructure; not an input of the construction but its result. The $P4$ ontology does not strike out the point but *rearranges* it: from the primary objects into the derived ones. The present chapter carries out this rearrangement: it shows by which operation on processes the point is recovered and what it turns out to be under such recovery. This operation is quotienting by an equivalence relation, and we now pass to the relation itself.

## The Relation “To Define One Number”

### When Two Processes Define One Number

To build a point from processes, we need to know which processes to *identify*. Two processes define one number when their approximations draw together without limit over time—differ by less than any prescribed precision. Chapter 4.2 has already introduced this relation; here it becomes a working instrument, and it is worth stating it precisely. In the file `CauchyReal.v` it is the predicate
`cauchy_equiv`:

```coq
Definition cauchy_equiv (a b : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (cs_seq a n - cs_seq b n) < eps.
```

Let us read it operationally. Demand any tightness $\varepsilon$ you like—there will be a cutoff $N$ from which on the approximations of the processes $a$ and $b$ differ by less than $\varepsilon$. The file introduces for this relation the sign $\mathbin{\sim\mkern-3mu\sim}$ (in the notation of the repository,
`a \~{}\~{} b`).

### Not Pointwise Equality

Here we must at once forestall a confusion that is easy to make. `cauchy_equiv` does *not* require the processes to coincide at every step. It speaks only of the *limit* of the discrepancy: the difference $|a_n - b_n|$ must eventually fall below every $\varepsilon$, but *at any concrete step* it may be nonzero.

The difference is one of principle. Pointwise equality of processes—“$a_n =
b_n$ for every $n$”—is a completely different, much stricter relation. Two processes can define one point without coinciding at *any* finite step: it suffices that their discrepancy decrease to zero. It is precisely this that will make possible the analysis of the equality $0{,}999… = 1$ in § 3.7—there the two processes will coincide nowhere, yet the number they define will be one. The relation “to define one number” is `cauchy_equiv`, a relation about a common limit, not about pointwise identity.

### Three Properties That Make the Relation Fit

For the relation to be fit for quotienting—for building the point as a class—it must be an *equivalence relation*: reflexive, symmetric, transitive. This is not a formal quibble but a substantive requirement. Reflexivity: every process defines the same number as itself—otherwise a process would not belong to its own class. Symmetry: if $a$ defines the same number as $b$, then $b$ defines the same number as $a$—otherwise “being one point” would not be mutual. Transitivity: if $a$ and $b$ define one number, and $b$ and $c$ define one number, then $a$ and $c$ define one number—otherwise the classes would not be stable, and representatives would “flow” between them.

`CauchyReal.v` proves all three. These are the lemmas `cauchy_equiv_refl`, `cauchy_equiv_sym`, and `cauchy_equiv_trans`. The proofs are standard $\varepsilon$-arguments: reflexivity is trivial (the difference is zero), symmetry relies on $|{-}x| = |x|$, and transitivity on the triangle inequality with $\varepsilon$ split in half. What is essential is not the arrangement of the proofs but their result: `cauchy_equiv` is a full-fledged, machine-checked equivalence relation on the type of representatives `CauchySeq`. This is the formal support of everything that follows: precisely because the three properties are proved, quotienting by `cauchy_equiv` will be a well-defined operation rather than an arbitrary grouping of processes.

### Two Representations of One Process: `CauchySeq`{CauchySeq} and `RealProcess`{RealProcess}

{
Before building a point from this relation, we must examine one circumstance that Chapter 4.2 outlined and that becomes essential here. Chapter 4.2 showed that the process is represented in the ToS repository by more than one construction: there is the bare `RealProcess`
${}={}$ `nat -> Q` from `ProcessCore.v`, and there is `CauchySeq` from `CauchyReal.v`, equipped with a proof. And on each of the two lines there is *its own* relation “to define one number”: on `CauchySeq`, the `cauchy_equiv` analyzed above; on the bare `RealProcess`, the predicate `process_equiv` from `ProcessCore.v`.
}

It is important to understand that `process_equiv` is *the same* relation in meaning. Its definition in `ProcessCore.v`:

```coq
Definition process_equiv (R1 R2 : RealProcess) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (R1 n - R2 n) < eps.
```

This is *the same* criterion of a common limit—the difference of the approximations falls below every $\varepsilon$—only written for bare processes. It should not be confused with pointwise equality: like `cauchy_equiv`, `process_equiv` says nothing about coincidence at individual steps. (A pointwise relation also exists in the repository—for example, the general `process_equiv` with a parameter in the file `ProcessGeneral.v`, which requires agreement at every step—but this is a *different*, stricter line, and the point is not built by
it.)

{
Since the relation “to define one number” exists on both lines, a question arises: are the two in agreement? If a representative `CauchySeq` is translated into the bare process `RealProcess`, will the relation be preserved? The Rocq formalization gives the answer explicitly—in the file `ProcessBridge.v`, whose header says directly that `CauchySeq` and `RealProcess` are *one and the same mathematical object*.[^1]
The file builds two translations:
}

```coq
Definition cauchyseq_to_process (cs : CauchySeq) : RealProcess :=
  fun n => cs_seq cs n.
Definition process_to_cauchyseq (R : RealProcess) (H : is_Cauchy R)
  : CauchySeq := mkCauchy R H.
```

The first forgets the proof and leaves the bare process; the second, receiving a process *together* with a proof that it is Cauchy, packs them into a `CauchySeq`. And the file proves that these translations *preserve the equivalence relation*—and in both directions:

```coq
Lemma cauchy_equiv_to_process_equiv : forall cs1 cs2 : CauchySeq,
  cauchy_equiv cs1 cs2 ->
  process_equiv (cauchyseq_to_process cs1) (cauchyseq_to_process cs2).
Lemma process_equiv_to_cauchy_equiv : forall cs1 cs2 : CauchySeq,
  process_equiv (cauchyseq_to_process cs1) (cauchyseq_to_process cs2) ->
  cauchy_equiv cs1 cs2.
```

{

The first lemma: equivalence on `CauchySeq` implies equivalence of the translated bare processes. The second: the converse. Together they mean that `cauchy_equiv` and `process_equiv` are *one relation seen on two representations*. The file also proves that the translations are mutually inverse: the lemmas `roundtrip_process_equiv` and `roundtrip_cauchyseq_equiv` establish that a translation there and back returns an object equivalent to the original.
}

{
For the present chapter this matters in the following way. When the chapter says below that “a point is an equivalence class of processes,” there is no ambiguity about *which* processes and by *which* relation. The line `CauchySeq` with `cauchy_equiv` and the line `RealProcess` with `process_equiv` are not merely similar—they are formally connected by a bridge proved in `ProcessBridge.v`. The point as a class is one and the same object on whichever of the two representations it is built. The chapter, as agreed, conducts the main line on `CauchySeq`; but this is now a choice of representation, not a choice between different objects.
}

## The Equivalence Class as a Point

### The Class of a Process

Now we can take the step toward which everything has been leading. A process is given—a representative `CauchySeq`. Consider *all* the processes equivalent to it by `cauchy_equiv`: all that define the same number. Let us call this collection the *class* of the given process.

The three proved properties of the relation (§ 3.3.3) guarantee that the classes are arranged correctly. Reflexivity: every process lies in its own class. From symmetry and transitivity a standard fact follows mathematically: two classes either coincide entirely or do not intersect at all—there is nothing in between. In the file `CauchyReal.v` this consequence is not singled out as a separate lemma—what is proved there is precisely `cauchy_equiv_refl`, `cauchy_equiv_sym`, `cauchy_equiv_trans`—but it follows directly from these three as a general property of every equivalence relation: such a relation *partitions* the type of representatives into disjoint classes, and every representative falls into exactly one. A class is a “bundle” of all the processes with a common limit, taken as a whole.

And here is the definition for the sake of which the chapter was written: *a real number is an equivalence class of processes*; *a point is such a class*. To be one point is to lie in one class; to lie in one class is to define one limit. The number $\sqrt{2}$ is not an atom of a ready line but a class: a bundle of all the processes of rational approximation converging to $\sqrt{2}$—decimal, continued-fraction, Newton—taken together as one object.

### What “Class” Means: A Setoid, Not a Completed Collection

Caution is required here, and it follows directly from $P4$. The words “the class of all processes equivalent to a given one” may sound as if we have formed a new *completed collection*—gathered all the equivalent processes into one as a ready infinite object. But that would bring back the completed infinity that the whole construction precisely avoids. If a point were a completed set of processes, we would not have built a number without completed infinity—we would merely have transferred it from the line to the class.

Therefore “class” must be understood here differently—as a *setoid class*, not as a completed collection. To say “the process $a$ belongs to the class of the process $b$” means exactly one thing: *$a$ is equivalent to $b$ by* `cauchy_equiv`. A class is not a new object assembled from processes and laid on top of them; a class is a *mode of identification*: a way of looking at processes in which equivalent ones are not distinguished. A point is not a completed collection of representatives but the type of representatives taken *together with the relation* by which some of them count as one. In type theory such a pair—a type plus an equivalence relation on it—is called a setoid; and “class” in the present chapter is always a setoid class, a mode, not an object.

In other words, the word “class” has two possible readings here, and the chapter chooses one of them. As a *completed collection*—a ready infinite set of all the representatives—it is not admitted by $P4$. As an *abstraction defined by a relation*—a mode in which equivalent representatives are not distinguished—it is exactly what the notion of a point requires. The chapter everywhere takes the second reading and rejects the first.

### What the Chapter Does Not Assert: The Quotient Type Has Not Been Built

With the same directness we must say what the Rocq formalization does *not* do. One could go beyond the setoid and build a *quotient type*—a genuinely new type whose terms are the classes themselves, so that equivalent representatives become literally *one* term. Many expositions of the real numbers do exactly this.

There is *no* such quotient type in the ToS repository. The file `CauchyReal.v` builds the type of representatives `CauchySeq` and the relation `cauchy_equiv`; it proves the reflexivity, symmetry, and transitivity of this relation—but it does *not* form a type whose terms would be classes. The chapter states this directly and does not pass off the desired as the accomplished.

{
It is essential, however, that for the content of the present chapter a quotient type as a separate Rocq object is *not* required—a setoid suffices, and this setoid is formalized. The file `RealPointSetoid.v` registers `cauchy_equiv` as an `Equivalence` (gathering `cauchy_equiv_refl`, `_sym`, `_trans` into one carrier of the setoid structure), names the point carrier `RealPoint := CauchySeq`, and proves that the operations are morphisms: `cauchy_add_Proper` and `cauchy_mul_Proper` respect the equivalence. This is enough to speak of classes correctly: the partition into classes is a direct consequence of the properties of equivalence, and the `Proper` morphisms carry arithmetic down to the classes. “The point as a class” in this chapter is work with this formalized setoid, and it rests entirely on what has been proved. Building a *quotient type* as a separate type, on the other hand, is not a missing link but a path that ToS consciously *declines*: a reified quotient would turn the mode of identification into a self-standing object (the very same $P4$ error as the completed collection, § 3.4.2) and would require axioms (the reals in Rocq have no canonical form; equality is undecidable). The setoid is not a temporary substitute for a quotient type but the axiom-free construction that the point needs.
}

## The Point as a Mode, Not an Object

### A Recurring Motif of the Volume

What has happened to the point is not new for this volume—it is a move that has already occurred, applied to a new subject. Part I and Part II did the same with the *set*: the set in ToS is not a primary container-object but a *mode* of consideration—a way of taking distinguished elements from a certain angle, as gathered into one. A set is not a thing but a view of things. In E/R/R terms (the analysis of § 3.8.2) both the set and the point are *role*-modes, not elements.

The point now receives the same reading. It is not an atom-object lying at the foundation of the line but a *mode* of consideration of processes. To pass to the point is to look at processes in a certain way: to stop distinguishing those of them that define one limit. The point is not an object among objects but an *angle of view* on processes. The volume carries out this move consistently: both the set and the point are derived modes, not primary objects; what is primary is what is distinguished and what unfolds—acts of distinction and processes.

### What Is Lost and What Is Preserved in the Passage to the Class

The passage from a process to its class is, in substance, an act of *abstraction*. The operator stops paying attention to some features of the process and keeps others in the field of view. It is worth saying precisely which ones.

What is *lost* is the individuality of the process. The decimal approximations of $\sqrt{2}$ and its continued-fraction approximations are different processes: they give different rational numbers at the same steps, converge at different rates, and are arranged by different rules. In the passage to the class, all this leaves the field of view. The class does not remember by which rule the process was generated; it does not remember how fast the discrepancy decreased; it does not remember the concrete approximations at concrete steps.

What is *preserved* is the equivalence invariant: what all the representatives of the class have in common *with respect to* `cauchy_equiv`. Not the concrete manner of motion, but the fact that these motions are connected by equivalence—that they define, in ordinary language, one and the same limit, that is, one and the same class. The class is that in the process which does not depend on the choice of the process among the equivalent ones. The point is the *invariant* of a bundle of processes: what they all share. (The word “limit” here is only the familiar name of this invariant; it is primary not as a ready point but precisely as that common element which the relation `cauchy_equiv` fixes.)

### The Point Is No Poorer than the Process

It may seem that in such a passage the point is *poorer* than the process—after all, it has “forgotten” the rule, the rate, and the approximations. But this is not an impoverishment; it is a *specialization of the view*. A process carries a great deal of information; part of it concerns the limit, part the very manner of going toward it. When it is precisely the limit that we need—when we ask “*which* number is given,” not “*how* it is computed”—information about the manner becomes an obstacle, superfluous detail. The passage to the class removes the obstacle and leaves the answer to the question asked.

The point, then, is neither less nor more than the process—it is the process *taken from a certain angle*: from the angle at which only the number is visible and the manner is not. This is the meaning of the word “mode.” One and the same process material can be considered as a process—then the rule and the rate matter—or as a point—then only the limit matters. The point and the process are not two different sorts of objects but two modes of working with one material. The $P4$ ontology does not take the point away from the mathematician—it only shows that the point is a *derived* mode into which the operator passes consciously, not a primary given with which one is forced to begin.

## Arithmetic and Order on Classes

### Why Compatibility Is Needed

If a point is a class, then it is classes that will have to be added—and here the question of well-definedness arises. A class is given by *any* of its representatives; one class has many representatives. To add two classes, it is natural to take a representative from each and add the representatives. But the result must not depend on *which* representatives we chose: otherwise addition would be an operation not on numbers but on processes, and “the sum of points” would have no meaning.

The requirement is precise: if the representatives are replaced by equivalent ones, the sum must remain in the same class. In the language of § 3.3 this means that the operations must *respect* the relation `cauchy_equiv`. Only operations with this property *descend* from representatives to classes—that is, are well defined on points.

### Addition and Negation: Compatibility Is Proved

For the additive operations the Rocq formalization proves this property directly. Chapter 4.2 has already cited the corresponding lemmas from `CauchyReal.v`; here they receive their true purpose—the justification of arithmetic on classes:

```coq
Lemma cauchy_add_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_add a b ~~ cauchy_add a' b'.
Lemma cauchy_neg_compat : forall a a' : CauchySeq,
  a ~~ a' -> cauchy_neg a ~~ cauchy_neg a'.
```

`cauchy_add_compat`: both summands have been replaced by equivalent ones—the sum has remained equivalent. `cauchy_neg_compat`: the same for the change of sign. So addition and negation *descend* to classes: the sum of two points and the point opposite to a given one are well defined, and the result does not depend on the choice of representatives. Subtraction is obtained from the same source—as addition of the opposite. On classes, then, there is an additive arithmetic: points can be added, subtracted, and negated, and these are operations on *numbers*, not on randomly chosen processes.

### Order: A Weaker but Important Fact

With order the situation is subtler, and here the chapter will say exactly what has been proved, no more. In `CauchyReal.v` there is the relation `cauchy_le`—the process “less than or equal to”—and about it the lemma `cauchy_le_of_equiv` is proved:

```coq
Lemma cauchy_le_of_equiv : forall a b : CauchySeq,
  a ~~ b -> cauchy_le a b.
```

It says: equivalent representatives are connected by the relation `cauchy_le` (and, by symmetry, in the reverse direction as well), that is, they are *mutually indistinguishable* by this order. This is a substantive and necessary fact: it means that equivalent processes are not strictly ordered relative to each other—which agrees with their defining one number.

This is the basic direction: the mutual indistinguishability of equivalent representatives. The full compatibility of order with the replacement of a representative is a statement of the form: if
$a \mathbin{\sim\mkern-3mu\sim} a'$ and $b \mathbin{\sim\mkern-3mu\sim} b'$,
then `cauchy_le` $a b$ implies `cauchy_le` $a' b'$;
it is precisely this statement that carries the order relation *from representatives to classes* in full. This lemma—under the name `cauchy_le_compat`—is now *proved*, in the file `RealPointTopology.v`, and with it `cauchy_le_Proper` (the relation `cauchy_le` is compatible with `cauchy_equiv` in both directions). Therefore the result is stronger than the chapter cautiously outlined: *both* the additive structure (through `cauchy_add_compat` / `cauchy_neg_compat`) *and* the order relation (through `cauchy_le_compat`) descend to classes—both are well defined on points, not only on processes.

### What This Yields

{
The result of the section is now fuller than it was. The equivalence class is not merely “a bundle of processes”: on classes there is a provably well-defined numerical *ring* structure and a compatible order. Addition, subtraction, and negation descend to classes (§ 3.6.2); order descends fully (`cauchy_le_compat`, § 3.6.3). Multiplication has been built too: `cauchy_mul` (the file `RealField.v`) with proved commutativity, associativity, unit, and distributivity, compatibility with equivalence (`cauchy_mul_compat`), and the morphism `cauchy_mul_Proper` (`RealPointSetoid.v`), which carries it down to the classes; on the bare line of processes it corresponds to `process_mul` (`CauchyProcessBridge.v`). So classes can be added, subtracted, multiplied, and compared—and these are operations on *numbers*, well defined on points. An honest measure remains: the multiplicative inverse (`cauchy_inv_is_cauchy`) is defined only for representatives bounded away from zero—division is partial, as befits a constructive field (a process that is merely *equivalent* to zero cannot be inverted). A full field structure with *total* division is not a gap to be closed but a boundary of the constructive notion of number itself.[^2]
}

## Analysis of $0{,}999… = 1${Analysis of 0,999... = 1}

### The Famous “Paradox”

The equality $0{,}999… = 1$ is one of the best-known stumbling blocks of school mathematics. Intuition resists: $0{,}999…$ “looks smaller” than one, “falls short” of it, as though an infinitesimal gap remained between them. And yet mathematics insists that this is *one and the same number*.

The present chapter gives this equality a natural reading—and, more importantly, shows that the “paradox” arises *only* in the point picture, while in the process picture it does not form. This is a good test of the whole construction: if the point as a class works, then the most disputed school example must become clear in it.

### Two Processes

In the process picture $0{,}999…$ is not “a number with an infinite tail of nines” but a *process*: a sequence of rational approximations unfolding according to a rule

$$
0{,}9; \quad 0{,}99; \quad 0{,}999; \quad 0{,}9999; \quad …
$$

At step $n$ this process outputs a rational number with $n{+}1$ nines after the decimal point. Let us call it the *decimal process*.

One is also a process, the simplest one: the constant process that outputs $1$ at every step. In the terms of Chapter 4.2 this is `cauchy_const 1`.

These are *two different processes*. And they differ not slightly: they differ *at every step*—the value of the decimal process (`nine_raw`) at step $n$ is $1 - 10^{-(n+1)}$, the value of the constant process is $1$, and these rational numbers do not coincide for any $n$. This is proved formally as well—the theorem `nine_raw_lt_one`: every truncation is strictly less than one (§ 3.7.5). And nevertheless the two processes, which coincide nowhere, define one number and lie in one class.

### Why They Are in One Class

They are in one class because their discrepancy *goes to zero*. At step $n$ the difference between one and the decimal process is exactly $1/10^{n+1}$: one minus a number with $n{+}1$ nines. And $1/10^{n+1}$ decreases without limit: name any tightness $\varepsilon$ you like, and from some step on the discrepancy will become smaller than $\varepsilon$ and will not go beyond it again. This is exactly the definition of `cauchy_equiv` from § 3.3: the decimal process and the constant process are *equivalent*.

And since they are equivalent, they are in one class. And therefore, by the definition of § 3.4, they define *one number*. The equality $0{,}999… = 1$ is neither a mysterious coincidence of two different numbers nor a “convention”; it is a simple statement of fact: *two different representatives of one class*. $0{,}999…$ and $1$ are two processes, one bundle, one point.

### Where the “Paradox” Was

Now it is clear where the sense of paradox came from. It is a product of the point picture. If the point is primary, if $0{,}999…$ and $1$ are *ready points* on a ready line, then a legitimate question arises: is this one point or two? And if two—where is the gap between them; and if one—why does it have two different “notations”? The point picture poses a question that it cannot answer clearly, and therefore the question feels like a paradox.

The process picture simply does not give rise to this question. In it $0{,}999…$ and $1$ are *processes* from the very beginning, and different processes—no one has claimed that they are one object at the level of representatives. The question “one number or two?” receives an exact meaning: *do the two processes lie in one equivalence class?*—and an exact answer: *yes, they do, for their discrepancy decreases to zero*. The “infinitesimal gap” that intuition sought between $0{,}999…$ and $1$ is precisely the discrepancy $1/10^{n+1}$; it is not an “infinitesimal quantity” frozen somewhere on the line, but a *term of a process* that decreases with each step. At every step the gap exists and is positive; in the limit the process of discrepancy falls below every $\varepsilon$. The paradox was an artifact of a picture in which the infinite process of approximation was replaced by a ready point. Remove the substitution, and the paradox does not form. In E/R/R terms (§ 3.8.2) this was a confusion of categories: the point-*role* (a class) was taken for an *element*-object.

### The Formal Proof: The File `ProcessNinePoint.v`

What has been said so far is a substantive analysis. Let us also indicate the *formal* status of this equality, and here the chapter can be precise: in the ToS repository the equality $0{,}999… = 1$ is *proved* as a theorem—the file `process/ProcessNinePoint.v`, the theorem `nine_equiv_one`, without a single axiom. The proof proceeds in exactly the four steps that the substantive analysis sketched; let us go through them in order.

*Step one*—the decimal process as a function from numbers to rationals:
```coq
Definition nine_raw : RealProcess := fun n => 1 - 1 / ten_pow (S n).
```
Here `S n` is the number following $n$, so that the numbering starts from the first nine: at step $n = 0$ the process gives $1 - 1/10 = 0{,}9$ (the machine check `nine_raw_0`), at step $n = 1$,
$1 - 1/100 = 0{,}99$, and so on. The power of ten is taken by a separate function `ten_pow` (through `pow10` over `positive`): the ordinary notation `10 \^{} (S n)` over $ℚ$ would not work in Rocq. Here, too, is the machine-checked resolution of the “paradox”: at the level of *elements* every truncation is strictly less than one (the theorem `nine_raw_lt_one`: `forall n, nine_raw n < 1`), while at the level of the *point* the process coincides with one (step four); the “paradox” $0{,}999… < 1$ is a confusion of these two levels.

{
*Step two*—to prove that `nine_raw` is a Cauchy process. The path is indirect, through the two representations, and it is carried out exactly so. First `nine_raw` is taken as a bare `RealProcess`, and its `process_equiv` with `const_process 1` is proved (step four). Then from the Cauchy property of the constant process (`const_is_Cauchy` from `ProcessCore.v`) and the lemma `equiv_cauchy_l` of the same file (a process equivalent to a Cauchy process is itself a Cauchy process), `is_Cauchy nine_raw` is derived—the theorem `nine_raw_is_Cauchy`. Thereby `nine_raw` can, if needed, be packed into a
`CauchySeq`.
}

*Step three*—the estimate of the tail: for every precision $\varepsilon$ there is a cutoff $N$ beyond which $1/10^{n+1} < \varepsilon$. In substance this is a statement about the unbounded growth of the powers of ten; technically it is obtained from the Archimedean lemma `q_archimedean` (from `ProcessArithmetic.v`) and the growth estimate `pow10_ge`.

*Step four*—to put it all together and prove the target theorem:
```coq
Theorem nine_equiv_one : nine_raw ~~ const_process 1.
```
The proof is a direct application of the tail estimate from step three: the discrepancy of the processes at step $n$ equals $1/10^{n+1}$ and falls below every $\varepsilon$—hence, by the definition of `process_equiv` ($\mathbin{\sim\mkern-3mu\sim}$), the processes name one point.

So one may write with full formal right: *$0{,}999…$
and $1$ are different processes* (different bearers: $`nine_raw` 0 =
0{,}9 \neq 1$), *but one class, one point*. The theorem is proved at
the level of bare processes ($`nine_raw` \mathbin{\sim\mkern-3mu\sim}
`const_process`\;1$); the transfer to the packaged line `CauchySeq` is available through `nine_raw_is_Cauchy` and the bridge, but the statement itself is the equality-as-points on processes. The formalization does not *change* the meaning of the substantive analysis of § 3.7.1–3.7.4 but *turns* it into a machine-checked theorem: $0{,}999… = 1$ is an equality of *points* ($\mathbin{\sim\mkern-3mu\sim}$), not an identity of objects ($=$)—the processes are distinct, the point is one.

## The Point Has Been Built

### What Has Been Done

The chapter began with the step that Chapter 4.2 left unfinished: quotienting. The type of representatives `CauchySeq` and the relation `cauchy_equiv` had been built earlier; the present chapter carried out this passage at the *setoid level*, and this setoid is now formalized (`RealPointSetoid.v`: `Equivalence` + `Proper` morphisms): a real number has been read as a setoid class of representatives under the relation `cauchy_equiv`. A separate *quotient type* in Rocq was not built along the way—and not for lack of means but deliberately (§ 3.4.3): the chapter worked with a formalized setoid and a proved bridge, without reifying the classes into a new type-space of points.

The path was as follows. First, why the point cannot be primary: a ready line of point-atoms is a completed infinity, and $P4$ excludes it; processes are primary, and the point must be *built* from them (§ 3.2). Then the relation “to define one number,” `cauchy_equiv`, with proved reflexivity, symmetry, and transitivity—a relation not reducible to pointwise equality (§ 3.3); and the bridge proved in `ProcessBridge.v`, connecting the two representations of the process into one object (§ 3.3.1). Then the definition: a point is an equivalence class of processes, where *class* is understood as a setoid mode of identification, not a completed collection, and the quotient type is honestly not built as a separate Rocq type (§ 3.4). Then the point as a mode, not an object: a derived angle of view on processes, from which the limit is visible and the manner is not (§ 3.5). Then arithmetic on classes: addition, negation, and multiplication provably descend to classes (`cauchy_mul_Proper`), and order descends fully (`cauchy_le_compat`) (§ 3.6). Finally, the analysis of $0{,}999… = 1$: two processes, one class, one number, and the “paradox” an artifact of the point picture; the equality is proved by the theorem `nine_equiv_one` (§ 3.7).

### E/R/R Analysis: The Point as a Class—a System

{
What has been built in this chapter also has an E/R/R arrangement (Part I), and its analysis crystallizes the main turn of the chapter. The headers of the supporting files give the labeling: `ProcessCore.v` declares the rule *every object is a finite process at each stage* ($P4$); and the relation `cauchy_equiv`/`process_equiv` and the bridge `ProcessBridge.v` give the rule of identification.[^3] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. A caveat on status: everything below is a substantive reading; the quotient type has not been built as a separate Rocq type (§ 3.4.3), and “system” here is not an object `System` $L$.}

*Rules* (the law $L5$). The constitution is the same as in Chapter 4.2—the principle $P4$: a number is a process, not a completed point, and therefore “class” is read as a setoid mode, not as a completed collection (§ 3.4.2). The main rule of the chapter is the *equivalence relation* `cauchy_equiv` (“to define one limit,” not pointwise equality, § 3.3): it is this relation that identifies processes. Its reflexivity, symmetry, and transitivity make quotienting legitimate (the partition into disjoint classes is a mathematical consequence of these three lemmas). Adjoining it are the rules of compatibility: addition and negation descend to classes (`cauchy_add_compat`, `cauchy_neg_compat`); order only partially (`cauchy_le_of_equiv`, § 3.6.3); and the bridge `ProcessBridge.v` brings the two representations of the process into agreement.

*Roles—the significance of positions* (the law $L4$). Here is the very turn of the chapter, read as E/R/R. *The point is a role, not an element.* It is not an object among objects but a *mode* of consideration of processes: an equivalence class, an angle of view from which equivalent processes are not distinguished (§ 3.5). This completes the progression of role statuses of Chapter 4.2: candidate $\to$ representative $\to$ *number* (class); the number-point is the final role, realized by the rule of quotienting. By $L4$ the role is grounded: the class is a structural invariant of a bundle of equivalent processes, not an arbitrary union of them.

*Elements—the bearers* (the law $L1$ and the principle
$P4$). The elements are the representative *processes* (`CauchySeq`) and the rational approximations beneath them. What is essential: the point *is not* an element—processes are primary, and the point is derived from them (§ 3.2). By $L1$ each representative process is identical to itself; by $P4$ it is observed through finite prefixes, and the class is not gathered into a completed collection.

 Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| representative processes (`CauchySeq`); approximations | bearers (the point is not an element) | Element |
| point ${}={}$ class ${}={}$ mode of identification | role (derived) | Role |
| $P4$: a number is a process, not a point | constitution | Rule |
| `cauchy_equiv` (refl/sym/trans) | rule of identification | Rule (concr.) |
| compatibility (`add_compat`); the bridge of representations | agreement | Rule (concr.) |
| laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: processes are elements, the point-class is a role, equivalence is a rule. And here the analysis turns into a *diagnosis*: the “paradox”
$0{,}999… = 1$ (§ 3.7) was a *confusion of categories*—the point-*role* (a class) was taken for an *element*-object, and people asked “is this one point or two?” In the correct labeling the question does not arise: two process-elements, one role-class. This is the very diagnosis of paradoxes as a confusion of E/R/R categories that was introduced in Part I.

 The analysis continues the E/R/R foundation of Part IV (Chapter 4.2). If there the process number was read as a progression of roles, here the concluding role—*the point as a class-mode*—receives an explicit meaning: it is not a primary element but a derived role, given by the rule `cauchy_equiv` over the process-elements. Just as the *set* in Parts I–II turned out to be a mode, not a thing, the *point* here turns out to be a mode, not an atom. Chapter 4.4 will ask *how many* such role-classes there are—and the count there will go by classes.

### The Point Restored to Its Proper Place

The result can be formulated in one sentence. The point has not been abolished or declared meaningless—it has been *restored*, but in its proper place: not as a primary atom with which the construction is forced to begin, but as a derived mode into which the operator passes consciously, quotienting processes by the relation “to define one limit.” What Chapter 4.1 outlined in § 1.8 (“the point is recovered later as a mode”), and Chapter 4.2 prepared with the equivalence relation, the present chapter has brought to completion.

{
It is worth specifying at once in what exact sense the point has been “built”—the heading of this section is strong, and it needs to be read precisely. The point has been built in the *mathematical-ontological* sense: as a setoid class of equivalent representatives, as a mode of identification of processes by `cauchy_equiv`. What has been built in the Rocq kernel is not a new type-space of points but a *setoid*: an equivalence relation registered as an `Equivalence`, with `Proper` morphisms for the operations (`RealPointSetoid.v`)—that on which the reading of the point as a class rests. The chapter has kept the difference between two things all along: the point as a setoid class—built and formalized; the reified quotient type as a separate Rocq type—deliberately not built (§ 3.4.3, by
$P4$).
}

The $P4$ ontology, as we see, does not impoverish mathematics. The familiar objects—set, point, number—remain; only their *order* and *status* change. Acts of distinction and processes are primary; the set and the point are derived modes. A real number is a class of processes; and this picture not only loses nothing necessary but also clarifies what remained obscure in the point picture—as the analysis of $0{,}999… = 1$ showed.

### The Bridge to Chapter 4.4

If a point is a class of processes, the question of *quantity* immediately arises. How many points are there—that is, how many classes? The processes of rational approximation are immeasurably many; how many classes does `cauchy_equiv` partition them into? Is their set countable, like that of the rational numbers, or uncountable?

This is the subject of Chapter 4.4. It will prove uncountability—a process reading of Cantor’s classical theorem. And here it is important to point out in advance two points of precision that follow directly from the present chapter.

The first concerns *what exactly* the next chapter will prove. Chapter 4.4 will not work with an already built quotient type of points: there is no such type in the repository, as established in § 3.4.3. The file `ProcessUncountable.v`, on which it relies, proves not a theorem about a quotient type but a statement equivalent to uncountability for the setoid approach: for every enumeration of processes there is a Cauchy process (lying, in the file’s formulation, in the interval $[0,1]$) that is *not equivalent* to any element of the enumeration. In other words, no enumeration of representatives covers all the equivalence classes—there is always a class not represented in the enumeration. This is process uncountability: the count goes by classes, and the count does not suffice for all the classes.

The second concerns the sense in which the diagonal process “differs” from the enumerated ones. It differs *by process equivalence*: it is built so as not to fall into one class with the enumerated processes—that is, not to be equivalent to them by `process_equiv`. This must be distinguished from pointwise non-coincidence. Pointwise non-coincidence is *not enough* here: two processes can differ at every finite step and still define one class (like the decimal process and one in § 3.7); and conversely, they can coincide at infinitely many steps without being equivalent. These are simply different properties. The diagonal argument of Chapter 4.4 needs precisely *non-equivalence* by `process_equiv`, not falling into a common class—and the count there will be conducted by classes, as the present chapter has prepared it.

{*The result of the chapter is in three parts. First: what a point is. A real number is an equivalence class of processes of rational approximation under the relation “to define one limit”; a point is such a class. A point is not a primary atom of the line but a derived mode: a process taken from the angle from which the limit is visible and the manner of going toward it is not. “Class” is understood as a setoid mode of identification of representatives, not as a completed collection.*}

{*Second: what has been proved formally. The relation by which the class is built is `cauchy_equiv` from `CauchyReal.v` on the representatives `CauchySeq`; on the bare processes `RealProcess` it corresponds to `process_equiv` from `ProcessCore.v`—the same relation of a common limit on another representation, and the bridge between them is proved in `ProcessBridge.v`. The relation is provably reflexive, symmetric, and transitive (and registered as an `Equivalence` in `RealPointSetoid.v`). Addition, negation, and multiplication of classes are provably well defined (`cauchy_add_compat`, `cauchy_neg_compat`, `cauchy_mul_Proper`); order also descends to classes fully (`cauchy_le_compat`).*}

{*Third: what has been built and what, deliberately, has not. The passage to classes has been carried out at the formalized setoid level (`RealPointSetoid.v`: `Equivalence` + `Proper` morphisms); a reified quotient type as a separate Rocq type is not built—by $P4$, not for lack of means (§ 3.4.3). Addition, negation, multiplication, and—fully—order have been carried down to the classes (`cauchy_le_compat`); division is partial, as befits a constructive field. The equality $0{,}999… = 1$ is proved by the theorem `nine_equiv_one` (`process/ProcessNinePoint.v`, without axioms): the decimal and the constant processes are different representatives of one class, and the “paradox” was an artifact of the point picture. How many such classes there are in all—countably or uncountably many—is analyzed by Chapter 4.4.*}

---

[^1]: `ProcessBridge.v` of the ToS Rocq repository (directory `src/process/`), 10 proved statements, 0 `Admitted`, 0 axioms. The header of the file: to connect `CauchySeq` and `RealProcess`, making the bridge between them explicit.
[^2]: This partiality is formalized as an *apartness field*. Being bounded away from zero is the predicate `apart0` (a presented rational gap $q<|x|$), and the theorem `apart_has_inverse` gives: the multiplicative inverse exists *exactly* for elements apart from zero; all together, `apartness_field`. Thus the partiality of division is not a defect but a proved constructive structure. Machine-checked, 6 Qed, 0 axioms.
[^3]: The E/R/R labeling in the headers of `ProcessCore.v` and `ProcessBridge.v`; here it is unfolded on the model of Part I.

---

Part: [[04 Process Real Numbers|Part IV. Process Real Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/02 RealProcess as a Type|Chapter 2. RealProcess as a Type]] · [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/04 Uncountability of Processes|Chapter 4. The Uncountability of Processes]] →
