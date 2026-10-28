---
title: "Chapter 1. The Primacy of One"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/02 Натуральные числа/01 Первичность единицы.md"
sourceBlob: 0278074b8569fcf917c95cbe6c0a600ce45275a2
translated: 2026-10-20
status: draft
---

Part I built the main axis of the Theory of Systems: $A = \exists$ as the pre-formal first principle; `Distinction` as the first formalizable trace; $L1$–$L5$ as structural properties of distinction and of the hierarchy; $P1$–$P4$ as principles of system construction; and $E/R/R$ as the ontological scheme of a system. The ontological core of the volume was outlined as well: the processuality of ontology and four ontological positions. Part II begins the application of this apparatus. Its subject is the natural numbers.

The application begins with a question that the standard exposition of mathematics usually does not pose, because it is considered settled by default: *where does the number series begin*? The standard answer is: with zero. The present chapter shows that for the ontology developed in ToS, what is primary is one, not zero; that zero is a derived notion; and that this rearrangement is a consequence of how anything *is* in ToS at all, more than a change of notation. The chapter opens Part II because the way in which the number series will be built in the subsequent chapters depends on the answer to the question of its beginning.

## The Standard Position: Zero Is Primary

### Three Forms of the Primacy of Zero

In standard mathematics, zero occupies the first place in the construction of the natural numbers. This position is carried out along at least three independent paths, and each of them deserves consideration, since it is relative to them that ToS makes its move.

**The axiomatic path: Peano.** In the Peano axioms, the natural number series is given by a base element and an operation. The base element is zero; the operation is the passage to the next, the *successor*. Every natural number is either zero or the successor of some natural number. In the formalization adopted in Rocq, this is written as an inductive type[^1]

```coq
Inductive nat := O | S : nat -> nat.
```

Here `O` is a constructor without arguments, and it is named first. One is not a separate constructor: it is `S O`, the successor of zero. Two is `S (S O)`, and so on. In this construction zero is the *initial point*, and every other number is obtained from it by finitely many applications of the successor. No number precedes zero; zero is not a successor, and therefore it is the *first thing* with which the natural number series begins.

**The set-theoretic path: von Neumann.** In the construction of the natural numbers through sets, which goes back to von Neumann, each natural number is identified with a definite set. Zero is the empty set $\varnothing$. One is the set containing the empty set: $\{\varnothing\}$. Two is $\{\varnothing, \{\varnothing\}\}$, the set whose elements are zero and one. In general form: the next number is the set of all the previous ones.

Here, too, zero is primary, and for the same reason for which the empty set is primary. The empty set is the simplest object of set-theoretic ontology: its construction requires *no* elements. Every nonempty set presupposes its elements as already available; the empty set presupposes nothing. It is therefore natural to begin the construction of the numbers with it, and the number assigned to it is zero.

**The categorical path: the initial object.** In the category-theoretic description, the natural number series arises as an object of a special kind: the carrier of a structure given by a map from a distinguished point and by the successor operation.[^2] The distinguished point, the image of the unique map from the terminal object, plays the role of zero. In this description, too, zero is that *from which* the structure is counted: it is the point to which the “empty input” is mapped, and everything else is defined relative to it.

### What Unites the Three Paths

The three paths differ in technique but agree on one thing: zero is the *reference point*. It is named first (Peano), assigned to the simplest object (von Neumann), placed at the beginning of the structure (the categorical path). In all three cases the remaining numbers are defined *through* zero and *after* it.

Precision is needed here. The three paths agree *structurally* (everywhere the natural number series is given through a distinguished initial, zero, element and the operation of succession), but *ontologically* they differ. Only von Neumann’s construction is genuinely set-theoretic: there the initial element is the *empty set*. Peano arithmetic and the type `nat` in Rocq need not rest on the empty set: `nat` is an inductive type with the zero *constructor* `O`, and `O` here is a base point, not “nothing.” The categorical natural numbers object is given by an arrow $1 \to N$, where $1$ is the *terminal* object, which is likewise nonempty. It is therefore incorrect to say that all three paths are united by a single set-theoretic ontology of an “initial nothing.”

*The primacy of zero in standard mathematics is not an arbitrary convention. In the set-theoretic path it follows from the ontology of the empty set; in the type-theoretic and categorical paths, from the choice of a *base point* (the zero constructor, the terminal object) as the origin of the count. What is common to all three is the structural role of the initial element, not one and the same ontology of “nothing.”*

From this we can see where exactly ToS will part ways with the standard position. The divergence will lie in *ontology*, not in the technique of constructing the number series and not in arithmetic: in *what* is taken as the origin of the count and *why*. ToS takes as its beginning the *act of distinction*, neither emptiness nor an indifferent base point; and the act of distinction is presence, not emptiness. What follows from this for the beginning of the number series is the subject of the next section.

## The Position of the Theory of Systems: One Is Primary

### The First Act of Distinction Is One

The initial object of ToS is the act of distinction, not the empty set. Chapter I.2 analyzed its arrangement: the act of distinction posits a positive side and a negative side, and these two sides are mutually exclusive and jointly exhaustive. The act does not exist without both sides, and the sides do not exist without the act.

Let us ask a question that has no meaning for set-theoretic ontology but has one for the ontology of ToS: *how many acts of distinction have been performed when the first has been performed*? The answer is direct: *one*. Not one side: there are two sides. Not one object: the object is not yet under consideration; the act is. *One act* has been performed, and this “one” is the first number that appears in the system.

It is essential that this “one” is not the result of counting. Counting is a process that is itself analyzed below, in § 1.6 and in Chapter II.2. Before any counting, before a list, a length, or a multiplicity appears, there is the *fact that the act has been performed*. This fact already has a number: one. One is the *cardinality of what has been performed*: the measure of the fact that the act has been carried out, taken before this measure is computed in any way.

In the repository this is fixed by the simplest possible definition. To each act of distinction, that is, to each object of type `Distinction`, a number is assigned, and this number is one:

```coq
Definition one_from_distinction (D : Distinction) : nat := 1.

Theorem one_is_first_from_existence :
  forall D : Distinction, one_from_distinction D = 1%nat.
Proof. reflexivity. Qed.
```

The definition is deliberately trivial, and its triviality is substantive. It does not *compute* the number of the act and does not *prove* the primacy of one in the strict sense; it *registers* the adopted interpretation: the decision to read each act of distinction as one unit. The theorem `one_is_first_from_existence` is proved by the single word `reflexivity`, that is, it machine-checks this computation: in the given formal interpretation every `Distinction` object, regardless of what exactly it distinguishes, receives the numerical imprint `1`. The ontological load itself, the statement “the act of distinction is one,” remains a substantive thesis of the chapter rather than a consequence of the code: the code registers the chosen reading and checks its consistency, while this reading is grounded by the ontology of the act of distinction (§ 1.2), not by a theorem. Here ToS makes explicit what remains unspoken in the standard construction: before counting objects, we must *have the act* by which they are distinguished, and ToS reads this act as one.

### One as an Act, Not as a Set of One

The position of ToS is more radical than it seems at first reading, and it is worth separating it from a close but different statement.

Standard mathematics also has one and can also obtain it early. In von Neumann’s construction, one is $\{\varnothing\}$, the set containing the empty set. This is a *one-element set*. But it is obtained *after* zero and *through* zero: to form $\{\varnothing\}$, we must already have $\varnothing$. One is secondary here: it is “a set in which there is one element,” and this “one” is counted relative to emptiness.

ToS asserts something else. ToS says: one is *the act itself*, not a set containing one element. The difference can be expressed as follows. In the set-theoretic picture, “one” is a *property of what has been gathered*: we took the empty set, placed it in a new set, obtained a collection, and counted that it has one member. In the picture of ToS, “one” is *what has been performed itself*: there is an act, and the act *is* one; it does not “contain one,” it “is one.”

*The standard position: one is a set in which there is one element. The position of ToS: one is one act. In the first case “one” is counted in a gathered collection; in the second, “one” is the very measure of what has been performed, which needs no collection in order to be.*

This difference is not verbal. It follows from it that in ToS one is available *earlier* than any collection, any set, any counting, because it is the imprint of the very first act rather than the outcome of gathering. And it is precisely for this reason that it is primary: nothing in the system precedes the first act of distinction, and the first act of distinction *is* one. In terms of E/R/R, one here is a *role* (the first count, the imprint of the act), not an element-object (analysis in § 1.8.7).

### Why One and Not Zero: The Structural Asymmetry

What has been said suffices to assert that in ToS one is primary. But a subtler question remains. The act of distinction posits *two* sides, the positive and the negative. Are they not symmetric? And if they are symmetric, why is the first number one (one side is marked) rather than, say, two (two sides), and why does zero turn out to be *behind* one rather than on a par with it?

The answer is that the two sides of the act of distinction are *not symmetric*. Their asymmetry is structural. The repository file `AsymmetricDistinction.v` fixes it formally; let us analyze it precisely.

**The negative is defined through the positive.** When a distinction is built from a proposition $P$, its positive side is $P$ itself, and its negative side is $\neg P$:

```coq
Theorem positive_is_given : forall P : Prop,
  positive (distinction_of P) = P.
Proof. reflexivity. Qed.

Theorem negative_depends_on_positive : forall P : Prop,
  negative (distinction_of P) = (~P).
Proof. reflexivity. Qed.
```

The positive side is *given*: it is $P$, and its definition is *direct*. The negative side is *defined through* the positive: it is $\neg P$, the result of a logical operation applied to $P$. To specify the negative, we must *already have* the positive to which negation is applied; the converse does not hold.

Precision is required here; otherwise the statement is easily distorted. The asymmetry is *not* temporal. The positive side does not arise “earlier in time” than the negative: both arise in one and the same act of distinction, simultaneously (Chapter I.2: the co-definition of the sides). The asymmetry is *definitional*: the positive is defined directly, the negative through the positive. And definitional dependence is stronger than dependence by co-definition. The positive and the negative equally *need* each other in order to be *determinate as sides* (without distinctness from something, $P$ is not the distinguished $P$); but the first is *given*, and the second is *derived by negation*.

**The marked side.** This definitional primacy is what ToS calls *markedness*. The positive side is the marked one: the one through which the other is defined. The negative is the unmarked one. And here is the formal bridge from markedness to number:

```coq
Definition mark   (D : Distinction) (h : positive D) : nat := 1.
Definition unmark (D : Distinction) (h : negative D) : nat := 0.

Theorem marked_greater_than_unmarked : forall D p n,
  (unmark D n < mark D p)%nat.
Proof. intros. unfold mark, unmark. lia. Qed.
```

One is assigned to the marked side, zero to the unmarked. This assignment is not arbitrary: one goes to the side that is *given*, zero to the side that is *derived through the given one*. And since the marked is definitionally primary, its number is primary too. *Therefore* the first recognizable magnitude is one, and zero stands behind it.

**A technical caveat on the status of `mark` and `unmark`.** This formal bridge must be read carefully. The functions `mark` and `unmark` take as their second argument a *proof*, an object of type `positive D` or `negative D`, rather than *a side as a role*. For one and the same distinction `D`, proofs of *both* sides at once are impossible: the field `exclusive` of the record `Distinction` rules out exactly `positive D /\ negative D`. Therefore the theorem `marked_greater_than_unmarked` in its literal form, `forall D p n, unmark D n < mark D p`, compares two numerical values under hypothetically given proofs, not two *really compatible* sides of one distinction. This is a *proof-level* construction: formally it is weaker than the role-level statement “the marked role corresponds to $1$, the unmarked to $0$.”

This last statement is formalized more precisely through a *role-side* than through proofs, for example as follows:

```coq
Inductive DistinctionSide := Marked | Unmarked.

Definition side_value (s : DistinctionSide) : nat :=
  match s with Marked => 1 | Unmarked => 0 end.

Theorem marked_role_gt_unmarked_role :
  side_value Unmarked < side_value Marked.
Proof. simpl. lia. Qed.
```

Here precisely two *roles*, `Marked` and `Unmarked`, are compared as values of one enumerated type, and the inequality $0 < 1$ expresses the priority of the marked role without appeal to proofs of the sides. `mark` / `unmark` meanwhile keep their meaning as a *proof-level interpretation* of the same priority: they show what number a side receives *when* it is presented by a proof. The substantive argument of the chapter (one marks the marked, given, side; zero marks the unmarked, derived, one) rests on the role-level distinction; `mark` / `unmark` are its proof-level shadow.[^3]

Here a second, deeper asymmetry is added to the definitional one. Chapter I.7 established positive ontology: everything that exists ontologically exists *positively*; non-being is not a special kind of being existing alongside being; what is not simply is not, and is no special object called “absence.” Positive ontology bears directly on the distribution of one and zero over the sides of the act. The positive side is *presence*: what the act has posited. The negative side is “not this”; it is fully real *as a side of the act* (Chapter I.2: the co-definition of the sides), but it is not an independent presence existing separately from the positive and on a par with it. One marks what *is*; zero marks what *is not*. And by positive ontology only presence can be primary: what is not cannot be posited first, because to be posited is to be presence. The asymmetry of the marked and the unmarked is thus not only definitional (the first is given, the second derived) but also ontological (the first is presence, the second marks its absence). Both asymmetries point in the same direction: one is primary.

From here, too, comes a warning that will be essential in § 1.3. If zero marks absence, and by positive ontology absence is not a special object, then zero cannot be introduced in ToS as an object-alongside-the-numbers formalizing some entity, “emptiness.” By what it is then introduced is analyzed in the section that follows the structural asymmetry; here it suffices to fix that positive ontology *rules out* a primary zero as an ontological figure, not as the least of the numbers.

**A distinction cannot be reversed.** One could object: is the marking of the positive side not the arbitrariness of an observer, who could just as well have marked the negative one? The file `AsymmetricDistinction.v` answers this formally. An operation `swap_distinction` is defined, which interchanges the sides, and it is proved that the interchange yields a *different* distinction, not the same one:

```coq
Theorem distinction_asymmetric : forall P : Prop,
  positive (distinction_of P)
    <> positive (swap_distinction (distinction_of P)).
Proof. (* ... uses classic ... *) Qed.
```

Interchanging the sides is a passage to the distinction $\neg P$ instead of $P$, to a *different* act. The sides are not interchangeable: the distinction $P$ and the distinction $\neg P$ are two different records, not one record read in two ways.[^4] The asymmetry is thus *inherent* in the act, not imposed on it from outside. It is precisely the positive side that is marked, because definitional primacy is a property of the arrangement of distinction, not the choice of whoever looks at the distinction.

### “Before” and “After”: The First Numerical Imprint

The structural asymmetry has a direct consequence with which it is convenient to close the section, because it sets the through-line of the whole of Part II.

From the asymmetry of the sides, the act of distinction receives an *orientation*: a direction from the marked to the unmarked. The file `AsymmetricDistinction.v` introduces for the sides, taken in their orientation, the names `before` and `after`:

```coq
Definition before (D : Distinction) : Prop := positive D.
Definition after  (D : Distinction) : Prop := negative D.

Theorem before_after_exclusive : forall D : Distinction,
  ~ (before D /\ after D).
Theorem before_after_exhaustive : forall D : Distinction,
  before D \/ after D.
```

“Before” and “after” are the positive and the negative sides taken with their orientation; they are mutually exclusive ($L2$) and jointly exhaustive ($L3$), exactly as the sides of the act, which is what they are. One act of distinction generates “before” and “after,” and this generation is one: one act, one distinguished pair with its direction.

Here lies the seed of the whole construction of the natural number series toward which Part II is heading. *One* act of distinction gives “before” and “after.” *Repetition* of the act (one more distinction, now between “what was performed earlier” and “what is being performed now”) gives “before—after—after.” The formal imprint of such repetition is the natural number; Chapters II.2–II.5 are devoted to unfolding this imprint. One stands at the beginning as the *first act* from which repetition keeps count, not as the least of the numbers and not as a “set of one.”

The structural asymmetry analyzed above is not confined to the foundations of arithmetic. The header of the file `AsymmetricDistinction.v` notes that the same asymmetry, the definitional primacy of one side over the other, shows through beyond number systems as well: behind the directedness of time, behind the predominance of matter over antimatter. These connections belong to physics and are not analyzed here; it suffices to note that in ToS the *primacy of one over zero* is one of the manifestations of the general asymmetry of the act of distinction, the asymmetry that sets the given apart from what is derived through the given, rather than an isolated feature of arithmetic.

## What Zero Is

### Statement of the Problem

The previous section established that the act of distinction is primary and that its number is one. Through positive ontology, it also closed zero’s path to primacy: zero marks absence, which by positive ontology is not a special object, and therefore zero cannot be posited first.

But it does not follow that there is no zero in ToS at all. In the type `nat` the constructor `O` is present; arithmetic uses it; the statement “zero distinctions have been performed” is meaningful and sometimes true. Zero is needed. The question of the present section is *by what it is introduced*, not “is there a zero”: what formal and ontological status it receives if being a primary object is closed to it.

The problem is subtler than it seems, and it is precisely positive ontology that creates the subtlety. The simplest answer, “zero is emptiness, absence as such,” is closed: it would return us to an ontology in which “absence” is an object alongside the objects that are present, and ToS holds no such ontology. Hence zero must be introduced so that it does *not* turn out to be a name for an object-emptiness. How exactly is analyzed below.

### Zero as a Boundary, Not as an Object

Let us draw the distinction between two ways in which something can “be zero” on a simple observation.

When we say “there is no sixth finger on the hand,” we do not point to a special object, an “absent finger,” lying somewhere next to the five that are present. We report something about the *five that are present*: there are exactly five of them, and there is no sixth among them. “There is no sixth finger” is a statement about what is present, taken from its *boundary*: about where what is present ends. It does not introduce the sixth finger as an object of a special, negative kind.

So it is with zero. Zero is the *boundary* of the series of distinctions: the mark of where the count of distinctions *begins*, before the first performed act. It is not an object, “absence of distinction,” lying next to the distinctions that are present. It is related to the acts of distinction as “there is no sixth finger” is related to the five that are present: it speaks about them (that there might have been none of them) without adding an object to them.

This is the status consistent with positive ontology. Zero is introduced *neither* as an object-alongside-the-numbers *nor* as a name of emptiness. It is introduced as a *boundary mark*: a limiting value relative to which the series of performed distinctions is counted, but which is not itself a performed distinction. In the repository the file `PrimalityOfOne.v` fixes this as follows:

```coq
Definition zero_from_no_distinction : nat := 0.

Theorem zero_is_absence :
  zero_from_no_distinction = 0%nat.
```

Precision is needed here in reading the code. `zero_from_no_distinction` is the *numerical value* `0` assigned to the situation “no distinctions have been presented”; the theorem `zero_is_absence` checks that this value is indeed `0`. It is essential what this code does *not* assert: it does *not* say that in the whole universe there exists not a single `Distinction` object. Such a statement would simply be false: the type `Distinction` is inhabited (for example, `distinction_of True` exists, and the file `Distinction.v` fixes this by the lemmas `one_distinction_exists` and `two_distinctions_exist`). Zero in ToS means the absence of presented distinctions *in a given counting context* (in a given list, at a given stage), not the absence of distinctions *in general*. In other words: zero does not mean that not a single act of distinction has been performed in the world; it means that not a single one has been presented in the list *under consideration* or at the stage *under consideration*. The numerical value `0` is assigned precisely to this *local* boundary.

*Zero in ToS is neither an object called “absence” nor a statement about the emptiness of the universe of distinctions. Zero is the boundary mark of the series of performed distinctions in a given context: a numerical value assigned to the state of affairs “in this list, at this stage, not a single distinction has been presented.” Absence is not introduced as an entity; it is relative to the context of counting.*

It is worth noting that this treatment of zero is *not* temporal. “Before the first act” does not mean “earlier in time” here: there is as yet no temporal order in which the act would be “later”; that order is itself something distinguished (physics). The “before” in the expression “before the first act” is *logical*, not chronological: it indicates a position in the order of *justification*, not in the flow of time. Zero is the boundary of the series in the sense of the order of justification: that relative to which the series of distinctions is determined as a series.

### Zero Is Not a Count of Distinctions

The boundary status of zero has a precise formal consequence, and it matters for the whole of Part II: *zero does not enter the count of distinctions*. (In the E/R/R analysis this is a role-boundary, not an object; § 1.8.7.) Let us analyze this carefully, because here the repository contains a subtlety that is easy to miss.

The file `Distinction.v` defines a predicate that assigns to a number the possibility of being realized by a list of distinctions:

```coq
Definition distinction_count (n : nat) : Prop :=
  exists Ds : list Distinction, length Ds = n.
```

This predicate is *technical*: it only asks whether there exists a list of distinctions of a given length. And for `n = 0` the answer is positive: the empty list has length zero:

```coq
Theorem zero_distinctions : distinction_count 0.
Proof. exists nil. reflexivity. Qed.
```

From the standpoint of `distinction_count`, zero is “realizable”: the empty list corresponds to it. But this is a statement *about the length of a list*, not about a count of *acts*. The empty list is a list in which *nothing has been performed*, not a list in which zero acts of distinction have been performed as something substantive. It has a length, zero; it contains no performed distinction.

To express a count of *acts*, a count in the ontological sense that Part II holds, a stricter predicate is needed. The file `PrimalityOfOne.v` introduces it:

```coq
Definition distinction_count_from_one (n : nat) : Prop :=
  exists Ds : list Distinction, length Ds = n /\ 1 <= n.
```

`distinction_count_from_one` adds to the technical length the condition $1 \le n$: the count of acts begins with one. And then the direct opposite of what was proved for `distinction_count` is proved about zero:

```coq
Theorem zero_not_a_count : ~ distinction_count_from_one 0.
Proof.
  intros [Ds [_ H]]. inversion H.
Qed.

Theorem first_count_is_one : distinction_count_from_one 1.
Proof.
  exists (cons (distinction_of True) nil).
  split. reflexivity. apply le_n.
Qed.
```

`zero_not_a_count` asserts: zero *is not* a count of distinctions. The proof is short (the condition $1 \le 0$ is false, and `inversion` closes this), but in substance it says something essential. The count of distinctions, taken as a count of *performed acts*, begins with one; zero does not fall into it. And `first_count
_is_one` shows where it begins: the first count is one, and a list of one distinction corresponds to it.

### What Two Predicates Are For

A question may arise: why does the repository keep *two* counting predicates, `distinction_count` and `distinction_count_from_one`, if they differ only in the fate of zero? Is this not redundancy? The answer is no, and it clarifies the arrangement of the whole construction.

The two predicates answer two different questions, and both questions are legitimate.

`distinction_count` answers a *technical* question: what is the length of a given list of distinctions? Length is a characteristic of a list as a data structure, and the empty list is a full-fledged structure of length zero. This predicate is needed wherever lists as such are concerned: lengths, indices, concatenations. It does *not* carry the ontological load of a count of acts; it works on the “layer of syntax” in the sense that Chapter I.6 introduced for the layers of formal work.

`distinction_count_from_one` answers an *ontological* question: how many acts of distinction have been *performed*? And here zero drops out, by the meaning of the question rather than by a technical oversight. “Zero acts” is a *boundary statement* about the absence of performance, not a positive count of what has been performed. “Three acts” is a positive characteristic of what is present, three performances; “zero acts” is not a characteristic of the same kind: it indicates a boundary, the state of affairs “nothing has been performed.” Therefore ToS sets the technical length of the empty list apart from the ontological count of the acts that are present. The predicate `distinction_count_from_one` draws exactly the line that positive ontology requires: the count of what has been performed begins with presence, that is, with one.

*The separation of the two predicates is the formal imprint of the separation of two layers. On the layer of syntax, zero is the legitimate length of the empty list; here `distinction_count` works. On the layer of ontology, zero is not a count of performed acts; here `distinction_count_from_one` works, and it begins with one.*

It is essential that this separation is not a conflict. The two predicates do not contradict each other; they speak about different things. The statements `distinction_count 0` (true: the length of the empty list is zero) and $\neg$ `distinction_count_from_one` `0` (true: zero is not a count of performed acts) are compatible without any tension: the first is about the length of a structure, the second about the number of acts. A conflict would arise only from a confusion of layers, if the technical length of the empty list were read as the ontological statement “zero acts of distinction have been performed.” ToS does not admit this confusion, and the two predicates are the formal means of not admitting it.

The cardinal path to the natural number series, which Chapter II.2 will unfold, will go through `distinction_count_from_one`: through the count of performed acts, which begins with one. The technical `distinction_count` will remain where it is appropriate: in work with lists as data structures. The natural number as the *imprint of performed distinctions* is built on the ontological predicate, and therefore it is built *from one*.

What has been said is conveniently summarized in a table. Zero is not denied in ToS; only *primacy* is refused to it; and this is seen most clearly if we separate the three modes in which zero is spoken of at all:

| Mode | What zero is | Where this works |
|---|---|---|
| Syntax of `nat` | the constructor `O`, the base point of the type | the standard type `nat` |
| List | the length of the empty list | the predicate `distinction_count` $0$ |
| Ontology of ToS | the boundary of the series of performed acts, the absence of anything presented | does not enter `distinction_count_from_one` |

The first two modes are legitimate and are not disputed: `O` is a correct constructor, and the empty list is a correct structure of length zero. ToS parts ways with the standard position only in the third mode: at the level of ontology, zero is not a count of performed acts and is therefore not primary.

### What Zero Inherits from One

It is worth closing the section with a clarification that ties zero back to one and forestalls a possible misunderstanding.

What has been said does not mean that zero in ToS is “worse” than the other numbers or less legitimate. Zero is fully legitimate: as a boundary mark it is necessary, and arithmetic cannot do without it. What has been said means something else: zero is *derived*. Its meaning is set *relative to* the series of performed distinctions: it is the boundary of *this* series. Without the series of distinctions that it bounds, zero would have no content: a boundary is a boundary of something.

Here a complete inversion relative to the standard picture described in § 1.1 becomes visible. There zero is primary and one is derived: one is `S O`, the successor of zero; it is defined *through* zero. In ToS the order of justification is the reverse: one is primary as the first act, and zero is derived as the boundary of the series that the acts form. Zero is defined *through* one (through the series whose beginning one is), not one through zero.

*In the standard picture, one is the successor of zero. In ToS, zero is the boundary of the series whose beginning is one. The order of justification is inverted: what is derived is what is defined through another, not what is smaller.*

This inversion of the order of justification (not of the order of magnitudes) is, in substance, the main thesis of the chapter. The next section (§ 1.4) analyzes how it coexists with the fact that in the type `nat` the constructor `O` does stand syntactically first; the section shows that the syntactic order and the order of justification are different things and that their divergence is not a contradiction.

## The Ontological Order versus the Syntactic: Compatibility with `nat`

### The Objection from the Arrangement of the Type `nat`

The previous sections carried out the inversion: one is primary, zero is derived. But this inversion runs into a visible obstacle, and the obstacle must be analyzed directly, without going around it.

ToS is formalized in Rocq, and the natural numbers in Rocq are the type `nat` of the standard library. Its definition is known (§ 1.1):

```coq
Inductive nat := O | S : nat -> nat.
```

Here `O`, a constructor without arguments, is named *first*. One is not a separate constructor: it is `S O`. Syntactically zero precedes one: to write one, we must apply `S` to `O`, that is, zero must already be at hand.

The objection is formulated as follows. *The chapter asserts the primacy of one. Yet it itself uses the type `nat`, in which zero is syntactically primary: it is the base constructor, and one is defined through it. Does the arrangement of `nat` not refute the central thesis of the chapter? And if ToS seriously holds the primacy of one, should it not redefine `nat`, making one the base constructor and deriving zero?*

The objection is substantial, and the answer to it is the subject of the present section. The answer consists of two parts. First: ToS does *not* redefine `nat`, and there are weighty reasons for this. Second: it does not redefine it *because* the syntactic order of constructors and the ontological order of justification are different things, and their divergence is exactly the distinction that the chapter draws, not a contradiction.

### Why ToS Does Not Redefine `nat`

Technically, redefining `nat` is possible. Nothing prevents us from declaring an inductive type of our own, say, with a base constructor “one” and an operator generating both the numbers beyond it and the boundary zero. ToS does not do this, and the refusal is *grounded*, not dictated by convenience.

**Compatibility.** The type `nat` of the standard library carries the whole arithmetic of Rocq: addition, multiplication, order, divisibility, the theory of prime numbers, the induction principle, thousands of proved lemmas. A type of its own would cut ToS off from this body of results: every theorem would have to be proved anew. This is not merely laborious; it would mean that the number systems of ToS exist *apart from* mathematics rather than *within* it. The task of ToS is the opposite: to show that its ontology lies at the foundation of *ordinary* mathematics, not to build an alternative mathematics.

**The isomorphism is unavoidable anyway.** Suppose ToS defined its own type; let us provisionally call it “the type with a base one.” Whatever it was, it would turn out to be *isomorphic* to `nat`: being discrete, with an initial element and a successor operator, it cannot fail to be isomorphic to the standard natural number series; this will be shown in Chapter II.3 using the example of the type `Level`. Isomorphic types carry one and the same mathematics. Hence a redefinition of `nat` would give no *new* mathematical content: it would give the same `nat` under another name, at the price of losing compatibility. Paying such a price for a renaming is unreasonable.

**The inversion requires no new type.** And most importantly: the inversion that the chapter carries out has *no need* of a new type. It is an inversion of the *ontological interpretation*, not of *syntax*. And an interpretation is not written into a type; it is laid over the type. One and the same `nat` can be read ontologically in different ways, and this is exactly what ToS does: it takes the standard type and reads it *from one*. How such a reading is possible without contradicting the arrangement of the type is analyzed in the next subsection.

### Two Orders

The resolution of the objection lies in distinguishing two orders that are easy to confuse, because both concern “what comes earlier and what later,” but they are earlier and later *in different senses*.

**The syntactic order of constructors.** In the inductive type `nat` the constructor `O` is named first, `S` second. This is the *syntactic* order: the order in which the constructors are listed in the definition of the type, and the order in which values of the type are *built*. To build `S O`, we must first have `O`. In this sense, the sense of building a term, zero precedes one.

**The ontological order of justification.** But there is another order as well, the order of *justification*: what receives its *meaning* through what. Chapter I.6, analyzing the layers of formal work, already drew this distinction for the general case; here it is applied to `nat`. In the order of justification, what is primary is what carries meaning independently, and what is derived is what receives meaning *through* another. And in this order, as § 1.2 and § 1.3 showed, one is primary: it is the imprint of the first act of distinction, carrying meaning by itself; zero, by contrast, is the boundary of the series of performed distinctions, receiving its meaning through this series.

*The syntactic order is the order of building terms: in it, `O` precedes `S O`. The ontological order is the order of the justification of meaning: in it, one precedes zero. These are two different orders on one and the same type, and they point in opposite directions.*

The opposition of directions is not a contradiction. There would be a contradiction if both orders were *one* order asserting different things about itself. But these are two different relations. “`O` is built before `S O`” and “one grounds zero” are compatible in the same way as “the foundation is laid before the roof” and “the roof is what the foundation is laid for”: the first concerns the order of construction, the second the order of purpose, and they legitimately diverge.

In the repository both orders are present explicitly, and their distinctness is fixed formally. The file `AsymmetricDistinction.v` defines the order of distinction, the order in which the marked side comes before the unmarked:

```coq
Definition distinction_order : nat * nat := (1, 0).

Theorem one_precedes_zero_in_distinction :
  fst distinction_order = 1 /\ snd distinction_order = 0.
Proof. split; reflexivity. Qed.
```

`distinction_order` is the pair $(1, 0)$: one in the first place, zero in the second. This is the ontological order, the order of justification, written down as an object. It coexists with the standard numerical order $0 < 1$, in which zero is less than one and in this sense “earlier.”

The file `PrimalityOfOne.v` fixes the same duality, but in another form, and this form must be stated precisely, so as not to ascribe to the code more than there is in it. In `PrimalityOfOne.v` we read:

```coq
Definition tos_first   := 1%nat.
Definition tos_absence := 0%nat.

Theorem tos_ordering : (tos_absence < tos_first)%nat.
Proof. unfold tos_absence, tos_first. lia. Qed.

Theorem orderings_dual :
  (tos_absence < tos_first)%nat /\ (0 < 1)%nat.
Proof. unfold tos_absence, tos_first. split; lia. Qed.
```

Let us read this carefully. `tos_first` is `1`, `tos_absence` is `0`; the theorem `tos_ordering` asserts the inequality `tos_absence` `<` `tos_first`, that is, since `tos_absence` is `0` and `tos_first` is `1`, in substance $0 < 1$. The theorem `orderings_dual` in this file, strictly speaking, does not fix two *opposite pairs*: after unfolding the definitions, both of its conjuncts reduce to one and the same inequality $0 < 1$. Therefore the *formal* record of the duality of the two orders as the pair $(1,0)$ against the pair $(0,1)$ is contained precisely in `AsymmetricDistinction.v`, in `distinction_order` and `one_precedes_zero_in_distinction`, while `PrimalityOfOne.v` registers the same idea in a weaker form: the numerical order $0 < 1$ is in place, and the ontological name of the beginning (`tos_first`) is assigned to one, not to zero.[^5]

In substance, the conclusion does not change because of this. *Two* orders are present in the system: the numerical order by magnitude, in which $0 < 1$, and the ontological order of justification, in which one is primary (the pair $(1,0)$ in `distinction_order`). ToS does not cancel the numerical order $0 < 1$: by magnitude zero is less than one, and arithmetic makes use of this. ToS only adds to it a *second* order, that of justification, in which one is primary, and insists that these two orders must not be confused.

### A Semantic Shift, Not a Redefinition

Now the objection from § 1.4.1 receives a complete answer.

ToS uses the standard type `nat`. The constructor `O` in it is syntactically primary, and ToS does not change this. But ToS sets its own *ontological reading* of the type: `O` is interpreted as a boundary mark (§ 1.3), not as a primary entity; `S O`, as the imprint of the first performed act, primary in the order of justification; `S n`, as “after $n$ performed acts, one more has been performed.” The type is taken as standard; the *meaning* with which it is endowed is set by ToS.

This is precisely the *semantic shift*: a redefinition of the interpretation of the type, not of the type itself. The file `PrimalityOfOne.v` carries out this shift through definitions and theorems that fix the *reading* of the standard `nat`, not through a new inductive type: `tos_first`, marking one as the first recognizable magnitude; `tos_absence`, reading zero as a boundary; `tos_ordering`, setting the order of justification. The syntax of Rocq remains untouched; the semantic layer changes.

*ToS reinterprets `nat`; it does not redefine it. The type remains standard; the whole arithmetic of Rocq is preserved. What changes is the ontological reading: `O` is the boundary, `S O` is the first act, and the order of justification proceeds from one. The syntactic order and the order of justification are distinguished, and their divergence is the content of the inversion, not an obstacle to it.*

This move, work on a standard syntax with a nonstandard semantics, is neither a trick nor a particular contrivance of the present chapter. It will recur in Part II twice more. Chapter II.3 will take the type `Level`, syntactically identical to `nat`, and endow it with a *different* interpretation, a hierarchical one. Chapter II.5, summing up, will formulate the general principle: one and the same formal object admits several ontological readings, and ToS makes consistent use of this.[^6] The present section has given the first and simplest case of this device; and it has also disposed of the objection with which it began: the arrangement of `nat` does not refute the primacy of one, because it speaks of a different order.

## The Historical Tradition: One as a Principle

### What History Is Here For

The inversion carried out in § 1.2–1.4 may at first sight seem an innovation of ToS, a technical peculiarity of one formal system. The present section shows that this is not so. ToS arrives at the primacy of one independently, from its own metaphysics ($A = \exists$) and its own ontology of the act of distinction, without relying on any preceding tradition. But European thought about number arrived at the same primacy independently throughout its whole history, long before any formalization: at the intuition that one is the beginning, while zero is derived or absent altogether. The present section *compares* these independent approaches.

Let us stress from the very beginning, so that there is no misunderstanding about the genre of the section: ToS does *not inherit* other doctrines of number; it neither borrows nor continues other lines of thought. Its path is independent and is derived in § 1.2–1.4 from the arrangement of the act of distinction. The historical part here is a *comparison*, not a genealogy and not an appeal to predecessors: a juxtaposition of the independently built position of ToS with the positions at which earlier thought arrived by its own paths.

The historical part here is neither an ornament nor an argument from authority. It does a precise job. If the primacy of one were an accidental feature of ToS, it would be natural to expect earlier thought about number to be indifferent to it. But, as shown below, in different traditions of thought about number, remote from one another in time and context, the motif of the primacy of one or of unity regularly appears, whereas the primacy of zero is historically *late* and came to European mathematics with difficulty. This is not a proof of the position of ToS but a *converging parallel*: the repeated appearance of one motif in independent traditions raises the plausibility that the inversion of ToS answers to something in the subject matter itself, and not only in the chosen formalism.[^7]

### The Pythagorean Monad

The earliest and most distinct assertion of the primacy of one is the Pythagorean one. For the Pythagoreans, one, the *Monad* (*monas*), was the *beginning* of number rather than one of the numbers: that from which the numbers are generated and without which they do not exist.[^8] The Monad is not the “first number” in the series; it is the *principle* of the series, its source.

For the present chapter two features of this doctrine are essential.

The first: the Pythagoreans had *no zero as a number at all*. And this is a consequence of their ontology, not a gap in their arithmetic. Number for them is *something*: a definite plurality, a counted multiplicity. “Nothing” cannot be a number, for the number would have nothing to count. The absence of zero among the Pythagoreans is a direct expression of the position that ToS formulates through positive ontology: what is present is counted, and absence is not a special object of counting.

The second: the Pythagorean Monad is *generative*. The numbers do not lie about as a ready-made set; they *proceed* from one. Two is the first departure from unity, and from there the series unfolds as generation. This generative role of one is close to what ToS will express in Chapters II.2–II.5: the natural number series is *built* by repeating the primary, not given; and the primary is one.

ToS does not share the Pythagorean metaphysics of number as a whole, the doctrine of numbers as substances of which the world is composed. But in the structural core (one as the beginning, zero as a non-number, the series as generation) the independently built position of ToS and the Pythagorean intuition coincide. ToS came to this core by its own path, the Pythagoreans by theirs; the result is the same for both.

### The Neoplatonic One: Plotinus and Proclus

Neoplatonism carried the intuition of the primacy of unity to its limit. In Plotinus, the *One* (*to hen*) stands above Being itself: it is the source from which Being proceeds, and therefore it is *prior* to all determinacy, all multiplicity, every “is.”[^9] All that is, is *after* the One and *through* it.

This metaphysics does not admit a direct transfer into ToS, and it is important to say where the boundary runs. ToS does not place one “above being”: its first principle is $A = \exists$, and one in ToS is the number of the act of distinction, that is, something *within* the domain of what exists, not above it. The Plotinian One and the one of ToS are not the same thing.

But in one structural feature the comparison reveals an exact coincidence, and it is essential. Neoplatonism thinks of generation as a *descent from unity to multiplicity*: first the one, then, through a series of stages, manifoldness. Multiplicity is *derived* from unity, not the other way round. This is exactly the order of justification of ToS: one is primary, and the manifold (the number series) unfolds from it by repetition. Proclus, in his commentary on the first book of Euclid, applies this scheme directly to mathematics: he arranges mathematical objects along the stages of descent from indivisible unity to divisible multiplicity. In Proclus, one stands on the side of the indivisible beginning; the series, on the side of what is produced.

The Neoplatonic tradition thus adds to the Pythagorean intuition a *sharpening* of it rather than a new assertion: what is primary is the one *as the source* of the rest, not merely the one among the rest. The position of ToS coincides with this sharpening as well, but in a weakened, non-metaphysical form: for ToS, one is the source of the *number series*, not the source of being. ToS arrived at this formulation independently, deriving it from the arrangement of the act of distinction, not from the Neoplatonic scheme; the coincidence with the Neoplatonists is *stated* here, not used as a support.

### Frege: Number as a Property of a Concept

What ToS shares with the Pythagoreans and the Neoplatonists is an intuition; with Frege, something more precise: a way of *defining* number under which one and zero receive their places by their nature, not by convention.

Frege defined number as a *property of a concept*[^10]: a number is a characteristic of a concept, not of things; it indicates to how many objects the concept applies. To the concept “moon of the Earth” belongs the number one; to the concept “planet of the solar system,” another number; and so on. Number is ascribed to a *concept*, through what falls under the concept.

For the present chapter what matters is how precisely one and zero arise under such a definition, and in what order.

In Frege, one corresponds to a concept under which *exactly one* object falls. The simplest case is the concept “object identical with $a$”: one object falls under it, $a$ itself, and the number of this concept is one. One is thus connected with the *presence of a definite object*: with the fact that something is, and is this.

In Frege, zero corresponds to a concept under which *nothing* falls. And (here is the point essential for ToS) Frege specifies such a concept quite definitely, not as “emptiness in general”: the concept “object not identical with itself,” that is, the concept $x \neq x$. No object falls under it, because every object is identical with itself ($L1$); and the number of this concept is zero.

Frege’s definition of zero agrees with ToS more precisely than it might seem. Zero arises here as the number of a *logically impossible* concept, a concept that directly contradicts the Law of Identity, not as a primary entity. Zero is *derived*: to obtain it, we must already have the law $L1$ at our disposal and build a concept that violates this law. One, by contrast, rests on the simple presence of an object. In Frege, as in ToS, one stands closer to presence and zero farther from it; and zero is defined through a logical construction rather than given directly.[^11]

### Cantor: One as the Principle of Assembly

Georg Cantor is the creator of set theory, of that very set-theoretic ontology relative to which ToS declared its divergence in § 1.1.[^12] All the more telling is it that in Cantor, too, one retains a special status: the status of a *principle*, not of an ordinary element.

In Cantor’s understanding of a set, one is that through which the manifold is gathered into *one*. To count a set is to put its elements into one-to-one correspondence with units; cardinality is the result of such a correlation. One works here as the *measure of assembly*: a set receives a number insofar as its elements are matched with units and then gathered under *one* number.

ToS parts ways with Cantor on the main point, the question of *completed infinity*, of the set as a ready object; this divergence is analyzed further on in Part II and unfolded in Chapter II.5. But on the role of one there is no divergence. In Cantor, too, one is more than the least of the numbers: it is that by which counting *is carried on* and by which the manifold is reduced to one. Even in the set-theoretic frame, where zero is syntactically primary (as $\varnothing$), one keeps the function of a principle. This shows that the primacy of one *as a principle* does not contradict even the ontology with which ToS disputes on other points: the dispute concerns infinity and the set, not the role of one.

### Spencer-Brown: The First Distinction

The last testimony is the closest to ToS, because it concerns *distinction*, from which ToS derives number, rather than number directly.

George Spencer-Brown in *Laws of Form*[^13] begins the construction of the whole of logic with a single injunction: *draw a distinction*. The first act, the drawing of a distinction, presupposes nothing before itself; it is the beginning from which everything else unfolds. The whole volume is built as the unfolding of the consequences of *one* primary gesture.

The resemblance to ToS is especially distinct here: a coincidence of the very setting of the problem, not an analogy. This does not mean that one derives from the other: Chapter I.2 already noted Spencer-Brown among the converging testimonies about the structure of the act of distinction, precisely as an independent testimony, not as a source. For the present chapter, what is essential is the numerical consequence of his initial gesture. The first distinction is *one*. Not zero distinctions (in Spencer-Brown nothing begins with zero: an “undrawn distinction” is the absence of a beginning, not a beginning), and not many at once, but one. For him, as in ToS, counting begins with the first performed gesture, not with emptiness, and this first gesture is one.

It would be wrong to compare ToS with *Laws of Form* as with a predecessor whose work ToS continues: ToS continues nobody’s line. The resemblance here is of another kind. Spencer-Brown came by his own path to the view that construction begins with one primary distinction; ToS came by its own path to the record `Distinction` and to one as the numerical imprint of the first act, which Chapters II.2–II.5 unfold into the full construction of the natural number series. The two edifices are independent; the fact that they converge at the starting point is the content of the comparison.

### What This Convergence Yields

The six testimonies (the Pythagorean Monad, the Neoplatonic One, Proclus on mathematics, Frege on the number of a concept, Cantor on the unit of assembly, Spencer-Brown on the first distinction) belong to different epochs and to different philosophical frameworks, in many respects incompatible with one another. A Pythagorean and Frege would agree on almost nothing; Cantor and ToS part ways on the very concept of the infinite. All the weightier is that on which they *converge*: one is primary *as a principle* (as the beginning, the source, the measure, the first act), while zero, where it exists at all, is *late and derived*.

*The primacy of one, at which ToS arrives independently from the arrangement of the act of distinction, turns out to be a position with which a stable intuition of European thought about number coincides, from the Pythagoreans to Spencer-Brown, rather than an innovation. The primacy of zero is a historically late position, which became entrenched together with the set-theoretic foundation. The coincidence of the independently built position of ToS with a long-standing and repeatedly attested intuition is an indication that the inversion answers to something in the subject matter itself.*

Here an understandable misunderstanding must be forestalled. What has been said is not the argument “true because ancient.” The historical prevalence of an intuition proves nothing by itself: the argument for the primacy of one is given in § 1.2–1.4 and rests on the arrangement of the act of distinction, not on anyone’s authority. The comparison of testimonies does a different, more modest job: it shows that the inversion of ToS is *not arbitrary*, that the independently built position has coincided with what those who thought about number noticed repeatedly and separately, long before any formalization. The justification of the inversion is given by § 1.2–1.4; the comparison testifies that the justified position answers to a stable feature of the subject matter itself, not to a peculiarity of one formalism.

One more thing. The fact that the primacy of zero is historically late does not make it an error. The introduction of zero as a full-fledged number is one of the major achievements of mathematics, and ToS does not dispute it: zero exists in ToS, it is necessary, and it has been assigned a precise place (§ 1.3). What ToS disputes is the *primacy* of zero, not its *presence*; and it disputes it by pointing to the order of justification, not by referring to the antiquity of the opposite intuition. History only testifies that this order was always discernible.

## Counting as Presence, Not as Accumulation from Zero

### Two Pictures of Counting

Sections § 1.2–1.5 established the inversion: one is primary, zero is derived. Until now this concerned *numbers*, what stands at the beginning of the number series. The present section shows that the inversion also concerns *counting*, the very action by which numbers are applied. If what is primary changes, what counting is changes too.

Let us distinguish two pictures of counting: the one that implicitly accompanies the primacy of zero, and the one that follows from the primacy of one.

**Counting as accumulation from zero.** If zero is primary, it is natural to think of counting as a *movement from emptiness*. We start with zero, with “nothing has been counted,” and add one unit at a time: zero, then one, then two. Each step *adds* a unit to what has already been accumulated. Counting in this picture is *accumulation*: successive addition setting out from an empty beginning. The number at which counting has ended is the *outcome of accumulation*, the sum of the units added.

This picture is consistent with the set-theoretic construction (§ 1.1) and with the syntactic order of `nat` (§ 1.4): we start with `O`, apply `S`, accumulate. It is familiar; the school count “zero, one, two, three” entrenches precisely this picture.

**Counting as the recording of presence.** If one is primary, the picture is different. To count is to *record the number of distinctions already performed*, not to accumulate from emptiness. To count something is to establish how many acts of distinction *have already been carried out*: “this here,” “this here,” “this here.” Counting here does not add units to an accumulated total; it *registers what is present*, marks the measure of what is.

In this picture counting begins with the first “this here,” with one (§ 1.2), not with zero. Each next step *marks one more performed distinction* rather than “adding to the sum.” The number at which counting has ended is the *measure of what is present*, how many distinctions are at hand, not the outcome of accumulation.

### What Changes in Intuition

The difference between the two pictures is worth making tangible on a simple example.

Suppose we need to count the fingers on a hand. In the picture of accumulation, the count looks like this: “we start with zero; here is a finger: one; here is another: two; …; five.” Zero here is the starting position through which counting *passes* before reaching the first finger. In the picture of presence, the count looks different: “here is a finger: one distinction; here is another: two distinctions; …; five distinctions.” Zero here is not a starting position and takes no part in the count at all: counting *begins* with the first “here is a finger,” and five is five performed distinctions “this finger here,” not the result of adding to emptiness five times.

Where is zero in the picture of presence? It appears in only one case: when *there is no occasion for counting*. “There are zero fingers on the hand” means “not a single *finger here* was found that counting could mark,” not “counting passed through zero and stopped.” Zero is the *absence of an occasion*: exactly the boundary of the series, as established in § 1.3, not a point through which counting passes on its way to the numbers.

*In the picture of accumulation, counting passes through zero on the way from emptiness to number. In the picture of presence, counting begins with the first distinction; zero is the absence of an occasion to count, not a point that counting passes through. To count is to record the measure of what is present, not to accumulate from emptiness.*

Let us stress that what is at issue is the *intuition* that accompanies the technique of calculation, not the technique itself. Technically both pictures give the same numbers: five fingers are five fingers whatever the way of counting them. What changes is the *understanding* of what the result means, not the result. In the picture of accumulation, “five” answers the question “how much has been added to zero?” In the picture of presence, “five” answers the question “how many distinctions are at hand?” The numerical value is one and the same; the meaning of the question differs.

### Why the Picture of Presence Is More Precise for ToS

The picture of presence is more than another way of speaking about counting: it corresponds more precisely to the ontology of ToS, and it is worth saying in what exactly.

**Agreement with positive ontology.** The picture of accumulation implicitly gives zero a substantive role: zero is the *start*, the initial state through which counting passes. This endows “emptiness” with a positive function, the function of a beginning. But positive ontology (§ 1.2.3) rules out exactly this: absence is not a special object capable of being a beginning. The picture of presence is consistent with positive ontology: the beginning of counting is the first *presence*, the first performed distinction, not emptiness. What is present is counted; emptiness is only the name of the situation in which there is nothing to count, not that *from which* counting proceeds.

**Agreement with processuality.** Chapter I.7 established that the ontology of ToS is processual: what is primary is the act, not a ready object. Counting as the recording of presence is processual in the same sense: it is the marking of *performed acts* of distinction. Counting as accumulation tends toward a different, substantial picture: it presents number as an *accumulated magnitude*, as if units were things piled up in one place. The picture of presence is free of this: it speaks of the number of *what has been performed*, not of an accumulated substance.

**Agreement with the counting predicate.** Finally, the picture of presence is a direct reading of the predicate `distinction_count_from_one` (§ 1.3.3). This predicate says: the number $n$ *is* in the system insofar as there exists a list of $n$ performed distinctions. It registers the *presence* of performed acts and their number; it does not describe an accumulation from zero. “To count” in the sense of this predicate is exactly “to establish for which $n$ a list of $n$ distinctions is at hand.” The picture of presence is the verbal expression of what the predicate `distinction_count_from_one` expresses formally.

### The Transition to the Cardinal Path

The present section completes the first half of the chapter, the half that established the primacy of one and the derived character of zero and analyzed the consequences of the inversion for the beginning of the number series and for counting. What has been obtained can be summed up in one proposition: *to count in ToS is to record the number of performed acts of distinction, and this counting begins with one*.

This proposition requires unfolding. To say “number is the measure of performed distinctions” is not enough: we must *build* the natural number series from this measure, showing how exactly performed distinctions give number, how the whole series arises from the possibility of repeating the act, and how this series is connected with the induction principle. Such a construction is the cardinal path to the natural numbers, and it makes up the content of the next chapter.

Chapter II.2 will take the intuition of the present section, counting as the recording of presence, and turn it into a construction. The list of performed distinctions, its length, the ontological counting predicate, the lemma on the realizability of every number, the origin of induction in the repeatability of the act: all of this will unfold the first of the four paths by which ToS arrives at the natural number series. The picture of presence, described here in substance, will receive its full formal apparatus there.

Before passing to this, the chapter still has to consider two more subjects without which the primacy of one is not fully understood. The first is the divisibility of one: can one be divided, and what does it mean that something is divided (§ 1.7). The second is the notation $0.999… = 1$, on which the inversion and the operational nature of divisibility are tested on a concrete and contested case: without an indication of the mode, this notation hides a change of type, from a process of approximations to its limit (§ 1.8). The chapter now turns to them.

## Divisibility as an Act

### What a Chapter on One Needs the Question of Divisibility For

The first half of the chapter established the primacy of one and analyzed the consequences of the inversion for the beginning of the number series and for counting. Before passing to the construction of the series (Chapter II.2), one question about one itself remains to be considered: the question of its *divisibility*.

The question is not an idle one. If one is primary (the first act of distinction, the imprint of what has been performed), it is natural to ask: is it *divisible*? Can one be divided, and if so, does this not undermine its primacy: what kind of “first” is it if it splits into parts? And if it is indivisible, then in what sense, and does an “indivisible one” not bring back the substantial picture of the atom that ToS rejects?

The answer of ToS to this question is an *application of what has already been established*, not a new doctrine. Chapter I.7 established operational divisibility. The present section applies it to one. Therefore it neither introduces the position anew nor repeats its justification: it shows that the divisibility of one is a particular case of operational divisibility, and traces the consequences.

### Divisibility Is a Performed Distinction

We must begin with what divisibility *is* in ToS, because here ToS departs from familiar usage, and the departure is essential.

In the familiar picture, divisibility is a *property of an object*. An object is either divisible (it can be divided into parts) or indivisible (it cannot), and this property belongs to it *in itself*, without relation to anything. Asking “is the object divisible?” in this picture, we ask about its inner nature.

ToS answers differently. Divisibility is a *performed distinction*, not a property belonging to an object in itself. An object is divisible *insofar as* an act of distinction has been performed within it, decomposing it into sides. If such an act has been performed (if relative to $X$ a distinction has been drawn yielding, say, $X = \langle A, B\rangle$), then $X$ is divisible, and divisible *into* $A$ and $B$. If such an act has *not* been performed, then $X$ is not decomposed into anything: it is *atomic*.

The shift here is the same one that runs through the whole chapter: from substance to act. “Divisible” in ToS does not describe a hidden arrangement of the object awaiting discovery. “Divisible” means: *the act of decomposition has already been performed*. Divisibility is an *event*, a drawn distinction, not a predisposition. And like every distinction in ToS, it is performed *relative to* some level of consideration at which it is drawn (Chapter I.4, the hierarchy of levels $P1$).

This is exactly operational divisibility: atomicity is relative; indivisibility indicates the level at which the object is not decomposed, not an absolute property of the object. ToS does not *postulate* this view anew for one: it *recognizes* in the divisibility of one a case of operational divisibility.

### The Atom as a State, Not a Nature

Operational divisibility has a direct consequence for the concept of the atom, and it is worth spelling it out separately, because it changes the meaning of the word.

If divisibility is a performed distinction, then an *atom*, an object within which no distinction has been performed, is an atom *by state*, not *by nature*. The atomicity of an object is a characteristic of the current state of the system of distinctions, not of the object’s hidden arrangement: relative to this state, no decomposition has *yet* been carried out within the object. An atom is “not decomposed here and now,” not “indecomposable in principle.”

It follows that atomicity is *revisable*. An object atomic relative to the present state of distinctions ceases to be an atom as soon as a distinction is performed within it. What changes is the state of the system of distinctions, not the object: what was not decomposed turns out to be decomposed, and the former atom reveals sides.

**Example: the quark.** An illustrative case is the quark. In the present state of physical knowledge, the quark appears as atomic: no structure has been distinguished within it; there is no performed act that would decompose the quark into constituents. But ToS does not assert that the quark is indivisible *by nature*, without relation to any state of knowledge. ToS asserts only that relative to the *present* state of distinctions the quark is atomic. If a future distinction decomposes the quark into sides, the quark will cease to be an atom, and this will be neither an error of the earlier judgment nor a transformation of the quark itself. The earlier judgment was correct: *at its level of distinctions* the quark is atomic. The new judgment is correct too: at the *new* level it is a system. Atomicity was and remains a characteristic of a state, not of a nature.[^14]

### The Dispute between Atomism and Continuity

Operational divisibility allows a new look at an old dispute, the dispute between atomism and continuity: does what is consist, in the final analysis, of indivisible atoms, or does it admit division without limit? ToS does not *decide* this dispute in favor of one of the sides; it shows that the dispute is *imprecisely posed*.

Both classical positions, the atomist and the continuist, are *substantial*: each ascribes to divisibility the status of a property belonging to what is, in itself. The atomist asserts: what is, in itself, has the property of being decomposable only down to a limit. The continuist asserts: what is, in itself, has the property of being divisible without limit. They dispute *which* property belongs to what is, but they agree that divisibility *is* such an inherent property.

ToS parts ways with both on this common presupposition. Divisibility is a performed distinction (§ 1.7.2), not an inherent property. And if so, the question “is what is divisible in the final analysis?” loses the meaning that the dispute put into it. At each given level of consideration there is what has *already* been decomposed (the current systems) and what has *not yet* been decomposed (the current atoms). “In the final analysis,” that is, without relation to any level, divisibility is not defined at all, because divisibility is *by definition* relative to the level at which a distinction has or has not been drawn.

*The dispute between atomism and continuity presupposes that divisibility is a property of what is in itself, and its parties differ only on which property it is. ToS rejects the presupposition itself: divisibility is a performed distinction, relative to a level. The question “is what is divisible in the final analysis” receives no answer because it is posed outside the relativity without which divisibility is not defined, not because it is difficult.*

It is worth being precise about what is asserted here. ToS does not declare the dispute meaningless and does not deny its participants a subject matter. ToS redescribes the subject matter: what the atomist and the continuist took to be a description of *what is* is in fact a description of the *process of distinguishing* what is. The atomist rightly notes that at every level there is something undecomposed; the continuist rightly notes that everything undecomposed can be decomposed at a lower level. Both correct halves belong to the operational structure of distinction, not to what-is-in-itself, and, once referred to it, they cease to contradict each other.

### Levels of Consideration of One

Now we can return to the question with which the section began: is *one* divisible? But first the question must be made more precise; otherwise the answer will come out imprecise.

One in ToS is a *number*: the imprint of the first act, the measure of what has been performed (§ 1.2). A number, however, is not what is divided. By § 1.7.2, what is divided is that *within which* a distinction has been performed: some *system*. Therefore the strictly posed question is not “is one divisible” but this: *is the system that one fixes divisible*? One as a number is not divisible at any level; what is divisible or indivisible is *what one marks at a given level*. And the answer is operational: it depends on which system one fixes at the level under consideration.

The question “is one divisible in general, without relation to a level” can now be answered definitely, and the answer is *no*. The number “one” is not divisible at any level or without relation to any level: divisibility is a performed distinction *within a system* (§ 1.7.2), and a number is a mark, not a system. Within a mark there is nothing to decompose. This exhausts the answer to the question as literally posed. Another question, however, is meaningful, about what the number marks rather than about the number: which system one fixes at *each* of the levels where it occurs in ToS, and whether this system is divisible. There are five such levels; they are worth listing, since this is at the same time a map of how one will behave further on in the volume.

**The level of the act (the present chapter).** Here one is the number of the first act of distinction, and what it fixes is the *act* itself, taken as a whole. Within this act-as-a-whole no distinction has been performed: the act is taken as one thing performed. The system that one marks here (the act itself) is *not decomposed*: at this level it is atomic. It is indivisible because no decomposing act has been carried out here, not because such is its nature.

**The level of the list (Chapter II.2).** At the level of the cardinal path, one fixes a *list of one distinction*. This list as a system is likewise not decomposed: within its single element no distinction has been drawn. It is essential to separate two operations that are easily confused. To *decompose* a list of one element is to draw a distinction *within* it; there is no such distinction here, and in this sense the system is not divisible. To *lengthen* a list is to attach one more distinction to it, passing to a list of two; this is *not* a division of one, and not a division at all, but a passage to a *different* number, to two. Division seeks structure *within* what there is; lengthening places *one more* alongside. One is not divided by the fact that the list can be lengthened: lengthening the list is the path to two (Chapter II.2), not a decomposition of one.

**The level of the interval (Part III).** When the rational numbers appear in Part III, one will fix the *interval* $[0, 1]$. Here the system marked by one *is* divisible: relative to the interval, distinctions are drawn that decompose it into rational parts, a half, a third, and so on. What is divisible here is the *interval*, a system, not the number “one”: the number still only marks this system as a whole. This does not contradict atomicity at the level of the act: the act marked by one there and the interval marked by one here are different systems at different levels, and the fact that the first is not decomposed while the second is violates no law.

**The level of the process (Part IV).** In Part IV, one will fix a *process* of convergence, structured from within without limit. This system, the process, is divisible without limit: within it an ever finer structure of approximations is distinguished. And again what is divisible is the *process*, not the number: one marks the process as a whole, while it is the inner arrangement of the process that yields to decomposition.

**The level of an element of a structure (Parts III and beyond).** It is worth naming separately the level at which the symbol $1$ appears as an *element of an algebraic structure*: the neutral element of multiplication in a ring or a field. At this level expressions of the form $1/2$, $1/3$ are entirely legitimate: in the field $ℚ$ or $ℝ$, one takes part in the operation of division, and the expressions “half of one” and “a third of one” have a precise meaning. This does not contradict what has been said. What is divided here is $1$ *in the role* of an element of a structure, of a measure, of a boundary, not the *primary one-as-count*, the numerical imprint of one act. One act of distinction does not become two because a new distinction has later been drawn within the system it marks; but $1$ as an element of a field is divided, because a field is a structure with a given operation of division. The objection “how can one be indivisible if there is $1/2$” is answered precisely by this distinction: $1/2$ is the division of an *element of a field*, not the division of the one-as-count.

The five levels do not contradict one another, and it is now clear why there is no contradiction even in appearance. It would arise if *one and the same system* were declared both divisible and indivisible; that would violate $L2$. But the systems are *different*: the act, the list, the interval, the process, the element of a structure. At each level one fixes its own system; the number “one” as the counting imprint of the act is one and the same throughout, while the systems it marks are different, and each is divisible or not according to its own state of distinctions.

Let us summarize the five levels in a table; it is at the same time a map of how one will behave in the later parts of the volume:

| Level | What one marks | Is what is marked divisible |
|---|---|---|
| act (this chapter) | one act of distinction | no: the act is taken as one performed whole |
| list (Ch. II.2) | a list of one distinction | not divisible as a list, but can be lengthened |
| interval (Part III) | the interval $[0,1]$ | yes: the interval is divisible into rational parts |
| process (Part IV) | a convergent process of approximations | yes: the inner structure of the process is distinguishable by stages |
| element of a structure (Parts III and beyond) | $1$ as the neutral element of a ring / field | yes: $1/2$, $1/3$ are legitimate operations of division |

In all five rows the primary one-as-count, the numerical imprint of one act, remains indivisible; what is divided is *what is marked*, a system or a structure, according to its level. The table makes it plain that “one is indivisible” and “there is $1/2$” do not contradict each other: they belong to different rows. The consistency is secured by the same $P1$, the hierarchy of levels, on which operational divisibility stands: “divisible / indivisible” always refers to a *system at a concrete level*, not to the number and not to all levels at once. The transitions between levels are the subject of later parts of the volume; for the present chapter it is essential only that the levels are distinguished and that the number “one,” remaining *one*, fixes its own system at each level.

*What is divisible or indivisible is the system that one fixes at a given level, not the primary one-as-count. One as the counting imprint of one act is not divided. The system (the act, the list, the interval, the process, the element of a structure) is divisible or not according to its state of distinctions: the act and the list are not decomposed, the interval and the process are decomposable, and $1$ as an element of a field takes part in division. This is one counting number marking different systems at different levels, not five different ones and not a contradiction, in accordance with operational divisibility, by which atomicity is always relative to a level.*

This exhausts the question of the divisibility of one, and the primacy of one has held. The divisibility of the interval $[0,1]$, of a process of convergence, or of $1$ as an element of a field does not undermine the primacy of the one-as-count: primacy was asserted of one as the numerical imprint of the first act (§ 1.2), and it is precisely this one-as-count that is not divided. What is divisible are the systems and structures that one marks at other levels; but their divisibility is their property at their levels and does not touch the first act.

One last thing remains. Operational divisibility and the relativity of levels, analyzed here, give ToS an instrument for a case that is considered simple in a naive exposition but in fact hides an unspoken change of mode: the notation $0.999… = 1$. With it the chapter concludes.

## Process and Atom: On the Notation $0.999…$

### What the Chapter Needs This Case For

The chapter concludes with the analysis of one concrete case: the notation $0.999…$ and the familiar statement $0.999… = 1$. The case has been chosen not for the sake of polemic with standard mathematics but because it *tests* everything the chapter has established: the primacy of one, its atomicity at the level of the act, operational divisibility, the relativity of levels of consideration. If these propositions are correct, they must give a clear answer to a contested case, and they do.

Let us state the genre at once. What is proved below is not that standard mathematics is *mistaken*: in its own mode, where the notation $0.999…$ by definition means a real number, the equality $0.999… = 1$ is correct. What is proved is something else and more precise: that behind the familiar equals sign, *when the mode is not indicated*, an unspoken change of type is hidden, from a process of approximations to its limit, and that ToS, by making this change explicit, obtains a different, more finely distinguished picture. The case $0.999…$ interests ToS as an example of what *happens* when the ontological nature of a notation remains unspoken.

### What the Notation $0.999…$ Is

Before asking what $0.999…$ *equals*, we must ask what this notation *is*. The question is usually skipped, and wrongly so, because everything turns on it.

$0.999…$ is a *notation*: a string of symbols in the positional decimal system, in which the digit $9$ stands after the decimal comma, repeated without end. What does this string mean, taken literally? It means an instruction: take $0.9$; then $0.99$; then $0.999$; and continue. The literal content of the notation $0.999…$ is a *scheme for generating approximations*, the sequence
$$
0.9,\quad 0.99,\quad 0.999,\quad 0.9999,\quad …
$$
in which each next term is obtained from the previous one by one more act of refinement, “closer than before.”

In the language of ToS such a scheme is a *process*: an unfolding sequence of acts of distinction, each step of which is a new distinction. This is a legitimate object of ToS, and it is consistent with the principle $P4$: the process can be *continued* without end, but nowhere does a completed infinity arise; there is an infinite possibility of taking one more step, not an attained infinite object. The ellipsis in the notation $0.999…$ means exactly this: “continue,” not “here is a completed infinite result.”

*The notation $0.999…$, taken literally, means a process: a scheme for generating the approximations $0.9,\ 0.99,\ 0.999,\ …$ The ellipsis is a sign of continuability, not a sign of completed infinity. By itself this notation introduces no object other than the process.*

### Where the “Number” Appears in the Notation

If $0.999…$ means a process, where does the familiar statement come from that $0.999…$ *is a number*, and the number $1$ at that?

It comes from an *additional act*. Standard analysis does not leave $0.999…$ a process: it *reassigns* this notation, declaring that $0.999…$ denotes the *limit* of the scheme of approximations rather than the scheme itself, that is, a single object to which the approximations converge. And then it proves that this limit equals $1$.

It is essential to see what has happened here. The string $0.999…$ itself “contained” no limit: the limit is *put into* it by a definition. The transition from “$0.999…$ is a scheme of approximations” to “$0.999…$ is the limit of the scheme” is not read off from the notation; it is *performed* as an act. And this act, as a rule, goes unspoken: in the familiar exposition, $0.999… = 1$ is presented as a discovered identity, not as the result of a decision to treat the notation in a certain way.

That this is precisely an act, not something self-evident, can be seen from the fact that in standard mathematics the real number *itself* is constructed in different ways, and in all the constructions $0.999…$ as a sequence and $1$ as a number are *different* objects:

- in the construction through fundamental (Cauchy) sequences, a real number is an equivalence class of convergent sequences of rationals; $0.999…$ is one of the sequences, $1$ is a class;
- in the construction through (Dedekind) cuts, a real number is a cut in the set of rationals; $0.999…$ is a scheme generating approximations, $1$ is a cut;
- in the axiomatic specification, a real number is an element of a complete ordered field; $0.999…$ is a notation, $1$ is an element.

In all three cases, to put the sign $=$ between $0.999…$ and $1$, we must *first* translate the left side into the same kind of object as the right: take an equivalence class, or a cut, or an element of a field. This translation is the unspoken act. Before it, $0.999…$ and $1$ are objects of different natures; after it, they are declared to be one.

### Where the Notation Hides a Change of Type

Now it is clear in what exactly ToS parts ways with the naive reading of $0.999… = 1$, and in what it does *not* part ways with standard analysis.

First, about where there is *no* divergence. In standard mathematics the notation $0.999…$ *by definition* denotes a real number: the limit of the corresponding sequence or its equivalence class. Under such a reading, given in advance, both sides of the equality $0.999… = 1$ lie in *one* type, $ℝ$, and the equality is correct. The law $L1$, $A = A$ (Chapter I.3), which requires that one and the same thing in one and the same type stand on both sides of the equals sign, is *not* violated here: the interpretation of the notation is given, and both objects are real numbers. ToS does not declare the standard equality false in its own mode.

The divergence of ToS is with the *naive* reading, in which the mode is not indicated. If we take $0.999…$ as a *process* generating rational approximations (§ 1.8.2), and $1$ as the unit atom, the number of the first act (§ 1.7), then these are objects of *different modes*: on the left a process, on the right an atom. An unconditional equality cannot be placed between them without a preliminary passage to a common mode, for example, to the equivalence class of processes or to the limit. The danger here lies in the *unspoken confusion* of two levels, the level of the process (raw process) and the level of value or class (quotient/value level), not in any falsity of the standard equality. The notation $0.999… = 1$, taken without an indication of the mode, hides a change of type: the passage from a process of approximations to its limit or equivalence class.

*Without an indication of the mode, the notation $0.999… = 1$ hides a change of type: from a process of approximations to its equivalence class or limit. The danger here lies in the unspoken confusion of the process level and the quotient/value level, not in any falsity of the standard equality, which is correct in the mode of real numbers. The error, if it arises, is an error of the naive reading, not of standard mathematics, where the interpretation of the notation is given.*

### The Mode of Classes: Where the Equality Is Legitimate

What has been said does not mean that the statement $0.999… = 1$ is false always and in every sense. It means that this statement has a *condition of meaningfulness*, and this condition is a spoken act.

Chapter I.7 established that sets and equivalence classes in ToS are a *mode of consideration*, not primary entities: a way of taking objects while abstracting from some of their distinctions. The passage to equivalence classes is a legitimate operation; it need only be *performed explicitly*, as a conscious act, rather than slip through by default.

In the spoken mode of classes, the statement $0.999… = 1$ is *correct*: if both objects are taken *as equivalence classes* (the process referred to its class, one to its own), then these classes do coincide, and the equality of classes is true. There is no violation of $L1$ here, because on the left and on the right stands an object of one type: a class. The error arises from a *tacit* passage, not from the passage to classes as such: when a result that is true *in the mode of classes* is passed off as an unconditional identity, true *outside any mode*.

ToS thus does not cancel $0.999… = 1$ and does not declare analysis mistaken. ToS *separates* two statements that the naive notation without an indication of the mode merges into one: “$0.999…$ and $1$ are one and the same equivalence class of processes” (true, in the spoken mode of classes; and this is exactly what standard analysis asserts, where the notation by definition means a class or a limit) and “$0.999…$-as-process and $1$-as-atom are one and the same object of one mode” (false: the process and the atom belong to different modes, and the equality between them has been set without a passage to a common mode). The familiar $0.999… = 1$ is dangerous not because it is false (in its own mode it is true) but because by itself it does not indicate its mode, and thereby prompts us to read what is true-in-the-mode-of-classes as an unconditional identity of objects of different modes.

### Why This Case Matters for ToS

The analysis of the notation $0.999…$ has found a place in the chapter not because of this equality itself but because it shows at work, for the first time, a distinction on which a considerable part of the volume will stand: the distinction between *process* and *atom*.

The case $0.999…$ is a particular and vivid one. But the same distinction will rise to its full size in Part IV. There the real number will be introduced as a *process*, `RealProcess`, an unfolding scheme of rational approximations, not as a point and not as a ready object. The repository already contains the core of this apparatus: the file `src/process/ProcessCore.v` defines `RealProcess` $:= \texttt{nat} \to ℚ$ (a process over $ℚ$ indexed by stages), `const_process` $q$ (the constant process yielding $q$ at every stage), and the relation `process_equiv` (denoted `~~`), which relates two processes *converging to one limit*; `process_equiv` has been proved to be an equivalence relation (reflexive, symmetric, transitive). It is essential that `process_equiv` is *not* pointwise equality: two processes can be `process_equiv` while differing at every single stage.

In this language the position of ToS on $0.999…$ is formulated precisely, and this is a convenient bridge to the future formalization. The notation $0.999…$ corresponds to the process $n \mapsto 1 - 1/10^{ n+1}$; one corresponds to the constant process `const_process` $1$. These two processes are *not* pointwise equal (at every stage the first is strictly less than the second), but they are `process_equiv`: they converge to one limit. The distinction of the three modes from § 1.8 maps onto this directly: as *raw processes*, $0.999…$ and $1$ are different (the difference is pointwise); as *classes under `process_equiv`* they coincide; in the standard notation of the real numbers the equality is legitimate, because the notation already means a class or a limit. A formal check of this picture, through theorems of the form “the process of nines is not pointwise equal to `const_process` $1$” and “the process of nines is `process_equiv` to `const_process` $1$,” belongs to Part IV; `ProcessCore.v` provides a ready language for it, but these theorems about the nines themselves are not yet in the repository. What looks like a particular subtlety in the example of $0.999…$ will turn out in Part IV to be the *general arrangement* of the real number: a real is a process, and convergence is its behavior, not a pointwise equality of the process to a point.

Here, too, it can be seen why a question that sounds acute in the standard frame is in many respects *lifted* in ToS. The acuteness of $0.999… = 1$ arises because the real numbers are taken as a ready set $\mathbb{R}$, in which a process and its limit *must* be one element, or else the set is “incomplete.” ToS does not build $\mathbb{R}$ as a ready set (the reasons are $P4$ and the derived character of sets; unfolded in Part IV). Without a ready $\mathbb{R}$ there is no compulsion to identify the process with the atom. There is a process with its behavior, and there is an atom; they are different; *and this creates no incompleteness*, because ToS does not require the completeness of a ready set. The contested case ceases to be contested as soon as the assumption that gave rise to it is removed.

*The case $0.999…$ matters to ToS as the first appearance of the distinction between process and atom, the distinction on which Part IV will build the real number as a process. In the frame of a ready set $\mathbb{R}$, the identification of a process with its limit is forced by the requirement of completeness; ToS does not introduce this set as a ready object, and the forcing requirement does not arise. The process and the atom remain different, and $L1$ remains in force.*

### E/R/R Analysis: One-as-First as a System

Before summing up, let us gather what has been covered into an E/R/R analysis (Part I): it secures *why* one is primary and sets the tone for the whole of Part II. The header of the supporting file labels this directly: *elements: counting from distinctions; roles: one is the first distinction, zero is absence; rules: the first is one, zero from absence, the next from distinction*.[^15] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. A caveat on status: the “system” here is a substantive interpretation; `one_from_distinction` machine-checks the *chosen registration* (to each distinction, the imprint $1$) and does not *prove* primacy, and the ontological order “$1$ before $0$” rests on `distinction_order` (§ 1.2, § 1.4).

*Rules* (the laws $L1$–$L5$).
The constitution is the rule of registration: the first act of distinction is marked by one (`one_is_first`), every next distinction gives the next number (`succ_from_distinction`); zero comes from the absence of distinction (`zero_from_absence`), not from counting. To these is added the rule of asymmetry: one precedes zero (`distinction_order`, § 1.2.3), not the other way round. And the rule of compatibility: the inversion of primacy is a *reinterpretation* of the type `nat` (two orders, the ontological and the syntactic), not its redefinition (§ 1.4).

*Roles—the significance of positions* (the law $L4$).
One is the role of the *first*: the imprint of the first performed act, the first positive count. Zero is the role of the *boundary*: the mark of the absence of distinctions in a given list or at a given stage, which does not enter the count of acts (§ 1.3). These are two *roles*, not two objects: one is the act itself (§ 1.2.2), not a “set of one”; zero is a boundary mark, not emptiness-as-an-entity. By $L4$ zero is derived: its presence requires an *explanation of absence*, and therefore it is logically later.

*Elements—the bearers* (the law $L1$ and the principle
$P4$). The elements are the acts of distinction themselves, which counting counts over (`ToS_nat` is counting based on distinctions). By $L1$ every act is identical with itself. By $P4$ counting is always a finite list of performed acts: the recording of presence, not the accumulation of a magnitude from emptiness (§ 1.6).

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| first act $=1$; the next from distinction | the constitution of counting | Rule |
| the asymmetry “$1$ before $0$”; zero from absence | order and boundary | Rule |
| inversion as a reinterpretation of `nat` | two orders (§ 1.4) | Rule |
| one: the first count (imprint of the act) | the role of the first | Role |
| zero: the mark of absence (not a count) | the role of the boundary | Role |
| acts of distinction (`ToS_nat`) | bearers (finite, $P4$) | Element |
| the laws $L1$–$L5$ | the universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: the acts are elements, one and zero are roles, registration and asymmetry are rules. $P1$ is observed: counting is a counting of *acts* (elements); number does not count itself. And here the analysis turns into a *diagnosis*, and one that is foundational for the whole of Part II. The standard position “zero is primary” takes zero as a primary *object*, the empty set from which number is built (§ 1.1). This is a confusion of categories: zero is a *role* (boundary, absence), not a grounding object, and one is a *role* (the first count), not a “set of one” (§ 1.2.2). Number is born of the act, of the *presence* of distinction, not of emptiness; to read it as an object built out of nothing is to take a role for an element. ToS will undo the same shift further on as well: for the set, the point, infinity (Part I; Parts III–IV).

What the analysis yields. It lays the *foundation* of the whole of Part II: number is a *role*, the count of performed acts, and one is the first such role. The four paths that the following chapters will take (list, levels, bits, positions) are four bearers of this one role structure; and all four begin with one, for one is the imprint of the first act, prior to any list, level, bit, or position. Having established *by what* one is primary, the chapter hands on to the next chapter the question of *how* the whole natural number series unfolds from it.

### Summary of the Chapter

The chapter has established the primacy of one and drawn out the consequences of this primacy.

One is primary as the number of the first act of distinction, as the numerical imprint of a performed act. It is available before developed counting: as that which the series later formalizes as the first positive count, not as an already built element of the number series in the full arithmetical sense (§ 1.2). Zero is derived: it is the boundary mark of the series of performed distinctions, neither an object nor emptiness-as-an-entity, and it does not enter the count of performed acts (§ 1.3). The inversion of primacy is a reinterpretation of the type `nat`, not its redefinition: the syntactic order of constructors and the ontological order of justification are distinguished, and their divergence is the content of the inversion (§ 1.4). The independently built position of ToS echoes a stable motif of European and other traditions of thought about number, from the Pythagoreans to Spencer-Brown; this is a converging parallel, not a proof (§ 1.5). To count in ToS is to record the number of performed distinctions, not to accumulate a magnitude from emptiness (§ 1.6). What is divisible or indivisible is what the number fixes at a given level, not the number itself: one as the counting imprint of one act is not divided, whereas the symbol $1$ in the role of an element of $ℚ$, of the length of the interval $[0,1]$, or of the neutral element of multiplication takes part in operations of division; what is divided is the structure in which $1$ plays the role of a measure, not the primary one-as-count (§ 1.7). And where the ontological nature of a notation remains unspoken, as in $0.999… = 1$, the naive reading confuses the process of approximations with its limit; ToS removes this confusion by making explicit the change of mode that the familiar notation hides (§ 1.8).

It has been established by what one is primary. It has not yet been established how the *whole* natural number series arises from this primary one, from the repeatability of the first act. This is the subject of the next chapter. Chapter II.2 opens the first of the four paths by which ToS arrives at the natural numbers, the cardinal path: number as the length of a list of performed distinctions.

---

[^1]: The type `nat` of the Rocq standard library; the constructor `O` is zero, `S` is the successor. A detailed discussion of this type and of its relation to the construction of ToS is in § 1.4.
[^2]: The natural numbers as an initial object, or the initial algebra of the functor $1 + (-)$; the categorical path will be considered in detail in the part of the volume devoted to the categorical organization of mathematics. Here it is drawn on only as the third form in which zero receives primary status.
[^3]: The type `DistinctionSide` and `side_value` are absent from the current repository; this is a proposal for strengthening `AsymmetricDistinction.v`. Until it is incorporated, the formal carrier of the priority remains the pair `mark` / `unmark` in its proof-level form, plus `distinction_order` $=(1,0)$.
[^4]: The proof of `distinction_asymmetric` relies on the axiom `classic`, the technical attestation of $L3$ in CIC (Chapter I.6). This is appropriate: the statement “$P$ and $\neg P$ do not coincide” is a statement about the *determinacy* of a distinction, and the determinacy of a distinction is exactly what $L3$ provides. Here `classic` works as the formal trace of a structural law of the act of distinction, not as an imported assumption.
[^5]: This divergence of form is a matter for synchronizing the repository. For `orderings_dual` in `PrimalityOfOne.v` to fix precisely two opposite pairs, it would have to be rewritten through `tos_conceptual_ordering` $:= (1,0)$ and `number_ordering` $:= (0,1)$, as has already been done for `distinction_order` in `AsymmetricDistinction.v`. Until such synchronization, the volume relies on `distinction_order` as the formal carrier of the pair $(1,0)$.
[^6]: A detailed consideration of the relation “one syntax, several semantics,” including the answer to the objection that working on the standard `nat` deprives ToS of originality, is in Chapter II.5. There, too, is the connection with the fact that some difficulties of the set-theoretic foundation are symptoms of interpretation, not of syntax.
[^7]: The device of converging parallels was already used in Part I, in Chapter I.2 and in the historical section of Chapter I.5. Here the same device is applied to the primacy of one. Let us stress its status: the parallel is heuristic, not demonstrative.
[^8]: The doctrine of the Monad is known from later testimonies; the main sources are Aristotle, *Metaphysics* I.5, and the compilation by Theon of Smyrna, “Exposition of Mathematical Matters Useful for Reading Plato.” No direct Pythagorean texts have survived, and the reconstruction of the doctrine of the Monad relies on the doxographic tradition.
[^9]: Plotinus, *Enneads*, treatise VI.9, “On the Good, or the One.” Proclus applies the scheme of descent to mathematics in the *Commentary on the First Book of Euclid’s “Elements”* (prologue).
[^10]: G. Frege, *The Foundations of Arithmetic* (Die Grundlagen der Arithmetik, 1884), § 46 (number as a property of a concept) and § 74 (the definition of zero through the concept $x \neq x$).
[^11]: The coincidence is all the more noticeable because the starting points differ. Frege works within the logicist program and in a concept-theoretic framework; ToS, in the processual ontology of the act of distinction. That two such different frameworks converge on the derived character of zero and on its connection with the violation of $L1$ is one more converging testimony in the sense of § 1.5.1.
[^12]: Cantor formulates the concept of a set as a collection into one whole of definite, distinguishable objects in “Beiträge zur Begründung der transfiniten Mengenlehre” (1895), § 1.
[^13]: G. Spencer-Brown, *Laws of Form* (1969); the construction begins with the injunction “Draw a distinction” in ch. 2.
[^14]: The example of the quark is an illustration of the operational view, not a statement of physics. The question of the structure of the quark belongs to physics; here the quark is drawn on only as a vivid case of an object that is atomic relative to the *present* state of distinctions.
[^15]: The E/R/R labeling is in the header of the file `PrimalityOfOne.v`; the asymmetry “one before zero” is in `AsymmetricDistinction.v`. Here it is unfolded on the model of Part I.

---

Part: [[02 Natural Numbers|Part II. Natural Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/07 Ontological Core Recurring Motifs|Chapter 7. The Ontological Core—Part I]] · [[Library/Branches/Mathematics/Volume/02 Natural Numbers/02 Counting as Length of a List of Distinctions|Chapter 2. Counting as the Length of a List of Distinctions]] →
