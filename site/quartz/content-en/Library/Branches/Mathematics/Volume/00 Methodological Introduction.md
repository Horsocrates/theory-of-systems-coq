---
title: "Methodological Introduction"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/00 Методологическое введение.md"
sourceBlob: c03ea0c43904c0a756ed2696716cff4fce4bb7c8
translated: 2026-10-20
status: draft
---

## The Place of Volume II in the Series

The series “Architecture of Reasoning” is built as a sequence of volumes, each of which unfolds a particular area of knowledge on a single ontological foundation.

- **Volume I. Metaphysics** unfolds ontology—the description of *what is* as the structure of reality. It establishes Logic as the primary meta-aspect of the Absolute, formulates the Law of Sufficient Reason as the action of Logic, derives the laws of logic, introduces the notions of the Source and the Witness, and describes the structure of the cascade of systems in which reality unfolds. Volume I is the metaphysical foundation of the whole series.
- **Volume II. Mathematics** (the present volume) unfolds mathematics as the operational manifestation of the ontology of Volume I. It works with the minimal fragment of metaphysics that suffices for mathematical work, and it carries the unfolding as far as quantum information.
- The subsequent volumes apply the established system to physics (Volume III), computer science, biology, social systems, and philosophy. Each subsequent volume rests on the preceding ones.

Volume II rests on Volume I *structurally*: its propositions presuppose that the ontological conclusions of metaphysics have already been drawn. At the time of writing Volume II, work on Volume I is not yet complete; the mathematical content turned out to be ready earlier than the metaphysical, which reflects the natural course of the research: mathematics unfolded through formal work in Rocq, and the accumulated material made up the content of a self-standing volume.

This gives the reader two options. Whoever wants a full metaphysical justification of the ontological presuppositions will find it in Volume I, once that volume is complete. Whoever wants to start on the mathematical content at once will find in the present section the *minimal ontological fragment*—a brief exposition of those propositions of metaphysics that are essential to Volume II. In the subsequent chapters these propositions are *accepted* as an ontological support, without rediscovering them in mathematical language.

## The Minimal Ontological Fragment

Here we set out those propositions of metaphysics on which Volume II rests. They are *not proved*—their justification belongs to Volume I. They are *marked out* so that the reader has a support throughout the mathematical unfolding.

### Logic as the Structure of Being

Logic is *the structure of being itself*, rather than the rules of inference of a formal system or an instrument of thought. Reality exists *in accordance with* logic, because without logical structure—without the identity of things with themselves, without the impossibility of $A$ and $\neg A$ at once, without a ground by which one thing *is* and another *is not*—there would be no reality at all. Logic is discovered as the condition of the very possibility of existence: it is neither chosen nor created.

This position is called *logical realism*. Volume II holds to it consistently. All the formal systems used in mathematics—set theory, type theory, category theory, the calculus of inductive constructions CIC on which Rocq is built—are *technical implementations* of logic in particular languages with particular rules of inference. They work *because* logic already exists; they *express* it within particular frameworks, and they *are not* logic themselves.

This difference matters for all the further work. When Chapter 3 says that L1–L4 *are derived as theorems* from the structure `Distinction`, this will mean a formal-mathematical statement about the provability of these theorems within Rocq, *not* a statement about the ontological grounding of logic. Ontologically the laws of logic are *primary*: the act of distinction becomes possible *thanks to* them, and they are not *derived* from it. That in the formal system they appear as theorems about a single object is the result of a particular way of formalizing; it is a *technical feature*, not an ontological position.

### The Law of Sufficient Reason as the Action of Logic

The Law of Sufficient Reason states: nothing exists and nothing is asserted without a ground. In Leibniz, Sufficient Reason was formulated as one of the laws alongside identity and non-contradiction. In the metaphysics of Volume I Sufficient Reason receives a deeper status: it is *the action of Logic itself* as a meta-structure, *not* one law beside the others.

The difference can be clarified as follows. The Law of Identity speaks of *what is*—the stability of things: $A$ is $A$. The Law of Non-Contradiction speaks of *what is impossible*: $A$ and $\neg A$ at once. Sufficient Reason speaks of *how* the establishing of these propositions *works*: every assertion requires a ground, every existence a ground, every structure a condition by which it is as it is. Sufficient Reason is the *work* of Logic, not a *law* in one row with identity and non-contradiction.

This formulation of Sufficient Reason will work throughout the volume. Every time we demand a constructive building, an explicit criterion, an algorithmically checkable condition, we will be applying Sufficient Reason. The principle $P4$ (infinity as a property of processes, Part IV) is a concrete application of Sufficient Reason: there is a ground for an infinite process as an unfolding entity, while actual infinity as a completed object has no ground by which it could be presented. The principle $\mathbf{M3}$ (sets as a mode, Part X) is an application of Sufficient Reason: there is a ground for the operator’s decision to work with a list in a certain mode, while the existence of a set *as ontologically given* has no ground. Thus Sufficient Reason will show itself throughout the volume as the structural principle of the work of Logic.

It is important that in the formal part Sufficient Reason *is not exhausted* by a single record or a single theorem. It has several distinct technical traces, and they must not be confused. The first is the *self-grounding of distinction*: from the positive side of the act of distinction follows the negation of its negative side, and this is expressed by a separate property of the record `Distinction`. The second is the *witnessing of existence*: from the fact that something exists, a definite witness of this existence is extracted; this is a separate principle of the axiomatic layer, and, as will be shown, it does not coincide with the Axiom of Choice. The third is the general *methodological principle of an explicit ground*, running through the whole volume: every construction must present a ground. These three technical traces neither replace the ontological Sufficient Reason nor reduce to one another: they express different working sides of one principle in the formal system. The ontological Sufficient Reason is the action of Logic; its formal traces are particular manifestations of this action at different levels of formalization.

### The Laws of Logic in the Ontological and in the Formal-Mathematical Exposition

Here an *explicit warning* is needed about a terminological distinction that will work throughout Chapter 3 and beyond.

In metaphysics (Volume I) the laws of logic are singled out and numbered as follows:

- **Sufficient Reason**—a meta-law, the action of Logic; *primary*.
- **The Law of Identity**—$A = A$.
- **The Law of Non-Contradiction**—$\neg(A \wedge \neg A)$.
- **The Law of Order**—the structure of the hierarchy of levels on which reality unfolds.
- **The Law of Excluded Middle**—$A \vee \neg A$; *derived* from Identity and Non-Contradiction.

In the formal system Rocq, in which Volume II is formalized, the laws receive a different numbering:

- $L1$—the Law of Identity: `positive D = positive D`, proved by `reflexivity`.
- $L2$—the Law of Non-Contradiction: `exclusive`, a field of the record `Distinction`.
- $L3$—the Law of Excluded Middle: `exhaustive`, a field of the record `Distinction` that relies on the axiom `classic`.
- $L4$—the Law of Sufficient Reason: the theorem `positive D -> ~ negative D`, derived from `exclusive`.
- $L5$—the Law of Order: the type `Level` with the relation `<<`, expressing the hierarchy of levels.

Strictly speaking, the laws $L1$–$L4$ are read directly off the structure of the record `Distinction`—off its four fields and their properties. The law $L5$ is arranged differently: it is introduced by *the next layer* of formalization, through a separate type of levels `Level` and the relation `<<`. Therefore $L5$ is *not* a field of the record `Distinction`: it expresses the hierarchical context in which distinctions and systems become protected from self-application. The distinction between these two layers—the structure of one act ($L1$–$L4$) and the hierarchy of acts ($L5$)—will be essential later on.

These two numberings *differ*, and the reader should clearly understand the reason for the difference.

In metaphysics the order of the laws reflects their *ontological* status: Sufficient Reason is primary as the action of Logic, and excluded middle is derived as a consequence of identity and non-contradiction. In the formal system Rocq this order *cannot be reproduced*: in the calculus of inductive constructions the Law of Excluded Middle cannot be derived as a theorem from the other laws—for this reason it enters Rocq through a separate axiom `classic` and receives in the formalization the status of an independent $L3$. Correspondingly, Sufficient Reason, which is primary in metaphysics, appears in the formalization as $L4$—a theorem derived from other fields of the record `Distinction`.

The numbering $L1$–$L5$ in Rocq is a *stable technical interface* of the formalization. It took shape historically—in the course of formalization, beginning with Identity and Non-Contradiction, familiar in the logical tradition—and from then on it is deliberately kept unchanged: its task is to ensure the stability of references, proofs, and dependencies in the machine-checked corpus of the repository, rather than to display the ontological hierarchy of the laws. We thus distinguish two things: the *interface names* ($L1$–$L5$ in the order in which they are fixed) and the *ontological order* of the laws (in which Sufficient Reason is primary and excluded middle is derived). The internal names of the formal system are not ontological statements, and they should not be mixed with the ontological order.

Volume II adopts the following terminological convention:

> In discussing *ontology* (references to Volume I, philosophical
> remarks, discussion of the nature of the laws of logic) we use the names
> without numbers: *the Law of Identity, the Law of Non-Contradiction,*
> *the Law of Sufficient Reason, the Law of Order, Excluded Middle*. The order
> of importance: Sufficient Reason as the meta-law, then Identity and
> Non-Contradiction as primary, Order as structural, Excluded Middle as derived.
> 
> In discussing *formalization* (records in Rocq, references to particular
> theorems and definitions) we use the numbers $L1$–$L5$ in the
> sequence in which they are fixed in the repository:
> $L1$—Identity, $L2$—Non-Contradiction,
> $L3$—Excluded Middle, $L4$—Sufficient Reason,
> $L5$—Order.
> 
> When we need to work with both levels at once, we say so
> explicitly—for example: “the Law of Sufficient Reason (formally:
> $L4$).”

This convention will let us avoid terminological confusion and at the same time stay faithful to both levels—the ontological and the formal.

### The Primary Fact: $A = \exists$

The existence of anything is a *primary fact*—neither an axiom nor a choice. Establishing this fact is the subject of Volume I. Here we indicate only the essentials.

First of all, a word on the notation itself. The expression $A = \exists$ is *not* a formula of the language of CIC: the symbol $\exists$ is not used here as a quantifier inside a formal equality, and $A = \exists$ does not mean the equality of some term with a quantifier. It is a brief symbolic notation of the primary fact: *something is, existence is given*. The formal system does not begin with this notation, and it cannot begin with it, since the notation presupposes an already existing system of types. Formalization begins with the first formalizable *consequence* of the primary fact—with the act of distinction, to which we turn below.

About the primary fact itself, it is enough here to fix three propositions.

- The assertion “something exists” *is self-witnessing*: its very denial requires the existence of the one who denies, of the denial, and of the context in which the denial takes place. Structurally, existence cannot be denied without falling into contradiction.
- This self-witnessing is *the work of Logic*—a manifestation of Sufficient Reason at the most primary level: “existence” asserts itself because there is no ground for denial that would not lead to contradiction.
- Existence is thus *discovered*, not *postulated*. It is a primary fact established by the analysis of the work of Logic upon itself—not the first axiom of the formal system (the formal system has not yet been built at this point), and not a philosophical choice.

In Chapter 1 of the present volume we will return to this fact and discuss it in the context of *the boundary of formalization*: how the primary fact of existence relates to the possibility of recording it in a formal system. Here it is important for us to fix only the fact itself and its status.

### The Act of Distinction as the First Formalizable

If *existence* is a primary fact that is not recorded in the formal system (because it is the condition of the system’s very possibility), then *the act of distinction* is the first thing that is recorded.

Distinction is the division of existence into *this* and *not this*. It is the work of Logic upon its own primary givenness: two sides and two conditions of distinction are applied to the fact of existence—the positive side is asserted, the negative side is asserted, their mutual exclusion is fixed, and their joint exhaustiveness is fixed. In this sense the act of distinction is *a manifestation of Logic in its full structure* at the most minimal possible point.

Formally, the act of distinction is written down as a record with four fields:

```coq
Record Distinction := mkDistinction {
  positive    : Prop;
  negative    : Prop;
  exclusive   : ~(positive /\ negative);
  exhaustive  : positive \/ negative
}.
```

This is the *record* of distinction in the types of CIC—the technical equivalent of an ontological object in the formal system—and *not a definition* of distinction: the definition takes place at the ontological level (Volume I). A detailed discussion of this record and of what it formalizes is in Chapter 2.

## What Volume II Does and What It Does Not Do

So that the reader has clear expectations, let us list them directly.

### What Volume II Does

- It unfolds mathematics from the act of distinction (Part I) to quantum information (Part XV) and the concluding synthesis (Part XVI), passing through number systems, analysis, algebra, geometry, number theory, and the theories of categories and information.
- It formalizes the key constructions in Rocq, in the repository `theory- of- systems- coq`.
- It develops four recurring motifs—**M1**, positive ontology; **M2**, operational divisibility; **M3**, sets as a mode; **M4**, structural inevitability—through all 16 parts of the volume, marking their returns in the margins.
- It prepares an *ontological bridge* to Volume III (physics), without itself entering into physical content.

### What Volume II Does Not Do

- It does not ground ontology anew. Establishing ontology is the work of Volume I, on metaphysics. Volume II accepts the ontological propositions as a support and develops mathematical content on them.
- It does not unfold the Source, the Witness, Light, and the cascade of nested systems as ontological structures. These are structures of metaphysics belonging to Volume I. The mathematical unfolding does not require them.
- It makes no claim to a new physical theory or to the solution of open problems of physics. Volume II is a mathematical work; physical application is the task of Volume III.
- It makes no claim to a “final” formalization of mathematics. The fundamental openness of the hierarchy of levels (Chapter 14.8) means that the mathematical unfolding is a process that no single volume completes.

## The Status of Mathematical Objects

A natural question for a reader who meets the operational ontology of Volume II: *what are* mathematical objects—number, function, group, manifold—in this picture?

Volume II stands outside the classical alternatives: Platonism (numbers exist independently of us in an ideal realm), pure formalism (numbers are merely names in a formal system), and pure constructivism (numbers arise only through our activity).

The position of Volume II is *operational realism*, consistent with the metaphysics of Volume I. Mathematical objects are:

- *Real*, in the sense that they are objective structures independent of the individual subject. The natural number $5$ is identical to itself regardless of who considers it.
- *Operational*, in the sense that their existence *unfolds* through acts of distinction; they *are actualized* in the process of work, rather than being *already given* as completed entities.
- *In agreement with Logic*, in the sense that their structure is a manifestation of the work of the laws of logic at a particular level. Sufficient Reason requires every object to have a ground; and it has one—through the explicit constructive path along which the object unfolds.

This proposition will work throughout the volume. Every mathematical definition in Volume II is accompanied by an *explicit ground* for the path along which the object unfolds—Sufficient Reason at the mathematical level. And every time classical mathematics turns to actual infinity, to the Axiom of Choice, to a completed union—that is, to structures without an explicit constructive ground—Volume II seeks an alternative path.

## Notation and the Order of Reading

**Notation.**  Labels **(M1)**–**(M4)** are placed in the margins of the text where the recurring motifs of the volume return. At the end of the volume there is an alphabetical index of the returns of the motifs: a reader interested in one particular motif can trace it through the whole volume by means of the index.

Special formulations are set off in boxes:

- *Ontological remarks* (references to Volume I, philosophical explanations)—in a box marked *Ontology*.
- *Technical details* (which can be skipped on a first reading without loss of meaning)—in a box marked *Technical*.
- *Recurring motifs* (introduced in Chapter 6 of Part I and returning throughout the volume)—in a framed box with a heading.

**The order of reading.**  The volume is built as a *deductive sequence*: each part rests on the preceding ones. Linear reading—from Part I to Part XVI—gives the full unfolding.

Two shortened routes are possible:

- A reader who wishes to obtain the philosophical-methodological picture without full mathematical detail may read Part I (Chapters 1–6), Part IV (which introduces the process ontology), Part X (sets as a mode), Part XIV (the categorical structure), and Part XVI (the synthesis). This comes to about 350 pages instead of the full 1,400.
- A mathematician-reader interested in concrete results in the formal system may skip the philosophical chapters and read the technical ones—Parts II–III (number systems), Parts IV–IX (analysis), Parts XI–XIII (algebra, geometry, number theory), Part XV (information). This comes to about 800 pages of denser mathematical content.

The full reading of the volume—a linear one—is assumed to be the main one.

**Sources.**  All key definitions and theorems are accompanied by references to particular files and theorems in the repository `theory-of-systems-coq`, available at

  <https://github.com/Horsocrates/theory-of-systems-coq>

A reader interested in the machine checking of the statements can verify them independently.

With the ontological support established and the terminological conventions fixed, we pass to Part I, which begins with Chapter 1, on the first principle and the boundary of formalization.

---

Volume: [[Mathematics|“Mathematics”]]

Navigation: [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/01 First Principle A Equals Exists|Chapter 1. The First Principle: A = ∃—Part I]] →
