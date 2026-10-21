---
title: "Galileo’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс Галилея.md"
sourceBlob: 4639105109df63be40ea0a3c1723fc8af33a3d6e
translated: 2026-10-20
status: draft
description: "“As many” changes its meaning (quantity → bijection)"
---

**D.22** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** “As many” changes its meaning (quantity → bijection)

## Exact Formulation

The natural numbers: 1, 2, 3, 4, … The squares: 1, 4, 9, 16, … To each number there corresponds exactly one square (n → n²), to each square exactly one number (n² → n): the correspondence is one-to-one—there are as many squares as there are numbers. But the squares are a part of the natural numbers, and a thinning part: among the first hundred there are ten of them, among the first million, a thousand. A part cannot equal the whole—there are fewer squares. As many—and fewer, at once.

## Origin

Galileo Galilei, *Discourses and Mathematical Demonstrations Relating to Two New Sciences* (1638): the problem is formulated by Salviati, the author’s voice. Remarks about “a part equal to the whole” occurred among medieval authors too, but Galileo gave the knot its canonical form—and his own verdict: “the attributes ‘equal,’ ‘greater,’ and ‘less,’ are not applicable to infinite, but only to finite, quantities.” Then the line forks. Bolzano (*Paradoxes of the Infinite*, 1851) took the bijections between part and whole seriously; Dedekind (1888) made an elegant reversal—he declared equinumerosity with a proper part to be the *definition* of an infinite set; Cantor laid correspondence at the foundation of the concept of cardinality: two sets are “equinumerous” if there is a bijection between them—and the paradox disappeared at the price of redefining the words “as many.” The catalog holds to Galileo’s verdict—following the canon of the volume “Mathematics”: it was the right diagnosis, not a capitulation.

## Consequence

The knot laid bare a conflict between two principles of comparison, a conflict invisible on the finite. Euclid’s principle: the whole is greater than the part. The principle of correspondence (later, Hume’s principle): things are equinumerous if they pair off without remainder. On finite collections the two always agree—which is why they seem to be one concept, “as many.” On infinite ones they diverge—and each school chose its own: Cantor sacrificed Euclid; Galileo set both aside as inapplicable. It is important to see the status of the choice: Cantor did not *discover* that there are as many squares—he *defined* “as many” so that this would become true; a definition can be fruitful, but it is not a discovery of “how many there really are.” The knot’s direct progeny is [[Hilberts Hotel|Hilbert’s Hotel]] (the same correspondence in the setting of rooms) and the whole ladder to the [[Cantors Paradox|hierarchy of infinities]].

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: two series, an inclusion (every square is a number), a correspondence (n ↔ n²), the question “how many.” Signal: two honest observations pull in different directions.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “As many” splits in two. The first meaning is the counting one: both collections have been counted, the count has been completed, the totals are equal; this meaning also carries the part–whole principle—both are defined through boundaries and completion. The second meaning is the correspondence one: there exists a pairing without remainder. On the finite the two meanings always coincide—on the infinite the first is undefinable (the count is never completed, there are no boundaries), while the second is definable and true. The “contradiction” is a collision of two meanings of one word, not of two truths about one subject. Signal: equivocation at the boundary of the domain of applicability.

**Domain 3—Framework Selection:** a second layer: the framework of counting—an instrument that requires completion—is applied to the unbounded; this is exactly what Galileo said.

**Domain 4—Comparison:** telling: both comparisons are carried out honestly—the inclusion is real, the bijection is real; what conflicts is not the operations but the gluing of their verdicts into one word.

**Domain 5—Inference:** both lines are flawless. The problem is not in the inference.

**Domain 6—Reflection:** “as many and fewer”—signal: separate the meanings; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—indeterminacy of a concept: the equivocation of “as many.” **Violated laws:** [[Identity]]—one word serves two relations: equality by count (through boundaries) and the existence of a correspondence; the predicates “equal,” “greater,” “less” are defined through boundaries, which the unbounded does not have. **Essence of the defect:** quantitative comparison is applied to objects for which it is not defined, and is replaced by comparison by correspondence under the same name. On the E/R/R triad: the Rule of comparing quantities, forged on finite Elements, is replaced by another Rule (correspondence) while the name is kept.

## Why There Is No Paradox

Separating the meanings closes the knot. “As many by count” is not defined on infinite series: the count is never completed, and “the part is less than the whole” presupposes boundaries that are not there—this branch is not false; it has no subject. “There exists a bijection n ↔ n²” is defined and true, but it is a fact about correspondence, not about quantity. The contradiction evaporates: it is left without a single bearer—“as many₁” does not apply, “as many₂” is true, and these are different predicates. Galileo’s verdict turns out to be an exact diagnosis of a categorial boundary: the attributes of comparison live where there are edges. The Cantorian line is honest as a *definition*—and dishonest as a *discovery*: “equinumerosity” works as long as one remembers that it is a term about correspondences, not an answer to the question “how many squares are there really”; there is no such answer, because the question lies beyond the boundary of the domain. Dedekind’s move is the most elegant in the family: he did not argue about the word but made the strangeness a criterion—infinite is what is equinumerous with a proper part of itself; a property of correspondence became a definition, and the word “quantity” was not needed at all. Euclid’s axiom and Hume’s principle are compatible on the finite and diverge on the infinite; the choice between them is a convention, and behind this choice there is no hidden fact.

## Lesson

**On equivocation at the boundary.** Two criteria that coincide on the familiar domain grow together into one word; beyond the boundary of the domain they diverge—and the word tears with the crack of a “paradox.” Check which criterion a word carries when the domain changes. **On definition and discovery.** “We have defined X thus” and “we have discovered that X” are different acts; passing off the first as the second is the source of half the “counterintuitive properties” of infinity. **On the signal of intuition.** The intuition “the part is less than the whole” is not foolish—it signals that the concept has gone beyond the limits of its applicability; listening to this signal is the work of domain 2.

## Kin by Mechanism

[[Hilberts Hotel|Hilbert’s Hotel]] (the same correspondence of part and whole in the setting of rooms), [[Cantors Paradox|Cantor]] (where the choice of Hume’s principle leads), [[Horned Man|the Horned Man]] (equivocation—the verbal mechanism in pure form), [[Banach Tarski|Banach–Tarski]] (the next rung of the same ladder: “parts” that have no measure).

**Machine check.** In the registry of 46 it is `D22_Galileo`: the field `ConceptualAmbiguity` (the splitting of “as many”), the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). The process ground is the same as for the hotel: infinity as a rule of continuation (`RealProcess := nat -> Q`, src/process/ProcessCore.v); on this reading the correspondence n ↔ n² is an honest operation on processes, and the question “how many” is not posed to them. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
