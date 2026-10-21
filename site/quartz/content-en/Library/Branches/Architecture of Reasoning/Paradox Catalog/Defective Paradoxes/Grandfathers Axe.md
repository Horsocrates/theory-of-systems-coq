---
title: "Grandfather’s Axe"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Топор дедушки.md"
sourceBlob: 9be61ed7ea17eb7238e2e69cac8069e1e7bf18f8
translated: 2026-10-20
status: draft
description: "The identity of an artifact is a matter of convention"
---

**D.5** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** The identity of an artifact is a matter of convention

## Exact Formulation

“This is my grandfather’s axe. True, my father replaced the handle, and I replaced the blade.” The axe has two parts—and both have been replaced; the speaker reports this himself and goes on calling the thing his grandfather’s axe. Is it the same axe? The [[Ship of Theseus]] in miniature: nine hundred years of Athenian replacements compressed into one sentence and two generations.

## Origin

The folklore line of the Theseus knot. The French tradition knows it as “Jeannot’s knife”—a saying about a knife that had first its blade and then its handle replaced; the English-speaking tradition, as “my grandfather’s axe”; modern everyday life, as “Trigger’s broom” from a British sitcom: one broom for twenty years—with seventeen new heads and fourteen new handles. The folk form is older than the philosophical fashion for it and more tenacious than the treatises—for the same reason that the [[Barber Paradox|barber]] has outlived many expositions of [[Russells Paradox|Russell]]: the defect is visible in one sentence, without the history of a ship.

## Consequence

The miniature adds a feature of its own to Theseus: self-undermining within the sentence itself. The speaker asserts identity and at once honestly lists the complete replacement of the material—the comedy arises because the listener hears both criteria at once: “the same” by the family line and “a different one” by iron and wood. The sentence is funny exactly where the philosophical version is hard—and that is why it serves as the best everyday test: instead of arguing about the “real” ship, ask the disputants about grandfather’s axe—the criteria they have tacitly chosen will surface within a minute. The practical field is the same as with Theseus: relics and museum work (where the material criterion is the main one—holy relics, an autograph, “that very” board), repair and warranty (how many replacements “the same” product survives), the ownership of restored things.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the axe, two parts (the handle, the blade), two replacements in two generations, the claim “grandfather’s axe.” No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “The same axe”—by what criterion? Materially—everything has been replaced, and the speaker himself has said so; structurally—the form and the arrangement are the same; functionally—an unbroken line of ownership and use: grandfather, father, grandson; conceptually—a family relic, a name and a place in the family’s history. Four relations under one “the same.” Signal: no criterion has been assigned—the question is incomplete.

**Domain 3—Framework Selection:** not reached.

**Domain 4—Comparison:** without a criterion the comparison is not set up—the domain waits for domain 2.

**Domain 5—Inference:** under each chosen criterion the answer is valid and simple. The problem is not in the inference.

**Domain 6—Reflection:** the very comedy of the sentence is the signal: two criteria have collided in it; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—indeterminacy of a concept, ambiguity. **Violated laws:** [[Identity]]—before asserting A = A, determine what A is: the axe as material, the axe as form, the axe as a line of ownership, or the axe as a relic. **Essence of the defect:** “the same” without a criterion; the question demands one answer where there are four legitimate answers. On the E/R/R triad: the identity of a relic is held by a Role (a place in the line of transmission), while the dispute is passed off as a question about Elements (iron and wood).

## Why There Is No Paradox

It inherits from Theseus—and is settled faster, because the speaker himself has laid all his cards on the table. Materially—a different axe, and this has been said outright; structurally—the same; functionally—the same: the line of ownership has not been broken; conceptually—the same: a relic is a place in a family’s history, and its value lies in who held it, not in what holds it together. Three criteria out of four favor “the same,” and the fourth has been honestly set aside by the narrator himself—there is no contradiction; there is a choice of what we are asking about. The reverse case is telling too: where a relic is defined materially—holy relics, an autograph, “that very” board of the barn—replacement kills the status, and a museum expert will rightly say “not the same,” while the grandson rightly says “the same”: both verdicts are correct by their own criteria, and the dispute between them is a dispute about the criterion, not about the axe.

## Lesson

The miniature is a test for the criterion: if the dispute about “the same” is funny in its everyday version, the philosophical version of the same dispute is no deeper—only longer. On hearing “the same?”, ask “the same by what?”—one word covers four relations, and the choice among them belongs to the goal, not to logic.

## Kin by Mechanism

[[Ship of Theseus]] (the canonical form—the full analysis is there), [[Teleportation Paradox]] (the same question about a person), Jeannot’s knife and Trigger’s broom (folklore brothers), [[Sorites Paradox|Sorites]] (a neighbor by type: vagueness next to ambiguity).

**Machine check.** The criterial mechanics is formalized in the analysis of Theseus: `verdict_depends_on_criterion`, `elements_flow` (src/foundation/KnowledgeIdentityRoles.v—the elements flow, the system stands). In the registry of 46 it is `D5_GrandfatherAxe`: the field `ConceptualAmbiguity`, the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
