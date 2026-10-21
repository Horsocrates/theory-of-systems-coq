---
title: "Ship of Theseus"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Корабль Тесея.md"
sourceBlob: 421565a0d1c797648a17709f552fe6e72c9b2ca0
translated: 2026-10-20
status: draft
description: "“The same” is undefined—a criterion of identity is needed"
---

**D.4** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** “The same” is undefined—a criterion of identity is needed

## Exact Formulation

The Athenians preserve the ship of Theseus, replacing rotting planks with new ones; in time every plank has been replaced. Is it the same ship? Hobbes’s scenario sharpens the question: someone has gathered all the discarded original planks and built the ship anew from them. Now there are two claimants: the maintained ship—with a continuous history and entirely new material—and the reassembled one—from the planks Theseus touched, but with a gap in its existence. Both have a right to the name—and the two cannot be one ship.

## Origin

The knot goes back to a real practice. The Athenians preserved the thirty-oared galley on which Theseus—according to tradition—returned from Crete; the ship sailed on the annual sacred embassy to Delos, and while it was at sea no executions could be carried out in Athens—which is why Socrates waited thirty days for death after his sentence. Plutarch (first century) records the dispute of the philosophers: the ship was preserved down to the time of Demetrius of Phalerum (who ruled in 317–307 BCE)—nine centuries of replacements—“some declaring that it remained the same, others that it was not the same vessel” (*Theseus* 23.1, trans. B. Perrin, Loeb, 1914). Plutarch does not settle the dispute—he leaves it open. In the seventeenth century Thomas Hobbes added a second claimant: a ship assembled from the preserved old planks “without doubt, had also been the same numerical ship”—and the problem went from difficult to seemingly insoluble.

## Consequence

The knot’s progeny is wider than that of any other defective paradox. Personal identity: Parfit (*Reasons and Persons*, 1984)—teleportation and the division of the brain show that intuitions about personal identity are torn apart just as intuitions about the ship are. Law: is a company that has changed its staff, its office, and its product the same company, and are its obligations inherited? Each time, the court chooses a criterion of identity. Restoration: Leonardo’s *Last Supper* retains less than a fifth of its original paint; the Ise Shrine in Japan is rebuilt entirely every twenty years—and for thirteen centuries it has been considered the same shrine. Technology: Windows 1.0 and Windows 11 have no lines of code in common. Every question “is this the same thing?” secretly chooses a criterion—the knot of Theseus makes the choice visible.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the ship, the planks (original and new), the time of gradual replacement, two claimants, the question of identity. No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “The same”—by what criterion? Possible meanings: materially (the same physical parts), structurally (the same form and organization), functionally (the same role, a continuous history of use), conceptually (the same name and recognition). Four different relations under one word. Signal: the question is incomplete—no criterion of identity has been assigned.

**Domain 3—Framework Selection:** not reached—a framework cannot be chosen until it is clear what is being compared.

**Domain 4—Comparison:** receives no task: comparing the two claimants requires a criterion, and no criterion has been set—domain 4 waits for domain 2.

**Domain 5—Inference:** both intuitions (“the same” / “a different one”) are valid—each under its own criterion. The problem is not in the inference.

**Domain 6—Reflection:** intuition is torn—signal: the dispute concerns different questions under one word; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—indeterminacy of a concept, ambiguity. **Violated laws:** [[Identity]]—the law A = A works for determinate entities; before asserting A = A, one must determine what A is—whereas the question applies the law to an entity without a criterion. **Essence of the defect:** “the same” is not a property of the object but a relation under a chosen criterion; the question demands one answer where there are four legitimate answers. On the E/R/R triad: the identity of a system is held by the Roles, not by the Elements—a dispute about which Role is constitutive is passed off as a question about planks.

## Why There Is No Paradox

The resolution is the explication of the question, not a search for the “right answer.” Aspect by aspect, the picture is clean: the maintained ship is the same structurally, functionally, and conceptually, and different materially; the reassembled one is the same materially and structurally, different functionally (it was taken apart), and conceptually disputed. There is no contradiction—there are different answers to different questions. The dispute about the “real” ship is a dispute about values: to a museum the material matters more, to an active fleet the function, to a culture the name; logic does not decide this dispute, but it clarifies what the dispute is about. Deeper still: identity is a process, not a property. An organism holds itself by metabolism, an artifact by maintenance, a company by social practices; the question “is it the same object?” means “has the process that maintains identity been preserved?” The Ise Shrine is a cultural answer of the same grade: the identity of the shrine is placed in the ritual of rebuilding, not in the wood. The full derivation of identity through change—necessary and permitted characteristics, the square on roles—is on the page [[Identity]].

## Lesson

**On the nature of identity.** Identity is a multidimensional relation; to demand a single answer is a category mistake. **On hidden assumptions.** “Identity must be unambiguous” is an assumption that seems self-evident; its explication unties the knot. **On values.** Disputes about identity often mask disputes about what is valued—material, history, function, recognition; logic clarifies the subject of the dispute, and the choice remains with the goal. **On practice.** An insoluble question is a reason to check whether the key concepts are defined: the dispute is often about different things under one name.

## Kin by Mechanism

[[Grandfathers Axe|Grandfather’s Axe]] (the same structure in miniature: the father replaced the handle, the grandson the blade), [[Teleportation Paradox]] (personal identity under copying), [[Masked Man]] (a substitution of the criterion of identity in knowledge), [[Sorites Paradox|Sorites]] (a neighbor by type—another kind of indeterminacy: vagueness).

**Machine check.** There is a named analysis: identity on roles—src/foundation/KnowledgeIdentityRoles.v: `verdict_depends_on_criterion` (the verdict depends on the chosen criterion), `hobbes_table` (the table of the two ships, machine-checked), `process_identity` and `elements_flow` (the elements flow—the system stands: identity as a process), `manifestation_varies_identity_stands` (the manifestation changes—identity holds). In the registry of 46 it is `D4_ShipOfTheseus`: defective, resolution by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
