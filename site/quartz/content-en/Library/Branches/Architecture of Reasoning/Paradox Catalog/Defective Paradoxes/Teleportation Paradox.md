---
title: "Teleportation Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс телепортации.md"
sourceBlob: 680f900baf9d8dc95d500956d460d860f7fbb9f5
translated: 2026-10-20
status: draft
description: "No criterion of personal identity is specified"
---

**D.6** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** No criterion of personal identity is specified

## Exact Formulation

A teleporter scans a body down to the atom, destroys the original, and assembles an exact copy on Mars—with the same memory, the same character, the same plans for the evening. The one who arrives is sure that he is the one who departed. Is this the same person—or did the original perish, while a double lives on? Parfit’s sharpening: the machine malfunctions—the original is not destroyed, and the copy has already been assembled. There are two of them, both remember one childhood, both call themselves you. Which of them is you?

## Origin

The question of the criterion of personal identity is older than the teleporter. Locke (*An Essay Concerning Human Understanding*, 1690) detached the person from substance: personal identity lies in the continuity of consciousness and memory; a prince who wakes in the body of a cobbler is the prince. Reid objected with the case of the officer: memory is not transitive, identity is. The twentieth century turned the dispute into a laboratory of thought experiments: Williams (“The Self and the Future,” 1970) showed that the intuition about the transfer of the psyche flips depending on how the same story is presented; the summit is Parfit (*Reasons and Persons*, 1984): teletransportation, a malfunction with branching, the division of the brain—and a radical conclusion: identity is not what matters; what matters is psychological continuity and connectedness, and these can exist without uniqueness. Science fiction made the knot an everyday one: the dispute over whether “the transporter kills,” started in front of the screen, is the same dispute as Locke’s and Reid’s.

## Consequence

Teleportation is the [[Ship of Theseus]] raised to the highest stake: the ship concerns a thing, while here the question concerns its own bearer. The same four criteria: material (the same atoms), structural (the same configuration), psychological (continuity of memory and character—the functional line of a person), conceptual (recognition: family, name, passport). And the knot’s own contribution: branching strikes at the hidden requirement of uniqueness—identity is a one-to-one relation, while psychological continuity can lead to two; the criterion that seemed best does not guarantee a single heir. The applied field is growing: cryonics, “mind uploading,” backup copies of agents—everywhere the question “will I survive?” comes up against the unchosen criterion of the word “I.”

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the original, the scan, the destruction, the copy, memory and character, the question “the same person?”; in the sharpened version, two claimants. No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “The same person”—by what criterion? Materially—the atoms are different (but metabolism replaces them even without a teleporter); structurally—the configuration is the same; psychologically—the continuity is complete; conceptually—recognition is decided by people. Branching adds a second layer: “the same” requires uniqueness, while psychological continuity branches. Signal: no criterion has been assigned, and the hidden assumption of uniqueness has not been spelled out.

**Domain 3—Framework Selection:** not reached.

**Domain 4—Comparison:** the copy and the original are compared honestly by each criterion separately; only the main question has not been posed—by which criterion to judge.

**Domain 5—Inference:** under each chosen criterion the verdict is valid. The problem is not in the inference.

**Domain 6—Reflection:** intuition wavers, and the presentation of the story changes the answer (Williams)—signal: the question is incomplete; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—indeterminacy of a concept, ambiguity. **Violated laws:** [[Identity]]—twice: A = A requires A to be determined, and the question has not determined it; and identity is a one-to-one relation, whereas the tacitly chosen criterion (psychological continuity) admits branching. **Essence of the defect:** “the same person” is a criterial verdict presented as a binary fact. On the E/R/R triad: the Elements of a person (atoms) flow even without a teleporter—identity is held by the Roles (the continuity of the psyche, a place in relationships); a question about the arrangement of the Roles is passed off as a question about the Elements.

## Why There Is No Paradox

The explication of the criterion takes the knot apart piece by piece. The material criterion drops out first—not because it is inconvenient but because it is unfit: metabolism replaces the matter of the body anyway; a criterion by which a person does not survive ordinary life is unfit for measuring a teleporter. By the psychological criterion, the one who arrives is continuous with the one who left—the same person; by the conceptual one—as practice decides (law already decides such things for companies and for ships). There remains branching—and it is settled by an honest separation of concepts: when two are psychologically continuous with one, what is not preserved is *identity* (unique by definition), but everything that made identity valuable is preserved—memory, character, the continuation of plans. The question “which of the two is I?” is incomplete: the word “I” in it presupposes a uniqueness that the scenario has canceled by its condition. The honest boundary of the analysis: there remains the question of the continuity of the experiencing perspective—“will I wake up on Mars?”; this is a question about consciousness, and the thought experiment does not settle it but tacitly assumes it settled. The knot about the word “the same” is untied; the question about consciousness is a separate one, and it should be posed separately.

## Lesson

**On uniqueness.** Identity is one-to-one; continuity can branch; confusing the two gives birth to pseudo-questions of the kind “which one is the real one?” **On the criterion.** “The same” without a criterion is empty—with things this is curious, with persons it is vitally important, because survival is measured by this word. **On the stakes.** The dispute over whether “the transporter kills” is a dispute about what we value in survival: matter, perspective, or the continuation of a line; logic clarifies the fork—the choice belongs to the one who answers.

## Kin by Mechanism

[[Ship of Theseus]] (the canonical form—a thing instead of a person), [[Grandfathers Axe|Grandfather’s Axe]] (an everyday miniature), the division of the brain and Parfit’s cases (branching without technology), [[Masked Man]] (the criterion for recognizing a person—the epistemic side).

**Machine check.** The criterial mechanics is in the analysis of Theseus: `verdict_depends_on_criterion`, `process_identity` (identity as a process—src/foundation/KnowledgeIdentityRoles.v). In the registry of 46 it is `D6_Teleportation`: the field `ConceptualAmbiguity`, the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
