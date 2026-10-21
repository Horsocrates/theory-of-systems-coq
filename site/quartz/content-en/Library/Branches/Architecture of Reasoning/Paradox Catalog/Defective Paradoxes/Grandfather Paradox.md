---
title: "Grandfather Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс дедушки.md"
sourceBlob: ff81128c136dd521078c529c91eb02e03a94b6e4
translated: 2026-10-20
status: draft
description: "“A changeable past” is a contradictory concept"
---

**D.12** · [[Defective Paradoxes|defective paradox]] · subtype: False Premise

**Essence of the error.** “A changeable past” is a contradictory concept

## Exact Formulation

A traveler goes into the past and kills his grandfather before his father is conceived. Then the traveler is not born—and there is no one to go into the past and kill the grandfather; the grandfather lives, the traveler is born, sets off, kills… A successful murder cancels the murderer; a canceled murderer cancels the murder. Every version of events refutes itself.

## Origin

The knot’s name came from science fiction: the dispute over the “murderous grandson” was already raging in readers’ letters to the pulp magazines at the turn of the 1920s and 1930s, and the classic scene was given by Barjavel (*Le Voyageur imprudent*, “The Imprudent Traveler,” 1943). Then the question became scientific on both sides. Physics: Gödel (1949) presented a solution of the equations of general relativity with closed timelike curves—the question of “travel into the past” ceased to be purely verbal; Novikov formulated the self-consistency principle; Hawking answered with the chronology protection conjecture (1992); the problem of a billiard ball flying into its own past was taken up seriously by Thorne’s school. Philosophy: Lewis (“The Paradoxes of Time Travel,” 1976) laid bare the ambiguity of the word “can”—the traveler *can* kill his grandfather in the sense of abilities (hands, a weapon, the grandfather in his sights) and *cannot* in the sense of compatibility with the facts: the year in which he has arrived already contains a grandfather who survived.

## Consequence

The knot became a touchstone for the concept of time. It produced a family: the predestination loop (an object or a piece of information without a source—the traveler hands his younger self the blueprint of the time machine: the blueprint has no author), the casuistry of “changed” biographies, the physical program of research into closed curves. The main consequence, though, is a watershed between questions: the logical one (can there be contradictory histories?—no, and this is settled) and the physical one (does the world admit causal loops?—open). Logic leaves room for journeys; it leaves no room for contradiction—and the story of the grandfather breaks exactly this, not a limit set by technology.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the traveler, the machine, the grandfather, the murder, the birth. Structure: an action is directed against the causal chain that leads to the action itself. Signal: the self-undermining is visible at once.

**Domain 2—Clarification: what do the terms mean?** “To change the past”—what is it? The past is what has happened; to change it is to make what has happened not have happened: A and not-A about one fact. Next to this stands Lewis’s ambiguity: “to get into the past” and “to change the past” are different concepts, and “can kill” splits between ability and compatibility with the facts. Signal: the premise of the scenario carries a contradiction within itself.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here is the defect. The scenario takes time in the framework of space: the past is a place where one can come and rearrange things. But the past is not a stage; it is the accomplished part of the causal order, and this order is strict: the ground comes before the consequence, and an event is never its own ancestor. The framework of an “editable past” brings a false premise into the very formulation. Signal: the acyclicity of the causal order is violated by the condition of the problem.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** flawless—and this is the key: from the premise “the past is changeable” a contradiction has been correctly derived. Before us is not a riddle but a ready-made reductio ad absurdum of the premise.

**Domain 6—Reflection:** every version of events cancels itself—signal: reject the premise; return to domain 3.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection: time taken as space). **Type:** defective—false premise: “the past is changeable.” **Violated laws:** [[Non-Contradiction]]—a fact both happened and did not happen; [[Order]]—the causal order is strict: an event that removes its own cause would be its own ancestor. **Essence of the defect:** the scenario requires a consequence to stand before its ground. On the E/R/R triad: the Rule of the causal order is acyclic—the scenario requires an Element that is its own ancestor.

## Why There Is No Paradox

Three layers, from logic to physics. The first is to read the story as a proof: the chain “killed the grandfather → was not born → did not kill” is a correct derivation of a contradiction from the premise of a changeable past; the premise is false, and that is all the story proves. The second is to separate Lewis’s senses: by abilities, the traveler can kill; given the facts as a whole, he cannot; the contradiction lives only when the two “cans” are confused. Arrival in the past *without change* is a self-consistent history: the traveler was always there in that year and always missed—nothing in this runs against logic; Novikov’s “self-consistency principle” is precisely non-contradiction, read off histories with a loop. The third is to give physics its own question: whether closed timelike curves exist is a matter of equations and observations (Gödel showed that the theory admits them; Hawking conjectured chronology protection), but whatever physics answers, there will be no contradictory histories: “changing what has happened” will not come back in any of them. In the formal base the causal order is derived as strict and acyclic—an event is never its own ancestor, and this is the same constraint of the vertical that blocks [[Russells Paradox|Russell]]: “its own ancestor” is the causal dress of “its own element.”

## Lesson

**On invisible premises.** “I can change the past” looks like a detail of the scenario, yet it carries a contradiction: check the setting—a defect likes to hide in the scenery. **On the ambiguity of “can.”** Ability and compatibility with the facts are different modalities; confusing them is the motor of half the disputes about freedom and fate. **On separating questions.** The logical question is settled (there are no contradictory histories), the physical one is open (whether there are loops)—confusing the two questions makes the settled one open. **On the kinship of constraints.** The acyclicity of the causal order is the same hierarchical vertical as in set theory: the knots of different sciences are held by one law.

## Kin by Mechanism

[[Russells Paradox|Russell]] (machine-recorded kinship: a single rule against the reflexive loop), the predestination loop (bootstrap: an object without an origin—the second trouble of the same framework), [[Newcombs Paradox|Newcomb]] (an action that “influences” what is already fixed), Polchinski’s billiard ball (the physical form of the knot).

**Machine check.** There is a named analysis: src/foundation/ObserverSystemTime.v—`no_causal_loop` (the causal order is acyclic: an event is never its own strict ancestor; the grandfather loop is blocked by the same irreflexivity P1 as Russell and Cantor—this is how the file records it), `proper_irreversible` and `cannot_move_back` (proper time is irreversible), the summary `observer_system_time`. In the registry of 46 it is `D12_Grandfather`: the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
