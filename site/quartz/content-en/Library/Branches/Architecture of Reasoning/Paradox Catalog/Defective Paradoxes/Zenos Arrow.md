---
title: "Zeno’s Arrow"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Стрела Зенона.md"
sourceBlob: 3a1bbda1b94c1e8b0033e86bbf2853cd55b0c0bf
translated: 2026-10-20
status: draft
description: "Motion is not a sequence of rests"
---

**D.15** · [[Defective Paradoxes|defective paradox]] · subtype: False Premise

**Essence of the error.** Motion is not a sequence of rests

## Exact Formulation

The flying arrow is at rest. At every instant it occupies a place exactly equal to itself; what occupies a place equal to itself does not move; so at every instant of the flight the arrow does not move. The time of the flight is composed of instants—at each of them the arrow is at rest—so the arrow is at rest throughout the flight. There is no motion.

## Origin

The third aporia of motion from Aristotle’s *Physics*—and the deepest: [[Zenos Achilles|Achilles]] and the [[Zenos Dichotomy|dichotomy]] cut the path, while the arrow cuts time—to the limit, down to the instant—and asks: where in the instant is the motion? Aristotle answered by rejecting the premise: time is not composed of indivisible “nows,” and in a “now” there is neither motion nor rest. The modern age added analysis: instantaneous velocity is defined as a limit over a neighborhood of a point. Russell (*The Principles of Mathematics*, 1903) carried the separation through to the end with the “at-at” theory: motion just is the occupying of different places at different moments—nothing over and above this correspondence, no “state of motion” within an instant, is required. Bergson objected from the other side: motion is indivisible, and slicing it into instants is a cinematographic device of the intellect; the dispute over which is primary—the process or the slice—is alive to this day. The aporia’s name migrated into physics: the quantum Zeno effect (frequent measurements hold a system in place)—a kinship in name only; the subject is a different one.

## Consequence

The arrow posed the question more precisely than its sisters: not “how many parts does the path have,” but **what is the bearer of motion**. The answer forged over twenty-three centuries: the bearer is the correspondence of moments and places, not a single moment. Hence a legacy along three lines. Mathematics: the derivative is a limit concept, that is, a concept of neighborhoods; even “velocity at a point” is defined through intervals around the point—science did not find motion within the instant; it stopped looking for it there. Philosophy: the distinction between the properties of a slice and the properties of a process—a property of the whole need not live in each part. Culture: cinema—twenty-four motionless frames per second represent motion without containing it; Zeno’s arrow spins in every film projector.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the arrow, the flight, instants, places, the predicates “moves”/“is at rest.” Structure: a property of the flight is derived from the properties of instantaneous slices. Signal: the word “is at rest” is applied to an instant.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. Rest is the same place at *different* moments; motion is different places at different moments. Both predicates concern a relation of moments; both require an interval as their bearer, not a point. “The arrow is at rest in an instant” applies a predicate of intervals to a point—categorially empty, like a question about the color of a number. The instantaneous slice of a flying arrow and of a hanging one is the same—and this is not a discovery about the arrow but the definition of a slice: a slice is not a bearer of motion. Signal: a substitution of the bearer of a predicate.

**Domain 3—Framework Selection:** the second, main layer of the defect: the instrument—the instantaneous slice—does not fit the object. Motion is a relation between slices; to look for it inside a slice is to look for a melody in a single note. Motion cannot be “assembled” from slices, not because there is no motion, but because it lives not in the slices but in their correspondence.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** flawless, given the accepted premises. The problem is not in the inference.

**Domain 6—Reflection:** the arrow reaches its target—signal: the premises need checking; return to domains 2 and 3.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection: the slice as an instrument for a process); the primary substitution is in Domain 2 (the bearer of the predicate). **Type:** defective—false premise: “what occupies a place equal to itself is at rest”—rest is undefinable at a point. **Violated laws:** [[Identity]]—“to be in a place” (a point predicate) is replaced by “to be at rest” (an interval predicate): different concepts are glued together; a property of a process is demanded of each of its slices. **Essence of the defect:** motion is sought inside an Element-slice, whereas it is a Rule of correspondence between slices; not finding the Rule inside the Element, Zeno declared the Rule nonexistent. On the E/R/R triad, exactly this: the flight is a Rule (moment → place), and in a single Element it is absent by construction.

## Why There Is No Paradox

Separating the predicates does all the work. Rest and motion are predicates of pairs of moments; in a single instant there is neither one nor the other—not because the arrow has “frozen,” but because the question has not been posed: a snapshot does not answer questions about change. “Motion cannot be assembled from rests” is true, but there is nothing to assemble either: there are no instantaneous “rests”—there are places-at-moments, and their correspondence *is* the flight; a property of a process lives in the rule of correspondence, which is why it cannot be found in a slice—like a melody in a note, like meaning in a single letter. To Aristotle belongs the priority of the rejection: time is not composed of “nows” as a wall is of bricks. To Russell belongs the purity of the result: motion is at-at, being there at that time, and nothing over and above; analysis merely gave this the form of a limit—even instantaneous velocity is an interval concept in the dress of a limit. The process base carries the laying open down to the structure itself: a process is given as a correspondence of step and value (`nat → Q`), a state is a step, velocity is the difference of neighboring steps; in a single step there is no motion by construction, and the arrow in this framework is not a paradox but the first property of any process. Bergson’s truth we will also keep honestly: slices are a device of description; a description is free to cut, while motion is whole.

## Lesson

**On the bearer of a predicate.** Every predicate has its own bearer: an interval or a point, a process or a slice; changing the bearer without checking is a category mistake, and the arrow is its purest specimen. **On slices.** A slice does not carry a process: frames represent motion without containing it; the stillness of a slice is a property of the slice. **On looking in the wrong place.** “Not found in the slice” does not mean “does not exist”—it means the search was in the wrong place: motion is in the rule of correspondence, not in the element.

## Kin by Mechanism

[[Zenos Achilles|Zeno’s Achilles]] and [[Zenos Dichotomy|Zeno’s Dichotomy]] (sisters in the block: there the path is cut, here time), [[Thomsons Lamp|Thomson’s Lamp]] (the demand for a state where it is not defined—kin by the substitution of the bearer), the cinematographic illusion (frames represent motion without containing it), the quantum Zeno effect (a kinship in name).

**Machine check.** The process structure that lays the aporia open is the core of the base: `RealProcess := nat -> Q` (src/process/ProcessCore.v, P4)—a state is a step, motion is a rule of correspondence between steps, and in a single step there is no motion by construction. In the registry of 46 it is `D15_ZenoArrow`: the field `InstrumentObjectMismatch` (“the instrument does not fit the object”—a slice against a process), the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
