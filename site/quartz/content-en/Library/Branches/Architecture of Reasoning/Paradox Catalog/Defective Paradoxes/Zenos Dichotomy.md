---
title: "Zeno’s Dichotomy"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Дихотомия Зенона.md"
sourceBlob: 874017b2864277abaf6f4253d551867886ae9629
translated: 2026-10-20
status: draft
description: "Infinite division ≠ the impossibility of completion"
---

**D.14** · [[Defective Paradoxes|defective paradox]] · subtype: False Premise

**Essence of the error.** Infinite division ≠ the impossibility of completion

## Exact Formulation

To traverse a path, one must first traverse half of it; then half of the remainder; then half of the new remainder—and so on without end: the remainder is never exhausted, and the goal cannot be reached. There is also a second version, a sharper one: before traversing half, one must traverse half of the half, and before that, half of that half… The series has no first member—motion has nothing to start from. One aporia denies motion an end; the other denies it a beginning.

## Origin

The first of the four aporias of motion in Aristotle’s *Physics*—and the purest: [[Zenos Achilles|Achilles]] is the same mechanics dressed up as a race, while the dichotomy makes do with one walker and one segment. The historical frame is shared with Achilles—the Eleatic weapon against the thinkability of motion, Aristotle’s answer (divisible does not mean divided), the strict reckoning of the modern age; the full line is in the card on Achilles. The dichotomy’s own trace is the most famous series in mathematics: 1/2 + 1/4 + 1/8 + … = 1; its convergence is the school stage on which the aporia is played out and settled by reckoning.

## Consequence

The two versions bequeathed two different confusions. The progressive one (“never to arrive”) bequeathed the same one as Achilles: the boundary of the description was taken for the boundary of the motion. The regressive one (“never to begin”) added its own: a description without a first member demanded a “first act” of the process—and passed off the absence of a first member in the partition as the impossibility of a beginning. This move comes back to life wherever a “first step” is demanded of the continuous: a segment has no first point after zero—yet the line gets drawn; a process has no “first instant after the start”—yet processes go on. The heirs of both versions are the supertasks ([[Thomsons Lamp|Thomson’s Lamp]], [[Ross Littlewood|Ross–Littlewood]]): the question “what comes after all the steps?” mirrors the question “what comes before all the steps?”

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the path, the walker, the operation of halving, the series of remainders (or of predecessors), the goal. Structure: one motion is cut up into an infinite series of parts. No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “Never to arrive”: the series of half-remainders enumerates positions *before* the goal—the goal is not among the members by construction, and “not on the list” is passed off as “not reached.” “Never to begin”: the series of predecessors has no first member—a property of the partition; the premise “motion is obliged to execute the members of the description in order, starting from the first” is false: a partition is not a program for the run. Signal: properties of the description are transferred to the motion—in both versions.

**Domain 3—Framework Selection:** a second layer, shared with Achilles: an infinite list of parts is applied to one continuous process; there are as many parts as the description has cut—divisible does not mean divided.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** within the description it is honest: every remainder is positive, and the predecessors have no first member—true. What is false is the transfer to the motion. The problem is not in the inference.

**Domain 6—Reflection:** every step taken refutes “never to begin,” every arrival refutes “never to arrive”; signal: the description does not cover the event; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification)—primary; Domain 3—secondary. **Type:** defective—false premise: “the infinity of the parts of a description is an obstacle to motion” (in the progressive version, an infinite time; in the regressive one, an impossible beginning). **Violated laws:** [[Identity]]—a property of the partition (no last member / no first member) is ascribed to the path and to the motion. **Essence of the defect:** the boundary and the arrangement of the description are passed off as the boundary and the arrangement of what is described. On the E/R/R triad: the Rule of partition yields a series without an edge—and this edge, absent from the Rule, is declared absent from the Element (the motion).

## Why There Is No Paradox

The computational part could not be shorter: 1/2 + 1/4 + 1/8 + … = 1; the times of the parts decrease by the same geometry—the sum is finite; “never to arrive” is refuted by the limit. The diagnostic part matters more than the computational one. The progressive version: the goal is not a member of the series of remainders, just as one is not a member of the sequence 1/2, 3/4, 7/8…; arriving at the goal is an event of the motion, not the last element of a list, and so it owes nothing to the list. The regressive version: there is no “first step” *in the partition*, and only there; motion does not execute a list of parts—it traces the path, which the description is free to cut as it pleases, even into a series without a first member. To demand of a process the first element of an arbitrary partition is like demanding of a segment its first point after zero: there is none, and this is a fact about the structure of the continuum; it does not rule out drawing lines. The ground is a process ground, common to the block: division is potential—it is a process without completion, and none of its stages presents the motion with a bill; the motion is whole, and partitions belong to the description. The full derivation of the ground is in the card on [[Zenos Achilles|Achilles]].

## Lesson

**On the two edges.** A description may have neither a first nor a last member—and both are facts about the description; transferring them to the object is one and the same error from two ends. **On “beginning.”** On hearing “it cannot begin,” check: does the process lack a beginning—or does the chosen partition lack a first member? **On the purity of form.** The dichotomy is Achilles without the tortoise: take away the race, and you see the mechanism bare; reducing a problem to its pure form is half of laying it open.

## Kin by Mechanism

[[Zenos Achilles|Achilles and the Tortoise]] (the same mechanics with characters—the full analysis of the ground is there), [[Zenos Arrow|Zeno’s Arrow]] (the third aporia: the instant instead of division), [[Thomsons Lamp|Thomson’s Lamp]] and [[Ross Littlewood|Ross–Littlewood]] (supertasks: “after all the steps” mirrors “before all the steps”), [[Sorites Paradox|Sorites]] (a neighbor by the registry field: the instrument does not fit the object).

**Machine check.** The convergence of the halving series is a special case of what has been formalized: `geometric_series_cauchy` with r = 1/2, `series_limit` (src/SeriesConvergence.v); infinity as a process—`RealProcess := nat -> Q` (src/process/ProcessCore.v, P4). In the registry of 46 it is `D14_ZenoDichotomy`: the field `InstrumentObjectMismatch`, the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
