---
title: "Ross–Littlewood Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс Росса-Литтлвуда.md"
sourceBlob: 5c4bd02070add685f9742e778105a7fdbc63af60
translated: 2026-10-20
status: draft
description: "Infinite operations do not commute"
---

**D.25** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** Infinite operations do not commute

## Exact Formulation

A minute before noon, balls numbered 1–10 are put into a vase and ball 1 is taken out. Half a minute before—balls 11–20 are put in, ball 2 is taken out. A quarter of a minute before—21–30 are put in, ball 3 is taken out… The steps speed up, and by noon infinitely many of them have been performed. How many balls are in the vase at noon? The count: each step adds nine—by noon, infinitely many. The fates: ball n is taken out at step n and not returned—no ball remains: the vase is empty. Infinitely many—and zero.

## Origin

Littlewood tossed off the problem in a single note in *A Mathematician’s Miscellany* (1953)—as a “paradox of infinity”; Ross developed it in a probability textbook (1988), adding a stinging variation: if at each step a ball is taken out *at random*, the vase is empty at noon with probability one. The literature split into three camps—“empty” (the elementwise limit: every ball is taken out), “infinite” (the count: more has arrived than has left), “the question is underdetermined”—and this dispute became the final exhibit of the supertask genre: here, unlike the [[Thomsons Lamp|lamp]], it even seems that there is an answer—and so it is all the more instructive to see where that answer actually comes from.

## Consequence

The knot’s main lesson is non-commutativity: the limit of the number of elements and the number of elements of the limit are different quantities, and their equality is a privilege of the finite. The second lesson is dependence on order: at each step take out not the smallest number but the largest—and at noon the vase is infinite (no one has touched any of the small numbers); the same balance of “plus ten, minus one”—the opposite “outcome.” So the outcome of a supertask is not a function of the balance: “how many were put in and taken out” does not determine “what remains” when there are infinitely many steps. The practical shadow of the lesson is every interchange of a limit with another operation (a sum, a count, an integral): on the infinite it requires a separate warrant, and half of the false “miracles” of analysis are interchanges without warrant.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the vase, numbered balls, a series of steps “add ten—take out one,” noon, the question “how many.” Signal: a question about a moment outside the series—as with the lamp.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “How many balls at noon” glues together two different questions. The first: what is the limit of the *quantity*? The process of the quantity—9, 18, 27, …—grows without bound: there is no limit (“∞” is jargon for divergence, not a value). The second: what is the *fate of each ball*? Ball n is taken out at step n and not returned—the fate of each converges to “outside the vase.” The answers “∞” and “0” answer different questions—there is no more contradiction between them than between the growth of a list and the emptiness of its intersection. Signal: one word, “how many”—two processes.

**Domain 3—Framework Selection:** a second layer: the tacit interchange of limit and count—“the number of elements in the limit = the limit of the number of elements”—is illegitimate on the infinite; an instrument of finite computation has been carried over without warrant.

**Domain 4—Comparison:** telling: “∞ versus 0” compares answers to different questions—a comparison without a common framework.

**Domain 5—Inference:** both lines are honest, each within its own question. The problem is not in the inference.

**Domain 6—Reflection:** the outcome changes with the order of removal while the balance stays the same—signal: the “outcome” is not determined by the condition but brought in by convention; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—indeterminacy: the question does not distinguish the limit of the number from the number of the limit. **Violated laws:** [[Identity]]—“how many at noon” serves two different questions; [[Sufficient Reason]]—the value “at noon” is not set by the series: noon is not a step, and the answer requires a convention of continuation. **Essence of the defect:** an illegitimate interchange of two operations—passage to the limit and counting. On the E/R/R triad: the process of the quantity and the processes of the balls’ fates are different Rules; the outcome of one is passed off as the outcome of the other.

## Why There Is No Paradox

Separating the questions does the main work. The limit of the quantity: the process 9, 18, 27, … diverges—it has no limit value, and the answer “infinitely many” is honest only as a description of growth, not as a state. The composition: for each n, ball n left the vase at step n for good—no fate leads to “remaining”; if the composition at noon is completed by the elementwise limit, the vase is empty. The answers do not dispute each other: the limit of the number of elements need not equal the number of elements of the limit—on the infinite these operations cannot be interchanged, and the knot stays alive exactly as long as the belief in the interchange lasts. The order variation drives the lesson home: by taking out the largest numbers we get an infinite composition with the same balance—“what remains” is determined by fates, not by bookkeeping. There remains the status of the answer “empty”—and here honesty matters more than victory: noon is a moment outside the series, as with the lamp; but unlike the lamp, where the states toss about and do not converge, here the fate of each ball converges—so the elementwise completion is singled out by the problem itself, and “empty” is the best of the answers; its status, however, is a completion of converging fates, not a conclusion from the series: the condition itself is silent about noon. Ross’s probabilistic cherry crowns it all: with random removal, the fate of each ball is “sooner or later taken out” almost surely, and the vase is empty with probability one.

## Lesson

**On interchanging operations.** Limit and count (sum, integral, cardinality) do not commute on the infinite; every equality “limit of the aggregate = aggregate of the limits” requires a separate warrant. **On balance and fates.** Global bookkeeping does not determine the elementwise outcome: what remains is a question of fates, not of the net balance. **On the status of answers.** “Empty” is a completion by converging fates; “infinite” is jargon about divergence; the “paradox” is the gluing of two questions into one word.

## Kin by Mechanism

[[Thomsons Lamp|Thomson’s Lamp]] (a pair for comparison: there the fate-states do not converge—everything is underdetermined; here they converge—the completion is singled out), [[Hilberts Hotel|Hilbert’s Hotel]] (bookkeeping on the infinite), [[Galileos Paradox|Galileo]] (count against correspondence—the same pair of operations three centuries earlier), [[Zenos Dichotomy|Zeno’s Dichotomy]] (a moment outside the series), conditionally convergent series (rearranging the terms changes the sum—the arithmetical twin of the order variation).

**Machine check.** In the registry of 46 it is `D25_RossLittlewood`: the field `ConceptualAmbiguity`, the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). The process ground: a limit value is a predicate of a fundamental process (src/CauchyReal.v); the process of the quantity 9, 18, 27, … is not fundamental—“the limit of the quantity” has no bearer, whereas the fate of each ball is a converging (eventually constant) process: the difference between the two questions is visible in the base itself. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
