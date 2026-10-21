---
title: "Yablo’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Парадокс Ябло.md"
sourceBlob: 2117a16e4e20f37387b07a67d6697404545149d2
translated: 2026-10-20
status: draft
description: "Distributed self-reference through an infinite chain"
---

**S.9** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** Distributed self-reference through an infinite chain

## Exact Formulation

An infinite series of statements: S₁: “all Sₖ for k > 1 are false”; S₂: “all Sₖ for k > 2 are false”; and so on—each Sₙ says: “all the following ones are false.” Suppose some Sₙ is true: then all the following ones are false—in particular, Sₙ₊₁ is false; but Sₙ₊₁ asserts “all after n+1 are false,” and under our premise this is *correct*—hence Sₙ₊₁ is true: a contradiction. Hence every Sₙ is false. But then for any n, “all after n are false” is correct, that is, every Sₙ is true: a contradiction. And no statement mentions itself.

## Origin

Stephen Yablo, 1993, the note “Paradox without Self-Reference”: to build the liar’s trouble without letting any statement refer to itself—and thereby to test whether self-reference is the cause. A dispute about the honesty of the title began at once: Priest argued that self-reference is hidden in the general *scheme* of the series (“each Sₙ speaks about all the following ones” is a sentence about the scheme itself), while Sorensen defended the purity of the construction. The dispute continues—and this is the best indicator of the knot’s value: it forces us to specify what exactly gives rise to the liar’s family.

## Consequence

Yablo shifted the diagnosis of the whole family: if the trouble reproduces itself without a loop “about oneself,” then the loop is packaging, not the root. The root is **ungrounded evaluation**: a chain of judgments about truth-value that nowhere rests on content. In the liar the bottom is knocked out by a loop, in Yablo by endless postponement: each link evaluates the following ones, and none evaluates *anything*—a regress without a first ground. For formal semantics the knot became a touchstone of theories of groundedness; for our catalog it is a witness that the vertical of evaluation requires not “the absence of loops” but **a bottom**: somewhere evaluation must stand on content.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: an infinite series of statements; each carries an evaluation of the truth-value of *all the following ones*; not a single loop. Structure: evaluations always directed forward along an open series. No signal yet.

**Domain 2—Clarification: what do the terms mean?** The first signal is “all the following ones”: a quantifier over an infinite series taken as actual; each Sₙ is a judgment about a completed collection of the unfinishable. The second: the content of each link is *only evaluations*: there is not a single statement in the series about anything other than the truth-value of other links.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect—a double one. First: evaluation (level 2) makes up the entire content of what is evaluated (level 1)—as in the [[Liar Paradox|liar]], only the confusion is distributed: not a loop but a chain without a bottom—the evaluation never gets any content, a regress instead of a ground. Second: “all the following ones” takes an open series as a completed object—the same reification of the unfinishable as in [[Cantors Paradox|Cantor]] and [[Hilberts Hotel|Hilbert]]; a finite segment of the series gives no knot (the last link speaks of an empty “after”—it is true, and everything is settled).

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** both moves are flawless under the accepted premises. The problem is not in the inference.

**Domain 6—Reflection:** a contradiction without a single loop is a signal to revise the diagnosis of the family: a return to domain 3, to ungroundedness and the reified series.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion in a distributed form. **Violated laws:** Identity · Non-Contradiction (evaluation as the sole content of what is evaluated—along the whole chain) · Order (an open series taken as completed; the regress of evaluations has no bottom). **Essence of the defect:** ungrounded evaluation: a chain of judgments about truth-value without a single content, masked by infinity. On the E/R/R triad: Rules without Elements—the evaluations have nothing to evaluate.

## Why There Is No Paradox

By two cuts. The first is groundedness: evaluation is legitimate when, after a finite number of steps, it stands on content; Yablo’s chain by construction never does—its links express no judgments, there is nothing for them to be true *about*; “true/false” does not apply to them, as it does not apply to the liar. The second is reification: the knot lives only on an actually completed infinite series; as a process (any finite segment, open to continuation) it is settled trivially—the last link at hand is true of an empty tail. Both cuts are one vertical of the [[Order|Law of Order]]: evaluation stands a storey above content, and the outcome of the unfinishable is not an object. The dispute over “is there a hidden self-reference” is settled by the analysis: it does not matter—the trouble lies not in the loop but in ungroundedness, and the loop is only its shortest packaging.

## Lesson

**On the root of the family.** The liar’s family arises not from self-reference but from ungrounded evaluation: the loop is one particular case, the regress another. **On the role of infinity.** Infinity here is not a source but a mask: it hides the absence of a bottom, allowing each link to nod at the following ones. **On checking chains.** The diagnosis of the vertical asks not “does it refer to itself” but “does the evaluation stand on content”—the question works even where there is no loop.

## Kin by Mechanism

[[Liar Paradox|The Liar]] (the loop—the shortest packaging of the same ungroundedness), [[Currys Paradox|Curry]] (self-evaluation in a condition), [[Carrolls Tortoise|Carroll’s Tortoise]] (a regress without a bottom—in the justification of inference), [[Hilberts Hotel|Hilbert’s Hotel]] and [[Cantors Paradox|Cantor]] (the reification of an open series).

**Machine check.** There is no named analysis in the base—what is inherited is the mechanics of the liar (`liar_no_truth_value`—ParadoxDissolution.v) and the rule about processes against completed infinity (P4; `binary_processes_not_enumerable`—ProcessDiagonal.v); in the registry of 46 the knot is classified as structural, with a guarantee that the paradox does not form (`all_46_dissolvable`, `structural_46_dissolves`). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
