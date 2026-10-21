---
title: "Horse Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс лошадей.md"
sourceBlob: b2bfee8bec8310b3eabf9c52e49dfda41eba4e75
translated: 2026-10-20
status: draft
description: "An error in the base case of the induction at n=1"
---

**D.18** · [[Defective Paradoxes|defective paradox]] · subtype: Error in Reasoning

**Essence of the error.** An error in the base case of the induction at n=1

## Exact Formulation

Theorem: all horses are of one color. Proof—by induction on the number of horses. Base: one horse is of one color with itself—true. Step: suppose any n horses are of one color; take n+1 horses. Removing the first, we get n horses—of one color by hypothesis; removing the last instead—another n, also of one color. The horses that belong to both groups link them: the color of the first group equals the color of the common horses, and that equals the color of the second. So all n+1 are of one color. By induction, all the horses in the world are of one color.

## Origin

A classroom joke with a precise address: Pólya analyzed it in *Induction and Analogy in Mathematics* (1954) as a model false proof. The genre is older—“proofs” that 1 = 2 by a hidden division by zero, “all triangles are isosceles” by a crafty drawing (in Rouse Ball)—but the horses became the canon of courses on mathematical induction: an example on which the student must find the hole himself. In the catalog the knot represents the purest subtype: the premises are sound, the concepts are clear (“color” is sharp enough—this is not the [[Sorites Paradox|sorites]]), and it is the move itself that is false.

## Consequence

The knot’s lesson concerns the quantifier in the proof of the step: “let n be arbitrary” obliges the reasoning to work for *every* n, including the smallest ones; a picture drawn for a large n tacitly presupposes what a small n does not have. Hence its direct practical kin: edge cases in mathematics (inductions requiring two bases; recursions with a special first step) and in programming—off-by-one errors, empty lists, degenerate inputs: half of real failures are the horse paradox in code. And a contrast that clarifies both knots: the sorites breaks induction with an unfit concept—the step is approximate everywhere; the horses break it with a pinpoint hole—the step is strict everywhere except one link. These two ways are enough to bring everything down.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the base, the inductive step with two groups, the conclusion. Signal: the conclusion is empirically false—a black horse and a white one stand side by side; there is a hole somewhere in the proof.

**Domain 2—Clarification: what do the terms mean?** The terms are clean: “color,” “group,” “common horses”—everything is defined. The defect is not here—and this distinguishes the knot from its neighbors in the catalog.

**Domain 3—Framework Selection:** induction is a legitimate instrument for sharp properties; the framework is correct.

**Domain 4—Comparison: how is it carried out?** Here is the defect. The bridge of the step is a comparison of the two groups through common members: the color of the first = the color of the common ones = the color of the second. But at n = 1 the two groups—one horse each—**do not overlap**: there are no common members, the comparison through them is not carried out, and the bridge hangs in the air. The reasoning tacitly assumes n ≥ 2. Signal: the comparison is announced, but at the boundary it does not exist.

**Domain 5—Inference:** all the transitions for n ≥ 2 are honest; exactly one is false—from one horse to two. One is enough.

**Domain 6—Reflection:** a false conclusion from a “rigorous” proof—signal: run the step on the smallest n; return to domain 4.

## Diagnosis

**Domain of the error:** Domain 4 (comparison—a bridge across an empty intersection). **Type:** defective—error in reasoning: the inductive step does not cover the boundary. **Violated laws:** [[Sufficient Reason]]—the transition 1 → 2 is grounded by nothing: the linking comparison rests on nonexistent common members. **Essence of the defect:** “for arbitrary n” has been proved only for n ≥ 2; a single uncovered link—and the whole conclusion hung on it (which is why the hole is often described as a “defect of the base”: the induction has no support at the first transition—one reckoning, different names). On the E/R/R triad: the Rule (the step) is claimed for all Elements but built for only a part of them—a Rule with a hole at the boundary.

## Why There Is No Paradox

A run at n = 1 lays everything bare. Two horses: remove the first—the second “group” is of one color with itself; remove the second—so is the first; but the groups have no common horse—the colors of the two groups are linked by nothing, and there is nothing from which to conclude “both horses are of one color.” The bridge across the intersection exists only for n ≥ 2—and the proof never gets there: to use the transitions 2 → 3 → 4 → …, one must first have P(2), and the whole weight of the world rests on the impossible transition 1 → 2. The counterfactual check is instructive too: if someone honestly proved that *any two* horses are of one color, the induction would then run flawlessly; the whole falsity of the “theorem” is concentrated in one link, and it can be found only by running the step on the smallest value. This is the rule of hygiene that the knot bequeathed: a proof “for arbitrary n” is checked on the smallest n that the formulation allows.

## Lesson

**On the bounds of a quantifier.** “Let n be arbitrary” is a promise that must be kept at n = 1 as well; a picture for a large n is not a proof for all. **On the price of a link.** Induction is a chain: one hole brings everything down, and the rigor of the other links does not redeem it. **On the two breakdowns of induction.** An unfit concept (the sorites) and a holed step (the horses) are different diseases with different treatments: there, the rejection of the instrument; here, a repair or an honest renunciation of the “theorem.” **On practice.** An empty list, a zero index, a single element—run reasoning and code on the degenerate case first.

## Kin by Mechanism

[[Sorites Paradox|Sorites]] (a contrast: induction on an unfit concept versus a holed step), “proofs” that 1 = 2 (a hidden division by zero—the genre of false proofs), “all triangles are isosceles” (a defect of the drawing), [[Two Envelopes]] (a neighbor by subtype: a defect in the move itself, with sound premises).

**Machine check.** In the registry of 46 it is `D18_Horse`: the field `ConceptualAmbiguity`, the level `L2_Operations`, the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). There is no named analysis—the defect is made explicit by running the step at n = 1. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
