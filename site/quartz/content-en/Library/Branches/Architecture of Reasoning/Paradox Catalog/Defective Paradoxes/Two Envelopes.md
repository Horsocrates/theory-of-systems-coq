---
title: "Two Envelopes Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс двух конвертов.md"
sourceBlob: 581f95072b75e34b0cd962ffc0cbb6a887a52d46
translated: 2026-10-20
status: draft
description: "An incorrect application of expected utility"
---

**D.16** · [[Defective Paradoxes|defective paradox]] · subtype: Error in Reasoning

**Essence of the error.** An incorrect application of expected utility

## Exact Formulation

Two envelopes; one holds twice as much money as the other. You have taken one—without opening it, you are offered a swap. The reasoning: let my envelope hold X; the other holds 2X or X/2, each with probability 1/2; the expectation of swapping = (2X + X/2)/2 = 1.25X > X—swapping pays. But the same reasoning works for the second envelope too—and after the swap it repeats again: swap, swap, swap. A symmetric problem has produced an eternally one-sided recommendation.

## Origin

The ancestor is Maurice Kraitchik’s necktie paradox (1930s): two men argue over whose tie is more expensive, and the loser hands over his own; each considers the game advantageous—“I risk my own, and I can win a more expensive one.” Gardner popularized the problem in the form of the wallet game; Nalebuff fixed the envelope form together with its name (“The Other Person’s Envelope is Always Greener,” 1989). Then came a path rare for a puzzle: a serious Bayesian literature (Zabell, Broome, and dozens of others), which laid bare the layered structure of the defect—from a simple substitution of a variable to subtle questions about distributions with infinite expectation, where the knot meets the St. Petersburg paradox.

## Consequence

A textbook specimen of two things. For probability theory—that “let my envelope hold X” is not a harmless phrase: a letter introduced before the hypotheses are distinguished glues different worlds into one formula. For decision theory—that a conclusion that breaks the symmetry of a problem exposes itself: if the problem does not distinguish the envelopes, no correct calculation can prefer one to the other. The practical progeny is the hygiene of conditional expectations in statistics and finance: an expectation can be computed only under a fixed condition, and “equally probable for any observed value” is a strong assumption about the prior distribution, most often an impossible one.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: two envelopes, the ratio 1:2, a choice, the option to swap. The structure is symmetric: the problem does not distinguish the envelopes. Signal: the recommendation “swap” is one-sided—the symmetry has already been broken somewhere in the calculation.

**Domain 2—Clarification: what do the terms mean?** “X”—what is it? The contents of my envelope are not a number but a quantity that depends on which of two hypotheses is true: the sums in the pair are A and 2A; “I have the smaller one”—X = A; “I have the larger one”—X = 2A. The first signal: one letter serves two different quantities.

**Domain 3—Framework Selection:** expected utility is a legitimate instrument; the framework is chosen correctly. The defect lies further down—in the execution.

**Domain 4—Comparison: how is it carried out?** Here is the defect. The formula (2X + X/2)/2 compares “the other envelope” with “mine,” holding X as if it were constant—but in the term 2X the letter X means A (the hypothesis “I have the smaller one”), and in the term X/2 it means 2A (the hypothesis “I have the larger one”). The comparison is carried out in a floating unit: quantities from two incompatible worlds are added, and the sum means nothing. The list of the comparison has been filled illegitimately. Signal: equivocation of a variable—the arithmetical dress of a substitution of terms.

**Domain 5—Inference:** flawless, given the accepted calculation; the damage was introduced a step earlier—in the comparison.

**Domain 6—Reflection:** “swap forever” and the broken symmetry—a double signal; return to domain 4.

## Diagnosis

**Domain of the error:** Domain 4 (comparison). **Type:** defective—error in reasoning: an incorrect application of expected utility. **Violated laws:** [[Identity]]—X must mean one quantity throughout one calculation, yet it means two; [[Non-Contradiction]]—a symmetric problem cannot give a one-sided recommendation. **Essence of the defect:** a conditional expectation is computed with the conditions glued together: values from different hypotheses are added as values of one. On the E/R/R triad: the Rule of comparison (expectation) is applied to an Element “X” that changes its referent between the branches—a comparison in an unfixed framework.

## Why There Is No Paradox

The right reckoning is short. Name the sums honestly: the pair holds A and 2A. If I have the smaller one (probability 1/2), the swap brings +A; if the larger one (1/2), the swap brings −A. The expectation of swapping: (+A − A)/2 = 0. The symmetry is restored, the eternal swap has vanished—together with the illusion of “1.25X.” The trick formula has been laid open: it added 2X from the world where X = A to X/2 from the world where X = 2A—two letters under one name, two different quantities; the calculation is not about any world at all. The Bayesian layer finishes off the remainder: for “2X or X/2, equally probable” to hold *for any* X, one needs a uniform prior distribution over all scales of sums—there is no such distribution; under any honest prior, the conditional probability of “I have the smaller one” depends on the sum hypothetically seen, and the recommendation ceases to be one-sided. The honest boundary: there exist exotic distributions (with infinite expectation) under which the conditional “swapping pays” holds for every observed value—there the knot meets the St. Petersburg paradox: the arithmetic of infinite expectations does not transfer to decisions, and this is a separate lesson about the limits of the instrument, not a rehabilitation of the trick formula.

## Lesson

**On the names of variables.** One letter, one quantity for the whole calculation; the equivocation of a variable is the same substitution of terms as in sophisms, only in arithmetical dress, where it is harder to notice. **On symmetry as a detector.** A conclusion that breaks the symmetry of a problem exposes itself—check the calculation without introducing new entities. **On the conditions of expectation.** “Equally probable for any observed value” is not a turn of politeness but a strong assumption about the prior distribution; often there is no such distribution.

## Kin by Mechanism

The necktie paradox and the wallet game (direct ancestors—the same gluing of hypotheses), the St. Petersburg paradox (infinite expectations against decisions—the neighbor at the honest boundary), [[Newcombs Paradox|Newcomb]] (a neighbor in the workshop of decision theory—but there the defect is in the conditions, here in the calculation), the sophisms of term substitution in the [[Fallacy Catalog|fallacy catalog]] (equivocation—the verbal form of the same thing).

**Machine check.** In the registry of 46 it is `D16_TwoEnvelopes`: the field `ConceptualAmbiguity` (the split referent of X), the level `L2_Operations`, the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). There is no named analysis—the defect is made explicit by honest reckoning through A and 2A. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
