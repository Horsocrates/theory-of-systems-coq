---
title: "Monty Hall Problem"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Проблема Монти Холла.md"
sourceBlob: 00061ef35a8e9ee76431e7129a4bead67a8c3c02
translated: 2026-10-20
status: draft
description: "A correct result: switching pays (2/3)"
---

**N.1** · [[Non Paradoxes|non-paradox]] · subtype: Counterintuitive Result

**Essence of the error.** A correct result: switching pays (2/3)

## Exact Formulation

Three doors: behind one is a car, behind two—goats. You choose a door. The host, who knows where the prize is, opens one of the two remaining doors—always one with a goat—and offers to switch your choice. Should you switch? Intuition insists: two doors are left, the chances are 50/50, switching is pointless. The correct answer: switch—the switching strategy wins with probability 2/3 against 1/3 for the strategy “stand your ground.”

## Origin

The name comes from Monty Hall, the host of the American television show *Let’s Make a Deal*. The problem in this form was posed by Selvin (1975); its ancestors are Gardner’s three prisoners problem (1959) and Bertrand’s boxes (1889). Worldwide fame came with Marilyn vos Savant’s column in *Parade* (1990): her answer “switch” provoked some ten thousand letters, among them hundreds from holders of academic degrees, confidently and indignantly demanding that she “correct the error.” Erdős—by the testimony of contemporaries—did not accept the answer until he saw a computer simulation. The history of the problem’s reception became its second essence: before us is not a defective problem but a reference measurement of the strength of false intuition.

## Why This Is Not a Paradox

What there is here is a conflict between a correct computation and the expectation of equiprobability; neither the condition nor the conclusion holds a contradiction. By the canon of the catalog a defect can sit in three places: in the construction, in the premises, in expectation; here it is in expectation. The problem is honest; the answer “2/3” is provable by enumeration, by a tree of outcomes, and by simulation—the “paradoxicality” lies entirely on the side of the reader, who applies the principle of indifference (“two doors—so equal chances”) where the doors are not on an equal footing: one was chosen blindly, the other survived a selection by an informed host. The host’s move is not a random opening but an action by a rule that depends on where the prize is—and therefore it carries information.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: three doors, a prize, your choice, an informed host, the rule “always open a goat among the remaining doors,” the offer to switch. Signal: the rule of the host’s behavior is a part of the condition that intuition throws out first.

**Domain 2—Clarification: what do the terms mean?** “The host revealed a goat”—what kind of event is that? Not an observation of chance but a move by a rule that uses knowledge of the prize: a filter. “Chances 50/50” is a predicate of situations about which nothing is known beyond the number of outcomes; here much is known. The defect of expectation: the asymmetry of the doors has been erased.

**Domain 3—Framework Selection:** the principle of indifference is an instrument for indistinguishable outcomes; the doors are distinguished by their history: a blind choice against one that survived a selection. The framework “two doors—equal chances” does not fit the object.

**Domain 4—Comparison:** an honest comparison of the strategies: “stay” wins when the first choice is right—1/3; “switch” wins when it is wrong—2/3.

**Domain 5—Inference:** the computation is correct and can be checked by three independent paths. The fault does not lie in the problem.

**Domain 6—Reflection:** ten thousand indignant letters are a signal not of a defect in the problem but of the strength of expectation; the honest move of reflection is simulation: let the world judge.

## Diagnosis

**Category:** non-paradox—a counterintuitive result. **Location of the defect:** expectation, not the problem: a false application of the principle of indifference to unequal informational positions. **No law is violated.** On the E/R/R triad: intuition counts Elements (doors), ignoring the Rule (the host’s informed selection)—and probability lives on the Rule: an event passed through a filter testifies about the filter.

## Resolution

Enumerating the cases settles the question. The prize is behind your door (probability 1/3)—switching loses. The prize is behind the second door—the host is forced to open the third, switching wins. The prize is behind the third—the host opens the second, switching wins. Two cases out of three favor switching: 2/3. A help for intuition—a hundred doors: you have chosen one, the host has opened ninety-eight goats and left one door closed; should you switch? Your door was worth 1/100 at the moment of the blind choice—the remaining one has absorbed 99/100. A control twist, showing exactly where the information lives: let the host *not know* where the prize is, and let the door opened at random turn out to hold a goat—then the chances really are 50/50; the whole difference between 2/3 and 1/2 lies in the rule of the move, not in the picture of “two closed doors.” Simulation was enough for Erdős; it is available to every disputant.

## Lesson

**On information.** An event selected by a rule carries information about the rule; “the same” observation under a different rule of the move is worth different probabilities. **On the principle of indifference.** “Equal chances” is the privilege of indistinguishable outcomes; outcomes distinguished by history and by a filter are not worth equal chances. **On the status of the category.** The counterintuitive is not the paradoxical: truth can be unexpected; indignation is not an argument, simulation is.

## Kin by Mechanism

The three prisoners problem (Gardner—the same mechanism in a prison setting), Bertrand’s boxes (an ancestor), [[False Positive|False positives]] (the same blindness to informational structure—to the base rate), [[Birthday Paradox|Birthdays]] (a neighbor in the category: computation against expectation).

**Machine check.** In the registry of 46—`N1_MontyHall`: category `NonParadox`, with a note in the entry itself—“Intuition misleads”; the status of the category is formalized: `nonparadox_46_not_paradox` (a non-paradox needs no laying open—there is nothing to lay open), the count `nonparadox_count_8` (ParadoxDissolution.v). There is as yet no named probabilistic computation of 2/3 in the base—a candidate for formalization for the “Probability” branch (see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
