---
title: "Lottery Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Парадокс лотереи.md"
sourceBlob: 085d31324fd339cb04b4784d7562b6df7c7fb2a3
translated: 2026-10-20
status: draft
description: "Belief in the individual ≠ belief in the conjunction"
---

**N.5** · [[Non Paradoxes|non-paradox]] · subtype: Epistemic Peculiarity

**Essence of the error.** Belief in the individual ≠ belief in the conjunction

## Exact Formulation

A fair lottery: a thousand tickets, exactly one wins. About any ticket it is rational to hold: “this one will not win”—the chance of being wrong is one in a thousand. But if it is rational to believe this of the first, the second, … the thousandth ticket, then, gathering the beliefs together, we get “no ticket will win”—while the opposite is known for certain: some ticket will win. Beliefs that are rational one by one add up to an irrational one together.

## Origin

Henry Kyburg, *Probability and the Logic of Rational Belief* (1961)—the knot was built on purpose, as a test of the concept of rational acceptance: can everything that exceeds a probability threshold be counted as a “belief”? Four years later Makinson presented a twin from life—the [[Preface Paradox|preface paradox]]—and the pair became a standard proving ground of epistemology: theories of acceptance, of knowledge, and of the aggregation of beliefs are tested on it. The camps formed quickly: Kyburg sacrificed the closure of beliefs under conjunction; the Bayesian line sacrificed binary “acceptance” itself (there are only degrees of confidence, and no threshold of “now I believe”); others make the threshold contextual. The dispute is alive, but the nature of the knot is clear and indisputable—and it is not paradoxical.

## Why This Is Not a Paradox

In the probabilities everything is consistent, to a hair: P(ticket i loses) = 999/1000 for every i, P(all lose) = 0—both estimates are correct and compatible; probability theory is built exactly so: a conjunction of highly probable propositions need not be highly probable. The “contradiction” appears only when an external step is added—binarization: the rule “probability above a threshold → accept it as a belief” plus the habit of combining what has been accepted by conjunction. The triad “threshold acceptance + closure under conjunction + consistency” is incompatible—this is not a paradox but a theorem about the price of quantization: rounding degrees to “yes/no,” one loses precisely the information that held the coherence. The defect lies in the expectation that threshold belief behaves like knowledge.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: tickets, probabilities, a threshold of acceptance, the operation of conjunction, the certain “one will win.” Signal: a graded scale and binary beliefs in one story.

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “To believe rationally”—what is that? If it is a degree of confidence of 0.999—everything is consistent, and there is no paradox. If it is a binary “accepted” by a threshold—then it is a different object: a rounding of the degree, and it does not inherit the properties of the degree (coherence under aggregation). Signal: two senses of “belief” are glued together.

**Domain 3—Framework Selection:** the logic of belief (closure under conjunction is a property of knowledge) is applied to threshold acceptances—an instrument of knowledge on an object that is a rounding.

**Domain 4—Comparison:** instructive: a thousand beliefs of one type, “at 0.999 each”—and their aggregate is “0”—a property not preserved under aggregation, a statistical relative of [[Simpsons Paradox|Simpson]].

**Domain 5—Inference:** every step is honest; the triad of premises about acceptance is incompatible—and exactly one of them must be given up.

**Domain 6—Reflection:** “the rational adds up to the irrational” is a signal: check the operation of adding up; a return to domain 2.

## Diagnosis

**Category:** non-paradox—an epistemic peculiarity. **Location of the defect:** expectation—that threshold acceptance is closed under conjunction, like knowledge. **No law is violated:** the probabilistic layer is coherent; the incompatibility lives between three conventions about “acceptance.” On the E/R/R triad: the degree of confidence is a graded Role on the Element-ticket; “to accept” is a binary Rule of threshold; conjunction is an operation that the Rule of threshold does not survive: a property of single applications is carried over to the aggregate.

## Resolution

The computational layer: the probability that “none of the thousand wins” in a fair lottery is exactly zero—the conjunction is defined and certainly false; there is no tension in the probabilities themselves. The conceptual layer is a choice of which premise to give up. The Bayesian move: give up binary acceptance—beliefs are degrees, “I believe the ticket will not win” means “I am 0.999 confident,” and degrees combine by the rules of probability, not by conjunction: irrationality arises nowhere. Kyburg’s move: keep acceptance, give up closure—beliefs accepted by a threshold do not combine freely; honest, but costly: “I believe A” and “I believe B” without the right to “I believe A and B.” The common upshot of both moves is one: threshold belief is not a lesser kind of knowledge; knowledge is closed under conjunction because it stands on grounds, not on frequency; rounding a degree up to “yes” adds no grounds. The difference between belief and knowledge by status is a theme of our own: see the section on the status of belief on the page [[Truth and Absolute Truth]].

## Lesson

**On quantization.** Rounding the graded to the binary is a loss of information, and aggregates of roundings lie: compare the sorites—there the threshold is on a heap of sand, here on a scale of confidence. **On closure.** Closedness under conjunction is a privilege of knowledge, not of every “rational belief”; check what has paid for an “I believe” before adding it up. **On the status of the knot.** No contradiction in the world or in the probabilities—what is incompatible are conventions about the word “accept”; the choice of a convention is a matter for theory, not a riddle of being.

## Kin by Mechanism

[[Preface Paradox|The Preface]] (Makinson’s twin: the same triad in the setting of authorial modesty), [[Simpsons Paradox|Simpson]] (a property not preserved under aggregation), [[Sorites Paradox|the Sorites]] (a threshold on a graded scale—a structural relative), [[False Positive|False positives]] (a neighbor in the category: the price of substituting probabilistic quantities).

**Machine check.** In the registry of 46—`N5_Lottery`: category `NonParadox`; the status of the category is formalized (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v). The computational core is exact Q-arithmetic (999/1000 per ticket, 0 for the conjunction with “exactly one win”)—a candidate for the “Probability” branch; the incompatibility of the triad of premises about acceptance is a candidate for a three-line formalization (see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
