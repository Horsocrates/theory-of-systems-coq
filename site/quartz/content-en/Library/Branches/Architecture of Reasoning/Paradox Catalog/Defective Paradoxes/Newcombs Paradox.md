---
title: "Newcomb’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс Ньюкомба.md"
sourceBlob: 3785c7eac3220ef225034456d28e04e43be0b287
translated: 2026-10-20
status: draft
description: "A conflict between determinism (for prediction) and freedom (for choice)"
---

**D.11** · [[Defective Paradoxes|defective paradox]] · subtype: Hidden Contradiction

**Essence of the error.** A conflict between determinism (for prediction) and freedom (for choice)

## Exact Formulation

Before you are two boxes. Box A is transparent—it holds $1,000. Box B is opaque—it holds either $1,000,000 or nothing. You may take both or only B. A Predictor with 99.9% accuracy has already filled the boxes: having foreseen that you would take both, it left B empty; having foreseen that you would take only B, it put in the million. The dominance argument: the boxes are already filled, and your choice will not change them—whatever the contents, “both” gives a thousand more; take both. The expected-utility argument: those who take only B leave with ~999,000, those who take both with ~2,000; take B. Both principles seem self-evident—and they give opposite answers.

## Origin

A rare paradox with a precisely known author: William Newcomb, a theoretical physicist at the Livermore laboratory, devised the problem around 1960 in conversations with colleagues. Oral tradition carried it to Robert Nozick; the 1969 publication (“Newcomb’s Problem and Two Principles of Choice”) caused an explosion—Martin Gardner noted the unprecedented sharpness of the split among experts. The split is stable: surveys of philosophers give about 50/50, the position correlates neither with school nor with field, and each side considers its own answer obvious. The debates took shape as a confrontation between decision theories: the causal one (Gibbard, Harper, Lewis: it is rational to cause oneself good; correlation without causation is no ground) against the evidential one (Jeffrey: a choice is evidence of which world you are in). Parfit proposed separating the questions “what is it rational to do” and “what is it rational to be”; new theories were built (the functional one and others)—there has been no consensus for half a century. Empirically, 60–70% of subjects take only B; argumentation does not shift the distribution, it only strengthens each side.

## Consequence

The structure of the knot recurs wherever a choice correlates with what it does not cause. The prisoner’s dilemma: with a partner who resembles you, “to cooperate” correlates with his cooperating—Nozick himself noted the connection with Newcomb. The Solomon problem: a common factor influences both the preference and the outcome—the choice does not cause the illness but is evidence of it. Copies and simulations: a choice correlates with the choices of the copies. AI alignment: which decision theory to build into an agent is a practical question, and Newcomb’s paradox serves as its touchstone. Variants of the formulation clarify how it is built: the transparent box, the pill for yesterday’s money, a version with no Predictor at all—a bare statistical correlation gives the same knot without the mysticism.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: two boxes, the Predictor, two options of choice, the rule of filling, an accuracy of 99.9%. The structure is clear; no signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “A predictor of free decisions with 99.9% accuracy” is two assumptions in one condition: your choice is almost absolutely predictable (the determinism of a type)—and you really do choose (the freedom of an act). Formally compatible, in substance they are in tension: the two arguments rest on opposite sides of this tension. Dominance presupposes freedom—the choice now is independent of the past filling; expected utility presupposes determinism—the type determines both the choice and the contents. Signal: a hidden contradiction of the conditions.

**Domain 3—Framework Selection:** both decision theories are honest frameworks; each is legitimate on its own assumption. The defect lies further down—in the conditions.

**Domain 4—Comparison:** the calculations of both sides are correct. Not here.

**Domain 5—Inference:** both lines of reasoning are internally valid—a rare and diagnostic case: two flawless inferences to opposite answers. The problem is not in the logic.

**Domain 6—Reflection:** half a century of an even split among experts—signal: what is incompatible is the premises, not the schools; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—a hidden contradiction in the conditions. **Violated laws:** [[Non-Contradiction]]—the conditions require accepting at once the freedom of the choice (otherwise there is nothing to “choose”) and its predictability (otherwise the accuracy is inexplicable). **Essence of the defect:** two internally valid arguments that split the experts in half are a symptom of contradictory premises, not of a hard question. On the E/R/R triad: one Element—the act of choice—is assigned two incompatible Roles: a free deed for the player and a computable function of the type for the Predictor.

## Why There Is No Paradox

The explication of the contradiction closes the “paradox.” Whoever accepts freedom rightly takes both: the contents are fixed, and dominance is correct. Whoever accepts determinism rightly takes B: the “choice” is a manifestation of the type, already taken into account, and expected utility is correct. The confrontation of the arguments is an exact cast of the contradiction in the conditions; after the explication what remains is not a riddle but a choice of assumption. The practical question “what is to be done?” also has a move at the meta-level: the Predictor predicts a deterministic logic of decision-making—its 0.1% of errors betrays that randomness is not given to it. Flip a coin: randomization takes you out of the class of the predictable—this is not evasion but a decision one level higher, the choice of a method of choosing. The empirical record confirms it: in penalty kicks both the kicker and the goalkeeper randomize close to the theoretical optimum (Palacios-Huerta, thousands of kicks): any deterministic pattern against a predictor is detected and exploited.

## Objections and Replies

**“The Predictor is impossible.”** Reply: the knot does not depend on 99.9%—it works at 90% and at 75% as well; the predictability of human decisions is an empirical question, and the version without a Predictor (pure correlation) reproduces the paradox entirely.

**“The Predictor knows the result of the coin too.”** Reply: then where do its 0.1% of errors come from? The errors are exactly the cases where the prediction failed; so what is predicted is a deterministic logic, not physical chance—and the coin remains a way out.

## Lesson

**On hidden contradictions.** Two convincing arguments to opposite conclusions are not a reason to choose a side but a reason to check the compatibility of the assumptions. **On freedom and prediction.** The tension of the knot lives wherever we are predicted—in economics, in technology, in relationships; Newcomb merely crystallizes it down to two boxes. **On the meta-level.** Sometimes the solution is not an answer to the question but a change in the way of answering: randomization as the choice of a method of choosing.

## Kin by Mechanism

[[Unexpected Hanging]] (a neighbor in the family: there the contradiction of the conditions becomes explicit on explication, here it is hidden), [[Crocodile Dilemma|the Crocodile]] (a prediction woven into a rule—structural kin), the prisoner’s dilemma (correlation without causation), the Solomon problem (a common cause of preference and outcome).

**Machine check.** In the registry of 46 it is `D11_Newcomb`, and the diagnosis is sewn into the entry itself: the mismatch field is `HiddenDeterminism`, hidden determinism; the category “defective,” the level `L2_Operations`, laying open by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
