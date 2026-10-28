---
title: "Paradox of the Court"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс суда (Протагор).md"
sourceBlob: cf0de4757c926bda7bc685773a8ec101fb03054e
translated: 2026-10-20
status: draft
description: "The contract includes the result of its own test"
---

**D.8** · [[Defective Paradoxes|defective paradox]] · subtype: Contradiction in the Conditions

**Essence of the error.** The contract includes the result of its own test

## Exact Formulation

Protagoras taught Euathlus forensic eloquence on an agreement: the fee was due when the pupil won his first case. Euathlus takes no cases—he has nothing to pay with and no occasion to pay. Protagoras sues him and reasons: “If I win, he will pay by the court’s judgment; if he wins, he will pay by the contract, for he will have won his first case.” Euathlus, a worthy pupil, answers in mirror image: “If I win, I do not pay by the court’s judgment; if I do not win, I do not pay by the contract, for I will not have won my first case.” Both lines of reasoning look flawless—and they lead in opposite directions whatever the outcome.

## Origin

An ancient case of the fifth century BCE: Protagoras was the first sophist to take fees for teaching, and the agreement “payment after the first victory” was an advertisement for his craft. The classical source is Aulus Gellius (*Attic Nights*, V.10): the judges, having heard both sides, adjourned the case indefinitely—an honest silence in the spirit of Chrysippus before the [[Sorites Paradox|sorites]]. The legal tradition returned to the case seriously: Leibniz analyzed such “perplexing cases” in his doctoral dissertation (*De casibus perplexis in jure*, 1666), and his line yielded a two-step solution that lives on to this day: dismiss the first suit—the condition of the contract has not yet been met; after this the condition is met (Euathlus has won his first case)—and a second suit recovers the fee. Kin by epoch and mechanics is the [[Crocodile Dilemma|crocodile]]: a promise whose fulfillment is hooked onto a statement about that very fulfillment.

## Consequence

The case became a textbook specimen of two things. For logic—a shift of ground within a single piece of reasoning: in one branch each side appeals to the court, in the other to the contract, choosing in each branch the ground that suits it; the mirror symmetry of the arguments is not depth but the symmetry of one and the same substitution. For law—a conflict of sources: the contract and the court’s judgment are two independent normative orders, and until their priority and the order of their application are established, “owes” is undefined. Hence the direct heirs in jurisprudence: rules on the competition of norms, clauses on jurisdiction and priority in contracts, the rule against deriving a decision at once from two uncoordinated grounds.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the contract (payment after the first victory), Protagoras’ suit, the court, two mirror-image argumentations. Structure: Protagoras made the fee itself the subject of the first case—the contract is drawn into a case about the contract. The signal is already visible.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “Euathlus owes the fee”—on what ground? There are two grounds: the court’s judgment and the condition of the contract, and the condition stipulated neither their priority nor the case in which the first case is a case about the fee itself. Both argumentations exploit this gap: they switch the ground between branches. Signal: two uncoordinated sources of a norm under one “owes.”

**Domain 3—Framework Selection:** not reached—before a framework, the ground must be assigned.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** within each branch each step is valid; the defect lies in the switch of ground between branches, that is, in the premises, not in the transitions. The problem is not in the inference.

**Domain 6—Reflection:** two mirror-image “flawless” lines of reasoning to opposite outcomes—a signal of uncoordinated premises ([[Newcombs Paradox|Newcomb]] gives the same symptom); return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—contradiction in the conditions: the contract and the court as two unranked grounds, made to collide in one act. **Violated laws:** [[Identity]]—“owes” changes its sense between branches (owes-by-the-court, owes-by-the-contract); [[Sufficient Reason]]—a verdict requires one ground, while the lines of reasoning draw on two by turns. **Essence of the defect:** the condition of the deal is undefined for the case in which the subject of the first case is the deal itself; the gap is filled by a substitution of ground. On the E/R/R triad: two Rules (the contract and the court) are applied to one Element (the fee) without a Rule about Rules—no priority is set.

## Why There Is No Paradox

Three moves, from diagnosis to practice. The first is to lay open the substitution: hold one ground for the whole reasoning. By the court alone: if Protagoras wins, Euathlus pays; if Euathlus wins, he does not pay; no loop. By the contract alone: as long as the first case has not been won, it is too early to pay; no loop here either. The knot is tied exclusively by the switch of ground between branches—making the switch explicit kills both “flawless” dilemmas at once. The second is the lawyers’ two-step solution: dismiss the first suit as premature (the condition has not been met); by this very loss of Protagoras the condition is met—Euathlus has won his first case; a second suit recovers the fee under the contract. Time separates the grounds that the condition made collide. The third is a lesson for the drafter: a contract whose condition may become the subject of a dispute under that very contract must carry a clause on priority and on such a case; silence about this is a defect of the text, and the case of Protagoras shows its price. Gellius’ judges, who adjourned the case, were honest: in the form presented, the question had no answer—not because it was deep, but because it was underdetermined.

## Lesson

**On the ground.** One reasoning, one ground; switching the source of the norm between branches is not an argument but an equivocation. **On mirror symmetry.** Symmetric dilemmas of the parties are a symptom: both are built on one gap in the conditions; the mirror doubles the defect, not the depth. **On drafting rules.** The self-applicable case is the first thing a rule must provide for: legal hygiene here coincides with logical hygiene.

## Kin by Mechanism

[[Crocodile Dilemma|The Crocodile]] (a structural loop of a single rule—there the condition is closed on its own fulfillment by construction), [[Buridans Bridge|Buridan’s Bridge]] (a norm without a performable subject), [[Unexpected Hanging]] (a neighbor by subtype: contradiction in the conditions), [[Newcombs Paradox|Newcomb]] (two valid arguments as a symptom of a defect in the premises).

**Machine check.** In the registry of 46 it is `D8_ParadoxOfCourt`: the field `ConceptualAmbiguity`, the level `L2_Operations`, the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). There is no named analysis—the performative mechanics of the loop is inherited from the crocodile, and the defect of the ground is made explicit by clarification. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
