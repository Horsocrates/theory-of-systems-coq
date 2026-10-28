---
title: "Crocodile Dilemma"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Дилемма крокодила.md"
sourceBlob: d3465f0f1ea8ca6603fa06ed4d31bcac79f464b1
translated: 2026-10-20
status: draft
description: "The rule depends on a statement about its own execution"
---

**S.7** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** The rule depends on a statement about its own execution

## Exact Formulation

A crocodile has seized a child and promises the father: “I will return him if you correctly predict what I will do; if you do not guess, I will not return him.” The father answers: “You will not return him.” If the crocodile does not return the child, the prediction has come true, and by the promise it is obliged to return him. If it returns him, the prediction is false, and by the promise it is obliged not to return him. No action fulfills the promise.

## Origin

An ancient knot from the arsenal of the sophists and the Megarian school—Quintilian (*Institutio Oratoria* I.10.5) counts “the Crocodile” among dialectical tricks, and Lucian in *Philosophies for Sale* puts it into the mouth of Chrysippus as the signature product of Stoic logic. A relative by epoch and by mechanics is the lawsuit of Protagoras with his pupil Euathlus ([[Paradox of the Court]]): the fee for the teaching depends on the outcome of the first case, which is the very lawsuit over the fee. Antiquity knew the taste of the performative loop: a promise whose fulfillment depends on a word about that very fulfillment.

## Consequence

The Crocodile is the oldest specimen of the **performative** branch of the liar’s family: the knot is tied not from the predicate “false” but from the link “word ↔ deed.” This is its value: it shows that the vertical of levels holds not only semantics but also the world of rules and contracts—a condition of a deal that refers to the outcome of the deal itself does not set an outcome. Its direct descendants are problems about self-referential predictions and decisions (relatives of [[Newcombs Paradox|Newcomb]]) and legal puzzles about contracts whose fulfillment is determined by a statement about their fulfillment.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: a promise-rule (return ⟷ a correct prediction); the father’s prediction—about the crocodile’s own action under this rule. Structure: the condition of the rule is closed on the execution of the rule. No signal yet.

**Domain 2—Clarification: what do the terms mean?** “Correctly predict”—the truth-value of the father’s word is set by the crocodile’s future action; “return / not return”—the action is set by the rule through the truth-value of the father’s word. First signal: truth-value and action are defined *through each other*—neither stands on its own ground.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect. The rule is an operation on predictions: it must *take* the ready truth-value of the word and output an action (level 2 over level 1). The father’s answer slips the rule a word whose truth-value is itself computed from the rule’s action—the operation is fed its own output. [[Identity]]: the input is not the output; [[Non-Contradiction]]: an action cannot be a condition of itself in one act; [[Order]]: the ground comes before what is grounded—while here there is a circle of grounds. Signal: a performative loop.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** both branches are flawless. The problem is not in the inference.

**Domain 6—Reflection:** no action fulfills the rule—a signal: with such an input the rule is incoherent; a return to domain 3.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion, performative form. **Violated laws:** Identity · Non-Contradiction (the input of the rule = its output) · Sufficient Reason (a circle of grounds: truth-value from action, action from truth-value). **Essence of the defect:** the rule is made dependent on a statement about its own execution. On the E/R/R triad: the Rule is fed, as an Element, its own result.

## Why There Is No Paradox

Given the father’s answer, the crocodile’s promise is **unfulfillable**—not hard, but undefined: the set of actions satisfying the rule is empty, as “a married bachelor” is empty. A deal without a performable subject is no deal: the contract is void, and there is no riddle of “what, then, must it do?”—the “must” is not set. The father did not solve the dilemma—he laid it open: his answer is a diagnostic move proving that the rule does not set an output for every input. An honest deal must close on an external ground: “predict whether it will rain tomorrow”—the truth-value comes from the world, and the rule works; the loop begins exactly where the subject of the prediction is the rule itself.

## Lesson

**On contracts.** A condition that refers to the outcome of the deal itself does not set an outcome: checking contracts for self-reference is logical hygiene, not only legal. **On the partiality of rules.** A rule may be defined not on all inputs; feeding it an inadmissible input does not defeat it but shows its boundary. **On the performative branch.** The liar’s family is wider than semantics: a word woven into a deed ties the same knots—and is resolved by the same vertical.

## Kin by Mechanism

[[Buridans Bridge|Buridan’s Bridge]] (the same loop: a promise about crossing, through a word about a throw), [[Paradox of the Court]] (a lawsuit about the outcome of the lawsuit itself—a defective relative), [[Liar Paradox|the Liar]] (the pure semantic form), [[Newcombs Paradox|Newcomb]] (a prediction woven into a decision).

**Machine check.** There is no named analysis in the base—the mechanics of self-evaluation is inherited from the liar (`liar_is_ill_formed`—ParadoxDiagnosis.v: evaluation inside the evaluated); in the registry of 46 it is structural, with the paradox shown not to form (`all_46_dissolvable`, `structural_46_dissolves`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
