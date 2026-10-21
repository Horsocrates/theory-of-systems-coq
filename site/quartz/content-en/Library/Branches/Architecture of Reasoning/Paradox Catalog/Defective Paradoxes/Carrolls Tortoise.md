---
title: "Carroll’s Tortoise"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Черепаха Кэрролла.md"
sourceBlob: 9081424cebdf26b55df9a5df7b2613ce7178624c
translated: 2026-10-20
status: draft
description: "A rule of inference (the level of operations) is confused with a premise (the level of elements)"
---

**D.20** · [[Defective Paradoxes|defective paradox]] · subtype: Level Confusion (Rule/Premise)

**Essence of the error.** A rule of inference (the level of operations) is confused with a premise (the level of elements)

## Exact Formulation

Achilles has at last caught up with the Tortoise, and they are talking about logic. The Tortoise proposes a syllogism: (A) if p, then q; (B) p; (Z) therefore, q—and declares: “I accept A and B, but I do not grant that Z follows from them. Let logic force me.” Achilles writes down a premise (C): if A and B are true, Z must be true. “Excellent,” replies the Tortoise, “I accept A, B, and C; now I need a premise that Z follows from them.” Achilles writes down (D)… The regress is infinite: Achilles will never bring the Tortoise to the conclusion.

## Origin

The dialogue “What the Tortoise Said to Achilles” appeared in the journal *Mind* in April 1895. Its author was Lewis Carroll, otherwise Charles Dodgson, a lecturer in mathematics at Christ Church, Oxford: the author of *Alice* was a serious logician—*Symbolic Logic*, *The Game of Logic*, his own method of diagrams for syllogisms. The choice of characters is precise: in [[Zenos Achilles|Zeno]], Achilles cannot catch up with the Tortoise—in Carroll he has caught up and got stuck in a logical race: the infinite regress of segments has given way to an infinite regress of premises, while the structure is the same—every step toward the goal creates the need for a new step. Carroll offered no solution—he broke off the dialogue and left the problem to the reader. The progeny is enormous: Russell and Whitehead in *Principia* distinguish assertions from rules of inference—exactly the distinction the Tortoise refuses to recognize; Wittgenstein developed the knot into the argument about rule-following (“every course of action can be made out to accord with the rule”—and answered: a rule is not an interpretation but a practice); Kripke (1982) turned it into a skeptical paradox about meaning—a direct descendant of the Tortoise.

## Consequence

Of all attacks on logic this one has the deepest address: the [[Liar Paradox|liar]] strikes at truth, [[Russells Paradox|Russell]] at the set, the Tortoise at inference itself: modus ponens, the rule without which logic does not work at all. Its kin by structure are the perennial problems: the regress of justification (every justification rests on premises that require justification), Hume’s induction (the justification of induction is inductive). The answers of the centuries: foundationalism, coherentism, infinitism; Brandom’s inferentialism (implicit knowledge of rules before their explicit formulation); the naturalistic move (rules of inference are strategies fixed by learning). Practice reproduces the knot daily: how rules are taught, how a machine “understands” an instruction, how a legal norm is applied to a case—a rule does not apply itself.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the premises (A, B), the conclusion (Z), the rule of inference, the Tortoise’s demand. The signal is already here: three types of entities—is the rule of the same type as the premises?

**Domain 2—Clarification: what do the terms mean?** Here is the defect. A premise is an assertion within reasoning: “X is true.” A rule of inference is a license for a transition, an instruction *over* the reasoning: “having X and Y, conclude Z.” Different levels: a premise is an element, a rule is an operation on elements. The Tortoise does not draw the distinction and demands that the rule be turned into a premise; but a rule written down as premise C ceases to be a rule—the transition needs a new one, and the regress is set going. Signal: category confusion.

**Domain 3—Framework Selection:** a secondary error—Achilles’ own: he accepts an illegitimate demand. Had he understood the difference of levels, he would have refused.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** the Tortoise’s reasoning is valid under the assumption it rests on: “a rule is a premise.” The assumption is false—the problem is not in the inference.

**Domain 6—Reflection:** a regress without end—signal: check the categories of the participants; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification)—primary; Domain 3—secondary (an illegitimate demand accepted). **Type:** defective—category confusion. **Violated laws:** [[Order]]—what organizes stands one storey above what is organized; [[Identity]]—a rule is not a premise. **Essence of the defect:** a rule of inference (the level of operations) is squeezed into the row of premises (the level of elements). On the E/R/R triad: a Rule is required to become an Element—the exact mirror of Russell, where an Element seized the place of a Rule; the mirroring is recorded by machine (see below).

## Why There Is No Paradox

Achilles’ right answer: “No, Tortoise. C is not a premise. It is the rule by which Z follows from A and B; you have accepted A and B—a rule is applied, not accepted, and Z follows.” To the question “why must I apply modus ponens?” the answer lies outside logic: a rule is not a statement about the world that one accepts but an operation that one applies; the Tortoise’s question is whether it wants to reason at all. If it does, the rules are in force; if it refuses, the conversation is over—not from any impotence of logic, but because the Tortoise has stepped out of logic. Refusing the demand stops the regress—at the very first step. The distinction holds everything around it: the rules of chess are not a piece on the board; a constitution is not one more law but the order of enacting laws; a grammatical rule is not a sentence of the language. The Tortoise, without meaning to, demonstrates the Law of Order: the organizing principle is not an organized element. Hence the honest remainder: some things are not grounded within a system because they are the conditions of the system; modus ponens is not proved by modus ponens, and this is the architecture of logic, not its weakness. Rules are what make inferences possible.

## Lesson

**On categories.** Premises and rules are different categories; the first step of analysis is to recognize to which category each participant in the reasoning belongs. **On levels.** To demand that rules be justified at the level of premises is a category mistake; logic has a level architecture, and it is load-bearing. **On illegitimate demands.** Not every demand deserves to be met: Achilles lost the moment he set about writing premise C. A refusal for a precise reason is not weakness but diagnosis.

## Kin by Mechanism

[[Russells Paradox|Russell]] (a machine-recorded mirror: there Element → Rule, here Rule → Element), [[Liar Paradox|the Liar]] (an evaluation inside what is evaluated), the regress of justification and the problem of induction (justifying a method by the means of that very method), Kripkenstein (rule-following), [[Zenos Achilles|Zeno’s Achilles]] (the ancestor characters: in Zeno it was motion that got stuck, in Carroll inference).

**Machine check.** There is a named analysis: `tortoise_demand_illegitimate` (the Tortoise’s demand is illegitimate—a rule does not turn into a premise), `regress_stopped` (refusing the demand stops the regress), `carroll_is_err_confusion` (the confusion Rule → Element; the neighboring line of the same definition records Russell as Element → Rule—the mirror, machine-checked); the registry entry `D20_CarrollTortoise` carries the diagnosis in its field: `RuleAsPremise` (all in ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
