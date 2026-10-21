---
title: "Curry’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Парадокс Карри.md"
sourceBlob: 5d151d9ef4276a3b7527c3aae44bf1485ac09ad0
translated: 2026-10-20
status: draft
description: "The conditional includes itself in its antecedent"
---

**S.6** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** The conditional includes itself in its antecedent

## Exact Formulation

C: “If this statement is true, then two times two is five” (any consequent will do in its place). Suppose C is true; then what it says holds: “if C is true, then two times two is five”; but C is true by supposition—hence two times two is five. In sum, from the supposition “C is true” we have derived “two times two is five”; but exactly this—“if C is true, then two times two is five”—*is* the content of C: we have proved C without any suppositions at all. Then C is true—and two times two is five. By the same move anything whatsoever can be proved—the construction is not contradictory, it is *omnivorous*, which is worse.

## Origin

Haskell Curry, 1942—the knot was found in combinatory logic during an analysis of foundations; kindred forms appear in Löb (Löb’s paradox, on provability) and in the medieval insolubilia (Albert of Saxony analyzed similar conditionals). It was built on purpose—as a blow that goes around negation: in the [[Liar Paradox|liar]] “false” is at work, and one may hope to escape by weakening negation; Curry assembles the trouble from implication and self-reference alone—negation takes no part at all.

## Consequence

The main technical lesson of the twentieth century about the liar’s family: **the defect is not in negation**. Paraconsistent logics, which admit contradictions, and three-valued semantics, which extinguish “false,” are powerless against Curry—it produces not a contradiction but *everything*, trivializing the system. That is why the formal answers strike deeper: substructural logics restrict the rule of contraction (the double use of an assumption), and theories of truth restrict the conditional itself. For our catalog, Curry is a witness for the prosecution against dialetheism: to accept the liar’s contradictions is no escape—Curry trivializes the paraconsistent world as well.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: a conditional statement; the antecedent “this statement is true” (a pointer to the whole construction); an arbitrary consequent. Structure: the conditional includes its own truth-evaluation in its own condition. No signal yet.

**Domain 2—Clarification: what do the terms mean?** “If… then” is a transition by a ground; a rule of inference in the form of a statement. First signal: the antecedent is not a fact about the world but *an evaluation of the construction itself*; the conditional “fires” on a judgment about itself.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect—the same as in the liar, only hidden in the antecedent: the truth-evaluation (level 2) is embedded inside what is evaluated (level 1). The difference is only in the packaging: the liar puts self-evaluation under negation, Curry puts it in the condition. [[Identity]] and [[Non-Contradiction]] hold the same boundary: what is evaluated and what evaluates are different roles of one act. Signal: level confusion, masked by an innocent connective.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** given the confusion admitted, every step is flawless—supposition, modus ponens, conditional proof. It is precisely the flawlessness of the inference that makes the knot instructive: the trouble is not in the steps.

**Domain 6—Reflection:** the outcome is the provability of anything: the strongest signal of systemic trouble; a return to domain 3—self-evaluation in the antecedent.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion, a form without negation. **Violated laws:** Identity · Non-Contradiction (the evaluated / the evaluating in one act); a consequence of the violation is the collapse of Sufficient Reason: “everything is provable” destroys the ground itself as a distinction. **Essence of the defect:** the predicate “true” about the construction itself is embedded in its antecedent; the self-evaluation is the same as in the liar, the packaging is different. On the E/R/R triad: an element applies a Rule to itself—through the condition.

## Why There Is No Paradox

“This statement is true” inside a statement is not a condition but a level confusion: evaluation lives a storey above what is evaluated, and the antecedent of C has no content until C is formed—while C is not formed as long as the antecedent is empty. The circle does not hold together: the construction expresses no judgment; there is nothing to fire. The formal remedies—restricting contraction, stratifying the truth predicate—break the same circle technically; our reading explains why they work: they return evaluation to its storey. The omnivorousness of the knot is not depth but a symptom: a system in which self-evaluation is legitimate does not distinguish the true from the false at all.

## Lesson

**On the place of the defect.** The liar’s family is treated neither by amending negation nor by tolerating contradictions—only by returning evaluation to its level: Curry proves this by reductio. **On the masks of self-evaluation.** Self-reference-with-evaluation hides in any connective—negation, condition, provability (Löb); a check of the vertical must look into antecedents. **On the price of tolerance.** “Let us accept the contradiction” is no way out: after the liar comes Curry and takes everything.

## Kin by Mechanism

[[Liar Paradox|The Liar]] (the same self-evaluation under negation), Löb’s paradox (the same on the provability predicate), [[Yablos Paradox|Yablo]] (self-evaluation without self-reference), the validity form of Curry’s paradox (“this inference is valid → P”).

**Machine check.** There is no named analysis in the base—the mechanics of self-evaluation is inherited from the liar (`liar_is_ill_formed`, `liar_violation`—ParadoxDiagnosis.v); in the registry of 46 the knot is classified as structural, with a guarantee that the paradox does not form (`all_46_dissolvable`, `structural_46_dissolves`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
