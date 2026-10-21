---
title: "Simpson’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Парадокс Симпсона.md"
sourceBlob: f73826f6197e104ede3e85a49f07d96d0aa01d06
translated: 2026-10-20
status: draft
description: "A correct result: aggregation can distort"
---

**N.3** · [[Non Paradoxes|non-paradox]] · subtype: Counterintuitive Result

**Essence of the error.** A correct result: aggregation can distort

## Exact Formulation

Treatment A is better than treatment B both on mild cases and on severe ones—yet over all patients together B is better. The numbers are honest: on small stones A has 81/87 = 93% against 87% for B, on large ones 192/263 = 73% against 69%; in total, however, A has 273/350 = 78%, B 289/350 = 83%. A trend that holds in every group reverses when the groups are combined. The general form: from a/b > c/d and e/f > g/h it does not follow that (a+e)/(b+f) > (c+g)/(d+h).

## Origin

The phenomenon is older than its name: Pearson described spurious correlations under mixing (1899), Yule analyzed the reversal of associations in tables (1903)—which is why strict authors say “the Yule–Simpson effect.” Simpson gave the canonical analysis (1951), Blyth fixed the word “paradox” (1972). Fame came with the Berkeley admissions case (1973, analyzed by Bickel, Hammel, and O’Connell): overall, women were admitted less often—yet department by department their share was no lower than men’s; women applied more often to competitive departments. The modern chapter was written by Pearl: the question “which figure to trust—the group one or the overall one?” is a question about the causal structure of the data, and it is answered by a causal diagram, not by arithmetic.

## Why This Is Not a Paradox

“Better in every group” and “worse overall” are statements about different quantities, so there is no contradiction. The share in the union is a weighted mixture, not an average of the shares: the weights are set by the composition of the groups, and if A and B have different compositions (A got the severe cases), the aggregate compares mixtures, not treatments. The expectation “better in every part—therefore better as a whole” is a false principle of composition: the properties of parts do not carry over to the whole when the rule of gluing is weighted. The defect lies in expectation; the numbers are flawless on both sides.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: two groups, two options, the shares in the groups, the shares in the union, a hidden variable of composition. Signal: two honest computations pull in different directions—look for a third quantity.

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “Better overall”—about what? The overall share mixes the outcome of the treatment with the composition of the patients; it is a property of the mixture, not of the treatment. A comparison of treatments requires equal conditions—the groups give them, the aggregate destroys them. Signal: the aggregate indicator has silently changed its subject.

**Domain 3—Framework Selection:** the framework “one number will decide” does not fit the object: with unequal compositions there is no single honest “total”—there are group comparisons, and there is the question of the causes of the composition.

**Domain 4—Comparison:** the knot is entirely about comparison: shares can be compared at equal weights; mixing the weights turns a comparison of aggregates into a comparison of compositions.

**Domain 5—Inference:** both computations are arithmetically correct. The problem is not in the computation.

**Domain 6—Reflection:** a reversal of the trend upon aggregation is a signal of a hidden variable; the right reflex is to slice the data and ask where the composition came from.

## Diagnosis

**Category:** non-paradox—a counterintuitive result. **Location of the defect:** expectation—a false principle of composition: “better in the parts ⇒ better as a whole.” **No law is violated**—there is an unaccounted Rule: on the E/R/R triad the shares of the groups are Roles on their Elements, and the union introduces a new Rule—the weights of composition; intuition carries the property of the Roles over to the mixture, ignoring the Rule of gluing. The properties of systems do not add up—this is the general law of composition, and Simpson is its statistical face.

## Resolution

The arithmetic layer: an inequality of shares is not preserved under the addition of numerators and denominators—(a+e)/(b+f) lives on the weights b and f, and a skew of the weights reverses anything; this is checked on the numbers of the formulation in a minute. The causal layer is the main one: which figure to trust is decided by structure, not by taste. If the composition of the groups is a *cause* of the assignment of treatment (the severe cases were given A), the group comparison is the honest one: it equalizes the conditions; the aggregate is an artifact of the distribution. If, however, the “group” is a consequence of the intervention itself (the treatment changes the severity by which we then divide), the grouping itself introduces a bias—and the aggregate is the honest one. Pearl’s rule: look at the causal diagram and close the “back doors”; one table—two conclusions, and what chooses between them is knowledge of how the data were born. Berkeley is the model: the department was the cause both of the applications and of the selectivity—the group count was the honest one, and the aggregate mixed selectivity with sex.

## Lesson

**On composition.** “Better in every part” does not carry over to the whole through a weighted gluing: the properties of mixtures are properties of the weights no less than of the parts. **On the third variable.** A reversal of the trend under aggregation is almost always the trace of a hidden variable; slice the data before the conclusion, not after. **On the limit of arithmetic.** Which of two honest numbers to trust is a question about the origin of the data; statistics without causal structure does not answer “which is better.” **On practice.** Simpson is the most dangerous exhibit of the category: it lives in real reports—medical, personnel, judicial—and reverses conclusions silently.

## Kin by Mechanism

[[Monty Hall]] and [[Birthday Paradox|Birthdays]] (neighbors in the category: the structure of the event against the picture), [[False Positive|False positives]] (the weights of base rates—the same mechanism in diagnostics), the ecological fallacy (carrying the group over to individuals), [[Two Envelopes]] (a distant relative: an illegitimate gluing of quantities from different conditions).

**Machine check.** In the registry of 46—`N3_Simpson`: category `NonParadox`; the status of the category is formalized (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v). The arithmetic core—the non-preservation of an inequality of shares under termwise addition—is a direct candidate for a Q-check in the “Probability” branch: the concrete numbers of the formulation give a machine counterexample in one line (see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
