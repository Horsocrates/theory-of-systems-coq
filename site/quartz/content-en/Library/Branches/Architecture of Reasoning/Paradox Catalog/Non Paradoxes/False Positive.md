---
title: "False Positive Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Парадокс ложноположительных.md"
sourceBlob: 53f48deafc20d4f45c31174bcf8f2afaab35774a
translated: 2026-10-20
status: draft
description: "A correct result: Bayes’ theorem"
---

**N.4** · [[Non Paradoxes|non-paradox]] · subtype: Counterintuitive Result

**Essence of the error.** A correct result: Bayes’ theorem

## Exact Formulation

A disease occurs in one person in a thousand. The test is 99% reliable: it almost always catches the disease, and it gives a healthy person a false alarm in 1% of cases. Your test is positive. What is the probability that you are ill? Intuition: 99%. The correct answer: about 9%. Out of a thousand people tested, one sick person and roughly ten healthy ones will receive a positive result—you are one of eleven.

## Origin

The classic measurement was made by Casscells, Schoenberger, and Graboys (1978), who surveyed physicians and students at Harvard Medical School on a similar problem: most answered “95%,” where the correct answer was ~2%—and those who erred were people who make diagnoses daily. Kahneman and Tversky had by then already described the mechanism—base-rate neglect (the taxicab problem); Eddy showed the scale of the trouble in medical practice; Gigerenzer found the antidote—natural frequencies: the same question, posed in people (“out of 1,000—one and ten…”) instead of percentages, is solved correctly by the majority. The judicial shadow of the knot is the “prosecutor’s fallacy”: the substitution of “the probability of the evidence given innocence” for “the probability of innocence given the evidence”; the Sally Clark case (1999) is a tragic monument to this substitution.

## Why This Is Not a Paradox

The defect lies in expectation; neither the problem nor Bayes’ theorem contains one: intuition reads “the test’s accuracy is 99%” as the answer to the patient’s question, whereas these are answers to *different* questions. Accuracy is the probability of a result given a known state: P(positive | ill). The patient asks the reverse: P(ill | positive). The arrow of the condition is reversed—and the reverse move is not free: it is weighted by the composition of the population, and with a rare disease (1 in 1,000) the crowd of the healthy, even with a small percentage of false alarms, supplies more positives than the handful of the sick. The expectation that conditional probability is symmetric is the same confusion as “all cats are animals, therefore all animals are cats,” only in probabilistic dress.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the base rate (1/1000), sensitivity, the share of false alarms, a positive result, the question “am I ill.” Signal: in the question and in the data the arrows of the condition point in different directions.

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “The test is 99% accurate” is a property of the test given a fixed state; “the probability that I am ill” is a property of my situation given a fixed result. These are different conditional probabilities; they are equal only by chance. Signal: the inversion of the condition is taken for an identity.

**Domain 3—Framework Selection:** the framework “the quality of the instrument decides” does not fit the object: the answer lives on a triple (sensitivity, false alarms, base rate), and the third term is the main one for rare events.

**Domain 4—Comparison:** the decisive comparison is of the two streams of positives: from the sick (~1 out of 1,000) and from the healthy (~10 out of 999); their ratio is the answer.

**Domain 5—Inference:** Bayes’ computation is flawless and is checked by recounting in people. The fault does not lie in the problem.

**Domain 6—Reflection:** “An accurate test—so why 9%?” is a signal to recount in natural frequencies; the surprise is removed by a thousand imaginary patients.

## Diagnosis

**Category:** non-paradox—a counterintuitive result. **Location of the defect:** expectation—the inversion of conditional probability and base-rate neglect. **No law is violated.** On the E/R/R triad: the accuracy of the test is a Rule leading from state to result; the patient’s question goes against the arrow of the Rule, and the reverse move must be weighted by the composition of the Elements (the base rate)—intuition, however, reads the Rule as symmetric and does not ask about the composition.

## Resolution

Natural frequencies solve the problem in one’s head. Take a thousand people. One is ill—the test will almost certainly show it: one true positive. There are 999 healthy ones—one percent of false alarms gives roughly ten false positives. Positives in total—eleven; among them one is ill: P(ill | positive) = 1/11 ≈ 9%. Bayes’ formula says the same in one line—but frequencies explain *why*: with a rare disease the crowd of the healthy outweighs the handful of the sick even with an excellent test. Hence the practice: a positive screening for something rare is a reason for a second, independent test (after which the base is no longer 1/1000 but 1/11—and a second positive weighs a lot), not for a verdict. And the judicial mirror: “the probability of such evidence in an innocent person is one in a million” is not “the probability of innocence is one in a million”; without the base rate—how many people could have left such evidence—the prosecution’s number means nothing.

## Lesson

**On the arrow of the condition.** P(A|B) and P(B|A) are different quantities; substituting one for the other is the probabilistic form of converting an implication. **On the base rate.** With rare events the composition of the population weighs more than the quality of the instrument; the question “how many such are there at all” comes first, not last. **On representation.** Percentages hide the structure, people show it: recounting in natural frequencies is the cheapest detector of this error. **On the price.** The error lives not in problem books but in clinics and courts; recognizing it is the hygiene of decisions about people.

## Kin by Mechanism

[[Monty Hall]] (informational structure against the picture), [[Birthday Paradox|Birthdays]] (the bearer of the event), [[Simpsons Paradox|Simpson]] (the weights of composition—the same third term), the prosecutor’s fallacy and the Kahneman–Tversky taxicab problem (direct forms of the same confusion).

**Machine check.** In the registry of 46—`N4_FalsePositive`: category `NonParadox`; the status of the category is formalized (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v). The count 1/11 is an exact fraction: natural frequencies are pure Q-arithmetic, the first candidate for formalization in the “Probability” branch (see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
