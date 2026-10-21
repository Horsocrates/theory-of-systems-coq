---
title: "Birthday Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Парадокс дней рождения.md"
sourceBlob: 44740789d54791a509339f2ccc03b0e024a972ef
translated: 2026-10-20
status: draft
description: "A correct result: the number of pairs grows quadratically"
---

**N.2** · [[Non Paradoxes|non-paradox]] · subtype: Counterintuitive Result

**Essence of the error.** A correct result: the number of pairs grows quadratically

## Exact Formulation

There are twenty-three people in a room. What is the probability that some two of them share a birthday? Intuition: twenty-three people over three hundred sixty-five days—a coincidence is unlikely, five percent or so. The correct answer: more than half—50.7%. With thirty people—70%, with fifty-seven—99%. A confident “yes” does not take even a third of a year’s worth of people.

## Origin

A classic problem of the probability theory of the first half of the twentieth century—it is usually associated with von Mises (1939); Gardner gave it to the wide public in his *Scientific American* columns. The fate of the problem is rare for a puzzle: it became a working tool. Cryptography builds the “birthday attack” on it: a collision of a hash function with n outputs is to be expected not after n attempts but after roughly √n—the square root, the same mechanism of pairs; hence the requirements on the length of hashes. Legal statistics and forensics rely on it in assessing “striking coincidences” of DNA profiles and features in large databases: with a sufficient number of comparisons, coincidences are bound to appear.

## Why This Is Not a Paradox

Two questions, glued together by expectation, are in conflict; neither the condition nor the computation has a defect. Intuition answers the question “will anyone coincide *with me*”: I have twenty-two potential twins, the chance is small—about 6%, and this estimate is *correct*. But a different question was asked: “will *some pair* coincide”—and among twenty-three people there are not twenty-two pairs but two hundred fifty-three. People grow linearly, pairs quadratically; expectation measures with a ruler what grows as a square. The defect is in expectation, the third place of the canon: the problem is honest; the surprise is a property of the reader.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: 23 people, 365 days, a question about a coincidence “for some two.” Signal: the quantifier of the question—“some pair,” not “someone with me.”

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “Coincidence” is an event on *pairs*, not on people; the bearer of the probability is 253 pairs, and each is a chance. Intuition silently substitutes the bearer: it counts people (23) or comparisons with oneself (22). Signal: substitution of the bearer of the event.

**Domain 3—Framework Selection:** the linear framework (“few people—few chances”) does not fit the object: the number of pairs grows as n²/2—a quadratic framework.

**Domain 4—Comparison:** the honest scale: 23 people—253 pairs; 57 people—1,596 pairs; what must be compared with 365 is pairs, not people.

**Domain 5—Inference:** the computation is elementary and flawless: P(no coincidences) = 365/365 · 364/365 · … · 343/365 ≈ 0.493. The fault does not lie in the problem.

**Domain 6—Reflection:** surprise at a correct computation is a signal to recheck what the event lives on; a bet on a coincidence in a lecture hall is won empirically—here too simulation is an argument.

## Diagnosis

**Category:** non-paradox—a counterintuitive result. **Location of the defect:** expectation—the substitution of the question (“with me” instead of “some pair”) and of the bearer of the event (people instead of pairs). **No law is violated.** On the E/R/R triad: intuition counts Elements (people), while the event lives on a Rule-relation (pairs)—the bearer of the probability does not coincide with the bearer of the gaze.

## Resolution

The exact computation goes through the complement: the probability of *no* coincidences is the product 365/365 · 364/365 · … · 343/365 ≈ 0.493; hence the probability of a coincidence is 0.507. The support for intuition is to count the chances of a miss: each new person must miss all the previous ones, and the factors decrease. A quick rule: a collision becomes probable at about √365 ≈ 19 people—a root, not a fraction of 365; in general form the threshold is ~√n, and this is exactly the constant that governs cryptographic attacks. A control that restores intuition’s honor: for someone to coincide *with you in particular* with probability 1/2, 253 people are needed—here the linear feeling is right, because the question really is linear. Both intuitions are right—each about its own question; the “paradox” is their gluing.

## Lesson

**On the bearer of the event.** Before estimating a chance, ask what the event lives on: on elements or on pairs—a linear feeling on a quadratic bearer errs many times over. **On two questions.** “With me” and “between anyone” are different questions with answers of different orders; half of all “striking coincidences” are an answer to the second, read as an answer to the first. **On large samples.** With a sufficient number of comparisons, coincidences are inevitable: the event is no miracle; it would be a miracle if it did not occur.

## Kin by Mechanism

[[Monty Hall]] (a neighbor in the category: informational structure against the picture), [[False Positive|False positives]] (blindness to the base rate—the third sister), the law of truly large numbers (in a large sample the rare happens regularly), the birthday attack in cryptography (the same square root of n in service).

**Machine check.** In the registry of 46—`N2_Birthday`: category `NonParadox`; the status of the category is formalized (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v). There is no named computation of 0.507 in the base—a candidate for formalization for the “Probability” branch (a product over Q is a direct task for process arithmetic; see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
