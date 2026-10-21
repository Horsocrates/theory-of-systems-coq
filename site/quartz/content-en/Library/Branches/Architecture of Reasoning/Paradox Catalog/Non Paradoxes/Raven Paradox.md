---
title: "Raven Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Парадокс воронов.md"
sourceBlob: 5d6f30639418ce88c4e6c325ba0555c6923bcc1f
translated: 2026-10-20
status: draft
description: "Shows the problem of inductive confirmation"
---

**N.8** · [[Non Paradoxes|non-paradox]] · subtype: Problem of Confirmation

**Essence of the error.** Shows the problem of inductive confirmation

## Exact Formulation

The hypothesis: “all ravens are black.” It is logically equivalent to its contrapositive: “everything nonblack is not a raven.” Observing a black raven confirms the first; observing a green apple—a nonblack thing that is not a raven—confirms the second. But equivalent hypotheses are confirmed by the same things. The conclusion: a green apple confirms that all ravens are black. Ornithology without leaving the kitchen.

## Origin

Carl Hempel, “Studies in the Logic of Confirmation” (1945)—the knot was built as a stress test of the theory of confirmation. The formal source of the conflict is exact: Nicod’s criterion (the hypothesis “all F are G” is confirmed by observations of Fs that turn out to be G) collides with the equivalence condition (equivalent hypotheses are confirmed equally)—together they produce the apple-ornithologist. Hempel himself proposed accepting the conclusion: yes, it confirms—intuition protests in vain. The Bayesian line (Good, Mackie, and onward) made precise *why* the protest is at once justified and unjustified: there is confirmation, but it is vanishingly small. Good added a gem (“The White Shoe Is a Red Herring,” 1967): with special compositions of the world and procedures of sampling, an observation can mean anything—up to refutation; confirmation is a property not of the object but of *how* it came into view. A neighbor from the same workshop is Goodman’s “new riddle of induction.”

## Why This Is Not a Paradox

Logic is intact: contraposition is flawless, and equivalent hypotheses really are confirmed by the same things. The conflict lies between two readings of the word “confirms”: the qualitative one (“raises the probability”—if only by a hair) and the everyday one (“testifies appreciably”). The apple confirms the hypothesis—qualitatively, by an amount of the order of the inverse cardinality of the class of nonblack things, that is, by a mere nothing; the black raven, by an amount of the order of the inverse cardinality of the class of ravens, incommensurably larger. Expectation measures confirmation in binary terms and therefore hears “the apple proves something about ravens”; the computation measures by weights—and the absurdity vanishes: yes, by an epsilon. The defect is in expectation; the asymmetry lives in the sizes of the classes, not in logic.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: a hypothesis, its contrapositive, two observations (a raven, an apple), the relation of confirmation. Signal: the evidence comes from the class about which the hypothesis is most loudly silent.

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “Confirms” is graded—it is an increment of probability, and it has a magnitude; the binary reading erases the magnitude and puts the apple on a par with the raven. Signal: the quantum against the quantity—kin to the [[Lottery Paradox|lottery]] threshold.

**Domain 3—Framework Selection:** a binary framework of confirmation does not fit the object; the honest framework is one of weights: evidence weighs according to the class from which it is drawn.

**Domain 4—Comparison:** the decisive comparison is of cardinalities: nonblack things are immeasurably more numerous than ravens; the weights of the observations stand in the ratio of the inverse cardinalities.

**Domain 5—Inference:** both the contraposition and the Bayesian computation are flawless. The problem is not in the inference.

**Domain 6—Reflection:** laughter at “ornithology by apples” is a signal about *magnitude*, not about the fact; and a second signal, Good’s: ask by what procedure the observation was obtained—whether it could have met a raven at all.

## Diagnosis

**Category:** non-paradox—a problem of confirmation: a counterintuitive truth about its arithmetic. **Location of the defect:** expectation—the binarization of graded confirmation and blindness to the weights of classes. **No law is violated:** the equivalence of the contrapositive is given by [[Identity]], and it is intact. On the E/R/R triad: the hypothesis is a Rule over classes of Elements; the weight of evidence is set by the cardinality of the class from which it is taken; intuition reads the Rule of confirmation without weights—and gets an apple equal to a raven.

## Resolution

Accept the conclusion—with the exact weight. A Bayesian sketch: in a world of a million nonblack things and a thousand ravens, a green apple raises the probability of the hypothesis by an amount of the order of a millionth, a black raven by the order of a thousandth: both confirm, they confirm unequally, and the “paradox” is the surprise at an epsilon read as zero or as one. A small world straightens intuition: there are ten objects in a room, and the hypothesis is “all ravens here are black”; to go through everything nonblack and find no raven is an honest *proof*: the contrapositive works at full strength when the class can be surveyed—the strategy “check the nonblack” is absurd economically, not logically: in a large world it is the most expensive path. Good’s correction completes the picture: what confirms is the sample, not the object—a random apple from a basket of apples confirms nothing, since it could not have met a raven; weight belongs only to an observation that could have refuted the hypothesis and did not. This is the Popperian core, extracted from an absurd example: the informativeness of a test equals its risk.

## Lesson

**On graded confirmation.** “Confirms” is a magnitude, not a checkmark; the dispute over “does the apple confirm” is a dispute of the quantum with the quantity. **On the weights of classes.** Evidence weighs according to its class of origin—the same third term as the base rate in [[False Positive|diagnostics]]. **On sampling.** Only what could have refuted confirms: the procedure by which an observation was obtained is part of its weight. **On laughter.** The absurdity of an example is often a signal about the size of an effect, not about its absence; check the order of magnitude before laughing at a fact.

## Kin by Mechanism

[[False Positive|False positives]] (the weights of classes—base rates), [[Lottery Paradox|the Lottery]] and [[Preface Paradox|the Preface]] (the binarization of the graded—a family motif of the category), Goodman’s “new riddle of induction” (a neighbor from the same workshop of confirmation), Popper’s falsifiability (risk as the measure of informativeness).

**Machine check.** In the registry of 46—`N8_Raven`: category `NonParadox`; the status of the category is formalized (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v), the general summary—`all_46_dissolvable` and `total_paradoxes_46`. The weight core (the inverse cardinalities of classes over Q) is the sixth and last candidate of the probabilistic six for the “Probability” branch (see [[Formalization]]).

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
