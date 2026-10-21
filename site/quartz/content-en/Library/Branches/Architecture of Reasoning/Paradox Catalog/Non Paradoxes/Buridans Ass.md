---
title: "Buridan’s Ass"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Не-парадоксы/Буриданов осёл.md"
sourceBlob: 1b5571841f575df1ec184f16ef60d0f23dbc71d2
translated: 2026-10-20
status: draft
description: "Resolved by random choice"
---

**N.7** · [[Non Paradoxes|non-paradox]] · subtype: Problem of Choice

**Essence of the error.** Resolved by random choice

## Exact Formulation

A hungry ass stands exactly midway between two identical stacks of hay. The stacks are indistinguishable: distance, size, smell—everything is equal. The ass has no ground to prefer one to the other, and without a ground a rational agent does not act. The conclusion: the ass will die of hunger between two dinners. The general form: rational choice between perfectly equal alternatives is impossible.

## Origin

The name is a historical irony: there is no ass in the writings of Jean Buridan. The root is older—Aristotle (*On the Heavens*) mentions a man equally hungry and thirsty, frozen between food and drink. Buridan discussed whether the will can defer a choice until the greater good has been made out; the ass was ascribed to him by his opponents as a caricature: this is where your intellectualism about the will leads. Spinoza accepted the scenario: a man placed in such an equilibrium “would die of hunger and thirst”; asked whether such a one “should not rather be considered an ass than a man,” he answered: “I do not know” (*Ethics* II, prop. 49, schol.; trans. R. H. M. Elwes, 1883). Leibniz brought the knot under the principle of sufficient reason and answered ontologically: perfect symmetry does not occur in the world—there are no two indistinguishable stacks. An unexpected second birth came from engineers: Lamport gave the name “Buridan’s principle” to the metastability of digital arbiters—a circuit obliged to choose between two simultaneous signals can hang in the boundary zone for an unbounded time; the ass has made its way into microchips.

## Why This Is Not a Paradox

What the story holds is a false model of decision, with no contradiction in it. The hidden premise of the story: “a rational act requires a ground for preferring one alternative to the other.” It confuses two different grounds: the ground *to act* (hunger—it is there, and it cries out) and the ground *to prefer A to B* (it is absent—and not needed). Rationality requires the first; the second is needed only by a model in which the sole rule of choice is the comparison of value. Real agents—and honest algorithms—hold a second rule: the resolution of ties. A tie is a legitimate verdict of comparison; the system has not broken down. After the verdict “equal,” the choice passes to another mechanism—a lot, a habit, an order—and dinner takes place. What dies is not the ass but the model with one rule.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: an agent, two equal alternatives, hunger, the demand for a ground. Signal: the conclusion (“it will die”) diverges wildly from the observed world—no ass has ever perished this way.

**Domain 2—Clarification: what do the terms mean?** Here lies the defect of expectation. “No ground”—a ground *for what*? A ground exists—it is present (hunger); a ground to prefer is absent. Gluing “the ground of the act” to “the ground of preference” is what produces the paralysis. Signal: [[Sufficient Reason]] requires a ground for action—and the story has one.

**Domain 3—Framework Selection:** a model of the agent with a single Rule (maximize preference) is a framework that does not fit the object: a complete system of choice contains both a rule of comparison and a rule for resolving ties.

**Domain 4—Comparison:** the comparison of the stacks honestly yields a tie—and this is not a malfunction of the instrument but its legitimate verdict: “equal.”

**Domain 5—Inference:** within the model the conclusion holds—the model’s ass dies; this is a reductio of the model, not of the world.

**Domain 6—Reflection:** the divergence of the model from reality is a signal to repair the model, not to declare the world paradoxical; a return to domains 2–3.

## Diagnosis

**Category:** non-paradox—a problem of choice: a counterintuitive conclusion from a truncated model. **Location of the defect:** the expectation that rational choice is exhausted by preference. **No law is violated**—on the contrary, the knot affirms one: the resolution of equalities is given by the Law of Order. On the E/R/R triad: two Elements with equal Roles of value; the choice need not pass through the Role of value—the Rule of order decides without it; the death of the ass is an artifact of a model that lacks such a Rule.

## Resolution

Separating the grounds settles the philosophical part: the principle of sufficient reason requires a ground for the act—hunger gives it; the equality of the stacks cancels only preference, not action. The theory of choice adds a name: picking versus choosing—choice without preference (the first to hand, a lot) is a legitimate operation, and where the stakes are equal, rationality does not merely tolerate it but prescribes it: to spend time searching for a nonexistent difference—that is what is irrational. Our own layer is the strongest: in the Theory of Systems the resolution of ties is a law—the fifth: the constitutive order. A system that meets equals takes the first in the order of consideration—deterministically, without any “axiom of choice” and without differences in the objects themselves; in the formal base this is a load-bearing construction: `l5_resolve_gen` resolves any nonempty list of candidates (L5Resolution.v), and the selection of the maximum by index works by the same order (EVT_idx.v). In this architecture Buridan’s ass does not starve, by construction. The honest boundary belongs to Lamport: in continuous physics, for an arbiter with two stable outcomes, the boundary zone is ineliminable—the circuit can hang; but this is a fact about the continuous dynamics of bifurcations, not about rationality: engineering answers with order and a timeout—the same L5, cast in silicon.

## Lesson

**On two grounds.** The ground to act and the ground to prefer are different things; paralysis sets in only when they are glued together. **On ties.** A tie is a verdict, not a malfunction; a mature system of rules is obliged to carry a tie-breaker, and the arbitrariness in it is no vice—it is the constitutive order. **On models.** When a model predicts death in the middle of two dinners, it is the model that gets buried; divergence from the world is a diagnosis of the premises, not the discovery of a paradox.

## Kin by Mechanism

[[Buridans Bridge|Buridan’s Bridge]] (a namesake through Buridan—but the mechanics differ: there it is a self-referential norm, the structural family), [[Newcombs Paradox|Newcomb]] (a neighbor from the same workshop, decision theory), Lamport’s Buridan’s principle (the physical shadow of the knot in digital arbiters), choice among indistinguishables in set theory (where, without a rule of order, an axiom really is needed—a contrast that throws L5 into relief).

**Machine check.** Our own analysis is named and load-bearing: `l5_resolve_gen`—the deterministic resolution of a nonempty list of candidates by the constitutive order, `l5_resolve_gen_some`—a nonempty list always yields a choice (src/L5Resolution.v); the same law at work is argmax by index (src/EVT_idx.v). In the registry of 46—`N7_BuridanAss`: category `NonParadox` (`nonparadox_46_not_paradox`, `nonparadox_count_8`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Non Paradoxes|Non-Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
