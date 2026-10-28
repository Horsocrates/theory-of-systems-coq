---
title: "Chapter 6. Complexity as the Price of Finitization"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/06 Сложность как цена финитизации.md"
sourceBlob: c0ddbdeaed0622aca91717fda721603525612249
translated: 2026-10-20
status: draft
---

## The Third Axis: Price

Until now the finitization boundary has had two axes. *Is it possible?*—the diagonal (15.3) rules out a total decider. *How to finitize?*—the discriminant (15.4) and fuel (15.5) give a finite procedure where there is one. The third remains:

> **once a computation is finite, what is its *price*?**

*Complexity* in our system is the *price of finitization*: a structural quantity of a finite process (the number of L5 steps, the size of the search). And this quantity is defined *precisely because* the process has been finitized: an unbounded process has no finite price—price is a property of a P4-finite run. In this chapter complexity is considered on the positive, *finitized* side: when a computation or a verification is already given as a finite process, we ask about the price—“how much does it cost,” not “is it possible.” At the same time, *complexity adds no new ontological boundary*: it measures distance *within* the Element side—two processes can be equally finite yet cost radically different amounts. Therefore it is a *metric* of the positive side of the boundary, not a third master structure alongside the diagonal and the discriminant.

The chapter is short on purpose: complexity theory is a large standard discipline (with its own intractability and lower bounds), and we do *not* retell it. Our contribution here is a *frame* (price as a quantity of the finitized side), and its main question we honestly *pose* rather than solve.

## Verification Is Cheap; Search Is a Question of Price

The central asymmetry is simple. The *verification* of a presented certificate belongs to the Element side: it is given by a finite Boolean computation (in the classical complexity frame this is refined as *polynomial* verification in a chosen cost model). To *find* a certificate is a search, and here the question of price arises. Formally: a problem is *in NP* if there is a verifier $v$ that checks an input / certificate pair; *in P* if there is a direct decider. A decider immediately gives a verifier that ignores the certificate, so $\mathrm{P}\subseteq\mathrm{NP}$ follows directly from the definitions.[^1]

The key P4 touch: a *bounded* search over certificates is **decidable**—if a bound on the size of the certificate is given, enumerate the finite carrier and check each element. That is, the question of complexity is *not* “can it be found” (under a given bound the search is finite) but *how large this bound is and how expensive the search is*. Complexity is about price, not about possibility; possibility is already secured by finitization.

## P vs NP: A Posing, Not a Solution

Hence the main open question: does *cheap verification* always imply *cheap search*—that is, $\mathrm{P}=\mathrm{NP}$? In our terms: can a search (a potentially high price) always be folded into a direct Element decider (a low price)?

We hold to this strictly and honestly. In our system this question is *named*—as a *predicate*-definition “NP collapses into P”—but it is **not solved** and is not declared solved.[^2] The chapter gives a *lens*—verification is an Element, search is a price, $\mathrm{P}=\mathrm{NP}$ asks whether the price of search reduces to the price of verification—but not a proof and not a survey of complexity theory. We *pose* the question in the Element / price frame, and there we honestly stop.

## E/R/R Analysis and What the Chapter Has Prepared

**Rules (L5).**  Price is a *quantity of the process*: how many times the rule-step has been applied, how large the search is. The rule constitutes not only the result but also its cost.

**Roles (L4).**  The *verifier* (the one who checks) and the *decider* (the one who searches) are two roles; the gap in price between them is the content of $\mathrm{P}$ vs $\mathrm{NP}$. “Cheap / expensive” are *cost statuses* of the process.

**Elements (L1${}+{}$P4).**  Concrete inputs, certificates, bounded searches. *Not* an element: an unbounded search without a budget—it has no finite price.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| step as a quantity; size of the search | the constitution and price of the process | Rule (L5) |
| verifier / decider; “cheap / expensive” | roles and cost statuses | Role (L4) |
| inputs; certificates; bounded search | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Price is defined only on the finitized side: an unbounded process has no price. Therefore complexity is a natural continuation of the finitization boundary, *not* a new boundary. Verification is an Element; the question $\mathrm{P}$ vs $\mathrm{NP}$ is open, and we only *pose* it.

**What the chapter has prepared.**  The third axis of the boundary has been named: after “is it possible” (the diagonal) and “how to finitize” (the discriminant / fuel) comes “how much does it cost.” Only the *framework* of the posing has been assembled by machine (verification is an Element, $\mathrm{P}\subseteq\mathrm{NP}$, bounded search is decidable; $\mathrm{P}=\mathrm{NP}$ is a named open question), 0-axiom; complexity theory is not retold, and $\mathrm{P}$ vs $\mathrm{NP}$ is not solved. Next comes the finale, 15.7: both master structures are brought together, *diagonal $\oplus$ discriminant—one finitization boundary*, and price takes its place as the boundary’s third axis.

---

[^1]: Machine-checked, **0 axioms**: `src/cs/PvsNP_Framing.v` (4 Qed)—`verifies`, `Decider`, `in_P` / `in_NP`; `verification_is_element` (verification is an Element), `P_subset_NP` ($\mathrm{P}\subseteq\mathrm{NP}$), `NP_bounded_search_decidable` (bounded search over certificates is decidable). There is also an applied complexity layer in `src/stdlib/complexity/`.
[^2]: `P_collapses_NP` ($\mathrm{in\_NP}\to\mathrm{in\_P}$) in `PvsNP_Framing.v` is a *definition* (a named open question), not a theorem: neither $\mathrm{P}=\mathrm{NP}$ nor $\mathrm{P}\neq\mathrm{NP}$ is proved or claimed.

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/05 Type Safety as Fuel Finitization|Chapter 5. Type Safety as Fuel Finitization]] · [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/07 Synthesis One Diagonal One Discriminant|Chapter 7. Synthesis: One Diagonal, One Discriminant]] →
