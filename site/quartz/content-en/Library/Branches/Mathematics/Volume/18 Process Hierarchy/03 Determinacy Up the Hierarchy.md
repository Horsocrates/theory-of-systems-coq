---
title: "Chapter 3. Determinacy Up the Hierarchy"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/18 Процессная иерархия/03 Детерминированность вверх по иерархии.md"
sourceBlob: 036d42d8f968d2230046074e0e7bd136cbd4719f
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The ascent has been built (Chapter 1) and supplied with a scale of depth (Chapter 2). Now the scale will go to work on a concrete classical “wall”—*the determinacy of games*.

Classically the matter looks like this. Martin’s theorem states: every Borel game is determined—one of the players has a winning strategy. But its proof *climbs a completed tower* of iterated power sets, and this tower has real proof-theoretic strength: it requires iterating the power-set operation up to $\omega_1$. Seen from the familiar packaging, this is exactly the blank “wall”: determinacy is *supposedly* inseparable from a completed infinite tower.

The thesis of the chapter is a P4 rollback: the wall turns out to be an *ascent*, and nonconstructivity enters it *not as a wall but at one precisely localized point*.

*Determinacy is an ordinal-process ascent: the lowest rung is free of the oracle, while all the “infinity” gathers in one step—and this step is exactly the LPO rung from storey 1.*

## What the Chapter Establishes and What It Does Not

*Proved exactly and without axioms*: on a finite game tree the winner is *computable* by backward induction; the step from the finite to the infinite—the question “will player I ever win”—is exactly LPO; and under the Law of Excluded Middle it collapses[^1].

*Not proved here (the horizon)*: the *full* strategic determinacy of Gale–Stewart open games (where one also needs a strategy of *evasion* for the second player), and still less Martin’s full Borel determinacy. They remain a *horizon-ascent*—honestly localized by rung, but not fully built. That the decidable “clopen/open” dichotomy of the outcome is equivalent to LPO is a known fact of constructive reverse mathematics; our contribution is to *place* this step on the ordinal-process ascent and to connect it by a bridge with backward induction.

## The Lowest Rung: Backward Induction without an Oracle

Let us begin with a finite game—a finite tree of positions in which at every leaf it is known whether the one to move wins. The outcome for “the one to move” is computed by *backward induction*: a position is won if there is a move after which the opponent loses. This is a *total computable function* on a finite tree—the answer always exists and is obtained by finite computation[^2].

*On a finite tree determinacy is rung 0: pure backward induction, without any completed tower and without an oracle.*

No hierarchy of power sets arises here: a finite game is the Element side of the finitization boundary. The completed tower one might have expected *was not needed*.

## The Step to the Infinite Is LPO Again

Now let us raise the game to an infinite horizon. We present an open game as a *process of finite truncations*: at horizon $K$ the game is cut down to a finite tree, and its winner is decided by backward induction (rung 0, without an oracle). We obtain an *outcome thread*: at each stage, “does player I win the game truncated at $K$.”

Let us ask about the whole game: *will player I ever win*—that is, does the outcome thread fire at some stage, or does it never fire? But this is *exactly* the question of storey 1 from Chapter 2—“fires or never”—and it is LPO.

And the equality here is complete: the outcome dichotomy *for all* such games is equivalent to LPO—for every Boolean thread is the outcome thread of a suitable game (a game consisting of leaves alone)[^3].

Here is the exact localization for the sake of which the chapter was written:

*The finite rungs of determinacy are free (backward induction, without an oracle); all the “infinity” gathers in **one** step—stitching the truncations into an infinite game—and this step is exactly the LPO rung.*

Nonconstructivity, then, enters the ascent not as a solid wall but *at one point*, and the point is named—the LPO rung. Let us stress: we do *not postulate* it—the theorem is an equivalence (the step and LPO are one and the same), and we only name the rung where the Law of Excluded Middle would be needed. And, like every rung (Chapter 2), it collapses classically: the Law of Excluded Middle decides the outcome dichotomy for every game[^4]—the depth of this step is visible only under P4.

## An Ascent, Not a Wall

Let us assemble the picture. The rungs of determinacy are indexed by an ordinal-process: their height is the same $\omega=\mathrm{OLim}$ as that of the tower of Chapter 1[^5], and the ascent is *generative*—there is no maximal rung. The chapter’s summary theorem gathers this into one statement: the finite rung is decidable without an oracle, the open rung is LPO and collapses classically, and the index is an ordinal-process[^6].

What lies above the open rung—the full strategic determinacy of open games and Martin’s Borel tower with its proof-theoretic strength—remains a *horizon*. But this horizon is *not a wall*: it is a *graded ascent* on which we know exactly how far we have climbed (rung 0 is free, rung 1 is LPO), and above lies an open path, not a locked door.

*The “wall” of determinacy has turned out to be an ascent: the reachable bottom is reached as a process, nonconstructivity is localized in one rung, and the height is honestly declared a horizon.*

## E/R/R Analysis: The Ascent of Determinacy as a System

Let us analyze the ascent by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is *backward induction*: on a finite tree the winner is determined by the move “there is a reply after which the opponent loses.” Adjoining it is the rule of passage to the limit—stitching the finite truncations into an outcome thread—and it is precisely this passage that charges the LPO rung. The third rule is the collapsing one: the Law of Excluded Middle decides the dichotomy for free.

**Roles (L4).** A strategy plays the role of a *process*—a rule leading from a position to a move. The rung plays the role of the *measure of omniscience* of the step (rung 0 for a finite game, LPO for the open horizon). The height of the ascent has the role of an *ordinal-process*.

**Elements (L1 + P4).** The bearers are the finite trees of the truncations and their computable winners. Under P4 the finite truncations are actual; “wins at stage $K$” is a completed search (an Element), while “never wins” is a role-limit, and it is for this that LPO is charged.

**Well-formedness check.** Backward induction, passage-to-the-limit, and the collapse are Rules; the strategy, the rung, and the height are Roles; the finite truncations are Elements; there are no overlaps. There is no self-application: the rule of passage stands above the truncations and is not one of them.

**What the analysis yields.** It shows that “is completed infinity needed for determinacy?” is formulated too coarsely: on the finite rung it is not (backward induction), on the open rung exactly one dose is needed, LPO, and above that lies an honest horizon. The completed tower was packaging, not necessity; what turned out to be necessary is one precisely named rung.

The chapter has given the rollback of one “wall.” In the next chapter the same device is applied to the second—to the minimal bad sequence of Kruskal’s theorem: there too “choice along a completed tower” will turn into a *process over the decidable*, axiom-free.

---

[^1]: The file `DeterminacyAscent`; machine-checked, 0 axioms (LPO/L3 are hypothesis-propositions). It relies on the finite determinacy of `FiniteGameDeterminacy` and on the ladder of omniscience `RoleLimitLadder` from Chapter 2.
[^2]: `finite_depth_decidable`: on a finite tree, being a win is *decidable* (a Rocq decision $\{ \cdot \}+\{ \cdot \}$), not merely “classically determined.” Backward induction `mover_wins` is total. 0 axioms.
[^3]: `eventual_decided_is_LPO`: the dichotomy “player I wins at some stage $\vee$ wins at none,” taken over all game-processes, is *equivalent* to LPO. Machine-checked, 0 axioms.
[^4]: `eventual_decided_classical`: the Law of Excluded Middle implies the decidability of the outcome dichotomy (through $\text{LEM}\to\text{LPO}$). 0 axioms.
[^5]: `determinacy_ascent_height_is_omega`: the index of the rung of determinacy is $\omega$ as the limit of a process. 0 axioms.
[^6]: `determinacy_is_ordinal_process_ascent`: finite determinacy $\wedge$ (open rung $=$ LPO) $\wedge$ (L3 collapses) $\wedge$ (index $=\omega$-process) $\wedge$ (no maximal rung). 0 axioms.

---

Part: [[18 Process Hierarchy|Part XVIII. The Process Hierarchy]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/02 Depth Equals Rung of Omniscience|Chapter 2. Depth = Rung of Omniscience]] · [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/04 Well Ordering as Process over the Decidable|Chapter 4. Well-Quasi-Ordering as a Process over the Decidable]] →
