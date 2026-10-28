---
title: "Chapter 2. Depth = Rung of Omniscience"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/18 Процессная иерархия/02 Глубина = рунг всеведения.md"
sourceBlob: 8ffa81ecb1ec4cb0f3f9930d156470dd6cf56894
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 1 showed that the role-limit side is an ascending tower of role-types: strictly growing (a diagonal on every storey), generative (without a top), indexed by the ordinal-process $\omega$. But “higher” there meant only *wider*—more predicates. The present chapter adds a second dimension: the storeys are not only wider, they are *deeper*. A question posed on a storey requires a definite measure of “completed infinity”—and this measure grows with height.

*To each storey of the tower there corresponds a **rung of omniscience**—exactly as much completed infinity as the question on that storey requires. The ascent is graded by depth.*

And here is the main observation of the chapter, one the classical view does not see: *this gradation is constructive*. Under the Law of Excluded Middle all the rungs collapse into one, the ladder becomes flat, and depth disappears. It shows through *only* in the constructive, P4 optics. In other words, “the depth of the hierarchy” is a phenomenon of *our* view of processes, not a property visible to classical logic.

## What the Chapter Establishes and What It Does Not

Let us outline the contribution honestly. *Proved exactly and without axioms*: the lowest storey is decidable (rung 0), the storey of predicates over ℕ corresponds exactly to the *limited principle of omniscience*, and this gradation collapses under the Law of Excluded Middle—that is, it is constructive[^1].

*Borrowed, not new*: the ascending implications between the rungs themselves ($\text{LPO}\to\text{WLPO}\to\text{LLPO}$ and others) are standard constructive reverse mathematics (Bishop, Ishihara). *Not proved here*: the *strictness* of the rungs—that the implications are irreversible, that the rungs are really distinct—requires model-theoretic constructions (realizability, Kripke models) and is not built in our foundation; this is stated honestly, and here we stop[^2]. Our own contribution is modest and exact: *to place the storeys of the tower on this ladder* and to record by machine *the constructivity of the gradation itself*.

## The Zeroth Storey: Decidability without Omniscience

The zeroth storey is the carrier ℕ. Here the question of the equality of two elements is *decidable*: for any $m,n$ one can establish in finitely many steps whether they are equal or not[^3]. No omniscience is required: the answer is given by a finite procedure, a pure Element. This is rung 0—the base of the ladder, the Element side of the finitization boundary.

It is essential that decidability here is *not* postulated but simply is: natural numbers are compared by a finite process. Everything that lies on the zeroth storey is free of completed infinity by its very arrangement.

## The Storey of Predicates Is Exactly LPO

Let us go up one storey: predicates over ℕ are Boolean threads $g:ℕ\to\{\text{yes},\text{no}\}$. Of such a thread it is natural to ask: *does it ever fire, or does it never fire?* That is:

$$
\bigl(\exists n:\ g(n)=\text{yes}\bigr)\quad\text{or}\quad
  \bigl(\forall n:\ g(n)=\text{no}\bigr).
$$

This is not an innocent question. To answer “never,” one must *survey the whole infinite process* of the thread—that is, complete infinity. The statement that this question always has an answer bears a name: the *limited principle of omniscience* (LPO).

*The question of the storey of predicates—“fires or never”—is exactly LPO.*

And this is not an analogy but an *identity*: the ability to decide the question on this storey is *equivalent* to LPO—no more and no less[^4]. Thus storey 1 receives an exact rung: $\Sigma^0_1$-omniscience, exactly one step of completed infinity above the decidable base.

Here the ontology of the finitization boundary is visible in miniature. “Fires somewhere” is a *terminating* search (the stage is found—stop: an Element). “Never fires” is a *non-terminating* process, a role-limit: no finite stage confirms it. LPO is precisely the demand to decide *which* of the two roles the thread has—and this is already a demand concerning one completed infinity.

## The Ladder of Omniscience

Storey 1 gives the first nontrivial rung, but not the only one. Beyond it there are finer and stronger principles, and they line up into a *ladder* ordered by *how much* completed infinity the question requires (by quantifier depth):

$$
\text{LLPO}\ \prec\ \text{WLPO}\ \prec\ \text{LPO}\ \prec\ \text{LPO}_\omega .
$$

LLPO is an ultra-weak fork principle (“if two events cannot both fire, then one of them never fires”); WLPO decides the truth-value of “never” without a witness; LPO is our storey 1, a decision with a witness; and $\text{LPO}_\omega$ is the *cascade* rung: “do infinitely many threads fire, or only finitely many”—the boundary of boundaries.

The ascending implications are proved: a higher rung implies a lower one[^5]. In particular, the cascade is strictly more demanding than a single question: $\text{LPO}_\omega\to\text{LPO}$ is proved directly[^6]. Thus the ladder grades the role-limit side: the higher up the tower a question rises, the higher its rung of omniscience.

## The Gradation Is Constructive (and Visible Only through P4)

Now for the observation for the sake of which the chapter was written.

Take the Law of Excluded Middle. Under it the question of storey 1 is decided *for free*: “either the thread fires somewhere, or it does not” is simply an instance of “either $A$ or not $A$”[^7]. The same holds higher up the ladder: classically *all* the rungs hold. Hence, under the Law of Excluded Middle, *the ladder is flat*—all the principles are theorems, and there is no depth.

*The depth of the storeys is visible only without the Law of Excluded Middle. This is a constructive, P4 phenomenon: classical logic does not distinguish it.*

This is the exact sense in which “the P4 optics is finer than the classical one.” It is neither a new theorem nor a dispute with classical mathematics; it is a known meta-fact—*classically flat, constructively graded*—made explicit by machine. For us it matters in principle: *the depth of the process hierarchy is a property of processes, readable only by a processual view*. Whoever accepts completed infinity for free (through the Law of Excluded Middle) does not see that different storeys require different measures of it—for them everything is already completed. P4, by declining completedness for free, makes the measure visible.

## E/R/R Analysis: The Ladder as a System

The ladder of rungs is itself a *system*, and its analysis by E/R/R—in the generating order Rules $\to$ Roles $\to$ Elements—clarifies what distinguishes “depth” from “width.”

**Rules (L5).** The holding rules are the ascending implications between the rungs (a higher one implies a lower one; proved constructively) and the *collapsing* rule: the Law of Excluded Middle implies every rung. Adjoining them is the boundary of the method: the strictness of the rungs (irreversibility) is *not* established by the rules of this level—it needs a model, and here we stop.

**Roles (L4).** Each rung plays the role of a *measure*: “how much completed infinity the question requires.” The quantifier depth of the question is the index of the rung. The Law of Excluded Middle plays the role of an *oracle* that collapses all the measures into one. The positions are grounded by structure: a rung is defined not by the “nature” of the question but by its relation to the rules—by which implications enter it and leave it.

**Elements (L1 + P4).** The bearers are the Boolean threads $g:ℕ\to\{\cdots\}$ and the finite prefixes that can be surveyed. Under P4 only finite prefixes are actual; the answer “fires” is actualized by a finite stage (an Element), while the answer “never” remains a role-limit—and it is precisely for it that the rung of omniscience is charged.

**Well-formedness check.** Each component is in one category: the implications and the collapse are Rules, the rung-as-measure is a Role, the threads and prefixes are Elements. There is no self-application: the rule that sorts the rungs stands above them and is not one of the rungs.

**What the analysis yields.** It shows that the “depth” of the hierarchy is not a second “width” but a *relation to completed infinity*: a storey is the deeper, the more of it its question requires. And it explains why depth is invisible classically: the oracle L3 equalizes all the measures, erasing the very relation by which depth is measured.

Chapter 1 gave the ascent; this chapter has given its *scale of depth*. In the next chapter the scale will go to work on a concrete problem—the determinacy of games: we will see that nonconstructivity enters the ascent not as a wall but *at one precisely localized point*, and this point is exactly the LPO rung from storey 1.

---

[^1]: The file `HierarchyDepthLadder` together with `RoleLimitLadder`; machine-checked, 0 axioms. The principles of omniscience are *hypothesis-propositions* (Prop) here, not axioms: none of them is declared true; what is proved is only the implications between them and their collapse under the Law of Excluded Middle.
[^2]: The irreversibility of the implications cannot be asserted without a model; invoking the Law of Excluded Middle, on the contrary, would *flatten* the ladder. Therefore the strictness of the rungs is cited as a known result rather than proved.
[^3]: `level0_decidable`: equality on the zeroth storey is decidable. 0 axioms.
[^4]: `level1_decision_is_LPO`: the decidability of the question “fires or never” on the storey of predicates is *equivalent* to LPO. Machine-checked, 0 axioms.
[^5]: The summary theorem `role_limit_ladder`: $\text{LPO}_\omega\to\text{LPO}\to\text{WLPO}\to\text{LLPO}$ (and $\text{LPO}\to$ Markov’s principle). Machine-checked, 0 axioms.
[^6]: `lpo_omega_lpo`: the ability to decide “finitely or infinitely many firings” implies the ability to decide “does a single thread fire.” 0 axioms.
[^7]: `lem_decides_level1`: the Law of Excluded Middle implies the decidability of the question of storey 1 (that is, LPO). 0 axioms. Likewise the whole top of the ladder: classically $\text{LPO}_\omega$ holds as well.

---

Part: [[18 Process Hierarchy|Part XVIII. The Process Hierarchy]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/01 Ascending Tower of Role Types|Chapter 1. The Ascending Tower of Role-Types]] · [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/03 Determinacy Up the Hierarchy|Chapter 3. Determinacy Up the Hierarchy]] →
