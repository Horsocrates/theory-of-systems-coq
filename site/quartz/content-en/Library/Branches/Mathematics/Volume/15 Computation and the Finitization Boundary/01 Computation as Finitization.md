---
title: "Chapter 1. Computation as Finitization"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/01 Вычисление как финитизация.md"
sourceBlob: 422884dae168a03cb2266134c74b782695ecf7c9
translated: 2026-10-20
status: draft
---

## Where the Part and the Chapter Stand

After the metatheoretical turn of Part XIV, where the category turned out to be the *language* of ToS, the volume passes to applied mathematics. Part XV asserts something simple and strong:

> **computation is the finitization boundary made algorithmic.**

The very boundary that divided the rational from the irrational (Part IV), the constructive from the classical, the discrete spectrum from the continuous one, here takes a computational form: an algorithm over finite data either *terminates*—and then it is on the *Element* side, *decidable*—or it does not terminate—and then it is a *role-limit*, undecidable or uncomputable.

This chapter lays the foundation: what computation is in our system and what its *central cut* is—*bounded* halting is *decidable*, while *unbounded* halting is a role-limit. Further on, the part will unfold the two sides of this cut: the undecidable one (one diagonal, 15.3) and the decidable one (one discriminant, 15.4), between which lies the graded ladder of languages (15.2).

## Computation as a Process

*Computation* in ToS is a process with its own E/R/R triad. Its *elements* are configurations (states of the machine). Its *rule* is the ordered *step*: it is precisely the ORDER of steps (L5) that turns a sequence of configurations into a *computation* rather than an arbitrary list. And its *status* is *halting*: whether the result has been reached (this is a status component, not a role—see\ the analysis in §15.1.6).

The machine is run to a *finite depth* $n$, not “to the end”—this is P4 (“infinity is a property of process, not of object”):

$$
\mathrm{run} 0 c = c, \quad
  \mathrm{run} (n{+}1) c =
    \begin{cases}
      \mathrm{run} n c, & \text{if } c \text{ has already halted at step } n,\\
      \mathrm{step} (\mathrm{run} n c), & \text{otherwise.}
    \end{cases}
$$

Once the result is reached, the configuration becomes a *fixed point* of the further run (halting is absorbing), and the fact of halting itself is *monotone* in the budget: having appeared at step $n$, it persists for all $m\ge n$.[^1] All these facts are constructive: they require neither classical logic nor choice.

To speak of computation as an *object* rather than a set of scattered definitions, our system binds configuration, step, and status into one *arena*—a model of computation as a single record.
[^2]

## The Element Side: Bounded Halting Is Decidable

Fix a budget $n$. The question “has the configuration halted within $n$ steps?” is

$$
\mathrm{halts_in} n c \;:=\; \bigl( \mathrm{halted} (\mathrm{run} n c) = \text{true} \bigr),
$$

and it is **decidable**: for any fixed $n$ there is a *constructive Boolean decision*—run $n$ steps and look at the status. This is a *terminating* procedure, and it is 0-axiom.
[^3] This is the *Element* side of computation: finitely actual, computable, observable. A countdown machine from $3$ halts within the budget—a fact checked by direct computation.

It matters *why* bounded halting is decidable: the budget $n$ makes the process *finite* (P4). The decision does not “guess the future”—it only reads the result of a finite run. There is not a shadow of undecidability here: all the difficulty of the part will arise exactly when the budget is removed.

## The Role-Limit Side: Unbounded Halting

Let us remove the budget. *Full* halting

$$
\mathrm{halts} c \;:=\; \exists  n,\ \mathrm{halts_in} n c
$$

is the completion of the run over *all* budgets. The positive case by itself has a finite witness (if the machine has halted within some $n$, then this is an Element); a **role-limit** arises *as a universal recognition problem*—to decide this predicate for *all* configurations at once (in particular, negatively) requires control over all budgets simultaneously. Dually, *divergence* \(\mathrm{diverges} c := \forall n,\
\mathrm{halted} (\mathrm{run} n c)=\text{false}\): the result is not reached at any finite depth; halting and divergence are mutually exclusive.

**P4 diagnostics.**  Unbounded halting is *not* an Element object. To take “does it halt at all?” as a decidable Boolean predicate is to *reify a role-limit into an Element*: a category mistake of the same kind as “infinity as a completed object” (Part IV). The honest formulation is “*a role-limit cannot be finitized into an Element decider*,” not “we cannot compute it.” The exact form of this—the absence of a universal halting decider—is given by the *diagonal* (15.3); here we only draw the cut: the *bounded* is an Element, decidable; the *unbounded* is a role-limit. An increment machine without a halting status gives an example of the negative side: every finite run exists, but there is no result at any budget—divergence, a pure role-limit.

## The Finitization Boundary Made Algorithmic

The cut “boundedly decidable / unboundedly a role-limit” is the **finitization boundary of the project** (Element / role-limit), now in computational form:

$$
\begin{gathered}
\text{terminates with a finite witness (within a fixed budget)} \\
  \Longleftrightarrow\quad \text{Element} \quad\Longleftrightarrow\quad \text{decidable at a finite stage}.
\end{gathered}
$$

Precision is essential here: the unbounded predicate $\mathrm{halts} c:=\exists n,\ \mathrm{halts_in} n c$ *in a concrete case* may have a finite witness $n$ (if the machine has indeed halted)—and then it is an Element; the role-limit arises in the demand for a *total* decider of this predicate for *all* programs, and it is this decider that the diagonal will rule out (15.3). This is the same line that in Part IV divided the rational (a terminating process) from the irrational (a nonterminating one) and, as a general principle, the constructive from the classical. Computation only makes it *algorithmic*: decidability becomes a property of a concrete procedure at a finite stage.

The boundary has two sides, and one arena carries both. The *undecidable* side has one engine—the diagonal (the fixed-point theorem), which yields halting, Rice, Cantor, and Kolmogorov (15.3). The *decidable* side has one criterion—the discriminant of the reduction atlas (15.4). Between them lies the graded ladder of languages (15.2). All of this is assembled into one machine result—“computation is the finitization boundary”: Element decidability on any machine, the role-limit as one diagonal, the root in Lawvere’s theorem.[^4]

## E/R/R Analysis: Computation as E/R/R

**Rules (L5).**  The ordered step (L5) makes a sequence of configurations a *computation*; `run` $n$ is the unfolding to a finite depth (P4); and the cut “terminates $\Leftrightarrow$ Element” is itself a rule constituting computability.

**Roles (L4).**  *Halting* (`halted`) is a *status* (what the configuration has *become* under the rules), not a role (the distinction Status $\neq$ Role); the halting decider is a role-oracle; *unbounded* halting $\mathrm{halts}$ is a role-limit (the completion of `run` over all $n$).

{

**Elements (L1${}+{}$P4).**  Concrete configurations, fuel-bounded runs `run` $n$, the countdown machine. *Not* an element: a total halting oracle—its role-limit cannot be finitized into an Element decider (P4 / the diagonal rule it out).}

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| ordered step + `run` $n$ + the cut “terminates${}\Leftrightarrow{}$Element” | the constitution of computability | Rule (L5) |
| halting status; decider-oracle; $\mathrm{halts}$ ${}={}$ role-limit | the status and limits of the process | Role (L4) |
| configurations; runs `run` $n$; `countdown` | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Bounded halting (a fixed budget) = Element: decidable, Boolean, 0 axioms. Unbounded = role-limit: “to decide halting in general” would be a level confusion. The boundary does not rule out—it *names the scale*: what is captured by a finite run, and what is a limit/process.

## What the Chapter Has Prepared

Computation has been presented as a process with the E/R/R triad: configurations (elements), the ordered step (the rule, L5), the halting status (role); `run` $n$ is the unfolding to a finite depth (P4), and the configuration arena binds them into one object. The central cut of the part has been drawn: **bounded halting is decidable** (Element, 0 axioms), **unbounded halting is a role-limit**; this is the finitization boundary made algorithmic. Everything rests on the 0-axiom machine-checked layer; the honest walls (uncomputability, the uncountability of the continuum) will take their places later and will be gathered in 15.7.

Next comes Chapter 15.2: *finite memory and the Chomsky ladder*, where the Element floor (the regular languages) turns out to be the lowest rung of a graded gradient of role-limits leading up to the very top—halting (15.3).

---

[^1]: `src/cs/HaltingRoleLimit.v` (13 Qed, 0 Admitted, **0 axioms**): `run`, `run_absorb` (absorption), `halts_in_mono` (monotonicity in the budget), `halts_not_diverges` (the mutual exclusion of halting and divergence).
[^2]: `src/cs/ComputationModel.v` (3 Qed, **0 axioms**): `Record CompModel` (configurations ${}+{}$ step ${}+{}$ status), `cm_halts_in`, `cm_halts`; a concrete inhabitant of the arena is the countdown machine (`countdown`).
[^3]: `HaltingRoleLimit.v`: `bounded_halting_decidable`, the decidability $\{\mathrm{halts_in} n c\}+\{\neg \mathrm{halts_in} n c\}$; the same decidability on the arena is `ComputationModel.cm_ bounded_ decidable`.
[^4]: `ComputationModel.computation_ is_ finitization_ boundary`: the conjunction of (1) bounded halting is decidable on any machine; (2) one diagonal in four faces; (3) the root is `lawvere_fixed_point`. **0 axioms**. Here it serves as an *orienting* synthesis; it is unfolded in detail in the finale, 15.7.

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/14 Category of Systems/07 Synthesis All of Tos as a Category Bridge to Type Theory Map of Boundaries|Chapter 7. Synthesis: All of ToS as a Category; the Bridge to Type Theory; the Map of Boundaries—Part XIV]] · [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/02 Finite Memory and the Chomsky Hierarchy|Chapter 2. Finite Memory and the Chomsky Ladder]] →
