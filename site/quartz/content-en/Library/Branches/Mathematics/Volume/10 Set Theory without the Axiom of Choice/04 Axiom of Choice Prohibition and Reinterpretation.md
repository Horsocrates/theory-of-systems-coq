---
title: "Chapter 4. The Axiom of Choice: Exclusion and Reinterpretation"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/04 Аксиома выбора запрет и переинтерпретация.md"
sourceBlob: 078b2c47d46708e7793502422b32a5ec792bcae3
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 10.3 localized choice: it is needed neither for the preorder of embeddings, nor for Schröder–Bernstein, nor for Cantor—but it appears in the passage surjection ${}\to{}$ injection and in the demand for the linearity of the cardinal scale. Now let us consider the Axiom of Choice directly. The answer of ToS is *dual*, and this duality is the central E/R/R diagnosis of a strong axiom:

- **Reinterpretation.** The admissible *work* of choice—taking one element from each set of a *finite* family (or from an approximation of a process)—is done by a *rule*: the positional resolution of L5 (“the head of the list”). Then choice is not an axiom but a *theorem* of finite combinatorics.
- **Exclusion.** The *completed-object* form of choice—a choice function $f:ℕ\toℕ$ whose *graph* $\{(n,f(n))\}$ is a ready infinite collection—*contradicts* P4. Already the nat-indexed completed-object form of AC is not merely “not accepted” but *incompatible* with Finite Actuality; full ZFC-AC contains such an object form all the more.

And—the synthesis: *the exclusion is strictly stronger than the reinterpretation*. If the completed form is impossible, then it should not be an axiom either. The precise diagnosis is this: the Axiom of Choice *mixes* a legitimate Rule (the resolution of L5 on demand) with an illegitimate Element-reification (the completed choice graph). ToS keeps the first and rejects the second. At once a reservation that runs through the chapter: the principle L4 (`L4_witness`) is *not* the Axiom of Choice.

*The Axiom of Choice is a role-confusion: the legitimate rule of resolution of L5 glued to an illegitimate completed graph. ToS reinterprets the first as a theorem and excludes the second as incompatible with P4; the exclusion is stronger than the reinterpretation.*

## The Admissible Core: Choice as the Rule L5

What is a “set” at stage $N$ in ToS? A finite list. And what does it mean “to choose an element from it”? To take the *first* in the constitutive order—the head of the list. This is exactly L5: positional resolution. For a nonempty list the head lies in it; for a family of nonempty lists the function “head” gives a choice for all of them at once.[^1]

Therefore the admissible core of choice is a *theorem* of finite combinatorics, not a postulate: L5 (an order that already carries the status of position) itself gives the choice function. From the same finiteness follows also the “finite Zorn’s lemma”: in a nonempty finite list there is a maximal element—simply the maximum of the list, without any choice.[^2]

An important honest reservation about the *boundary* of this core. The version with a quantifier over *all* natural indices ($\forall i$) reads two ways. As a *rule of a process*—“choice on demand for any presented index”—it is P4-compatible. As a *completed graph* $\{(i,f(i))\}$, it falls under the exclusion set out in the next section. Therefore it is precisely the *stage-by-stage* version with a finite front $N$ that is unambiguously P4-compatible; the unbounded one should be read as a rule-on-demand, not as a ready object.[^3]

*Choice on a finite/stage-by-stage family is a role-rule of L5 (the head in the constitutive order); the choice function and the finite Zorn’s lemma are theorems (0 axioms), not postulates. We read the unbounded version as a rule-on-demand, not as an object.*

## The Exclusion: The Completed Choice Graph Is Incompatible with P4

Let us take the full form of choice over $ℕ$: for any family of nonempty lists $F:ℕ\to$ `list` $ℕ$ there exists a function $f:ℕ\toℕ$ with $f(n)\in F(n)$ for *all* $n$. The key point: such an $f$, taken at once over *all* $n$ as a ready object (in the code this completed totality is encoded by `choice_graph`—the completed support of the domain, not a set of pairs with their values), is a *completed infinity*. And P4 (Finite Actuality) requires that at each stage only the finite be actual. A completed infinite collection violates this boundedness—a contradiction.[^4]

Hence already the *nat-indexed* completed-choice form of AC is incompatible with P4—this is stronger than “we do not accept it”; full ZFC-AC contains such an object form all the more, but the formal file records precisely the nat-indexed diagnosis. Here one must draw a precise line between *potential* and *completed* infinity. ToS does not exclude infinite *processes*: potential infinity is fully compatible with P4.[^5] What is excluded is exactly *completed* choice-as-an-object: the graph taken at once, as a whole, as a ready thing. This is the refusal of the Element layer to reify what is legitimate only as a rule-on-demand.

*The full Axiom of Choice is a role-reification: the completed graph $\{(n,f(n))\}$ as a ready infinite object. P4 rules it out (`completed_inf_contradicts_P4`); the potential infinity of a process remains compatible with P4. An exclusion, not merely a refusal of a postulate.*

## Synthesis: The Exclusion Is Stronger than the Reinterpretation

The two levels are not one and the same, and their connection is itself a theorem. *Reinterpretation* says: P4 makes choice *unnecessary* as an axiom, since its work is done by L5. The *exclusion* says: P4 is *incompatible* with the completed form of choice. In the formal synthesis the exclusion *gives* the reinterpretation (if a completed object is impossible, all the more is it not needed as a postulate), whereas reinterpretation by itself does not give the contradiction of the object form—in this sense the exclusion is stronger.[^6]

This is the precise E/R/R diagnosis of a strong axiom. The Axiom of Choice *glues together* two different things: a legitimate *rule* (the resolution of L5 on demand, on a finite front) and an illegitimate *Element-reification* (the completed graph as a ready object). ToS unglues them: it keeps the rule (a theorem, 0 axioms) and rejects the object (incompatible with P4). The same diagnosis applies to the other strong axioms too—we will see this in 10.5 for infinity, impredicativity, ATR$_0$, and $\Pi^1_1$.

*Exclusion ${}\Rightarrow{}$ reinterpretation (strictly): the impossibility of the completed object is stronger than its being unnecessary. The E/R/R diagnosis of AC: unglue the legitimate rule of L5 and the illegitimate completed graph; keep the rule, reject the object.*

## L4 Is Not Choice; and Why There Is No Banach–Tarski

A critical distinction on which the whole of Part X rests. The principle L4 (`L4_witness`) extracts a witness from a *single* existence: from $\exists x, 
P(x)$, the object $\{x\mid P(x)\}$. The Axiom of Choice takes a function over an *arbitrary family* of existences at once. These are objects of *different ontological categories*: the definiteness of a single existence versus simultaneous selection over an unbounded completed collection.[^7] Therefore the results of 10.3 (Schröder–Bernstein, antisymmetry) use L4 but *not* choice: L4 inverts what is *unique*, whereas choice would select over fibers. At the same time, L4 is not a 0-axiom construction but a separate witness principle at the level of L4 (in 10.3 it was applied through `L4_definite`); its price is counted *separately* from choice.

Hence the fate of the pathologies of choice. The Banach–Tarski paradox and the non-measurable Vitali sets require *manufacturing* a non-measurable set by choice over an uncountable family of classes. In the current finite/list layer of P4 there is no such ground: every *decidable* subset of a finite list is itself a finite list (a filter), and length is preserved under finite decomposition—the paradoxical doubling has nothing to stand on.[^8]

*L4 is a rule of extraction, not a completed graph of choice: the strength is comparable, the categories differ. The pathologies of choice (Vitali, Banach–Tarski) lose their footing: under P4, decidable subsets of the finite remain finite, and length is additive.*

## E/R/R Analysis

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the resolution of L5 (head of the list)—choice on a finite/stage-by-stage family; the P4 boundedness of a stage (the source of the exclusion of the completed graph) |
| *Roles* (L4) | “choice” ${}={}$ the role-rule of resolution; the completed graph $\{(n,f(n))\}={}$ an illegitimate role-reification; L4${}={}$ a witness from a single $\exists$ (not choice) |
| *Elements* (L1${}+{}$P4) | finite lists at each stage; the choice function as a completed infinite graph is *not* an Element |

**What it yields.** The admissible core is a theorem (`AC_is_L5`,
`P4_eliminates_AC_finite`, `finite_zorn`; 0 axioms). The full form is
excluded (`P4_prohibits_AC`, `completed_inf_contradicts_P4`). The link is
`prohibition_implies_reinterpretation` (the exclusion is stronger).

**Diagnosis.** In the P4 ontology of ToS, the Axiom of Choice is a gluing of the rule of L5 and the completed graph-Element. L4 is a rule of extraction, not a completed graph of choice: the strength is comparable, the categories differ.

**Honest boundaries.** `P4_eliminates_AC` is proved for families of *finite lists* (finite sets) / as a rule-on-demand—this is *not* full ZFC-AC, which P4 in fact rules out. The anti-Banach–Tarski result is an absence of footing (decidable finite subsets ${}+{}$ additivity of length), not a metatheorem about the falsity of the paradox. Potential infinity is compatible; only the completed object is excluded.

*Choice splits in two: the rule of L5 (a theorem, 0 axioms) and the completed graph (excluded by P4). The exclusion is stronger than the reinterpretation; L4 is a different category, not choice; the pathologies of choice are deprived of footing.*

## Summary and Transition

The Axiom of Choice has received a dual fate in ToS. Its admissible core—choice over a finite (or stage-by-stage) family—is a theorem: the positional resolution of L5 gives the choice function without any axiom (`AC_is_L5`, `P4_eliminates_AC_finite`). Its completed-object form—the choice graph as a ready infinity—is excluded, since it is incompatible with P4 (`completed_inf_contradicts_P4`); and the exclusion is strictly stronger than the reinterpretation (`prohibition_implies_reinterpretation`). The principle L4 is not choice but the definiteness of a single existence; under P4 the pathologies of choice lose their footing.

Chapter 10.5 will extend the same two-level diagnosis to the rest of the tower of strong axioms: ordinals as processes, and Infinity, impredicative comprehension, arithmetical transfinite recursion (ATR$_0$), and $\Pi^1_1$ comprehension as strong principles whose admissible core is reinterpreted and whose completed-object form is excluded.

*The Axiom of Choice in ToS is neither accepted nor rejected as a whole: its rule-core becomes a theorem of L5, and its completed graph is excluded by P4. This is a model E/R/R analysis of a strong axiom—to unglue the legitimate rule and the illegitimate completed object—and Part X will apply it further to the whole tower of foundations.*

---

[^1]: `P4_Eliminates_AC.v`: `L5_choose` (the head of the list), `finite_choice` (the head of a nonempty list lies in it), `AC_is_L5` (for a family of nonempty lists the choice function is the head), `P4_eliminates_AC_finite` (an explicit version for the finite front $\{0,\dots,N-1\}$). All **0 axioms**.
[^2]: `finite_zorn` (`P4_Eliminates_AC.v`): $\forall l\neq\varnothing,\ \exists m\in l,\ \forall n\in l,\ n\le m$. 0 axioms.
[^3]: This distinction is explicitly recorded in the comment of `P4_Eliminates_AC.v` on `P4_eliminates_AC`: read as a process rule, it is P4-compatible; read as a completed graph, it falls under `P4ProhibitsAC.v`.
[^4]: `P4ProhibitsAC.v`: `AC_on_nat` (the full form), `ac_implies_completed` (AC gives a completed graph), `P4_prohibits_AC`. And `P4CompletedInfinity.v`: `CompletedInfSet` against `P4_stage_bounded`, with the outcome `completed_inf_contradicts_P4`. All **0 axioms**.
[^5]: `P4CompletedInfinity.v`: `potential_compatible_with_P4`—potential infinity does not contradict P4. What is excluded is precisely the *completed* object, not the process.
[^6]: `P4ProhibitionSynthesis.v`: `prohibition_implies_reinterpretation` (the exclusion entails the reinterpretation), `reinterpretation_weaker` (the converse fails), `P4_is_prohibition`. 0 axioms.
[^7]: `ToS_Axioms.v`—the header says this outright: “This is NOT the Axiom of Choice”; `L4_witness` is `(exists x, P x) -> {x | P x}`, neither ZFC-AC nor dependent choice. In strength they are comparable (`l4_statement_gives_functional_choice`); the difference lies in category: a rule versus a completed object.
[^8]: `P4_Eliminates_AC.v`: `decidable_subset_finite` (a decidable subset of a finite list is finite), `finite_decomposition_preserves_length` (length is additive under concatenation). This is not the metatheorem “Banach–Tarski is false” but the absence of *footing* for the construction: there are no non-measurable pieces—and so no paradoxical decomposition either.

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/03 Comparing Cardinalities without Choice Schroeder Bernstein and Cantor|Chapter 3. Comparing Cardinalities without Choice: Schröder–Bernstein and Cantor’s Theorem]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/05 Ordinals as Processes the Tower of Strong Axioms and Its Removal|Chapter 5. Ordinals as Processes; the Tower of Strong Axioms (ATR₀, Π¹₁) and Its Removal]] →
