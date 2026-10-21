---
title: "Chapter 3. Comparing Cardinalities without Choice: Schröder–Bernstein and Cantor’s Theorem"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/03 Сравнение мощностей без выбора Шрёдер–Бернштейн и теорема Кантора.md"
sourceBlob: 275833e7861d0ab00d6febf19a82a775d86bec38
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 10.2 showed that countability and uncountability are not sizes of ready sets but rules about processes. The natural next question: how are cardinalities to be *compared*—and is the Axiom of Choice needed for this? In ZFC with choice, the classical theory answers thus: the cardinals form a linearly ordered scale (well-ordered *thanks to* choice), and cardinal arithmetic is defined on completed $\aleph$-objects.

ToS reads comparison differently. If “being countable” and “being uncountable” are roles, then their *ordering* is a *rule*: one bearer embeds into another. Cardinality is not a number glued to a completed set but a *role* that a bearer (a type) plays in the preorder of embeddings. Two bearers are *equinumerous* when they play one role (there is a bijection).

The chapter stands on two pillars, both *without the Axiom of Choice*:

- **Schröder–Bernstein**: if $A$ embeds into $B$ and $B$ into $A$, then $A$ and $B$ are equinumerous. This makes the preorder of embeddings *antisymmetric* up to bijection—and it is proved without choice, at the price of L3 and L4 (not 0 axioms), on a finite depth of the chain.
- **Cantor’s general theorem**: no bearer covers (surjectively) its space of bool-predicates. There is no maximal cardinality—and this is *constructive*, without a single axiom.

And at once an honest reservation, which the chapter will carry through to the end: the *reverse* bridge—from a surjection $A\twoheadrightarrow B$ to an embedding $B\hookrightarrow A$—is exactly the Axiom of Choice. In ToS it is *not* proved; it is there, and only there, that choice lives in the theory of cardinalities.

*Cardinality is a role-mode of comparison, not a cardinal-number; its ordering is a rule of embedding. Antisymmetry (Schröder–Bernstein) and the absence of a maximum (Cantor) hold without choice; choice is localized in one passage—surjection into injection.*

## Comparison as a Role; Injection as a Rule-Preorder

Let us fix three roles of comparison for bearers (types) $A,B$:

$$
A \le B \;:=\; \exists \text{injection } A\to B; \quad
  A \twoheadrightarrow B \;:=\; \exists \text{surjection}; \quad
  A \simeq B \;:=\; \exists \text{bijection.}
$$

The relation $\le$ (embedding) is a *preorder*: reflexive (the identity injection) and transitive (a composition of injections is injective). Both properties are constructive, without axioms. Surjection and bijection behave the same way: composition preserves each of these roles.[^1]

The point, as before, is in the category. “The cardinality of $A$” is not a number ascribed to a completed set but a *role* that $A$ plays in this preorder: below some bearers, above others. Equinumerosity $A\simeq B$ is a coincidence of roles. No $\aleph$-objects are needed for this: comparison is a rule about bearers, not arithmetic of ready cardinals.

*$\le$ is a role-rule (the preorder of embeddings), constructively reflexive and transitive; cardinality is the position of a bearer in this preorder, equinumerosity a coincidence of roles.*

## Schröder–Bernstein without Choice

The antisymmetry of the preorder is the substantive core of the theory of cardinalities: if $A\le B$ and $B\le A$, then $A\simeq B$. This is the Schröder–Bernstein theorem.

The classical proof traces for each point an infinite “shuttle” chain $…\to a\to f(a)\to…$ under the two injections. ToS replaces the completed infinite chain with a *finite depth*—a natural number: each point is either rooted at a finite depth (reaches a point without a preimage in a finite number of steps) or belongs to a two-sided infinite chain. The bijection $h$ is assembled by this test: on points rooted in $B$ we take the partial inverse $g^{-1}$, otherwise $f$. An infinite object is replaced by a finite process—a move in the spirit of P4.[^2]

What is the axiom price? Exactly `classic` (L3) and `L4_witness` (L4)—and *not* the Axiom of Choice.[^3] L3 enters as the decidability of the rootedness test; `L4_witness` picks a witness from a *single* existence, not a function over an arbitrary family—both are strictly weaker than choice. Therefore the fundamental theorem on cardinalities holds without choice.

*Schröder–Bernstein is the role-rule of the antisymmetry of $\le$: two embeddings in opposite directions give a bijection. The completed chain is replaced by a finite depth (P4); the price is L3${}+{}$L4,
not choice.*

## Cantor’s Theorem: There Is No Maximal Cardinality

The second pillar is Cantor’s general theorem: for *any* type $X$ there is no surjection $X \to (X\to\mathtt{bool})$. The proof is the same diagonal as in 10.2, but for an arbitrary bearer: the predicate $g(x) := \lnot f(x)(x)$ coincides with no “row” $f(a)$, since at the point $a$ they differ. Remarkably, *no inhabitant* of the type $X$ is required: surjectivity itself supplies the witness—the $a$ for which $f(a)=g$—and leads to the contradiction $f(a)(a) = \lnot f(a)(a)$.[^4]

Hence no bearer covers its space of bool-predicates—*there is no maximal cardinality*. Over any $X$ there is a role that it *does not cover surjectively*: the space of predicates $X\to\mathtt{bool}$.[^5] It is precisely in this Cantorian (surjective) sense that there is no maximum: this is *not* strictness in the injective order (an injection $X\hookrightarrow(X\to\mathtt{bool})$ for an arbitrary $X$ would require decidable equality), nor the construction of a full linear scale of cardinals.

An honest reservation about the category. What is at issue is the *type* of bool-predicates $X\to\mathtt{bool}$, *not* the completed power set $\mathcal{P}(X)$ as an object. The power set as a set is structurally not built in ToS (P1, Chapter 10.1): “the set of all subsets” would require a criterion over its own level. Therefore “there is no maximal cardinality” is a statement about the role-comparison (there is no covering surjection), not about the construction of $\mathcal{P}(X)$.

*Cantor’s theorem is the role-rule of the absence of a maximum: every bearer fails to cover its bool-power surjectively. Constructively (0 axioms), and about role-types, not about a completed power object.*

## Where Choice Lives: The Honest Boundary

Now let us indicate precisely where the Axiom of Choice appears in the theory of cardinalities. Antisymmetry gave $A\simeq B$ from two *injections*. But what if there are two *surjections*—or a surjection $A\twoheadrightarrow B$ from which one wants to obtain an embedding $B\hookrightarrow A$?

Precisely this reverse bridge—*choosing one preimage for each $b\in B$*—is the Axiom of Choice (choice over the fibers of a surjection). In ToS it is *not* proved and is honestly marked as a boundary.[^6] With `L4_witness` alone one can invert a *bijection* (the preimages are unique), but not an arbitrary surjection (a fiber may contain many preimages, and choice is needed over *all* fibers at once).

That is why the antisymmetry of $\le$ rests on Schröder–Bernstein (L3${}+{}$L4), not on choice: it works with *injections*, where the partial inverse is single-valued. The substantive results of the chapter—the preorder, antisymmetry, the absence of a maximum—do not require choice; choice is localized in exactly one passage that is not carried out.

*Surjection-into-injection is exactly the place where choice is required, and ToS does not carry this passage out. Antisymmetry lives on injections (L4 inverts what is unique), not on the fibers of a surjection (where choice is needed).*

## E/R/R Analysis

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the preorder of embeddings $\le$ (refl. ${}+{}$ trans.); Schröder–Bernstein (finite depth of the chain) for antisymmetry; Cantor’s diagonal for the absence of a maximum |
| *Roles* (L4) | cardinality ${}={}$ role-position in the preorder; $\simeq{}={}$ coincidence of roles; bool-power ${}={}$ a role not covered surjectively |
| *Elements* (L1${}+{}$P4) | bearers (types) and their points; the finite depth of the chain (`nat`); a cardinal-number is not a completed Element |

**Well-formedness.** $\le$ is a well-formed preorder (injections compose); the $h$ of Schröder–Bernstein is well-formed as a bijection (injective ${}+{}$ surjective).

**What it yields.** The antisymmetry of $\le$ is `cardinal_antisym` (L3${}+{}$L4);
the absence of a maximum is `no_maximal_cardinality` (0 axioms); the preorder takes 0 axioms.

**Diagnosis.** In the P4 ontology of ToS, the cardinal *as a number* and “the scale of all cardinals” are a reification of the role of comparison. The well-ordering of all cardinalities into one linear scale is a theorem of choice (Zermelo’s), not presupposed here.

**Honest boundaries.** The reverse bridge surjection ${}\to{}$ injection is choice itself; it is not carried out. The power set as an object, $\mathcal{P}(X)$, is not built (P1). The linearity of the cardinal scale (the trichotomy of cardinalities) requires choice and is not asserted here.

*Comparing cardinalities is a preorder of roles; antisymmetry (Schröder–Bernstein) and the absence of a maximum (Cantor) hold without choice (L3${}+{}$L4 and 0 axioms
respectively); choice is localized in the only passage not carried out and in the linearity of the scale.*

## Summary and Transition

Comparing cardinalities has turned out to be a preorder of role-bearers, not arithmetic of completed cardinals. Embedding is the constructive rule $\le$; Schröder–Bernstein makes it antisymmetric up to bijection (`cardinal_antisym`, L3${}+{}$L4,
a finite depth instead of an infinite chain); Cantor’s general theorem deprives the scale of a maximum (`no_maximal_cardinality`, 0 axioms). The Axiom of Choice would be needed only for the reverse bridge surjection ${}\to{}$ injection and for the linearity of the scale—and precisely these ToS does not carry out.

This leads to Chapter 10.4, where the Axiom of Choice is considered directly—in its dual fate: the *exclusion* of the completed-object form (the choice graph as a ready infinity, incompatible with P4) and the *reinterpretation* of the admissible core as a rule of the positional resolution of L5.

*Cardinality is a role in the preorder of embeddings, not a cardinal-number; antisymmetry and the absence of a maximum are provable without choice. Choice does not disappear—it is precisely localized: in the passage from surjection to injection and in the linearity of the cardinal scale, which ToS leaves not carried out.*

---

[^1]: In `settheory/CardinalityWithoutChoice.v` (this work): `injects`, `surjects`, `bijects`; `injects_refl`, `injects_trans` (the preorder $\le$), `surjects_refl/_trans`, `bijects_refl/_trans/_injects/_both`—all **0 axioms**.
[^2]: `Schroeder_Bernstein` (`SchroederBernstein_ERR.v`): from two injections a bijection $h$ is built (injective and surjective). The depth of the chain is `nat`; the test `B_rooted` is decided via `L3_informative` (the informative excluded middle)—this is exactly the price of L3.
[^3]: The axiom status is checked by `Print Assumptions`: `Schroeder_Bernstein` and the wrapper `cardinal_antisym` (`CardinalityWithoutChoice.v`, this work) give exactly `classic` ${}+{}$ `L4_witness`. In the proof itself `L4_witness` is applied through the derived lemma of definite description `L4_definite` (CDD), which extracts the *unique* partial preimage from $\exists!$—this is exactly how the file header labels the technique. See the distinction between L4 and choice in Chapter 10.4.
[^4]: `cantor_no_surjection` (`settheory/CantorTheoremGeneral.v`, this work): $\forall X (f:X\to(X\to\mathtt{bool})),\ \lnot `surjective` f$. Purely constructive, **0 axioms**; it works for any $X$ without assuming that it is inhabited.
[^5]: `no_maximal_cardinality` (`CardinalityWithoutChoice.v`): $\forall X,\ \lnot (X \twoheadrightarrow (X\to\mathtt{bool}))$. A consequence of `cantor_no_surjection`; **0 axioms**.
[^6]: Documented in the header of `CardinalityWithoutChoice.v`: the passage `surjects` $\to$ `injects` in the reverse direction is choice and is not derived here.

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/02 Countability Is Constructive Uncountability Is a Rule About Processes|Chapter 2. Countability Is Constructive; Uncountability Is a Rule about Processes]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/04 Axiom of Choice Prohibition and Reinterpretation|Chapter 4. The Axiom of Choice: Exclusion and Reinterpretation]] →
