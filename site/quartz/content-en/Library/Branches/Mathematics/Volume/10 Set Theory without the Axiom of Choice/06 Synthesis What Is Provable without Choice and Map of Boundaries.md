---
title: "Chapter 6. Synthesis of Part X: What Is Provable without Choice, and the Map of Boundaries"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/06 Синтез Части X что доказуемо без выбора, и карта границ.md"
sourceBlob: ee26e7ea77fd7c14dc1cc43be5a9212b69da666d
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Part X has traveled the path from the foundations to their boundary. Chapter 10.1 rearranged the ontology: a set is a role-System, membership a role, paradoxes errors of reification. Chapter 10.2 read countability and uncountability as rules about processes. Chapter 10.3 reduced comparing cardinalities to the preorder of embeddings (Schröder–Bernstein, Cantor)—without choice. Chapter 10.4 split the Axiom of Choice in two: the rule of L5 is reinterpreted, the completed graph is excluded by P4. Chapter 10.5 extended the same two-level diagnosis to ordinals-as-processes and the tower of strong axioms (Infinity, impredicativity, ATR$_0$, $\Pi^1_1$).

The present, concluding chapter of Part X sums up: *what else* is provable without choice (results of the theory of well-quasi-orderings and of determinacy), the *full map of axiom prices*, and the *honest wall*—the line beyond which ToS does not go. The single thesis of the part holds: ToS does not “prove ZFC without choice” but *changes the category*—a set becomes a system, membership a role, cardinality/choice/infinity rules and processes; a strong axiom is in every case a gluing of a legitimate rule with an illegitimate completed object.

*The concluding chapter of Part X: a synthesis of what is provable without choice, a map of axiom prices, and an honest wall. The single result is a change of category, not a proof of ZFC without the Axiom of Choice.*

## What Else Is Provable without Choice: wqo and Finite Determinacy

Besides the core (countability, the diagonal, Schröder–Bernstein, Cantor), the `settheory/` cluster carries out some “higher” results without choice as well. *Higman’s lemma*: lists over a finite alphabet form a well-quasi-ordering (wqo)—proved for concrete alphabets (one-letter, Boolean, $ℕ$) with Dickson’s lemma at the base.[^1] *Kruskal’s theorem*: finite trees are wqo under homeomorphic embedding—proved for concrete families (chains, forks, growing sequences, trees of depth $\le 1$).[^2] *Cantor–Bendixson*: the derivative of a closed set as a process; the $\omega$-limit is the perfect kernel.[^3] And the *determinacy of finite games* (Zermelo, 1913): every finite game is determined.[^4]

The honest measure is the same everywhere. These results are classically considered “high” (the full Kruskal theorem has great ordinal strength); ToS carries out their *constructive cores for concrete families* without choice—but *not* in full generality. This is what leads to the map of boundaries.

*Without choice, the wqo results (Higman, Kruskal—for concrete families) and finite (Zermelo) determinacy are provable too. These are the constructive cores of “high” theorems, not their full generality.*

## The Map of Axiom Prices

All the results of Part X line up by *price in axioms*. This is laid out as a decidable table: each result is assigned a tier, and the outcome is proved—no *proved* result *requires* the full Axiom of Choice (ZFC).[^5]

| **Tier (price)** | **Results** |
|---|---|
| 0 axioms | the countability of ℚ (Calkin–Wilf); the diagonal (`diagonal_differs`); general Cantor $X\to(X\to\mathtt{bool})$; Cantor–Bendixson; ordinals, $\varepsilon_0$, `wf_ord_lt`, `transfinite_ind` (checked by `Print Assumptions`: Closed); level induction; the `P4_Eliminates`/`Prohibits` cluster—ATR, Infinity, impredicativity |
| classic (L3) | the uncountability of $[0,1]$ (trisection); Higman; Kruskal (concrete families); finite determinacy |
| classic ${}+{}$ L4 | Schröder–Bernstein; the antisymmetry of cardinalities (`cardinal_antisym`) |
| computational primitive | the $\Pi^1_1$ reinterpretation—0 logical axioms, but with `eval_program` (`Parameter`) |
| **Boundary (`PBoundary`)** | the completed actually infinite *object*—the only P4 exclusion (incl. the completed choice graph and $\mathcal{P}(\mathbb{N})$ as an Element; the rule-core of choice is, for us, L5); the process forms of the high theorems (full Kruskal wqo, Borel determinacy)—*not invoked*, not built |

The main observation: the substantive core of set theory—from countability to Cantor–Bendixson and wqo—lives on the tiers 0/ L3/ L3${}+{}$L4, and *not one* proved result requires the full Axiom of Choice.

Important: the boundary is named in *our* terms. “Full AC” as an axiom and its metatheoretical independence are statements about ZFC (another system), not points of our space; to bring them into “our boundary” would be to repeat the very category mistake of level confusion with which Part X opens. Our boundary is a single *object* excluded by P4 (completed actual infinity); and the illusory “completed infinity” of the high theorems turns out on rollback to be ZFC packaging (below).

*The map of prices is a role-audit: each result carries a tier (0 / L3 / L3${}+{}$L4), and it is proved that what has been proved does not *require* full AC. The price is measured explicitly, not passed over in silence.*

## The Honest Wall: Where ToS Does Not Go

The boundary of Part X is twofold, and these two kinds of frontier must not be confused.

*The first kind—not invoked / not built* (open, but not contradictory): the *process forms* of the high theorems—the full Kruskal theorem in all its generality and Borel (Martin’s) determinacy (their rollback is below); the reverse bridge surjection ${}\to{}$ injection (this is choice itself); the linearity of the cardinal scale (the trichotomy of cardinalities, also choice); transfinite recursion beyond constructive notations. ToS does not go here—but does not deny these either: they are directions, not contradictions. (The completed power *object* $\mathcal{P}(X)$ is not on this list: its bool-predicate layer
$X\not\twoheadrightarrow(X\to\mathtt{bool})$ is *proved* in 10.3, and the completed object itself is not an open direction but an artifact of packaging: see the rollback below and the second kind.)

*The second kind—excluded by P4 (the object form is incompatible)*: the completed choice graph (`completed_inf_contradicts_P4`); completed infinity as an object; the power set $\mathcal{P}(X)$ as a completed Element (P1); the impredicative totality-in-itself (P1${}+{}$P4). This is not “not yet proved” but *incompatible* with Finite Actuality.

The distinction is essential: *not invoked* is weaker than *excluded*. The greater part of the wall is of the first kind (honest open directions); the smaller but fundamental part is of the second (completed objects contradicting P4).

And one audit for all the axioms at once. Of the *nine* axioms of ZFC, three—Extensionality, Pairing, Union—are structurally trivial; Infinity, Separation, and Replacement are replaced by P4; Foundation by P1; Choice by L5; and exactly *one*, Power Set, falls on the role-limit side of the boundary: the finite power object $2^n$ is enumerable explicitly (an Element, proved), while the full $2^{\mathbb{N}}$ is uncountability. Power Set is the only “price.”[^6]

And the same rollback for the “high” theorems; here the strength of the system is seen directly. What classically requires *completed infinity*—the full $\mathcal{P}(\mathbb{N})$, Kruskal’s minimal bad sequence, the Borel tower of iterated power sets—turns out on analysis to be ZFC *packaging*, not a wall: the content is attained *without* a completed object. The power set is the role-type $\mathbb{N}\to\mathtt{bool}$: at each finite stage there are exactly $2^n$ subsets, and its core, “uncountability,” is the absence of an enumerator of roles (the diagonal), with 0 axioms; finite determinacy is backward induction on the game tree, also without the tower. What remains is exactly one genuine exclusion—completed actual infinity *as an object*; full wqo and Borel determinacy are not walls but *not invoked* process constructions.[^7]

*The wall is twofold: *not invoked* (the process forms of full Kruskal and Martin, the bridge of choice, the linearity of the scale—open) and *excluded* by P4 (the completed graph, completed infinity, the power object, the totality-in-itself—incompatible). And “full AC” and its metatheoretical independence concern ZFC itself, not our boundary. Do not confuse them.*

## The Unified E/R/R Structure of Part X

The whole part is one system: *set theory as a process of roles over finitely actual bearers*.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the level order P1; criterion ${}+{}$ P2; the resolution of L5 (choice); diagonal/trisection; the finite depth of the chain (SB); structural recursion on `Ord`; function ${}={}$ code |
| *Roles* (L4) | set ${}={}$ System; $\in{}={}$ the role of position; cardinality ${}={}$ role-comparison; choice ${}={}$ role-rule; ordinal ${}={}$ role-process |
| *Elements* (L1${}+{}$P4) | at each stage, finite data (a list, ℚ, a path, a notation, a code); completed totalities (the choice graph, the $2^{\aleph_0}$-object, $\mathcal{P}(X)$, the uncountable space of functions) are *not* Elements |

**The two-level diagnosis, uniformly.** Each strong axiom glues a legitimate *rule* (which ToS keeps and reinterprets as a theorem) to an illegitimate *completed-object* form (which ToS does not invoke or which P4 rules out). The paradoxes (Russell, Cantor, Burali-Forti) are the limiting case: the reification of a rule-totality as an Element, removed by P1${}+{}$P4.

**The final formula.** ToS does not “prove ZFC without AC.” ToS changes the category: a set is a system, membership a role, choice a rule, infinity a process. The admissible core of the strong axioms becomes a procedure; the completed-object form is excluded by P4.

*Part X is one system: set theory as a process of roles. Each strong principle is split in two (rule ${}+{}$ completed object); the rule is kept, the object set aside or excluded. A change of category, not a weakening of ZFC.*

## The Closing of Part X

Set theory has been rebuilt without the Axiom of Choice and without completed infinity—with P4 as the central filter in the level-based E/R/R framework (P1, P2, L3–L5). The substantive theorems have survived: Schröder–Bernstein and Cantor’s general theorem without choice, the constructive countability of ℚ, uncountability via the diagonal and trisection, the Cantor–Bendixson dichotomy, the wqo results of Higman and Kruskal for concrete families, and finite determinacy. The strong axioms—choice, infinity, impredicativity, ATR$_0$, $\Pi^1_1$—have received a unified two-level analysis: the legitimate core is reinterpreted, the completed-object form is set aside or excluded. And the boundary has been drawn honestly, in two kinds: *not invoked* and *excluded*.

This is the set theory of ToS: not things but roles over processes; not postulates about completed totalities but rules constituting the finitely actual. The Axiom of Choice in it is neither a cornerstone nor an outcast, but exactly that gluing of rule and object which Finite Actuality carefully unglues.

*Set theory without the Axiom of Choice is not ZFC with something subtracted but a different category: a set is a role-System, cardinality and choice are rules, infinity is a process. What is provable without choice extends to Schröder–Bernstein, the bool variant of Cantor’s theorem ($X\not\twoheadrightarrow(X\to\mathtt{bool})$), Cantor–Bendixson, and wqo; behind the honest wall lie open directions and completed objects incompatible with P4. Such is the outcome of Part X.*

---

[^1]: `HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `dickson_pair`, `higman_unit`, with the outcome `higman_synthesis`. 15 Qed, uses `classic` (L3).
[^2]: `KruskalFull.v`/`KruskalTree.v`: `chain_wqo`, `fork_wqo`, `growing_wqo`, `depth1_wqo`, with the outcome `L5_from_kruskal`. 15 Qed, 0 new axioms.
[^3]: `CantorBendixsonFull.v`: `CB_deriv` (removal of isolated points), `CB_omega` (the $\omega$-limit); a perfect-or-empty kernel, finite sets are scattered. 20 Qed, 0 axioms.
[^4]: `BorelDeterminacy.v`: `weak_determinacy`, `zero_game_determined`. 15 Qed, 1 axiom (`classic`). NB: contrary to the file name, what is proved is precisely *finite* (Zermelo) determinacy, *not* Borel (Martin) determinacy.
[^5]: `settheory/ChoicePriceMap.v` (this work): `AxiomPrice` (`PZero`/`PL3`/`PL3_L4`/`PBoundary`), the function `price`, and `proven_results_below_boundary`—every proved result lies strictly below the boundary. This is an audit layer recording the checked `Print Assumptions` statuses, not new mathematics.
[^6]: `foundation/ZFCAxiomLedger.v` (9 Qed, 0 axioms): a machine registry-verdict on the nine axioms of ZFC—`tos_verdict`, `eight_axioms_eliminated`, `only_powerset_is_role_limit`; `bitvectors_length` ($| 2^{[0,n)} | = 2^n$, the finite power set is an Element). The registry is a *synthesis/classification* (the verdicts cite existing 0-axiom files), not a new theorem. Machine-checked.
[^7]: The rollback is anchored in the machine layer (0 axioms each): `foundation/PowersetRoleType.v` (`powerset_card`: $|\mathcal{P}(l)| = 2^{|l|}$; `cantor_bool_seq`: there is no surjection $\mathbb{N}\to(\mathbb{N}\to\mathtt{bool})$), `foundation/FiniteGameDeterminacy.v` (`finite_game_determined`, backward induction), `foundation/FiniteWqoPigeonhole.v` (the finite pigeonhole core of wqo). The summary verdict is `foundation/FormerWallsLedger.v` (`former_walls_are_artifacts`, `only_completed_infinity_is_a_wall`): exactly completed infinity is excluded, and the three “walls” roll back (`ReachedFreely`/`NotYetBuilt`). The concrete witnesses are genuine; the summary is a synthesis/classification, not a proof of full Kruskal/Borel. Machine-checked.

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/05 Ordinals as Processes the Tower of Strong Axioms and Its Removal|Chapter 5. Ordinals as Processes; the Tower of Strong Axioms (ATR₀, Π¹₁) and Its Removal]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/01 Field as Role Extension Degree as Tier|Chapter 1. Field as Role-Extension; Degree as Tier—Part XI]] →
