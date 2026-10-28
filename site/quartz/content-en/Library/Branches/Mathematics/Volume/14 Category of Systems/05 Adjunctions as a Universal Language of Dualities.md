---
title: "Chapter 5. Adjunctions as a Universal Language of Dualities"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/14 Категория систем/05 Сопряжения как универсальный язык двойственностей.md"
sourceBlob: feec197ca262fa33f1af185cb4ce8d2d21c8ed41
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 14.4 presented *one* adjunction—$\texttt{embed}\dashv\texttt{forget}$, the crown of P2. This chapter raises its sights: an adjunction is a **universal language of
dualities**, not a one-off construction. One and the same pattern, “left ${}\dashv{}$ right, unit, counit, triangles,” recurs throughout the volume—from levels to Galois theory and geometry–gauge.

We do three things. First, we write out the *general* adjunction $F\dashv G$ (between any categories, not only between levels). Second, we prove the main structural consequence: **a right adjoint
preserves limits** (RAPL)—by machine for the terminal case, with an *honestly exposed* naturality hypothesis. Third, we unfold the *catalog of the volume’s dualities* and honestly mark where a bridge is an adjunction and where it is a different pattern.

**The tiers of the chapter (mixed, honestly).**  The general $F\dashv G$ and the monad are in `stdlib/` (0 axioms, in `origin/main`); RAPL is in the *local* layer `src/category/` (0 axioms, awaiting `push`); the geometry–gauge Galois connection is in the process layer (it inherits `classic`); the Galois theory of fields is Part XI (0 axioms). We mark each anchor explicitly.

## The General Adjunction $F\dashv G$

An adjunction between categories $C$ and $D$ is a pair of functors $F:C\to D$ (the *left* one) and $G:D\to C$ (the *right* one) together with a *unit* $\eta$ and a *counit* $\varepsilon$:

$$
\eta_c : c \to G(F c), \quad \varepsilon_d : F(G d) \to d,
$$

subject to two *triangle identities*. In the machine layer this is the record `Record Adjunction` (`adj_left` $F$, `adj_right` $G$, `adj_unit`, `adj_counit`); the identities are formalized as `triangle_left`/`triangle_right`, and their conjunction is `is_adjunction`. The identity adjunction $C\dashv C$ (both functors are the identity) serves as a concrete witness (`id_adjunction`, `id_is_adjunction`).
[^1] This is the *algebraic skeleton* of duality: the unit and the counit are “almost inverse” natural passages $1\Rightarrow G F$ and $F G\Rightarrow 1$, and the triangles keep track of their coherence.

**The honest boundary of the record.**  `Record Adjunction` carries the *data* (the unit, the counit) and the triangle identities, but does *not* carry a field for the *naturality* of the unit. For most concrete adjunctions naturality holds; as a field of the record, however, it is absent. This will become important already in the next section: the deep theorem about limits *requires* naturality—and we will present it as an *explicit hypothesis*, not as a tacit assumption.

## What a Right Adjoint Preserves: RAPL

The main *classical* structural property of adjunctions is the *RAPL slogan*: “**right adjoints
preserve limits**” (Right Adjoints Preserve Limits); dually, left adjoints preserve colimits. In full form this is a theorem about *arbitrary* limits; we prove it by machine for the *terminal* object (the limit of the empty diagram):

$$
\text{if } t \text{ is terminal in } D,\quad\text{then } G t \text{ is terminal in } C
$$

(`right_adjoint_preserves_terminal`). At its basis is the lemma on the *transposition bijection*:

$$
G(\varepsilon_d \circ F h)\circ \eta_c \;=\; h
$$

(`right_adjoint_transpose_roundtrip`), an eight-step diagram chase (the functoriality of $G$, associativity, the naturality of $\eta$, a triangle, units).
[^2]

**An honestly exposed hypothesis.**  Transposition becomes a *bijection* only under the naturality of the unit—and that, as was said, the record `Adjunction` does not carry. Therefore we introduce an *explicit* predicate `unit_natural` and add it to the premises of the theorem. This is not a hidden axiom: the hypothesis is *satisfiable*—for the identity adjunction it is proved (`id_adjunction_unit_natural`), and it holds for any adjunction whose unit is a genuine natural transformation. **A model of honest formalization:** the missing condition is *exposed* as a premise rather than smuggled in silently. (The full RAPL for arbitrary limits is incremental work; the terminal case captures the essence.)

## The Monad: The Trace of an Adjunction

Every adjunction has a “shadow” on one side—the *monad* $T=G\circ F$ (and, dually, the *comonad* $F\circ G$). A monad is a pattern of computation: a type constructor with `return` and `bind`, subject to three laws (left/right unit, associativity). In the machine layer this is `Record Monad` with the instances `Option`/`List`/`Result`, Kleisli composition (`kleisli_assoc`), and `m_map`.
[^3]

**An honest boundary.**  The *general* theorem “every adjunction induces a monad” has *not* been formalized by us as a *single* machine result (it requires naturality and the triangles assembled into $\mu,\eta$). Both supports, however, are machine-checked separately: (1) the abstract monad laws (`Monad.v`, 0 axioms); (2) the *concrete* monad of the adjunction of levels—in the *process* layer, which inherits `classic`—$T=\texttt{forget}\circ\texttt{embed}$, and by the tightness of 14.4 it *is the identity* (`monad_is_identity`), while the dual comonad $\texttt{embed}\circ\texttt{forget}$ is isomorphic to the identity on the forgettable systems.
[^4] The triviality of this monad is a *sign*, not poverty: a unit that is an isomorphism means that the “round trip” of a level adds nothing.

## The Catalog of the Volume’s Dualities

One and the same pattern “$\dashv$” occurs in the volume three times—in three different encodings. We bring them together in *prose* (a single Coq object would require a deep re-unification: the encodings are heterogeneous).

**(1) Levels (Chapter 14.4).**  $\texttt{embed}\dashv\texttt{forget}$ is a genuine categorical adjunction between $\Sys(L)$ and $\Sys(LS L)$, the machine form of P2; its unit is an isomorphism, and it is not an equivalence (because of P1). Tier: **0 axioms, `origin/main`**.

**(2) The Galois theory of fields (Part XI).**  The Galois correspondence for $ℚ[\sqrt2,\sqrt3]$ is an *antitone Galois connection*: the lattice of subgroups of $\Gal$ and the lattice of intermediate fields correspond to each other *by reversing inclusion* (`correspondence_inclusion_reversing`), with $[E:ℚ]=|\Gal|=4$ (`degree_equals_galois_order`), and $V_4$ has exactly $5$ subgroups (`klein_four_subgroups`).
[^5]
The antitone Galois connection is *read* as an adjunction between an order and the *opposite* order—the same skeleton “$\dashv$,” reversing the direction; in the formal layer of XI this is a *concrete* table of correspondence and `correspondence_inclusion_reversing`, not a theorem-object of a full poset adjunction.

**(3) Geometry ${}\leftrightarrow{}$ gauge (Part XII, phase 14A).**  Between ordered geometries (“coarser ${}\leq{}$ finer”) and gauge configurations (“more trivial ${}\leq{}$ more excited”) there is a *Galois connection on orders*: $F\circ G\le\mathrm{id}$ is proved literally (`galois_lower_trivial`: $F(G(gc))$ is more trivial than $gc$), and $\mathrm{id}\le G\circ F$ is read through the uniformization of geometry (`galois_upper`); the theorem `geom_gauge_galois` packages the *components* (preservation of vertices, trivialization of connections, uniformization). The physical meaning: coarser geometry ${}\to{}$ more trivial gauge, and conversely (`galois_physical_meaning`).
[^6] *Important:* here a *strict* categorical adjunction does *not* go through—it was deliberately *weakened* to a Galois connection on partial orders (this is the honest finite-process form of duality).

**What unites the catalog.**  The encodings are *heterogeneous*: `LevelAdjunction` is a pointwise adjunction with hypotheses; the Galois theory of fields consists of lattices on `nat`; geometry–gauge is an order $\le$ over ℚ. They are *not* reduced to one Rocq object `Adjunction`, and the catalog honestly remains a *prose* generalization of a *pattern*, not a single machine theorem. But the pattern is one: *left ${}\dashv{}$ right, unit, counit, triangles*—the language in which the volume speaks of dualities.

## Not Every Bridge Is an Adjunction

The discipline of the language requires the converse: being able to say where there is *no* adjunction. The bridge E/R/R${}\to{}$gauge is one of these. There the gauge group is the *group of automorphisms* of the E/R/R category: $\Aut(\mathrm{ERR}_N)$ has $N^2-1$ generators, which combine into $SU(3)\times SU(2)\times U(1)$. This is a *functor* plus a *group of automorphisms*, *not* an adjunction.
[^7] In addition, the identification $\Aut(\mathrm{ERR}_N)\cong SU(N)$ is a *continuum* bridge (it requires a topology, which P4 assigns to process limits), not a discrete machine theorem: what is proved is the *finite* structure (the group, the count of generators), while the Lie group is a conceptual bridge.

The lesson is methodological: the categorical language *distinguishes* patterns—adjunction (levels), Galois connection (fields, geometry–gauge), functor-automorphism (gauge). Lumping everything into “adjunction” would be an overclaim; an honest map calls each pattern by its own name. (A detailed analysis of the bridge and its continuum price is in 14.7.)

## E/R/R Analysis: Adjunction as E/R/R

**Rules (L5).**  The triangle identities + naturality (honestly exposed where it is needed) + the monad laws; for Galois connections, in the *abstract* reading, $F\circ G\le\mathrm{id}\le G\circ F$ (unfolded in the file as the trivialization of connections and the uniformization of geometry). These rules *constitute* duality as a structure, not as a metaphor.

**Roles (L4).**  The left adjoint (free-like); the right adjoint (forgetful, *limit-preserving*—RAPL); unit/counit, the passages $1\Rightarrow GF$, $FG\Rightarrow 1$; the monad, the role-trace of the adjunction; the antitone Galois connection, a role-adjunction on *opposite* orders.

**Elements (L1${}+{}$P4).**  Concrete data: `id_adjunction`; $T=\texttt{forget}\circ\texttt{embed}={}$ the identity; the $5$ subgroups of $V_4$ and $[E:ℚ]=4$; the order $\le$ on geometries/gauges. *Not a field of the current record* `Adjunction`: the *naturality* of the unit is needed as a *premise/rule* (exposed as the hypothesis `unit_natural`), not as a ready field of the record. And $\Aut(\mathrm{ERR}_N)\cong SU(N)$ is a continuum limit (P4), not a discrete fact.

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| triangles + naturality + monad laws; $F G\le\mathrm{id}\le GF$ | the constitution of duality | Rule (L5) |
| left ${}\dashv{}$ right; unit/counit; monad-trace | the status of the partner functors | Role (L4) |
| `id_adjunction`; $T={}$ identity; $\lvert V_4\rvert$, $[E:ℚ]$; order $\le$ | computable witnesses | Element (L1${}+{}$P4) |

**P4 diagnostics.**  The continuum walls show through precisely in the dualities: $\Aut\cong SU(N)$ requires a topology; the strict geometry–gauge adjunction does *not* go through and has been honestly weakened to a Galois connection. P4 here is an *indication of scale*, not an exclusion: at the finite-process level duality lives as a connection of orders; its continuum form is a limit, not a ready object.

## What the Chapter Has Prepared

The adjunction has been presented as a *language*: the general $F\dashv G$ with unit, counit, and triangles (`Adjunction.v`); the main consequence—a right adjoint *preserves limits* (RAPL, the terminal case, by machine, with honestly exposed naturality); the monad as the trace of an adjunction (abstractly, `Monad.v`; concretely, the identity monad of levels). The catalog of the volume has gathered three dualities (levels / the Galois theory of fields / geometry–gauge) under one pattern and has honestly noted that the bridge E/R/R${}\to{}$gauge is *not* an adjunction but a functor-automorphism.

**Tiers (honestly).**  The general adjunction and the monad: `Adjunction.v` (5 Qed) + `Monad.v` (20 Qed), **0 axioms, `origin/main`**. RAPL: `RightAdjointPreservesLimits.v` (3 Qed), 0 axioms, but a **local layer** `src/category/` (`90ebd74`), awaiting `push`. The Galois theory of fields: Part XI (0 axioms, `origin/main`). Geometry–gauge: `ProcessGGGalois.v` (15 Qed), the process layer (it carries `classic`), `origin/main`.

Next comes Chapter 14.6: *processes as universal constructions* (P4: limits and colimits are processes) and the *topos kit* of `SetoidCat` (finite (co)limits, cartesian closedness, a predicate subobject classifier)—two readings of universal constructions, the process one and the setoid-topos one.

---

[^1]: `src/stdlib/Adjunction.v` (5 Qed, 0 Admitted, 0 axioms; in `origin/main`): `Record Adjunction` (`mkAdj`), `triangle_left`/`_right`, `is_adjunction`, `id_adjunction`, `id_adjunction_triangle_left`/`_right`, `id_is_adjunction`, `id_defect_zero`. (The lemma `adjunction_unique_up_to_iso` in the file is a *placeholder* for the identity case, *not* the general theorem on the uniqueness of the right adjoint: the latter has not been formalized.)
[^2]: `src/category/RightAdjointPreservesLimits.v` (3 Qed, 0 Admitted, 0 axioms; **local layer** `src/category/`, commit `90ebd74`, awaiting `git push`): `unit_natural`, `id_adjunction_unit_natural`, `right_adjoint_transpose_roundtrip`, `right_adjoint_preserves_terminal`.
[^3]: `src/stdlib/Monad.v` (20 Qed, 0 Admitted, 0 axioms; in `origin/main`): `Record Monad`, `m_left_id`/`m_right_id`/`m_assoc`; `OptionMonad`, `ListMonad`, `ResultMonad`; `kleisli_assoc`, `kleisli_id_left`/`_right`, `m_map_id`.
[^4]: `src/process/ProcessAdjunction.v` (the process layer, inherits `classic`; in `origin/main`): `level_monad`, `monad_is_identity`, `monad_unit_is_iso`; `level_comonad`, `comonad_counit_is_iso`.
[^5]: `src/algebra/GaloisQ23.v`, `GaloisDegreeQ23.v`, `GaloisCorrespondence.v` (Part XI, 0 axioms; in `origin/main`): `fixed_by`, `base_fixed_by_all`, `correspondence_inclusion_reversing`, `degree_equals_galois_order`, `klein_four_subgroups`.
[^6]: `src/process/ProcessGGGalois.v` (15 Qed, 0 Admitted; the process layer, imports `Classical` and so inherits `classic`; in `origin/main`): `geom_coarser`, `gauge_more_trivial`, `galois_lower_trivial`, `galois_upper`, `geom_gauge_galois`, `galois_physical_meaning`.
[^7]: `src/foundation/ERRGaugeFunctorSynthesis.v` (9 Qed by grep; the banner says “12”; 0 Admitted; in `origin/main`): `distinction_is_category`, `gauge_is_automorphism`, `generators_match_sm`, `err_gauge_synthesis`.

---

Part: [[14 Category of Systems|Part XIV. The Category of Systems]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/14 Category of Systems/04 Functors Between Levels and Adjunction|Chapter 4. Functors between Levels and Adjunction]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/06 Processes as Universal Constructions Setoid as Topos|Chapter 6. Processes as Universal Constructions; Setoid as a Topos]] →
