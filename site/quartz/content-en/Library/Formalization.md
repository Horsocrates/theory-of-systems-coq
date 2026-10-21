---
title: Formalization
aliases:
  - Formalization
lang: en
translationOf: "Библиотека/Формализация.md"
sourceBlob: 2400b7361354e51d04201ad4b40aa33409e6f028
translated: 2026-10-20
status: draft
---
Here is the machine layer of the corpus: which of the claims derived on the pages have been brought to a formal record and checked by the Rocq system (formerly Coq), in which files they are located, under which numbers the laws are known to the code, and what price each result pays. Anyone can check it independently: [github.com/Horsocrates/theory-of-systems-coq](https://github.com/Horsocrates/theory-of-systems-coq).

| | |
|---|---|
| **27,286** | proofs (Qed) |
| **0** | unproved statements (Admitted) |
| **2,041** | files in the build |
| **Rocq 9.0.1** | proof assistant |

*Count taken on the `main` branch of the repository, 2026-10-20; `Qed` marks outside comments are counted.*

## What Formalization Is

Formalization is the writing of definitions and proofs in a formal language in which every step is checked by a program rather than by the reader’s trust.

**CIC** (the Calculus of Inductive Constructions) is the logical core of this language: every definition is an exact construction, every step of inference the application of an explicit rule. **Rocq** (formerly Coq) is the proof assistant that checks this language; its compiler builds the files. A proof closed with `Qed` is accepted by the kernel only when complete. An incomplete one can be closed with `Admitted`—the statement then enters the base as an assumption, and the command `Print Assumptions` lists it together with the axioms. There are no such statements in this base.

This gives the project two things. The first is reliability: behind every claim of the theory that has been brought to this layer stands a checked proof, not the author’s authority. The second is clarity of boundaries: the code shows exactly what has been proved, what has been accepted as a condition, and what remains open.

## Names and Numbers

In the code and in the author’s articles the laws and principles appear under numbers; on the pages, under their names ([[Logic#The Unity of the Laws|“Logic”]]; the principles—[[Logic#From Laws to Principles|“From Laws to Principles”]]).

| Number | Law | Number | Principle |
|---|---|---|---|
| L1 | [[Identity]] | P1 | Hierarchy |
| L2 | [[Non-Contradiction]] | P2 | Criterion Precedence |
| L3 | [[Excluded Middle]] | P3 | Intensional Identity |
| L4 | [[Sufficient Reason]] | P4 | Finite Actuality |
| L5 | [[Order]] | | |

The label E/R/R in file names is the triad Rules → Roles → Elements ([[Theory of Systems]]).

## The Ground

Two assumptions of the instrument are declared in the code: the excluded middle (`classic`) and witness extraction (`L4_witness`, file [ToS_Axioms.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/ToS_Axioms.v); in its wording it coincides with the axiom `constructive_indefinite_description` of the Rocq standard library). These are technical axioms, not the grounds of the system: in the theory itself both laws are derived—from the act of distinction. The logical core of Rocq is constructive and does not have them built in, so they enter the code as explicit assumptions—a requirement of the instrument.

`L4_witness` is witness extraction by [[Sufficient Reason]] (L4): existence is determinate. The derivation is given in the volume “Mathematics” ([[06 Axiomatic Minimum and Status Mechanism|Part I, Chapter 6]], section “The Substantive Ground: The Determinacy of Existence”): to exist is to be determinate, distinguishable from everything else; the ground of the truth of the claim “there exists an *x* with *P*” is that *x* itself; where there is a ground, there is therefore access to it. The witness here is a logical term: the object on which a claim of existence is fulfilled. It is not chosen—it is presented as the ground of the very fact of existence.

The chain of the ground itself—**the act of distinction → the laws → the principles → Rules, Roles, Elements**—is derived on the pages [[Logic|“Logic”]] and [[Theory of Systems|“Theory of Systems”]];[^1] the code holds its model, and all links of the model are built without axioms. Distinction is given as a record with the fields “exclusion” and “exhaustion” ([Distinction.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/Distinction.v)); the laws L1–L5 are lemmas about this record and about the type of levels, gathered by the theorem `five_laws_from_distinction` ([LawsFromDistinction.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/LawsFromDistinction.v)). The principles P1–P4 are given by the build of the types: levels do not precede themselves, the criterion by construction stands a level below the system, the identity of systems is by criterion, the value of a process at every step is a finite fraction; the theorem `derivation_chain` ([PrinciplesFromLaws.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/PrinciplesFromLaws.v)) gathers these four facts, while the derivation of each principle from the named laws is an argument of the prose (as on the “Logic” page). Rules, roles, and elements are three sides of the act of distinction (`ERRFromDistinction.v`; the summary of the file, `complete_foundation`, which extends distinction to every proposition, rests on totality); with the principles the triad stands in correspondence, not in derivation (`principles_err_correspondence`, [PrinciplesToERR.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/PrinciplesToERR.v)). For a completed distinction exhaustion is recorded in the distinction itself (`L3_completed`); that every distinction has already been completed is totality, discussed below.

L3 itself is split in machine-checked form ([BinarityVsTotality.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/BinarityVsTotality.v)): **binarity**—“no third is given”—is a theorem without axioms in three forms (`side_binarity`, `L3_binarity`, `pending_binarity`—true already for an uncompleted act), and only **totality**—“the assignment has always already happened”—requires `classic` (`totality_completes`). The uncompleted act has received a formal type (`PendingDistinction`—“can be, but is not”), actualization is an event with a witness (Sufficient Reason is built into the type of the transition), and the canonical `distinction_of` is, by pure conversion, the actualization by totality (`distinction_of_is_actualization`): the axiom enters the constructor exactly in the argument of assignment. Totality is a mode of reckoning about the “now”: “can be” and “will be” are different statuses, potential expires unrealized (the apples have rotted—the juice was not made); the future is open—from one state both continuations are legitimate, and this is the field of freedom. The model of this is [TotalityNow.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/TotalityNow.v) (`potential_expires`, `eternalism_refuted`, `totality_now`, `future_not_readable`; without axioms): the state in it is a pair of features, a step one of three actions, and the lemmas carry the argument on this model. Whoever accepts `classic` accepts a mode of reckoning, not a thesis about the world.

## Assumptions in the Code

The results of this page rest on at most two assumptions of the instrument. The excluded middle in the mode of totality (`classic`) is declared in the code several times, with one wording: in the standard library (re-exported by ToS_Axioms.v), in Distinction.v, in EVT_idx.v, and in BorelDeterminacy.v; which declaration stands behind which result is shown in the section “The Price of Results.” Witness extraction (`L4_witness`) is declared once—in ToS_Axioms.v. The repository also contains assumptions on which the results of this page do not rest: functional extensionality from the standard library—in five files (Ordinal.v, DependentSystems.v, Conversion.v, ProcessWholeness.v, GameTheory.v); two axioms of the Navier–Stokes section (`C_B_positive`, `B_coeff_bounded`, TriadicInteraction.v)—assumptions of a particular model: regularity there is conditional on the bound `B_coeff_bounded`, as recorded in the audit HeavyWallAudit.v; three abstract parameters—`C_B` and `B_raw`, about which only these two axioms speak, and `eval_program`.

## Comparison with ZFC

The classical foundation of mathematics—ZFC—rests on **axioms of existence**: infinity is postulated by the existence of an infinite set, the power set by the collection of all subsets, choice by a choice function for an arbitrary family of nonempty sets. The path here is different: the structure is derived from the laws of logic, and each principle derived from the laws does the work of one of the axioms:

| Principle | from the laws | does the work of the ZFC axiom |
|---|---|---|
| **P1**—no `S ∈ S` (hierarchy of levels) | L1 + L5 | Foundation |
| **P2**—the criterion is established before questions of membership (impredicative definitions are blocked) | L5 | Separation (together with P4) |
| **P4**—finite actuality (any system is finite at any moment; infinity is a process, not a completed object) | L5 | Infinity |
| **P3**—identity by criterion | L1 + L4 | Extensionality |
| choice by Order: the status goes to the first that fits | L5 | Choice |

The comparison is by the work the principle does. The exclusion of circular definitions goes back to the vicious-circle principle of Russell (1908) and Poincaré; ZFC does not contain it: the property in the separation schema is given by any formula of the language of set theory, and ZFC blocks Russell’s construction by allowing separation only from a set already given.

The full axiom-by-axiom analysis is gathered in the ledger [ZFCAxiomLedger.v](https://github.com/Horsocrates/theory-of-systems-coq/blob/main/src/foundation/ZFCAxiomLedger.v): the nine axioms of ZFC are classified by the function `tos_verdict`—a table written by hand. The verdicts “replaced” rest on axiom-free elimination lemmas: for Infinity—`P4_eliminates_Infinity` (P4_Eliminates_Infinity.v), for Separation—`p4_impredicative_synthesis` (P4ProhibitsImpredicative.v), for Foundation—`P1_no_self_membership` (TheoryOfSystems_Core_ERR.v), for Choice—`P4_eliminates_AC` (P4_Eliminates_AC.v) and the μ-operator (MuRecursion.v); Replacement has no such lemma. The ledger is a classification, not a theorem:

| ZFC axiom | Status | Position |
|---|---|---|
| Infinity | replaced by P4 | ℕ is an inductive type; infinity is only a process |
| Power Set | **role-limit** | the only price: the finite power set is an element (exactly 2ⁿ subsets, an explicit list: `bitvectors_length`), the full 2^ℕ is a role-limit (uncountability) |
| Foundation | replaced by P1 | the hierarchy of levels is well-founded: `S ∈ S` is impossible |
| Separation (schema) | replaced by P4; the impredicative definition is also blocked by Criterion Precedence (P2) | decidable—and hence predicative—separability; Russell’s paradox is a type error |
| Replacement (schema) | replaced by P4 | bounded process families; transfinite reach is not built; no elimination lemma |
| Pairing | trivial | the dependent pair is given by the very structure of types |
| Union | trivial | structurally constructive, a separate axiom is not needed |
| Choice | replaced by L5 | Order gives the places: the status goes to the first that fits; where a result rests on witness extraction, it also carries choice over families—the price is named below |
| Extensionality | replaced by P3 in substance | identity is by the defining criterion: coincidence of elements does not give identity; in the code the verdict is still “trivial” |

The outcome of the ledger is read by the lemma `only_powerset_is_role_limit`: in this classification exactly one axiom of the nine—Power Set—stands beyond the finitization boundary; the other eight are trivial or replaced by a named law. And even the power set axiom is rejected not as an operation: on the finite side the power set is built explicitly; the price is only its extension to completed infinity.

**Calibration.** “Fewer axioms” is not claimed here: a dispute about quantity has little content. What has to be compared are the substrates: ZFC is classical first-order logic plus axioms about sets, for the most part axioms of existence; here—the constructive core of CIC plus two explicit assumptions of the instrument: the excluded middle in the mode of totality (its binary half is derived without axioms—section “The Ground”) and witness extraction. The second is what logic calls indefinite description: choice over any family follows from it (`l4_statement_gives_functional_choice`), and together with the excluded middle—Hilbert’s epsilon (`l3_l4_statements_give_epsilon`; both lemmas are in ChoicePriceMap.v, without axioms: the statements of the assumptions are taken as premises). The volume calls this the choice-like power of witness extraction and separates it from choice out of a completed family of sets, which Finite Actuality excludes. Hence the price of each result is named separately: what is proved without assumptions or with the excluded middle alone rests neither on witness extraction nor on any axiom of choice.

## The Price of Results

A real number here is a **process**: `RealProcess := nat → Q`—a sequence of rational approximations; the Cauchy condition is a separate predicate (`is_Cauchy`). Each result rests on its own assumptions; `Print Assumptions` (Rocq 9.0.1) lists them. “None” means: the proof rests on no assumption.

| Result | Theorem (file) | Assumptions |
|---|---|---|
| Countability of ℚ | `Q_countable`, `Q_bijection` (Countability_Q.v) | none |
| Uncountability of [0, 1]: an enumeration of regular Cauchy processes in [0, 1] does not cover the interval (nested intervals with division into three) | `unit_interval_uncountable_trisect_v2` (ShrinkingIntervals_ERR.v) | none |
| Binary processes are uncountable: no enumeration exhausts them | `binary_processes_not_enumerable` (ProcessDiagonal.v) | none |
| Cantor’s general theorem; there is no largest cardinality | `cantor_no_surjection`, `no_maximal_bool_power` (CantorTheoremGeneral.v); `no_maximal_cardinality` (CardinalityWithoutChoice.v) | none |
| There is no level of all levels; ℕ and the levels are well-ordered without choice | `no_universal_level` (TransfiniteInductionLevel.v); `nat_well_orderable`, `level_well_orderable` (StructuralWellOrdersWithoutChoice.v) | none |
| Kruskal’s theorem for particular families of trees | `kruskal_chains`, `kruskal_forks` (KruskalTree.v); `depth1_wqo`, `L5_from_kruskal` (KruskalFull.v) | none |
| ≤ on ℕ is a well-quasi-order (wqo); Higman’s lemma for a one-letter alphabet | `wqo_nat_le`, `higman_unit` (HigmanLemma.v) | none |
| Dickson’s lemma for pairs | `dickson_pair` (HigmanLemma.v) | excluded middle (standard library) |
| Choice by Order for a countable family of nonempty lists of natural numbers: the first element of each | `ac_on_nat_free` (ChoicePriceMap.v); `P4_eliminates_AC` (P4_Eliminates_AC.v) | none |
| The Schröder–Bernstein (Cantor–Bernstein) theorem; antisymmetry of cardinalities | `Schroeder_Bernstein` (SchroederBernstein_ERR.v); `cardinal_antisym` (CardinalityWithoutChoice.v) | excluded middle (standard library), witness extraction |
| The dichotomy “at most countable or contains a perfect subset” for closed sets of binary processes | `process_continuum_hypothesis` (ProcessContinuumHypothesis.v) | excluded middle (standard library), witness extraction (over a countable family) |
| Choice over any family—from the statement of witness extraction | `l4_statement_gives_functional_choice` (ChoicePriceMap.v) | none: the statement is taken as a premise |
| Hilbert’s epsilon—from the statements of both assumptions | `l3_l4_statements_give_epsilon` (ChoicePriceMap.v) | none: the statements are taken as premises |
| Intermediate value: a process *c* on [*a*, *b*] with *f*(*c*) ~ 0; for every ε > 0 there is a step from which on \|*f*(*cₙ*)\| < ε | `IVT_process` (IVT_ERR.v); `ivt_cauchy_real` (IVT_CauchyReal.v) | none |
| Extreme value: the process of upper bounds converges, on a plateau as well | `EVT_strong_process` (EVT_idx.v) | excluded middle (EVT_idx.v) |
| The point of maximum is the first of the greatest (L5 resolution) | `argmax_idx_maximizes` (EVT_idx.v) | none |
| Heine–Borel given a Lebesgue number | `Heine_Borel` (HeineBorel_ERR.v) | none |
| The laws and principles in the model; binarity of the excluded middle | `five_laws_from_distinction`, `derivation_chain`; `side_binarity`, `L3_binarity`, `pending_binarity` | none |
| Totality: every distinction has already been completed | `totality_completes` (BinarityVsTotality.v) | excluded middle (Distinction.v) |
| The ledger of the nine axioms of ZFC | `zfc_axiom_ledger` (ZFCAxiomLedger.v) | none |

Over ℚ an exact zero may be missing—*x*² − 2 on [1, 2] has none—so the intermediate value theorem is given in approximate form.

## The Finitization Boundary

A process either terminates in an element or remains a role-limit. That the finitization boundary coincides with the boundary of constructivity is, in general form, a through-line of the volume, not a theorem; in decidable cases it has been proved without axioms:

- for the square root of a rational number the test “element or role-limit” is computable: a procedure decides whether the number is an exact square (`is_square_Q_reflect`, `decidable_finitization_boundary_Q`; DecidableBoundary.v, DecidableBoundaryQ.v—14 Qed);
- on the same classes the excluded middle for this test is a theorem, not an assumption: for squares of integers (`H1_constructive_half_is_theorem`) and for a perfect *k*-th power for every *k* (`H1_degree_uniform_decidable`, `decide_QkthElement`; H1ConstructivityDecidable.v, H1ConstructivityComputable.v, H1CubicConstructivity.v, H1GeneralDegreeConstructivity.v, H1RationalDegreeUniform.v—60 Qed);
- for nondecreasing bounded streams over ℕ, the claim “every such stream is constant from some step on—it reaches an element” is equivalent to the limited principle of omniscience, LPO (`boundary_frontier_is_lpo`; DynamicBoundaryDecidable.v, DynamicBoundaryFrontier.v, DynamicBoundaryLPO.v, RoleLimitLadder.v—40 Qed);
- the undecidable side is fenced off by one diagonal—the halting problem and uncountability (`computation_is_finitization_boundary`, `one_boundary_four_faces`; ComputationModel.v, KolmogorovRoleLimit.v).

## Selected Results: Support and Price

*The rows of the showcase on the page [[Mathematics#Selected Results|“Mathematics”]]: level, part of the volume, price, and support in the code.*

| Result | Level | Part | Price | Support in the code |
|---|---|---|---|---|
| Finite Actuality and Order—mathematics without the axioms of ZFC | synthesis; a new framing of the known | [[10 Set Theory without the Axiom of Choice\|Part X]] | 25 Qed, 0 axioms | `MuRecursion.v`: `mu_le_some_iff`, `mu_le_process_stabilizes`, `mu_le_strong_induction` |
| Choice by Order without the Axiom of Choice | synthesis | [[10 Set Theory without the Axiom of Choice\|Part X]] | 37 Qed (7 + 7 + 7 + 8 + 8), 0 axioms | `DecidableSelection.v`, `CountableSelectionFree.v`, `CountableDependentChoiceFree.v`, `DecidableKonig.v` (Kőnig’s step as a hypothesis), `SelectionWithoutChoiceSynthesis.v` |
| For the square root of a rational number the boundary is computable over ℚ | new theorem | [[15 Computation and the Finitization Boundary\|Part XV]] | 14 Qed, 0 axioms | `DecidableBoundary.v`, `DecidableBoundaryQ.v`: `is_square_Q_reflect`, `decidable_finitization_boundary_Q`, `half_is_role_limit` |
| One diagonal | synthesis and observation | [[15 Computation and the Finitization Boundary\|Part XV]] | 12 Qed, 0 axioms | `ComputationModel.v`: `computation_is_finitization_boundary`; `KolmogorovRoleLimit.v`: `one_boundary_four_faces`; `RiceRoleLimit.v`: `rice_role_limit` (Rice’s diagonal as a premise) |
| The uncountability of [0,1], the extreme value and intermediate value theorems—without the axioms of infinity and choice | synthesis and observation | [[05 Topology and Analysis of Processes\|Part V]] | uncountability and intermediate value—0 axioms; extreme value—excluded middle (its own declaration in `EVT_idx.v`) | `unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`); `IVT_process` (`IVT_ERR.v`); `EVT_strong_process` (`EVT_idx.v`) |
| The Galois correspondence for ℚ[√2, √3] | synthesis and observation | [[11 Algebra Fields Galois\|Part XI]] | 91 Qed, 0 axioms | eight files of Part XI in `src/algebra` (`GaloisQ23.v`, `GaloisDegreeQ23.v`, `IndependenceQ23.v`, `SplittingFieldQ23.v`, `FiniteFieldFp.v`, `RationalRootTest.v`, `SolvableGroup.v`, `AlgebraicClosureProcess.v`): `galois_group_four_distinct`, `sqrt3_not_in_Qsqrt2`, `no_maximal_rung` |
| The zeta function is a process | synthesis; a new framing of the known | [[13 Zeta Function and Number Theory\|Part XIII]] | 692 Qed; excluded middle, and in three lemmas of `ZeroStructure.v` also witness extraction; the formal `RH_zeros` is written without the condition ζ(ρ) = 0 and does not coincide with the Riemann hypothesis—it is a research line here | `src/zeta` (30 files): `zeta_process_cauchy`, `euler_partial_nonzero`, `RH_iff_reflect_equiv` |
| Nonstandard analysis over processes | synthesis; a new framing of the known | [[19 Nonstandard Analysis over Processes\|Part XIX]] | 54 Qed, 0 axioms | four files of `src/nonstandard` (`GermInfinitesimal.v`, `StandardPart.v`, `UltrafilterRoleLimit.v`, `DerivativeViaInfinitesimal.v`): `derivative_summary`, `ultrafilter_role_limit_summary` |
| Catalan numbers—three independent derivations | a new framing of the known; methods and exposition | [[17 Discrete Mathematics Probability Information\|Part XVII]] | 155 Qed, 0 axioms | `Catalan.v`, `Catalan_recurrence.v`, `Andre_reflection.v`: `catalan_explicit_formula`, `catalan_recurrence`, `catalan_forms_consistent` |

*Level is a self-assessment of novelty on the HIGHLIGHTS scale (the file `Книги/HIGHLIGHTS.md` of the repository): new theorem · synthesis and observation · a new framing of the known · methods and exposition; “synthesis” is the gathering of known results into one frame. Price is the set of assumptions reported by `Print Assumptions`.*

## The Volume “Mathematics”: An Extended Reading

The formal base and the volume [[Mathematics|“Mathematics”]] are two sides of one corpus: the volume unfolds in prose what stands here as code, and each of its parts rests on its own `src/` files. Points of support:

- **The axiomatic minimum**—how the status “Law/Principle” differs from the status “axiom” and what exactly is accepted on top of CIC: [[06 Axiomatic Minimum and Status Mechanism|Part I, Chapter 6]].
- **Real numbers as processes**—`RealProcess := nat → Q` in prose: [[01 P4 Infinity as Process|Part IV, Chapter 1]].
- **Set theory without the Axiom of Choice**—a set as a system; countability is constructive, uncountability a rule about processes; Schröder–Bernstein and Cantor without choice; the double fate of the Axiom of Choice itself: the completed choice graph is not built, the rule of choice is reinterpreted: [[10 Set Theory without the Axiom of Choice|Part X]].
- **The illusory constructions of ZFC**—what exactly is lost—and what is not lost—without its axioms: [[06 Illusory Constructions of ZFC|Part XIX, Chapter 6]].
- **The finitization boundary**—the closing line of the corpus: a process either terminates in an element or remains a role-limit; in decidable cases the boundary is computable (section above): [[01 Finitization Boundary|Part XX, Chapter 1]].

## The Boundaries of Formalization

The principle: **the boundary of the possible is part of the result.** In the source article the formalization carried 8 unproved statements (Admitted)—not lacunae but **boundary markers** of three kinds:

- **The ℚ limitation**—theorems that require the completeness of ℝ are false over ℚ (nested intervals over ℚ can converge to an irrational number): a marker of the ℚ/ℝ boundary; their unprovability over ℚ is a correct result.
- **The level of universes**—by default the type system of Coq does not admit a universe that contains itself (the assumption Type : Type leads to a contradiction—Girard’s paradox): such constructions are rejected with the error “Universe inconsistency,” and Hierarchy (P1) is held here by the type system itself.
- **The stability of digits**—`Qfloor` is discontinuous; the interval approach (167 Qed) displaced the digit approach entirely.

Later all these statements were closed—by weakening statements and by explicit assumptions (Heine–Borel is proved with an explicit hypothesis of a Lebesgue number: over ℚ the interval is indeed not compact); the current state of the base is **0 Admitted**.

## A Map by Branches

The branches of the corpus named below are represented in the code by models. All lines below are about the model: the concepts are given by enumerations, numbers, and functions, and most lemmas fix the definitions of the model; where the model carries a substantive argument, it is named; what the machine has not checked is stated in the line. The lemmas of the map are built without axioms; the one exception is named in the line “Pointing is not yet access.” The files are in the directory `src/foundation/` of the repository unless stated otherwise.

### Logic

- **Binarity of the excluded middle—also for an uncompleted act**—section “The Ground” above (`pending_binarity`, BinarityVsTotality.v).
- **Two theorems of the stability of identity**—in the model the constitution of a system marks roles as necessary, permitted, or excluded: in a well-manifested system a necessary role is occupied by a manifestation (`essence_always_manifest`), and a change in the status of a necessary role gives another *A*, not the former one changed (`critical_mutable_impossible`, `essence_change_is_other_A`). The statuses of the roles give the modal square: a necessary role is the necessary layer, a permitted one the actual or the potential layer depending on its filling, an excluded one the impossible layer (`square_covered`); in a well-manifested system an excluded role is empty (`forbidden_never_manifest`): `KnowledgeIdentityRoles.v` (17 Qed). Analysis—[[Identity]].
- **The point of maximum is the first of the greatest**—`argmax_idx_maximizes` (EVT_idx.v); analysis—[[Order#Order and the Assignment of Statuses|“Order”]].
- **Philosophy**—the only formal claim: completed wisdom (the wholeness of what is understood) does not exist as an object—this is “no completed corpus” (`as_object_fails`, `KnowledgeProcess.v`), applied to wisdom ([[Philosophy]]).

### Metaphysics

- **The witness is a positional role, not a thing**—one system can stand on both sides of cognition: `KnowledgeSubject.v` (`subject_is_positional`, `same_system_both_positions`). The constitutive core is a threshold of at least one, at least one channel, selective attention; reflection and memory are not necessary (`minimal_subject_without_reflection`). There is no outside view of oneself: knowing itself, the knower is inside the system it knows (`no_external_self_view`). Analysis—[[Metaphysics#The Witness|“Metaphysics,” “The Witness”]].
- **The three moments of perception**—in the model a moment is a type with three values, and there are exactly three of them (`moments_count_three`); perception takes place exactly when all three are present (`perceives_iff_all_moments`); it does not depend on the directedness of the will (`perception_independent_of_aim`): `PerceptionTriad.v` (15 Qed).
- **Two fields, channels, and the potential of the will**—data are a rung of the objective field, information and record of the subjective one (`rung_field`); there is no transition without a channel (`no_channel_no_transition`), designation does not require a channel, the ladder skips no rung (`ladder_no_skip`); the potential of the will—the difference of the fields—does not fall below its starting level and is not exhausted (`will_inexhaustible`—under the condition of the model: every new record opens no less than it closes), the marking out of a part is possible at every step (`selection_always_possible`): `KnowledgeMentalField.v` (27 Qed). Analysis—[[Metaphysics#The Mental Field|“Metaphysics,” “The Mental Field”]].
- **The modal square of the field**—three layers exhaust the witnessable (`witnessable_three_layers`); the necessary is in the field but without a generating step (`necessary_no_generating_step`), exactly the actualized is generated (`generated_iff_actual`); time applies exactly to the generated—to the necessary it does not apply (`necessary_timeless`, `timed_iff_generated`); the negation of being is an involution, the extreme corners pass into each other (`non_being_involutive`, `square_extremes`): `KnowledgeMentalField.v`.
- **The scale of the will and the count of witnesses**—the will is never zero, there are exactly two values by the number of statuses (`will_never_zero`, `will_injective`); the minimum is nirbīja-samādhi (`seedless_minimum`); return is guaranteed (`no_extinction`); two statuses over three positions—six states of the witness (`states_complete`); there is one more witness than there are differences, and Logic is not perceived in any experience (`consc_eq_diff_plus_one`, `logic_never_perceived`): `KnowledgeWillStatus.v` (17 Qed). In the model statuses and positions are given by enumeration, and the lemmas read this table.

### Theory of Systems

- **The triple does not determine a system**—in the model two systems with the same elements and the same constitution differ in the level of the elements (`triple_not_complete`); the full record of a system is ground, structure, and level (`err_representation`): `ERRRepresentation.v` (8 Qed). Analysis—[[Theory of Systems]].
- **The hierarchy of levels is strict**—no level precedes itself (`level_lt_irrefl`, TheoryOfSystems_Core_ERR.v).
- **Characteristics as roles, and constitution**—the modal square of the constitution is in the line “Two theorems of the stability of identity”; constitution as a condition on the process of binding: the stagewise condition on a constant relation coincides with the constitution itself, stagewise fulfillment of a stronger constitution implies fulfillment of a weaker one, and the model contains a binding that is not yet fulfilled at the first stage and is fulfilled at the second (`err_process_constitution`, `relating_genuinely_unfolds`): `ERRProcessConstitution.v` (5 Qed).
- **The canon of interaction**—a linked whole does not decompose into a sum of its sides (`linked_not_sum`); two boards with different states share one operator without merging (`boards_not_merged`); a record table reads only statuses (`table_reads_status_only`); all of it together—`interaction_canon`: `ERRLink.v` (18 Qed).
- **Dynamics**—the arrow of steps does not return: in the model a step is the next natural number (`arrow_never_returns`, `L5_Arrow.v`, 13 Qed); a slice can recur, a step cannot (`state_recurs_time_does_not`; in the code the slice is called a state), a bounded orbit does not escape (`attractor_excludes_escape`): `ERRDynamicsArrow.v` (11 Qed); a quantity that a step does not increase does not grow along the whole orbit either (`lyapunov_nonincreasing`, `ERRDynamicsLyapunov.v`, 11 Qed); approach without arrival—halving from one never gives zero, and only zero arrives at zero; the model records approach as the boundedness of the orbit (`halve_one_approaches_never_arrives`, `halve_arrival_only_zero`): `ERRDynamicsGroupBasin.v` (12 Qed).
- **Emergence**—in the model a property of the whole not carried over from the sides is a relation that the product of the sides lacks: the parity system has it, the product is separable, and parity is not (`err_emergence_deepened`, `ERREmergenceSystem.v`, 7 Qed); the measure of emergence is the count of pairs on which the relation of the whole differs from the relation composed from the sides: for coincidence the measure is zero, and a positive measure presents a witness pair of the discrepancy (`err_emergence_measure`, `ERREmergenceMeasure.v`, 8 Qed); the kinds of relation of the whole to its sides—reducible, superadditive, subadditive, inseparable: in the model each kind is inhabited by an example, the reducible is separable, the superadditive and the subadditive are irreducible (`err_emergence_taxonomy`, `ERREmergenceTaxonomy.v`, 8 Qed).
- **The bridge to the Architecture of Reasoning**—the well-formedness check rejects the constructions of Russell, the Liar, and Grelling (`russell_is_ill_formed`, `liar_is_ill_formed`, `grelling_is_ill_formed`): `ParadoxDiagnosis.v` (11 Qed).

### Epistemology

- **Knowability in principle**—everything determinate is decidable to one of the sides: `KnowledgeDistinctionGrounding.v` (`knowable_in_principle`). The knowable is not yet known: determinacy is given with the thing, while the record requires a particular knower (`knowable_not_yet_known`; `KnowledgeSubject.v`, `knowable_not_known_witness`). To know is to settle a distinction: the atoms of knowledge are the laws of the primary distinction (`knowledge_is_distinction`, grounded in `Distinction.v`).
- **The root and the synthesis of the branch**—one boundary (learnable = finitizable = constructible, `KnowledgeFinitization.v`), one diagonal (unlearnable = undecidable = uncountable—particular cases of one Lawvere fixed-point theorem, `KnowledgeDiagonalBridge.v`: the code has one instance for Cantor, halting, and Russell; Gödel by reference, not in the code; halting was brought into Lawvere’s scheme by Yanofsky, 2003), a map of the four pillars as one (`KnowledgeSynthesis.v`).
- **The ladder data → information → record**—the watershed is twofold by carrier: data are carried by the source, information adds the witness (`KnowledgeInformation.v`); a difference becomes information only for the witness—an active taking, not a mirror; channel and selective attention—`KnowledgeSubject.v`. The phenomenal side—filter, illusion, expectation—is empirical and left to the prose ([[1 Recognition|“Recognition”]]).
- **Knowledge-about and its sources**—knowledge-about is taken from presence (from outside or from inside; from inside—knowledge-how); transmission is second-hand, a distillate; the meeting is necessary: `KnowledgeSourceOrder.v`.
- **Knowledge-how is a process and irreducible**—behind every stage there is a next one, there is no step “everything has been gone through”: `KnowledgeProcess.v` (`as_object_fails`); the gap diverges without limit: `KnowledgeGap.v` (`deficit_diverges`); a skill does not reduce to a corpus of facts (Ryle’s regress): `KnowledgeIrreversible.v` (`how_underdetermined_by_that`).
- **The gap: catching up is impossible by construction**—the theorem of the nondecreasing gap `self_deepening_gap_nondecreasing` (`KnowledgeGap.v`): under the premise that every new record opens no less of the knowable than it closes, the difference “field − slice” does not decrease at any speed of recording.
- **A phase transition**—the outcome of the race is decided by the threshold: a bounded field is overtaken by the record (`knowledge_completes_when_bounded`), an immense one gives a diverging gap (`knowledge_race_phase_transition`, `KnowledgeGap.v`); interaction as a tier with a trace—`KnowledgeInteraction.v`.
- **There is no completed corpus as an object**—all-embracingness in the course exists, a ready-made corpus does not: `KnowledgeProcess.v` (`knowledge_process_capstone`, `as_object_fails`).
- **Intuition is a channel of knowledge-about, not of presence**—it carries knowledge-about taken as a whole; presence is not obtained through a channel: `KnowledgeInsight.v` (`usmotrenie_is_a_that_channel`). Method and position are two axes: insight and discursive thought (method) are separated from “from outside” and “from inside” (position) (`position_method_disentangled`, `both_positions_yield_that`, `usmotrenie_unique_up`). One can grasp the whole at once—one can understand it only in order (`KnowledgeInsight.v`). Analysis—[[Intuition]].
- **Effective depth is the least of three limiters: the object, the channel, the threshold**—`KnowledgeDepth.v`; the vertical is bidirectional (the threshold fails both downward and upward); thresholds are mastered in order—a tier cannot be held without mastering the one below (`tiers_mastered_in_order`); comparison across verticals is partial—there is no global numerical scale of depth (`KnowledgeDepthCrossVertical.v`).
- **The order of sources**—presence is the root, knowledge-about the sink: `KnowledgeSourceOrder.v` (`presence_is_root`, `that_is_sink`); knowledge-about is a distillate of the meeting with losses: the distillate is strictly thinner, the meeting is necessary (`that_is_distillate`, `no_meeting_no_that`).
- **Irreversibility**—presence cannot be recovered from a proposition, the going-through cannot be reduced to facts: `KnowledgeIrreversible.v` (`presence_underdetermined_by_that`, `no_section_for_distillation`).
- **Determinacy decides the loss in transmission**—what is fully determinate is transmitted without loss, what is indeterminate loses the more, the wider the field of readings: `KnowledgeDeterminacy.v` (`determined_transmits_losslessly`, `logic_lossless`, `indeterminate_can_lose`).
- **Untruth and the lie: a double root**—untruth is a status of content, the lie a status of the act: the same content, two act-statuses (`same_content_two_acts`, `untruth_without_intent_not_lie`); every act has a root of the act, a root of the content exists only for truth—the lie is rooted only as an act (`lie_rooted_only_as_act`); the sophist conceals both deficits (`sophistry_double_concealment`); projection is legitimate, the lie is a modal substitution: the possible passed off as what is (`projection_itself_legal`, `substitution_dishonest`); the field is not damaged—another’s record is (`objective_field_undamaged`); refusal turns the vector away, it does not erase the record (`refusal_turns_away_not_erases`); an overlay stands only while it is held—one breach brings it down (`overlay_needs_every_moment`, `overlay_falls_at_first_gap`), truth carries itself (`truth_needs_no_effort`): `KnowledgeTruthLie.v` (21 Qed).
- **The rungs of representation and the two paths of untruth**—two axes of representation: link (opinion · knowledge-that · understanding) and correspondence; knowledge cannot be false: “false knowledge” is an illusion of knowledge (`know_that_never_wrong`, `wrong_link_is_illusion`); the Gettier case does not become knowledge: a correct coincidence without a chain is a true opinion (in Gettier, a justified one), the tie of the *Meno* is a path (`gettier_dissolved`, `meno_binding`); absolute truth about the potential is two-faced—the structure is open to reasoning, the filling without a meeting gives only a projection (`structure_always_open`, `no_meeting_only_projection`); non-contradiction is an admission to absolute truth, not a sign of it (`consistency_not_truth`, `possibility_not_guarantee`); one who does not know absolute truth can only resort to replacement—hence replacement is widespread (`ignorant_only_substitutes`); distortion falls at the first uncovered meeting of another, replacement at the first meeting of one’s own, truth stands without effort (`distortion_falls_at_first_gap`, `substitution_falls_at_own_meeting`, `truth_stands_free`): `KnowledgeTruthLadder.v` (29 Qed). Analysis—[[Truth and Absolute Truth]].

### Ethics

The files are in the directory `src/ethics/`.

- **The status “right” is computed**—in the model the status of an act is a comparison of correspondence against a threshold; it is decidable (`correct_dec`) and coincides with the answer of the computing procedure (`passes_reflect`); the pool of the admissible is exactly the right ones among those offered (`in_pool_iff`, `pool_correct`): `EthicsStatus.v` (15 Qed).
- **The status is two-valued**—in the model the status is a type with two values (`status_bivalent`, `status_exclusive`); the wrong is given by a pair “kind, depth,” and every pair occurs—the axes are independent (`intent_magn_independent`): `EthicsModality.v` (14 Qed).
- **One who is coerced is not responsible**—in the model responsibility includes the freedom of the act, and an unfree act does not carry it (`forced_not_responsible`): `EthicsResponsibility.v` (11 Qed).
- **A technically safe but deceiving operator**—in the model there is an operator that is safe by the technical criterion and at the same time not aligned (`tech_safe_not_imply_aligned`): `EthicsAI.v` (7 Qed).

Analysis—[[Ethics]].

### The Architecture of Reasoning

#### Question

- **A question is a pointing act, not a gap**: `KnowledgeInquiry.v` (`question_is_pointing_not_access`, `gap_not_sufficient`). The ring of the field: a well-formed question lives in the middle layer of the boundary (`three_zones`, `well_founded_question`).
- **Pointing is not yet access**—a well-formed question does not promise an answer: `KnowledgeInquiry.v` (`question_without_road`, `question_access_independent`). The answer itself and its content are different things ([[Question]]): in the model the content is the side of the distinction of the goal that holds; that one of the sides always holds, the model takes in the mode of totality (`answer_exists` is `classic` applied to the goal); the road to the answer is concrete (`road_is_concrete`, without assumptions): `KnowledgeAnswerExists.v`.
- **The structure of a question: goal · direction · ground**—the defects of posing (group 1.A of the catalog) are corruptions of the parts, and the classification is complete (`ill_formed_classified`); the constitutive order is goal → direction → ground (`complete_passed_goal`); three kinds of goal by the measure of givenness, with closing acts (`closers_injective`)—the direction of questions of fact and of decision stands in the known, that of a completing question in the ring (`wf_filling_on_ring`); the path to the answer—completing, choice, ascertainment—with an invariant of polar closure (`path_closes_polar`); the ground is two-faced—content and active, the faces independent (`grounds_two_faces`; the active ground is attention together with sustained interest: `act_ground_needs_both`): `KnowledgeQuestion.v` (37 Qed).
- **The ladder of questions, the root, connectedness, the ethics of entry**—three tiers of questioning; distraction is outside the law (`legal_two`); hierarchy: the Source within Logic (`source_inside_logic`), the summit is self-grounded and unique (`self_grounded_unique`), the path outward is finite for every system (`chain_to_root`), any two points are connected through a common meta-system (`path_via_common_meta`), a corpus of systems is impossible (`no_svod_of_systems`); duality: everything that is an answer carries a root, the sophist conceals an existing root (`answer_has_root`, `sophistry_conceals`); all defects of 1.A distort the intention and lead away from the root (`all_defects_distort`, `defect_leaves_root`); walking through the tiers without skipping (`no_skip`), the fields of questions are nested transitively (`within_trans`): `KnowledgeQuestionPath.v` (26 Qed).
- **Questions and domains: the cycle realizes the path**—the cycle of domains is monotone in the stages of the path and, folded, is exactly the full path: completing (building the pool), choice, ascertainment (`cycle_monotone`, `cycle_is_full_path`); construction before any choice, choice before verification (`build_before_select`, `select_before_verify`); decision enters reasoning exactly once—as the framework, and the will closes it (`unique_decision_domain`, `will_closes_frame`); verification is unique and last (`unique_verifier`, `verifier_is_last`); goals are formed before any choice (`goals_before_every_choice`); reflection is the only change of object: the path itself becomes the object (`unique_reflexive`, `world_before_path`): `KnowledgeDomainCycle.v` (16 Qed).

#### Domains

- **Six domains: the structural core**—in the model the slice is a growing network of records, and every operation of the knower touches exactly one of its five places: the entry of a record from outside, the meaning of a record, a link between records, a record inferred from those present, and the slice as a whole. The place of the link splits in two—the axis of the relation is not given with the data: first the axis is taken, then things are related along it—and the five places give six operations (`edge_split`, `place_surjective`, `count_ops`); domains and operations correspond one to one (`dom_op_left`, `dom_op_right`); the dependence of the domains is a strict linear order (`dep_irrefl`, `dep_trans`, `dep_total`, `chain_order`): `KnowledgeReasoning.v` (22 Qed). Reflection as a process is given in the model by the same pass of the domains over the trace of the path already traveled—the model introduces no seventh operation; the lemmas fix this definition (`reflection_no_seventh`, `reflection_is_instantiation`: `ReflectionRecursion.v`, 23 Qed). That the five places are exhaustive and the six necessary is not checked by the machine: this is an argument of the prose; on the hub [[Domains]] it stands as a thesis about the minimal architecture.
- **Comparison in the model**—comparison stands on a common tier: the ladder data → information → qualities → characteristics is irreversible, comparison is defined where both sides have the tier—otherwise it is a category mistake (`category_mistake_iff`, `comparable_downward`); changing the measure along the way invalidates the gathered list of relations (`switch_invalidates`): `ComparisonLevels.v` (10 Qed).
- **Reflection in the model**—the conclusion requires both checks of the outcome (`conclude_needs_both`), abstention occurs exactly when one is missing (`abstain_iff_missing`), a defect of a rung is inherited by the whole ladder (`defect_inherits`), passive reflection does not change the trace (`passive_no_mutation`); there is no slice that holds the whole path (`no_full_self_view`; `whole_strictly_more`—about the growth of the model’s field by a step): `ReflectionRecursion.v`.

#### Paradox Catalog

- **The paradox and the solvable problem are separated**—in the model of the catalog a solution is admitted exactly by a non-paradox (`only_nonparadox_admits_solution`, `Architecture_of_Reasoning/ParadoxDissolution.v`, 29 Qed); the constructions of Russell, the Liar, and Grelling are rejected by the well-formedness check—the line “The bridge to the Architecture of Reasoning” above. Analysis—[[Paradox Catalog]].
- **Probabilistic non-paradoxes**—the Monty Hall problem, birthdays, the false positive, the lottery, the preface, Simpson’s paradox, the ravens: in the model of the catalog they are assigned the category “non-paradox” (`nonparadox_46_not_paradox`, `nonparadox_count_8`, `Architecture_of_Reasoning/ParadoxDissolution.v`); their numerical count—2/3, 0.507, and others—is not yet written in the code: these are candidates for the branch “Probability.”

### What Is Not, and Cannot Be

- **A substitution is never legal**—in the model of the registry each entry names the category from which it is built and the category for which it is passed off; the model calls an entry legal when it keeps its category, and the lemmas fix this definition: none of the sixteen entries of the model is legal (`impossible_never_becomes_legal`, `all_registry_illegal`, `registry_size`). The model repeats the registry of the page; the categories of each entry are assigned from its text. A derivative is given by a source category it shares with the root: for the view from nowhere and nothing this is absence, for the death of the ego and the ego as agent it is an element, for an occupied role-limit and actual infinity it is a process (`nowhere_derives_from_nothing`, `ego_death_derives_from_reification`, `role_limit_derives_from_infinity`); the classes of a shared source category repeat the structure of the page: groups of two, two, and three entries and nine standalone entries (`registry_structure`); the Ego zone has two independent axes (`axes_independent`); only the witness wills and only an organism can die—by the tables of the model (`only_witness_wills`, `death_only_for_organisms`); disidentification keeps the zone (`disidentification_keeps_zone`), and after the peak—identification dropped and attention withdrawn—the return finds the zone intact (`return_with_zone_intact`): `KnowledgeEgoZone.v` (24 Qed). The thesis “every impossibility is built by a category substitution” is a working rule of the registry: a new entry must present its substitution ([[What Is Not and Cannot Be]]).
- **A change of essence as a change of *A***—the line “Two theorems of the stability of identity” above.
- **The muteness of the element and the speech of the rule**—there is no rational square root of 2 (`no_rational_sqrt2`, `src/analysis/Sqrt2Irrational.v`, 14 Qed: infinite descent); in the Pell process pₖ² − 2qₖ² = ±1 (`pell_pm`), hence the exact error of the approximations xₖ = pₖ/qₖ: \|xₖ² − 2\| = 1/qₖ² (`sx_abs_eq`, `src/Sqrt2Approx.v`, 14 Qed). Both are theorems, not definitions.
- **Neighboring supports**—the corpus (`no_svod_of_systems`, `as_object_fails`), the will (`will_never_zero`, `no_extinction`), the outside view of oneself (`no_external_self_view`), Gettier (`gettier_dissolved`), the arrow of time (`arrow_never_returns`), the role-limit (`halve_arrival_only_zero`, `halve_one_approaches_never_arrives`)—in the lines above.

## The Repository

All the code is open: [github.com/Horsocrates/theory-of-systems-coq](https://github.com/Horsocrates/theory-of-systems-coq). Every proof can be read and rebuilt: the compiler will not accept an incomplete proof under `Qed`, and everything a theorem accepts without proof (`Admitted`, `Axiom`) is listed for it by the command `Print Assumptions`.

## Summary

1. **Here is the machine layer of the corpus:** which of the claims derived on the pages have been brought to a formal record, in which files, and at what price.
2. **A proof marked `Qed` is accepted by the kernel only when complete;** an incomplete one can be accepted only as an assumption (`Admitted`), and `Print Assumptions` shows it. There are no such statements in the base.
3. **The chain of the ground is present in the code as an axiom-free model;** its derivation is on “Logic” and “Theory of Systems.”
4. **There are two assumptions of the instrument:** the excluded middle in the mode of totality and witness extraction—by Sufficient Reason: existence is determinate. The second is indefinite description, and choice over families follows from it; hence the price of each result is named separately.
5. **Of the nine axioms of ZFC, one remains beyond the finitization boundary in the ledger**—Power Set; the ledger is a classification, not a theorem.
6. **In decidable cases the finitization boundary is computable,** and the excluded middle there is a theorem without axioms.
7. **Where the model only fixes a definition, this is stated;** what the machine has not checked is stated too.

---

Navigation: ← [[Mathematics]] · [[What Is Not and Cannot Be]] →

[^1]: Horsocrates. *Theory of Systems: A First-Principles Foundation for Mathematics*. 2026. — [philpapers.org/rec/HORTOS](https://philpapers.org/rec/HORTOS).
