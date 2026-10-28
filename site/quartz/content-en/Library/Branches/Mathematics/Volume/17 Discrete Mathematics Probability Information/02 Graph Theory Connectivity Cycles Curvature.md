---
title: "Chapter 2. Graph Theory—Connectivity, Cycles, Curvature"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/02 Теория графов — связность, циклы, кривизна.md"
sourceBlob: f08ad90fead964c859f5ff1b5bf5d405fe380457
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

A graph is the simplest relational system: a finite list of vertices and a finite list of edges. Nothing beyond this; “the set of vertices” and “the set of edges” are modes of consideration of two lists. After counting (Chapter 1), graphs add a *relation* to finite structures—and almost all the basic questions we consider here remain, in the finite list model, on the Element side: connectivity and acyclicity are *decided by a terminating search*, and the graph Laplacian is computed exactly over ℚ (its spectral invariants are the numerical shadow of the structure).

*A graph is a pair of finite lists; connectivity and cycles are **terminating
processes** (fuel-bounded search), not properties of a completed object.*

The chapter leads from structure (vertices/edges) to connectivity and cycles, then to the graph Laplacian and the spectrum, and closes with bridges: to discrete curvature (Part XII) and to the physical substrate—lattice field theory, tensor and spin networks.

## The Graph as a Finite Structure

A graph is built from the empty one by adding vertices and edges; the membership of a vertex and the presence of an edge are *decidable* predicates (Boolean functions), and the degree of a vertex and the list of neighbors are computable from the list of edges[^1]. We do not start from an abstract set of vertices—we work with a list implementation: there is a concrete pair of lists, and all questions about it are settled by finite exhaustive search of these lists. This is an Element structure by its very construction.

## Connectivity and Acyclicity—Terminating Processes

The main questions about a graph—whether one vertex is *reachable* from another and whether there is a *cycle*—are settled by depth-first search. And the key P4 point: this search *terminates*, because the graph is finite, and the depth of the search is bounded by the number of vertices itself[^2].

*The fuel bound is finitization itself: a search over a finite graph must stop, and reachability becomes an Element predicate.*

The comparison with the finitization boundary is direct. Reachability in a finite graph is a terminating process (Element). Reachability in an *infinite* graph is already the role-limit side: the search may not terminate, and “is it reachable?” becomes a question about a completed infinite object. Discreteness keeps us on the finite side precisely because the fuel is finite.

## The Laplacian and the Spectrum

It is convenient to gather the structure of a graph into one operator—the *graph Laplacian* $L = D - A$ (degrees minus adjacency). It is computed exactly over ℚ, and its rows *sum to zero*—a structural conservation law, a direct property of the definition[^3].

The spectrum of the Laplacian is a bridge from structure to number: its eigenvalues (algebraic in general, not necessarily rational) encode connectivity (the smallest nonzero one is the algebraic connectivity), and the spectral entropy measures the “spread” of the structure[^4]. And the same Laplacian links the graph with physics: the spectral gap plays the role of the mass gap[^5].
All of this is exact ℚ-arithmetic on a finite matrix: the Element side.

## Discrete Curvature and the Physical Substrate

A graph is not only a combinatorial object but also a *discrete space*. Discrete curvature is defined on it (a bridge to the geometry of Part XII: a manifold as a process of gluing local charts—and its discrete model is a lattice graph), and it serves as the *substrate* of the physical theories: lattice gauge theory lives on a lattice graph, and tensor and spin networks are graphs with data on the edges[^6].

What is essential for the ontology: everywhere here space is *discrete and finite* at every stage—the continuous manifold appears only as a limit-process of lattice refinement (Part XII), not as an initial completed object. In the geometric reading, the lattice graph is the Element substrate, and continuum space arises as a limit-process of refinement.

## E/R/R Analysis: The Graph as a System

Let us analyze the graph by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *adjacency relation*: which vertices are joined by an edge. From it, by rules, the degree, the neighborhood, reachability (the rule of fuel-bounded search), and the Laplacian $L=D-A$ are derived. The rule of the relation stands above individual vertices and organizes them into a structure.

**Roles (L4).** A vertex and an edge are *elements* of the list carrier, but their graph meaning is a role within the adjacency relation; connectivity/reachability is a *status* of a pair of vertices, computed by the rule of search; the Laplacian is the role of *structure-as-operator* that translates the graph into a spectrum. “The set of vertices” is a mode of consideration of a list (operational divisibility).

**Elements (L1 + P4).** The bearers are finite lists of vertices and edges and the rational entries of the Laplacian matrix. Under P4 the finite structure is actual; the infinite graph and the continuum limit of the lattice are role-limits, not completed objects.

**Well-formedness check.** The adjacency relation and the rule of search are Rules; vertex/edge/connectivity/Laplacian are Roles; finite lists and the ℚ-matrix are Elements; there are no overlaps. There is no self-application: the relation stands above the vertices and is not a vertex.

**What the analysis yields.** It shows that the graph is the purest Element system: finite bearers, decidable predicates, a Laplacian exact over ℚ (the spectrum is its numerical shadow); and that its exit to the continuum (discrete curvature $\to$ smooth manifold, lattice $\to$ field) is the passage to the role-limit, the same one that the whole volume carries. The graph is the place where discrete mathematics meets physics while remaining on the finite side.

The structure and its spectrum are built; in the next chapter a measure is laid onto the finite bearers—we pass to probability as an operational theory over finite spaces, without Lebesgue measure and without the Axiom of Choice.

---

[^1]: `Graph` as a pair of lists `mkGraph`; `has_node`, `has_edge` (Boolean, decidable), `neighbors`, `out_degree`, `well_formed`. Machine-checked, 0 axioms.
[^2]: `is_reachable` and `is_acyclic_bool` are Boolean functions computed by fuel-bounded search (fuel $=$ the number of vertices). Machine-checked, 0 axioms.
[^3]: `graph_laplacian` $=$ `path_degree` $-$ `path_adj` ($D-A$); the lemmas `L_row_sum_*`: every row of the Laplacian sums to $0$. Machine-checked, 0 axioms.
[^4]: The spectral entropy of a graph and the graph propagator are formalized in separate clusters (`graph/SpectralEntropy`, `graph/GraphPropagator`); machine-checked, 0 axioms.
[^5]: `laplacian_mass_gap_connection`: the spectral gap of the Laplacian as a discrete analogue of the mass gap. Machine-checked, 0 axioms.
[^6]: The graph zoo and the graph–physics synthesis (`graph/GraphZoo`, `graph/GraphPhysicsSynthesis`, the Anderson model) gather these bridges; machine-checked, 0 axioms.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/01 Combinatorics Process Counting|Chapter 1. Combinatorics—Process Counting]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/03 Probability as an Operational Theory|Chapter 3. Probability as an Operational Theory]] →
