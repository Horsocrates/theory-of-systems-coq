---
title: "Chapter 4. E/R/R: The Ontology of a System"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/01 Перво-различие и законы логики/04 ERR онтология системы.md"
sourceBlob: 771d4cc7c7caf80ac58b32fee5f7fb4bb3b1e3b5
translated: 2026-10-20
status: draft
---

## Where We Have Come From

The body of theorems in the file `LawsFromDistinction.v`, analyzed in Chapter 3, has shown that a single structure—the record `Distinction` together with the type `Level`—already carries all five laws of logic $L1, L2, L3, L4, L5$ as its structural properties. The laws themselves, however, remain *ontologically primary*: they are not *derived* from the act of distinction as from a source; they are only *traced* in it as theorems, which is a methodological step within a formal system and not an ontological claim about their origin.

**The next step.**  After this work it is natural to turn to the question: what is the structure of that which all these laws determine? In other words: *what is a system*? This question is central to the Theory of Systems, within which the present work is written, and posing it completes the movement of Part I from the first principle to the ontological arrangement.

The answer unfolded in the present chapter is as follows. The derivation chain begun in Chapter 2 and continued in Chapter 3 has one more step that has not been taken so far. After the laws $L1$–$L5$ comes an intermediate link: four principles, derived from the laws as their structural consequences. And after the principles comes the concluding link: the E/R/R structure (Elements / Roles / Rules), which realizes the necessary conditions of systemhood. *Architecturally*, the full chain of the book has the form:

$$
A = \exists \;\to\; \text{Distinction} \;\to\;
  L1\text{–}L5 \;\to\; P1\text{–}P4 \;\to\; E/R/R.
$$

Here, however, precision is needed about what exactly has been formalized. The links $\text{Distinction} \to L1$–$L5$ and $L1$–$L5 \to P1$–$P4$ are formal theorems of Rocq (the files `LawsFromDistinction.v` and `PrinciplesFromLaws.v`). The concluding link is analyzed in the file `ERRFromDistinction.v`, and this file fixes a *narrower* core of the chain than the full architectural scheme: it derives the E/R/R structure directly from the record `Distinction` and the laws, without carrying out a *separate* formal theorem of the form “from $P1$–$P4$ follows E/R/R.” The full bridge through $P1$–$P4$ is a conceptual interpretation of the architecture: it is substantively correct and may later be strengthened by a separate theorem, but *at present* it is not written in the repository as a single formal dependency. We shall keep this difference between the architectural scheme of the book and the actual content of the file in view throughout the chapter.

Let us begin by completing the derivation chain.

## The Four Principles

### From Laws to Principles

The laws $L1$–$L5$, derived in Chapter 3, are the conditions of determinacy in their most general form. For these conditions to yield the *structure of a system*, one more intermediate step is needed: bringing to light the *principles* in which the laws work together.

There are four such principles: $P1$ (Hierarchy), $P2$ (Criterion Precedence), $P3$ (Intensional Identity), $P4$ (Finite Actuality). Each is obtained from the joint work of particular laws:[^1]

| **Principle** | **Content** | **Source** |
|---|---|---|
| $P1$ | Hierarchy ($S \notin S$) | $L1 + L5$ |
| $P2$ | Criterion Precedence | $L5$ |
| $P3$ | Intensional Identity | $L1 + L4$ |
| $P4$ | Finite Actuality | $L5$ |

Each principle fixes a structural consequence of the laws that is *already at work* in the record `Distinction` but becomes explicit only when the arrangement of systems is at issue. Let us consider each.

### $P1$: Hierarchy

**Structural content.**  In any system $S$ that organizes elements under some criterion, the *organizer* stands at a level above the *organized*. By $L1$, $S$-as-organizer has a determinate identity that does not blur; by $L5$, the level of the organized is below the level of the organizer. The joint work of $L1$ and $L5$ gives an asymmetric hierarchical structure: $\text{Level}(\text{organizer}) > \text{Level}(\text{organized})$.

**Formal theorem.**  In Rocq the hierarchical asymmetry is expressed by the irreflexivity of the order operator:

```coq
Theorem P1_from_L1_L5 : forall l : Level, ~ (l << l).
Proof. exact level_lt_irrefl. Qed.
```

Particular structural properties are also at work in the $L5$-hierarchy: $L_1 \ll L_2$ and $\neg (L_2 \ll L_1)$ (the ground level $L_1$ is strictly below the second); $l \ll LS l$ for any $l$ (every level is strictly below its successor); asymmetry (if $l_1 \ll l_2$, then $\neg(l_2 \ll l_1)$).[^2]

**Consequence: $S \notin S$.**  If a system $S$ contained itself as its own element, it would be at once the organizer and the organized—that is, it would stand at two different levels at once. This would mean $\text{Level}(S) <
\text{Level}(S)$, which contradicts irreflexivity. Thus no system contains itself.

**Consequence: [[Russells Paradox|Russell’s paradox]] is blocked.**  “The set of all sets that do not contain themselves” presupposes a construction in which the question of self-membership is meaningful. By $P1$ such a question has no determinate content: there is no self-membership in any correctly constructed system.[^3]

### $P2$: Criterion Precedence

**Structural content.**  By $L5$, every operation stands above its operand: an operation presupposes the operand as already existing. Applied to systems: the criterion that defines a system is an operation *on* that to which it is addressed; consequently, it stands at a level above the level of the result. This is *criterion precedence*: the level of the criterion $<$ the level of the system it sets.

**Formal theorem.**  The principle is presented in two forms:

```coq
Theorem P2_from_L5 : forall L (C : Criterion L), P2_valid L C.
Proof. exact P2_always_holds. Qed.

Theorem P2_structural : forall L (C : Criterion L),
  crit_level_witness L C << L.
Proof. intros L C. exact (crit_level_valid L C). Qed.
```

**Structural embeddedness.**  The peculiarity of $P2$ is that it does not *follow* from a law as a separate theorem: it is *built into* the very record of the criterion. The field `crit_level_valid` in the record `Criterion` *requires* a proof that the level of the criterion precedes the level of the system. Without this proof the criterion *cannot be constructed*: Rocq refuses to compile the definition.

This parallels the way $L2$ is built into the record `Distinction` through the field `exclusive` ((see the corresponding chapter) of Chapter 3): the law works as a part of the structure without which the structure itself is impossible, not “from outside.”

**Consequence: circular definitions are ruled out.**  From $P2$ it follows formally that no criterion can be constructed whose level coincides with the level of the system it defines:

```coq
Theorem P2_no_circularity : forall L,
  ~ exists C : Criterion L, crit_level_witness L C = L.
```

In other words, “$S$ is what satisfies $S$” is a formulation blocked by the type system of Rocq itself, since it requires constructing a criterion that violates $P2$.

**Consequence: stepwise definition is possible.**  The positive side of $P2$ is that it *provides* a sequence of definitions. Every new definition in Rocq can rest on what is already defined and stands at a level below. This sequence is a structural condition of the very possibility of building a formal system.

### $P3$: Intensional Identity

**Structural content.**  By $L1$, every system has a determinate identity ($S = S$); by $L4$, this identity requires a sufficient reason. The ground of a system is its criterion, that through which it *is* precisely itself. The joint work of $L1$ and $L4$ gives this: the identity of a system is determined through its criterion, not through its elements. This is *intensional* identity.

**Formal theorems.**  $P3$ is presented by four statements—properties of the relation of intensional equality `systems_intensionally_equal`:

```coq
Theorem P3_reflexivity : forall L (S : System L),
  systems_intensionally_equal S S.

Theorem P3_symmetry : forall L (S1 S2 : System L),
  systems_intensionally_equal S1 S2 ->
  systems_intensionally_equal S2 S1.

Theorem P3_transitivity : forall L (S1 S2 S3 : System L),
  systems_intensionally_equal S1 S2 ->
  systems_intensionally_equal S2 S3 ->
  systems_intensionally_equal S1 S3.

Theorem P3_from_L1_L4 : forall L (S1 S2 : System L),
  sys_criterion L S1 = sys_criterion L S2 ->
  sys_pos_bound L S1 = sys_pos_bound L S2 ->
  sys_uniqueness L S1 = sys_uniqueness L S2 ->
  systems_intensionally_equal S1 S2.
```

The first three ensure that intensional identity is an equivalence relation (reflexivity, symmetry, transitivity); the fourth fixes a substantive condition: the coincidence of the three components of the criterion entails the intensional equality of the systems.

**Consequence: identity through the criterion, not through the elements.**  Traditional set theory works with extensional identity: “$A$ and $B$ have the same elements, hence $A = B$.” In ToS intensional identity is at work, and it is stronger: even if two systems contain the same elements, they are *not identical* if these elements are obtained under different criteria. Consider a classical example from Euclidean geometry: the set of *equilateral* triangles (the criterion: three equal sides) and the set of *equiangular* triangles (the criterion: three equal angles) in the plane contain the same figures. But the *criteria* differ essentially: one rests on the measure of the sides, the other on the measure of the angles. By $P3$ these two systems coincide extensionally but are not intensionally identical: they have different grounds, different ways of being what they are.

**Consequence: the ontological priority of the criterion.**  From $P3$ it follows that a system is determined by *that through which it is*, not by *what is in it*. The criterion is an ontological ground, as opposed to a description of content (see (see the corresponding chapter) of Chapter 2). This position draws an essential methodological distinction between ToS and the set-theoretic approach, and it is at work throughout the rest of the volume.

### $P4$: Finite Actuality

**Structural content.**  By $L5$, every process has a sequential structure (stage after stage). At each stage a finite number of steps has been completed; each step adds a finite number of elements; finitely many steps times finite additions give a finite total. Applied to systems: at each particular stage $t$ a finite number of elements is actually present: $|S_t| < \infty$.

**Formal theorems.**  In Rocq the principle is formalized through the type `RealProcess` $:= \mathbb{N} \to \mathbb{Q}$—a sequence of rational numbers indexed by the naturals:

```coq
Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat),
  exists q : Q, R n = q.

Theorem P4_no_completed_infinity :
  forall q : Q, exists (n : Z) (d : positive), q = n # d.

Theorem P4_finite_at_each_stage : forall (R : nat -> Q) (n : nat),
  exists (num : Z) (den : positive), R n = num # den.
```

At each stage $n$ the process $R$ yields *one particular* rational number: a ratio of finite integers.

Here precision is needed about the strength of these theorems. Formally they prove a *modest* statement: each observed stage of the process has a particular rational value, represented by finite data—a numerator and a denominator. This is *not* the same as a formal theorem “actually infinite sets do not exist” or “the infinite set of traditional theory does not exist”: the theorems cited do not by themselves prove such a global exclusion. They prove the finiteness of *each stage*, not the absence of completed infinite totalities in general.

**The philosophical interpretation of $P4$.**  A broader *interpretation* of the principle $P4$ rests on this modest formal fact: infinity is to be understood as an unbounded *process*, not as a completed *object*. In traditional theory an *infinite set* is thought of as a completed, actually infinite object; the interpretation of $P4$ offers in its place a process that is not bounded above in the number of steps but has a finite state at each particular moment. What is called an infinite set, ToS is inclined to understand as an *unbounded process*: the sequence $R$ itself, not its “limit in actual infinity.” We shall unfold this interpretation—and its difference from the formal content of the theorems above—in the process mathematics of Part IV.

**Consequence: a construction of the real numbers without AC and
Infinity.**  In Part IV of the present volume the real numbers will be constructed through `RealProcess`—sequences of rational approximations. This construction *does not use* either the Axiom of Infinity (which postulates the existence of a completed infinite set) or the Axiom of Choice (which allows elements to be extracted from an infinite family by an algorithm that cannot be presented). This is a direct methodological consequence of $P4$: the whole construction rests on processes, not on completed objects.

### All Four Principles Together

All four principles work jointly: for any system $S$ at any level $L$, Hierarchy ($P1$), Criterion Precedence ($P2$), Intensional Identity ($P3$), and Finite Actuality ($P4$) hold at once. Formally, this unifying statement has the form:[^4]

```coq
Theorem four_principles_from_five_laws :
  (forall l : Level, ~ (l << l)) /\                  (* P1 *)
  (forall L (C : Criterion L), P2_valid L C) /\     (* P2 *)
  (forall L (S : System L),
    systems_intensionally_equal S S) /\              (* P3 *)
  (forall (R : nat -> Q) n, exists q : Q, R n = q). (* P4 *)
```

The proof of the unifying statement is the conjunction of the four theorems analyzed above.

With the derivation of the principles completed, we reach the last step before the formulation of E/R/R. The principles $P1$–$P4$ are the necessary conditions of systemhood, derived from the laws of logic. The structure that realizes these conditions in their minimal form is E/R/R itself. We pass to its formulation in the next section.

## E/R/R as the Ontology of a System

### Completing the Derivation Chain

The derivation chain that began with the first principle $A = \exists$ and passed through the record `Distinction`, the laws $L1$–$L5$, and the four principles $P1$–$P4$ has exactly one concluding link: the E/R/R structure. *Architecturally*, the full chain has the form:

$$
A = \exists \;\to\; \text{Distinction} \;\to\;
  L1\text{–}L5 \;\to\; P1\text{–}P4 \;\to\; E/R/R.
$$

Each link of the chain is a structural condition derived from the preceding ones. Each step *traces* the necessity by which any system is arranged, rather than *generating* it. The ontology of a system itself, the ultimate result of this tracing, is E/R/R.

Here, however, it is necessary to state precisely what the formalization fixes. The theorem `complete_foundation` from the file `ERRFromDistinction.v`[^5] proves the following: from any proposition a `Distinction` is built; for every `Distinction` the laws $L2$ and $L3$ hold; every `Distinction` gives an E/R/R structure with at least two roles; and the level hierarchy is irreflexive. This is the core of the concluding link. What the theorem does *not* contain is a separate formal dependency of the form “from $P1$–$P4$ follows E/R/R”: the file `ERRFromDistinction.v` does not import `PrinciplesFromLaws.v` and works with the record `Distinction` directly. The full bridge through $P1$–$P4$ is an architectural interpretation of the chain, substantively correct but not yet written as a single theorem. In the exposition that follows we speak of the chain in the architectural sense, noting where the formalization has already caught up with it and where it has not yet.

### Three Aspects of a System

**Structural content.**  Every system necessarily has three aspects:

- **Elements**—*what* there is in the system, its substrate: the particular bearers that occupy positions.
- **Roles**—*what* the elements are significant *for*, what function they perform in the system.
- **Rules**—*how* the interaction of the elements is organized, the laws that hold the system together as a system.

It is of fundamental importance:

***E/R/R are not three parts of a system but three aspects of one arrangement.***

They cannot be separated from one another. An element without a role is something amorphous rather than an element; a role without an element is an empty position with no bearer; rules without elements and roles are an abstract scheme that refers to nothing particular. Either all three aspects work at once, or the system does not exist. In the original formalization this principle is fixed directly: *“These are not three parts but three aspects of one act.”*[^6]

**The epistemic order vs. the ontological.**  The abbreviation E/R/R lists the aspects in the *epistemic* order: from what is outwardly observable to what lies deep. In analyzing an unfamiliar system it is natural first to see its *elements* (something directly accessible), then to recognize the *roles* (to see that the elements have significance, that they do something), and only then to bring to light the *rules* (to understand by what laws all of this works).

*Ontologically*, the order is the reverse. Rules are primary: they set *what it means* to be in the system. Roles are secondary: they are defined by the rules as positions that must be filled. Elements are tertiary: they are selected for the roles as their bearers. This ontological order (Rules $\to$ Roles $\to$ Elements) is known as the *generative order*—the order in which the structure *generates* itself. It will be analyzed in detail in “Asymmetry and the Generative Order.”

The abbreviation E/R/R is nonetheless kept for the generally accepted epistemic order, for practical reasons: it is with the elements that analysis begins. But in each particular case the structure *works* in the reverse direction: rules $\to$ roles $\to$ elements.

**Formal representation in `Distinction`.**  At the level of the simplest system, the act of distinction, the three aspects receive particular content:

- Elements: the positive and the negative sides (the fields `positive` and `negative` of the record `Distinction`).
- Roles: the position of “the singled-out” and the position of “the background against which it is singled out”—two positions occupied by the sides.
- Rules: exclusivity and exhaustiveness (the fields `exclusive` and `exhaustive`), which hold the act together precisely as a *distinction*.

This is the E/R/R structure of *one* particular system (the act of distinction). In § “Application to Distinction”–“Application to distinction_of” this representation will be analyzed formally.

### Minimality: Two Elements, Two Roles, Two Rules

**Structural content.**  In the simplest system, the act of distinction, each aspect of E/R/R is represented by exactly *two* constituents. This number is not arbitrary: it is *derived* from the already established structure of the record `Distinction` and cannot be changed without destroying the act of distinction itself.

**Derivation of two elements.**  In Chapter 2 ((see the corresponding chapter)) it was shown that the record `Distinction` has exactly four fields—`positive`, `negative`, `exclusive`, `exhaustive`—and that none of these fields can be removed without losing the very nature of distinction. The fields `positive` and `negative` have the type `Prop`: they express *what exactly* is distinguished. These are the Elements in the simplest act: two substantive poles between which the distinction is drawn.

A difference of *one* pole from itself is identity, not distinction. Therefore *one* element does not form an act of distinction. Consequently, the number of elements in the simplest act cannot be less than two—and it is exactly two, since the record `Distinction` has exactly two fields of type `Prop`.

**Derivation of two roles.**  Each of the two sides of the act of distinction occupies a definite position: one the position of *what is singled out*; the other the position of *the background against which it is singled out*. These positions are *functional roles* played by the fields `positive` and `negative`; they are not separate fields of the record.

Why precisely *two* roles? If there were one role, both sides would occupy one and the same position—that is, they would be functionally indistinguishable, and the act of distinction would collapse into identity. Consequently, the *minimum* number of roles in a system is two. And this minimum is *attained* in the act of distinction: exactly two positions, occupied by exactly two sides.

**Derivation of two rules.**  The fields `exclusive` and `exhaustive` express how exactly the sides relate to each other: `exclusive` asserts the incompatibility of the sides; `exhaustive`, their joint exhaustiveness. These are two *logically independent* rules: neither reduces to the other, and both are obligatory.

What would happen if one of them were removed? In (see the corresponding chapter) of Chapter 2 it was shown: without `exclusive` the sides can coincide, and the act of distinction collapses into identity; without `exhaustive` a “third way” appears between the sides, and the division becomes incomplete. Consequently, *fewer than two* rules are not enough to hold the structure of distinction together. And *more than two* rules are not needed in the simplest act: exclusivity and exhaustiveness together already fix all the laws of distinction—and this is precisely what the minimality of the record `Distinction`, proved in Chapter 2, consists in.

**Numerical fixing in the formalization.**  In Rocq the duality is fixed by numerical invariants:[^7] for every $D : `Distinction`$:

$$
`err_element_count`(D) = 2, \quad
  `err_role_count`(D) = 2, \quad
  `err_rule_count`(D) = 2.
$$

**Consequence: duality as a structural minimum.**  The derivation shows that the number “two” in the simplest system is a structural minimum below which distinction does not exist, not an arbitrary convention. One element: no difference; one role: no functional asymmetry; one rule: the structure collapses. Duality is the minimal nontrivial structure of determinacy.

**Consequence: complex systems as superstructures.**  Systems more complex than the simplest act of distinction contain more elements, roles, or rules. But this complexity is a *superstructure* over the basic dual structure, not an alternative to it. Additional elements are multiple bearers of roles; additional roles, multiple positions of significance; additional rules, a concretization of the general laws for the specifics of a particular system. The structural core—the duality of the act of distinction—remains: any complexity decomposes in the end into the work of distinctions “this—not that,” each of which has at least two sides.

### What a System Is

**Structural definition.**  With the derivation chain completed, we can fix the central concept of the Theory of Systems.

***A system is that which has an E/R/R structure.***

In other words, a system is any determinate whole in which the three aspects—Elements, Roles, Rules—are at work, in their minimal dual form or in superstructures over it.

This is *not a definition through something simpler*. It would be impossible to give a system an “external” definition, since any such definition would itself rest on the structure of that same system (it contains elements playing roles according to rules). The definition of a system is obtained *at the very end* of the derivation, as the final result of tracing the chain $A = \exists \to E/R/R$, not as a new postulate.

**Consequence: a system is neither an object nor a process taken separately.**  A system is not a “thing among things”: it is not localized as an object alongside other objects. Nor is it a process: processes are sequences of states of a system, unfolding in time or in logical order. A system is *the very mode of arrangement*, the meta-arrangement itself, which gives a place both to objects and to processes.

**Consequence: universality.**  Since E/R/R is obtained as the completion of the derivation chain begun with the very first principle, all determinate entities—from elementary particles to mathematical structures—have an E/R/R structure. They are systems *by the very fact that they are*; not to have an E/R/R structure would mean not to be determinate, not to exist as something particular.

With the formulation of E/R/R we obtain the basis for everything that follows: the analysis of particular systems (§ “Application to Distinction”–“Application to distinction_of”), of their well-formedness (“The Self-Application of E/R/R,” “Paradoxes as a Confusion of E/R/R Categories”), and of their place in the hierarchy (“The Hierarchy of Levels,” “The Meta-System: The Absolute”). Before passing to these cases, let us consider each of the three aspects separately in more detail.

## The Three Aspects in Detail

### The Order of Exposition

In “Three Aspects of a System” we fixed the distinction between the *epistemic* order—the abbreviation E/R/R, in which the aspects are listed from the outwardly observable (Elements) to the deep (Rules)—and the *ontological* order (the generative order), in which rules are primary, roles secondary, and elements tertiary.

The detailed unfolding of the three aspects proceeds in the *ontological* order: Rules $\to$ Roles $\to$ Elements. This is the order in which a system *unfolds*: first the rules are set, then the roles are defined under them, and only then are the elements selected.

### Rules: The Laws of Organization

**Structural content.**  Rules are *how* the interaction in a system is organized, the laws that hold it together as a system. Rules are the primary aspect: they set *what it means* to be in this system before any particular roles and elements appear in it.

**Connection with $L5$.**  Rules work *over* elements and roles: by $L5$, laws stand at a level above what they organize. This is the fundamental hierarchy: rules set the interaction, and elements and roles are subordinate to the rules. If rules stood at the same level as elements or roles, they would lose their organizing force.

**The two layers of rules.**  In any particular system *two layers* of rules are at work:

- *The universal layer*—the laws of logic $L1$–$L5$. They work *always and everywhere*: in any system, at any level of the hierarchy, for any configuration.
- *The concrete layer*—the rules specific to the given system. They *define the roles* (what positions there are in this system) and *set the selection of elements* (which bearers can occupy which positions).

A detailed analysis of the two layers is in “The Two Layers of Rules: The Universal and the Concrete.”

**The selection mechanism.**  Let us note in particular: the rules of the concrete layer may contain a *selection mechanism* for elements under roles—an automatic algorithm by which, from the available potential bearers, those are chosen that will occupy the corresponding positions. If such a mechanism exists, the actualization of the system is carried out *systemically*, without external intervention. If there is no mechanism, then by $L4$ an explicit action of an operator is required: an act of selection grounded in the structure of the system.[^8]

**Examples.**  In a group the universal layer of rules is $L1$–$L5$; the concrete layer is the group axioms (associativity, the existence of a neutral element, the existence of inverses). The selection of elements for the role “the inverse of a given element” in the additive group $\mathbb{Z}/n\mathbb{Z}$ is carried out automatically: the inverse of $a$ is $-a \bmod n$ (for a nonzero representative $a$ this is $n - a$; for zero, zero itself). In a formal grammar: $L1$–$L5$ plus the productions of the grammar. In a physical system: $L1$–$L5$ plus the equations of motion and the conservation laws.

**Consequence: rules set the possibility of a system.**  Before particular roles and elements appear in a system, the rules already set *what system is possible*. The very possibility of a system—its *potential*—is determined by the work of the rules. We shall return to this point in the discussion of Elements.

### Roles: The Significance of Positions

**Structural content.**  Roles are *what* the elements are significant *for*, what function they perform in the system. A role is a *position* that is set by the rules of the system and must be filled, not a property of an individual element. One and the same element can play different roles in different systems; one and the same role can be performed by different elements.

**Connection with $L4$.**  Each role in a system is grounded by the structure: this is the work of $L4$, the Law of Sufficient Reason. The distribution of roles is not arbitrary: it follows from the rules, which require precisely these roles and not others. Without such grounding the system would have no determinate structure: it would be unclear *why* it has these positions and not others.

**At least two roles.**  In the simplest act of distinction there are two roles: the position of what is singled out and the position of the background. This minimum, as was shown in “Minimality: Two Elements, Two Roles, Two Rules,” is structurally necessary: one role would mean the functional indistinguishability of the sides, and the act of distinction would collapse. Fewer than two roles: no distinction; more than two: a superstructure over the basic duality.

**Examples in different systems.**  In a group $G$ the roles are “neutral element,” “inverse of a given element,” and “result of the operation.” In a formal grammar: “terminal,” “nonterminal,” “start symbol.” In a physical system: “invariant,” “parameter,” “state variable.” In all cases there may be several roles, but their distribution is always grounded by the structure (by $L4$): one cannot arbitrarily appoint just anything as the neutral element of a group—it must be a particular element satisfying the equations that define this role.

**Consequence: roles as part of the potential of a system.**  Roles defined by the rules exist in a system *before* any particular selection of elements. They are structural positions that *can* be filled. Together with the rules, the roles form the *potential* of the system: its ontological structure, set prior to any actualization.

### Elements: The Actualization of Potential

**Structural content.**  Elements are *what* actually is in a system: the particular bearers occupying roles set in advance. Elements appear in a system as the result of *selection* for already defined roles; this is the concluding step in the unfolding of a system.

**Potential and actual existence.**  It follows from the exposition above that a system has *two modes of existence*:

***The main systemic criterion of existence is Rules and
Roles (the potential); Elements are actualization.***

In the *potential* mode the system is set by rules and roles; the elements may not yet be selected. In the *actual* mode the positions are filled by particular bearers. This distinction is essential: a system *is* even without filled positions—it is as a potential, as a structural possibility. Actualization is the passage from potential to a particular filling, not the coming-into-being of the system itself.

**Example.**  Consider the *parameterized scheme* $S_c$: “the set of natural numbers $n$ such that $n^2 < c$,” where $c$ is a parameter. The rules of the scheme are defined: the condition $n^2 < c$ sets the role “element of the set” through an explicit arithmetic requirement. For $c = 10$ the roles are filled by the elements $\{1, 2, 3\}$—if the naturals are counted from one[^9]—and the system $S_{10}$ is actualized by three bearers. For $c = 2$ there is a single element $\{1\}$, and the system $S_2$ is actualized minimally. For $c = 1$ the roles have no bearers: the system $S_1$ remains in the potential mode—the set is empty as an actual collection but *is* as a structurally defined possibility with an explicitly set criterion.

Here it is important to avoid an imprecision. It would be wrong to say that $S_{10}$, $S_2$, $S_1$ are “one and the same system with different fillings.” By the principle $P3$ (Intensional Identity, “: Intensional Identity”), the identity of a system is set by its *criterion*, and the criterion of $S_c$ includes the value of the parameter $c$. Different $c$ are different criteria, and hence *different systems* in the intensional sense. The precise formulation is this: there is one parameterized *scheme* $S_c$, and $S_{10}$, $S_2$, $S_1$ are different *instances* of this scheme—intensionally different, for their criteria differ. What they have in common is the scheme (the form of the criterion, the type of the role); what differs is the particular criterion and therefore the system itself. The distinction between the potential and the actual runs *within* each instance $S_c$: the rules and roles set its potential, the bearers its actualization.

**Connection with $L1$.**  Each actualized element in a system is identical to itself: this is the work of $L1$ applied to bearers. Without the identity of the elements, their stable identification in different contexts would be impossible. $L1$ works in Elements as the condition of the very possibility of treating actual bearers as determinate.

**Multiplicity of elements.**  In the simplest act of distinction there are two elements (the positive and the negative sides). In complex systems there are more elements: a group has bearer-elements on which the group operation is defined; a formal language has symbol-elements of the alphabet; the natural numbers have the elements $1, 2, 3, …$. In all cases the elements are the actual bearers of roles, existing *in addition* to the structural potential set by the rules and roles.

### The Joint Work of the Three Aspects

Although the three aspects are distinguishable—we can speak separately of Rules, Roles, Elements—they are *inseparable* in the work of a system. Elements *already* play roles (defined by the rules); roles are *already* filled by elements (chosen according to the rules); rules *already* work on particular elements and roles. The three aspects are three inseparable sides of one arrangement, as was fixed in “Three Aspects of a System.”

**Connection with the laws.**  The correspondence between the three aspects and the laws of logic:

| **Aspect** | **Question** | **Law** |
|---|---|---|
| Rules | How is it organized? | $L5$ (Order) |
| Roles | What is it significant for? | $L4$ (Sufficient Reason) |
| Elements | What is actual? | $L1$ (Identity) |

Here $L2$ (Non-Contradiction) and $L3$ (Excluded Middle) work *in all three* aspects: rules are applicable without contradiction; roles are distributed without contradiction; elements are non-contradictory in themselves and mutually exclusive. These two laws are not tied to one aspect: they work as structural conditions of the coherence of all three.

**Consequence: the unity of E/R/R analysis.**  In analyzing any system the three aspects come to light together. Although rules are ontologically primary, it is epistemically convenient to begin with the elements (which are observable) and move toward the roles and the rules. A systematic E/R/R analysis—passing through all three questions in sequence—gives a full description of the ontological structure of a system regardless of the order in which these questions are asked.

With the three aspects unfolded in their connection with the laws, we obtain the basis for the subsequent analysis of subtler structural features: the two layers of rules, the asymmetry of the generative order, the hierarchy of levels. We pass to the two layers of rules in the next section.

## The Two Layers of Rules: The Universal and the Concrete

In “Rules: The Laws of Organization” it was briefly indicated that Rules in any system work *in two layers*: the universal layer of the laws $L1$–$L5$ and the concrete layer of the rules of the given system. This two-layered arrangement is a *structural* one, without which rules could not work in any system; it is not a methodological convenience for classification.

***The universal layer of Rules—the laws $L1$–$L5$—
works always and everywhere; the concrete layer defines the roles in the given
system and sets the selection of elements for these roles.***

### The Universal Layer: The Laws $L1$–$L5$

**Structural content.**  The universal layer of Rules is the laws of logic $L1$–$L5$. They are *not tied* to a particular system: they work in any system, at any level of the hierarchy, under any configuration of elements and roles. These are the conditions of the very possibility of systemhood, obtained in the derivation chain and fixed in Chapter 3 as formal theorems of Rocq.

**What the universal layer provides.**  This layer holds the *structural coherence* of any system—that without which a system could not be a system:

- $L1$ provides that the elements are stably identifiable.
- $L2$ provides that one and the same thing cannot at once be and not be in the system (in one and the same respect).
- $L3$ provides that between “is in the system” and “is not in the system” there is no third.
- $L4$ provides that every assertion about the system requires a ground—a structural one, not an arbitrary one.
- $L5$ provides that the system has a hierarchical arrangement: rules above roles, roles above elements.

**Universality as a structural property.**  The universal layer works *before* and *independently of* whatever particular system is under consideration. When we define a group, a grammar, or a physical system, we do not *add* $L1$–$L5$ as part of the definition: these laws are *already at work* in any attempt at such a definition. The definition itself is possible only through their work.

### The Concrete Layer: The Rules of a Given System

**Structural content.**  The concrete layer of Rules is the rules specific to the given system. Unlike the universal layer, they *characterize precisely this* system, distinguishing it from others. The concrete layer sets two things:

- *The definition of roles*—what positions there are in this particular system and what functions they perform.
- *The selection of elements*—which potential bearers can occupy which positions, and (where there is one) how this selection is carried out.

These two aspects are inseparable: the rules that define the roles implicitly set the type of objects that can play these roles as well. For example, the rule “an even natural number is an $n$ such that $n = 2k$ for some $k \in \mathbb{N}$” at once defines the role “to be an even number” and indicates which elements can play it (only those representable in the stated form, that is, $2, 4, 6, 8, …$).

**Formalization in Rocq.**  In the ToS-Coq repository the two layers are fixed through the structure of the type `System`, in which the universal requirements and the concrete rules of a system are joined.[^10] The type `System L` is parameterized by the level $L$ (the universal layer works through the hierarchy of levels) and contains the field `sys_criterion` (the concrete criterion specific to the given system). The universal layer shows itself as requirements on `sys_criterion` (its level must be strictly below the level of the system, by $P1$); the concrete layer, as the very content of the criterion.

**Consequence: each system has its own profile of the concrete
layer.**  A group, a grammar, a physical system—each has its own set of concrete rules. The universal layer is the same for all ($L1$–$L5$ work in the same way); the concrete layers differ. It is the concrete layer that makes a system *this very* system and not another.

### Selection of Elements: Automatic and Operator-Driven

**Two kinds of selection.**  In “Rules: The Laws of Organization” a distinction was introduced between two kinds of selection of elements for roles. Let us unfold it in more detail.

*Automatic selection.* The concrete layer of rules contains an algorithmic mechanism: for any role in the system it is specified how to choose the element that will occupy it. In this case the actualization of the system takes place without external intervention; it is enough to apply the algorithm. Example: in the additive group $\mathbb{Z}/n\mathbb{Z}$ the role “the inverse of $a$” is automatically filled by the element $-a \bmod n$—the mechanism is given by a formula.

*Operator-driven selection.* The concrete layer contains no algorithmic mechanism; the roles are defined, but *how exactly* to choose the bearer is not specified. By $L4$ an explicit action of an operator is required, grounded in the structure of the system.[^11] Example: “choose a representative of an equivalence class” when the relation is given in general and the rules themselves specify no method of canonical choice—the role is defined, but without an additional specification the operator must make the choice explicitly.

**Connection with potential and actualization.**  The distinction between the two kinds of selection has a direct consequence for the modes of existence of a system (“Elements: The Actualization of Potential”):

- If the selection mechanism is *automatic*, the passage from the potential to the actual mode takes place *systemically*: once the rules are defined, the elements are obtained.
- If the mechanism is *operator-driven*, the passage requires an act of the operator. Without this act the system remains in the potential mode, even if all its rules and roles are defined.

### The Joint Work of the Two Layers

**Hierarchical structure.**  The universal and the concrete layers of rules are *hierarchical*, not “parallel.” The universal layer works *over* the concrete one: the laws $L1$–$L5$ are the conditions under which concrete rules can be formulated and applied at all. Concrete rules cannot contradict the universal ones: they work *within the bounds* of what the universal ones admit.

**Examples of the two layers.**
*The additive group $\mathbb{Z}/n\mathbb{Z}$.* Universal layer: $L1$–$L5$. Concrete layer: the associativity of addition modulo $n$, the existence of a neutral element ($0 \bmod n$), the existence of an inverse for each element (the inverse of $a$ is $-a \bmod n$). Selection: automatic (the formulas are explicit). Let us note that everything said concerns the *additive* structure; in the multiplicative group of units $(\mathbb{Z}/n\mathbb{Z})^{\times}$ the neutral element is $1$, and an inverse exists only for the invertible classes, not for every element of $\mathbb{Z}/n\mathbb{Z}$.

*A formal grammar.* Universal layer: $L1$–$L5$. Concrete layer: the alphabet of terminals, the alphabet of nonterminals, the start symbol, the productions. Selection: automatic (for each string one can check algorithmically whether it is derivable).

*The set of even natural numbers.* Universal layer: $L1$–$L5$. Concrete layer: the rule “$n$ is even if and only if $n = 2k$ for some $k \in \mathbb{N}$.” Selection: automatic (an explicit parity test for each natural number).

In each example the universal layer is the same; the concrete layers differ and characterize precisely this system. The two-layered arrangement is the common structure; the concrete content is what makes a system unique.

**Consequence: systems as two-layered constructions.**  Any particular system is $L1$–$L5$ (the universal layer) plus its specific rules (the concrete layer), which together define the roles and set the selection of elements. The universal layer provides structural coherence; the concrete one, specific content. Without the universal layer a system could not be a system; without the concrete one it would not be *this* system.

{
With the two layers of Rules we complete the analysis of the ontological arrangement of rules. The next section unfolds the asymmetry of the relations among the three aspects of E/R/R—the generative order by which rules set roles, and roles set elements.
}

## Asymmetry and the Generative Order

In “Three Aspects of a System” and “The Order of Exposition” two orders were distinguished: the epistemic (Elements $\to$ Roles $\to$ Rules) and the ontological (Rules $\to$ Roles $\to$ Elements). The present section unfolds the ontological order—the generative order—as a structural asymmetry of the relations among the three aspects of E/R/R.

***The generative order: Rules set Roles; Roles constrain
Elements. There is no reverse asymmetry: Elements do not define Roles,
and Roles do not set Rules.***

### Three Asymmetric Relations

**Structural content.**  Three relations are at work among the three aspects of E/R/R, and each of them is *asymmetric*: one side determines the other, but not conversely.

**Rules $\to$ Roles: the rules set the roles.**  The rules of a system determine what positions there are in it. From the rules it follows which roles are required: the rule “a neutral element exists” sets the role “neutral element”; the rule “there exists an inverse for each element” sets the role “inverse of a given element.” Without rules the roles would be arbitrary; with rules they receive particular content.

*The converse is false.* Roles do not set rules. One can imagine a “neutral element” outside the context of a group—but this will no longer be a role in the sense of ToS, since there are no rules grounding this role. Roles exist only *under* rules; the reverse direction does not work.

**Roles $\to$ Elements: the roles constrain the elements.**  The roles defined by the rules constrain the range of elements that can play them. Not every object can occupy every position: only those that satisfy the conditions of the role. The rule “neutral element,” together with the role, admits only a particular element as its bearer; in the group $\mathbb{Z}_n$ this is the number $1$ under multiplication or $n$ under addition (with indexing from one).

*The converse is false.* Elements do not define roles. A particular element—for example, the number $2$—can play different roles in different systems: in one group as a generator, in another as the neutral element, in a third as an arbitrary bearer. The element itself does not *set* the role it plays; the role is set by the rules and *prescribed* to the element.

**The third relation: Rules $\to$ Elements (through Roles).**  The direct relation from rules to elements is mediated by roles: rules by themselves do not determine particular elements; they determine *roles*, which are then filled by elements. This is the *transitive* aspect of the generative order: rules determine roles, roles determine elements, and therefore rules (through roles) determine elements.

### The Generative Order: The Ontological Order of a System

**Structural content.**  Together, the three asymmetric relations give a single order of the unfolding of a system:

$$
\text{Rules} \;\to\; \text{Roles} \;\to\; \text{Elements}.
$$

This is the *generative order*, the ontological order in which a system *unfolds*: first the rules are set, then the roles are defined under them, and only then are the elements selected.

**Why precisely this order.**  The generative order is not arbitrary: it follows from the work of the laws of logic at different levels:

- $L5$ (the Law of Order) sets the hierarchy: rules stand at a level above roles, and roles at a level above elements.
- $L4$ (the Law of Sufficient Reason) requires that each role be grounded—the rules serve as the ground; accordingly, roles can be defined only *after* the rules.
- $L1$ (the Law of Identity) provides the stability of elements as bearers of roles—but this stability is possible only when the roles for which the elements are bearers have already been defined.

The generative order is a structural consequence of the work of $L1$, $L4$, $L5$ applied to the aspects of a system.

**Consequence: reverse unfolding is impossible.**  A system cannot be “unfolded in the reverse direction”—starting from the elements and deriving the roles and rules from them. Particular elements by themselves do not determine what system they are in: the number $2$ plays one role in one group, another in another, a third in a third. To understand what role a given element plays, one must first know which *rules* are at work in the given system and which *roles* they define.

### The Connection with Potential and Actualization

**Structural content.**  The generative order and the distinction between the *potential/actual* modes of a system (“Elements: The Actualization of Potential”) are two sides of one structural picture:

- The *potential* of a system is what is set by the rules and roles. These are the first two links of the generative order: Rules $\to$ Roles.
- The *actualization* of a system is the selection of elements for already defined roles. This is the concluding link: Roles $\to$ Elements.

**The generative order as the unfolding of potential into the actual.**  When we say that a system *unfolds* in the order Rules $\to$ Roles $\to$ Elements, we mean a structural relation rather than a temporal process: *potential precedes actualization*, and actualization *follows* from potential, not conversely. Particular elements may be selected (or not—if the roles have no bearers), but the very possibility of selection presupposes rules and roles set in advance.

**Consequence: the act of selection as the closure of the generative order.**  The selection of elements for roles is the concluding moment of the unfolding. If the rules contain a selection mechanism, the closure takes place automatically; if there is no mechanism, an act of the operator is required (“Selection of Elements: Automatic and Operator-Driven”). In both cases this is the *last* step of the generative order; before it the system exists as potential.

### The Epistemic Order as the Reverse

**Structural content.**  The generative order is the order in which a system *is* (unfolds ontologically). The epistemic order is the order in which a system *is known* (recognized by us in analysis). These two orders are *the reverse* of each other:

| **Generative order (ontologically)** | **Epistemic order** |
|---|---|
| Rules set Roles | Elements are recognized |
| Roles constrain Elements | Roles are brought to light from Elements |
| Elements actualize the system | Rules are inferred from Roles |

{

**Why the two orders are reverse.**  The unfolding of a system goes from the top down (Rules $\to$ Elements), because rules are primary. The recognition of a system goes from the bottom up (Elements $\to$ Rules), because the observer first sees the elements: they are directly accessible in experience. The same phenomenon occurs in the natural sciences: the structure of the atom *in reality* unfolds from the laws of physics but *is known* starting from observable phenomena (spectra, scattering).
}

**Consequence: the consistency of the abbreviation E/R/R.**  The abbreviation E/R/R is epistemic (Elements first, Rules last), which agrees with the practice of analysis: in analyzing an unfamiliar system it is natural to begin with the elements. This is a *practical* convention, not an ontological claim. Each time we carry out an E/R/R analysis, we move along the epistemic order—but we *discover* a system unfolded in the generative order.

With the generative order unfolded, we obtain the basis for the analysis of multilevel systems—those in which the elements of one level are themselves systems of a lower level. We pass to the hierarchy of levels in the next section.

## The Hierarchy of Levels

The preceding sections showed that E/R/R are the three aspects of any system. In “Asymmetry and the Generative Order” the unfolding of a system was traced along the generative order. The present section unfolds the *vertical* structure: the hierarchy of levels in which systems of different complexity are arranged.

***The elements of a system of level $n+1$ are themselves systems of level
$n$.***

### The Principle of Hierarchy

**Structural content.**  Systems of different complexity form a *hierarchy* in which a more complex system has as its elements systems located at more fundamental levels; they are not arranged “side by side” as equals. It is often convenient to consider the nearest case—when the elements of a system of level $n+1$ are systems of level $n$—and below we shall use it as the illustrative one; but the formal idea is *broader*: it is only required that the elements be located *lower in level*, not necessarily exactly one step lower. This is the law of the vertical structure of E/R/R.

**Derivation from $L5$ and $P1$.**  The hierarchy is a *consequence* of what has already been derived, not an additional postulate:

- By $L5$ (the Law of Order), every operation stands above its operand: the rules of a system are above its elements and roles.
- By $P1$ (Hierarchy, “: Hierarchy”), the level of the organized is strictly below the level of the organizer: $\text{Level}(\text{organized}) < \text{Level}(\text{organizer})$.

Applying these two principles: the elements of a given system ($\text{Level} = n$) are themselves organized—that is, they have their own E/R/R structure. Hence they too are systems. Their own level is *strictly below* the level of the organizer: they are located beneath it in the order $\ll$. In the nearest, illustrative case this is the level $n-1$; but formally only the relation “lower in level” is required, not exactly one step down. The hierarchy of levels is a structural consequence of the joint work of $L5$ and $P1$.

**Consequence: every system is multilevel.**  From the principle of hierarchy it follows that every nontrivial system[^12] has *several* levels, not one. At the very top the rules of the system are at work; at the next level, the roles and their bearers (which are themselves systems); at the next, the elements of these bearers; and so on downward.

### The Connection with the Type `Level`

**Formalization in Rocq.**  In Chapter 3 ((see the corresponding chapter)) the type `Level` was briefly introduced, with the strict order operator $\ll$ and the depth function `level_depth`.[^13] The hierarchy of levels of E/R/R systems is formalized through this type:

- Each system $S$ is located at a definite level: $\text{Level}(S) \in `Level`$.
- The elements of a system $S$ are located at a strictly lower level: $\text{Level}(e) \ll \text{Level}(S)$ for every element $e \in S$.
- Each particular level has a finite depth relative to the ground; this is what the theorem `L5_no_infinite_descent` from Chapter 3 fixes. It is natural to interpret this fact as the absence of non-well-founded descent; but a theorem on the impossibility of an infinite descending chain of levels would have to be formulated separately—the theorem `L5_no_infinite_descent` proves the weaker statement that each level has finite depth.

**Consequence: the levels are numbered.**  Since each level has finite depth, a natural number can be assigned to it: this depth, counted from the ground. This gives a numbering of the levels: $L_1$ (the ground level), $L_2$, $L_3$, and so on, without bound upward.

### Multilevel Systems: Examples

Let us consider several examples in which the hierarchy of levels shows itself explicitly. First, an important caveat about terms. In the examples below we speak of *domain-relative tiers*: of the first, second, third tier of a *particular model* (arithmetical, physical, linguistic). These domain tiers *should not* be identified with the formal constructors of the type `Level` from `TheoryOfSystems_Core_ERR.v`, where $L_1$ denotes *Logic / the ground*, not “the first tier of some subject domain,” and $L_2, L_3, …$ denote the levels stacked over it. A domain tier is an explanatory notion relative to the chosen model; the formal `Level` is a fixed structure with $L_1 = \text{Logic}$. To keep them apart, in the examples we write “the first domain tier,” “the second domain tier,” and so on, and reserve the notation $L_1, L_2$ for the formal `Level`.

**The natural numbers and their sets.**
*The first domain tier of the arithmetical model:* the natural numbers $1, 2, 3, …$. Each natural number is a system of the simplest type (a minimal act of distinction fixing “this number” and not another).[^14]
*The second domain tier:* sets of natural numbers. For example, the set of even numbers $\{2, 4, 6, …\}$ or the set of primes $\{2, 3, 5, 7, …\}$—systems whose elements are natural numbers of the first tier.
*The third domain tier:* functions acting on sets of natural numbers (addition, multiplication, the operations of number theory); their elements are systems of the second tier (sets).

**The physical world.**
*The first domain tier of the physical model:* elementary particles (the electron, quarks).
*The second domain tier:* atoms—systems whose elements are elementary particles.
*The third domain tier:* molecules—systems whose elements are atoms.
*The fourth domain tier:* macroscopic objects—systems whose elements are molecules.

**A formal language.**
*The first domain tier of the linguistic model:* the symbols of the alphabet.
*The second domain tier:* words—systems whose elements are symbols.
*The third domain tier:* expressions—systems whose elements are words.
*The fourth domain tier:* formal texts—systems whose elements are expressions.

**The common structure.**  In each example one and the same principle holds: systems of a higher tier have as elements systems of a more fundamental tier. Only the particular rules and the particular elements differ; the *vertical structure* is one and the same. This is a manifestation of the ontological character of the hierarchy: it works in *all* subject domains, not in one. Let us stress once more: the hierarchy of domain tiers in each model is an *application* of the structure of order, while the formal type `Level` with $L_1 = \text{Logic}$ is the structure used in these applications; “the first tier of arithmetic” should not be identified with the formal $L_1$.

### Hierarchy as the Unfolding of E/R/R

**Structural content.**  Each level of the hierarchy is an unfolding of E/R/R *anew*, but now at a higher level. The rules, roles, and elements of a system $L_2$ themselves have their own E/R/R structure, but on the scale of $L_2$. Likewise for $L_3$, $L_4$, and further.

**The universal layer works at all levels.**  The laws $L1$–$L5$—the universal layer of rules (“The Universal Layer: The Laws –”)—work in the same way at every level. Only the concrete layer differs: at $L_2$ the rules of set theory are at work, at $L_3$ those of the theory of functions, at $L_4$ those of higher theories. The universal laws are the common structure; the concrete rules are what characterizes precisely the given level.

**The lowest level as a boundary.**  By the theorem `L5_no_infinite_descent` ((see the corresponding chapter) of Chapter 3), there is no infinite descent: the hierarchy has a *lower bound*—the base level $L_1$. What is at $L_1$? In each particular hierarchy, its own elements: the natural numbers in the arithmetical hierarchy, elementary particles in the physical one, the symbols of the alphabet in the formal-linguistic one. But in all cases $L_1$ is the level of elements *not further decomposable* in the given hierarchy: the limit below which the given hierarchy does not go.

**Consequence: the limiting act of distinction.**  At the very lowest level of the hierarchy the simplest act of distinction is at work: the record `Distinction`, analyzed in Chapter 2. The elements of $L_1$ are *determinate* objects (distinct from what is not themselves), and this determinacy is provided by the work of $L1$–$L5$ in its simplest form. The hierarchy of levels begins with the act of distinction and unfolds upward through the repeated application of E/R/R at each next level.

**Consequence: the upper bound and the meta-system.**  What is at the top of the hierarchy? The hierarchy of levels has no *internal* upper bound: one can always build a system of a higher level whose elements are systems of the preceding one. But within this unboundedness there is a *limiting* structure: the *meta-system*, formed by the universal laws and by the very fact of existence. We pass to this meta-system—the Absolute—in the next section.

## The Meta-System: The Absolute

In “Hierarchy as the Unfolding of E/R/R” it was noted that the hierarchy of levels of systems has no internal upper bound but has a *limiting* structure: the meta-system, formed by the universal laws and by the very fact of existence. This meta-system is the Absolute, analyzed in the metaphysics of Volume I. The present section shows that the Absolute has an E/R/R structure—and thereby closes the ontological chain between the metaphysical arrangement and the formal work of the present volume.

Before unfolding this analysis, its status must be stated precisely. Nothing said below about the Absolute *is* a theorem of the current Rocq formalization. The Coq files of the repository contain no formal object `Absolute`, no Logic and Source as elements of some meta-system, and no theorem of the form “$E/R/R \to \text{Absolute}$.” The formalization analyzed in the preceding sections gives E/R/R as the structure of *systems*; the present section is a *metaphysical application* of this structure—the application of E/R/R to the Absolute, which connects the present volume with the metaphysics of Volume I. This step is substantive, not machine-checked. Therefore, when it was said above that each link of the derivation chain is derived from the preceding ones, this does *not* apply to the link “E/R/R $\to$ Absolute”: it belongs to the metaphysical interpretation, not to the current formal corpus. The reader must keep this distinction in mind throughout the section.

### What “Meta-System” Means

**Structural content.**  The Absolute is not “a system among systems”: its place is not in the hierarchy $L_1, L_2, L_3, …$ alongside other levels. The Absolute is a *meta*-arrangement: that which sets the very possibility of the hierarchy of levels before any particular level appears in it. In this it differs from any system within the hierarchy: an inner system is one of many; the meta-system is the condition of the very possibility of the existence of any of them.

***The Absolute is the meta-system formed by Logic and
the Source as its elements.***

**The Absolute is not an entity.**  This clarification is of fundamental importance; without it all the further work would be misunderstood. The Absolute is not an *entity*—not a separate thing existing alongside other things. It is not a “something” one can point a finger at or of which one can say “here it is.” The Absolute is the *meta-arrangement of existence*: that which makes possible the existence of anything at all. To say “the Absolute is” in the ordinary sense of “here it stands before me” is to commit a category mistake: to confuse an entity with the meta-level.

**What “formed” means.**  The Absolute does not *consist of* two entities (Logic and the Source); that would be a reading of the Absolute as a “thing with parts.” Rather, the Absolute is *formed*: its structure *arises as a result* of Logic and the Source working with each other in definite roles. The meta-system is *the very arrangement* of how Logic and the Source together make up the possibility of existence, neither an object nor a process taken separately.

### The E/R/R Structure of the Absolute

**Structural content.**  The Absolute as a meta-system has an E/R/R structure, analyzed as follows:

| **E/R/R aspect** | **In the Absolute** |
|---|---|
| Elements | Logic, the Source |
| Roles | Structure, Filling |
| Rules | $L1$–$L5$ + rules for the distribution of roles |

**The Elements of the Absolute: Logic and the Source.**  At the level of the Elements of the Absolute exactly two bearers are at work:

*Logic*—the structural, organizing principle; that by which the laws $L1$–$L5$ work.
*The Source*—the filling toward which the action of Logic is directed; that which Logic organizes.

**The Roles of the Absolute: Structure and Filling.**  Logic and the Source do not merely “exist”: they occupy definite positions in the meta-arrangement:

*Structure*—a role that must be performed. In the Absolute this role is played by Logic. Without something playing the role of structure, existence would be amorphous, not determinate.
*Filling*—a role that likewise must be performed. In the Absolute it is played by the Source. Without filling, structure would be an empty form with no content.

**Two obligatory roles.**  The minimal duality of E/R/R (“Minimality: Two Elements, Two Roles, Two Rules”) shows itself in the Absolute through two obligatory roles. This is not an arbitrary distribution: *both* roles are necessary by $L4$ (the Law of Sufficient Reason) for the very fact of existence. Without structure there is no form; without filling, no content. Both roles are necessary conditions of existence.[^15]

**The Rules of the Absolute: the universal and the concrete.**  At the level of the Rules of the Absolute two layers are at work, as in any system (“The Two Layers of Rules: The Universal and the Concrete”):

*The universal layer*—the laws $L1$–$L5$. They work in the Absolute as in any system, holding it together as a *determinate* meta-arrangement.
*The concrete layer*—the rules that fix the distribution of roles. They set that the roles of the Absolute are Structure and Filling (and not any others), and that Logic plays the role of Structure and the Source the role of Filling.

**The peculiarity of the meta-system: an exception to the general rule of
selection.**  In ordinary systems elements are *selected* for roles defined in advance—either automatically (if a mechanism is given) or through the action of an operator (“Selection of Elements: Automatic and Operator-Driven”). In the Absolute there is no such selection. Logic and the Source are not *selected* for the roles of Structure and Filling: they are *already given* as primordial and *form* the meta-system by working with each other in these roles.

This is a structural exception, in agreement with the primordial status of the Absolute (“Primordial Status”). In an ordinary system the generative order (Rules $\to$ Roles $\to$ Elements) unfolds sequentially: the rules are defined, then the roles under them, and the elements are selected for the roles. In the meta-system all three aspects are given *at once*: there is no “moment before selection,” since there is nothing that would be “before” the meta-system. Logic, the Source, their roles, and the rules establishing the distribution of roles are a single meta-arrangement, given as the condition of existence as such.

**Consequence: the laws of logic work at the level of the Rules of the Absolute.**  It follows from the E/R/R analysis of the Absolute that the laws $L1$–$L5$ stand *at the level of the Rules* of the meta-arrangement, not *within* the Absolute as part of its content. This agrees with the position already fixed ((see the corresponding chapter)): the laws are ontologically primary—they work at the meta-level as the conditions of the very possibility of any existence.

### Primordial Status

**Structural content.**  The Absolute does not “appear” at some moment: it does not arise as the result of any process and is not created by an act or a cause. The Absolute is *primordial*: that which always is, as the *condition* of the very possibility of existence and not as a result.

**Derivation from $L4$.**  The Absolute is primordial for the following structural reason: the very fact of existence requires a meta-arrangement in which there are Structure and Filling. By $L4$ this requirement is structurally necessary, not arbitrary: without the two obligatory roles determinate existence would be impossible. Consequently, the meta-arrangement realizing these roles (that is, the Absolute) cannot “appear” later than any existence: it is the *condition* of existence as such.

**Consequence: the question “where does the Absolute come from?” is impossible.**  To ask where the Absolute came from, or what was “before” the Absolute, is to commit a category mistake. The question “from where?” presupposes the existence of that relative to which it is posed; but the Absolute is the very *condition* of such existence. There is no “before the Absolute,” because there is nothing relative to which this “before” could be determined.

**A remark on the act of Light.**  The metaphysics of Volume I fixes a *first event*: the act of Light, in which Logic for the first time actualizes the witnessing property of the Source. This event belongs to the unfolding of particular content within the Absolute, not to the coming-into-being of the meta-system itself. The act of Light is not “the moment of the appearance of the Absolute”; it is the *first application* of the rules of the Absolute within it. In the present volume the act of Light is not relevant: it belongs to the substantive metaphysics of Volume I; here we are interested only in the *structure* of the meta-system.

### Closing the Ontological Chain

**Structural content.**  With the introduction of the Absolute as the meta-system, the ontological chain begun in the first chapters of the present volume closes:

$$
A = \exists \;\to\; \text{Distinction} \;\to\;
  L1\text{–}L5 \;\to\; P1\text{–}P4 \;\to\; E/R/R
  \;\to\; \text{Absolute}.
$$

Each link of the chain is a structural condition derived from the preceding ones. The concluding link is the Absolute as the meta-system realizing the E/R/R structure at the meta-level.

**The connection between Volume I and the present volume.**  In Volume I the Absolute is analyzed from the standpoint of metaphysics: as the original meta-arrangement that makes any existence possible. In the present volume the Absolute appears as the *limiting* structure of E/R/R: a meta-system to which the same categories Elements, Roles, Rules apply as to ordinary systems, but with its primordial status taken into account—the selection of elements for roles, which works in ordinary systems, does not operate in the meta-system: Logic and the Source are given at once with their roles. These are not two different Absolutes: this is one structure, analyzed from two sides—the metaphysical and the formal.

**Consequence: the formal apparatus of E/R/R is universal.**  From the work of E/R/R at the meta-level (in the Absolute) and at each particular level ($L_1, L_2, L_3, …$) it follows that the E/R/R structure is a *universal* ontological structure, not a limited instrument applicable only to a certain class of systems. It works wherever determinate existence is at work—from the simplest act of distinction to the meta-system of existence as such. In the meta-system, moreover, the generative order is realized in a *limiting* form: as the simultaneous givenness of all three aspects rather than as a sequence of unfolding.

**Consequence: ontological primacy is confirmed.**  The ontological primacy of the laws $L1$–$L5$, fixed in Chapter 3, receives further confirmation: these laws work at the level of the Rules of the meta-system itself, not *within* any particular system. They are already there in the very structure of the meta-arrangement; they are not “introduced” into the formal theory. Their derivation in Rocq as theorems (Chapter 3) is a methodological tracing, not an ontological ground.

With the analysis of the Absolute we obtain a full picture of the ontological structure of E/R/R: from the simplest act of distinction, through the hierarchy of levels, to the meta-system. In the next section we shall check the tenability of the E/R/R structure itself through its *self-application*: we shall analyze the structure of E/R/R as a system by means of its own apparatus.

## The Self-Application of E/R/R

In the preceding sections the E/R/R structure was analyzed as the ontology of any system—from the simplest act of distinction through the hierarchy of levels to the meta-system of the Absolute. A natural question of verification arises: is the E/R/R structure *itself* well-formed as a system? In other words, if we apply an E/R/R analysis to E/R/R as a system, shall we obtain a consistent result, or will structural contradictions arise?

This question is a test of the *tenability* of the structure. There is a parallel with the work of Chapter 3: in (see the corresponding chapter) it was shown that $L4$ is *self-grounded* in the formal system of Rocq—the Law of Sufficient Reason grounds itself. An analogous check is required for E/R/R: if the structure is internally contradictory under self-application, it is unfit to be the universal ontology of systems.

### Setting the Problem

**Structural content.**  To apply E/R/R to E/R/R is to consider the E/R/R structure itself as a system and carry out its E/R/R analysis. Concretely: what *Elements* are there in the E/R/R structure itself? What *Roles* do they play? What *Rules* are at work?

**The difference in principle from the Absolute.**  In “The Meta-System: The Absolute” the Absolute was analyzed as a *meta-system*, with a peculiarity: its elements are given as primordial rather than selected for roles. E/R/R is not the Absolute. It is an *ontological structure*, traceable in any system (the Absolute included), but not itself a meta-system. Under self-application E/R/R works *in the ordinary mode*—with the selection of elements for roles, as in any system at a level of the hierarchy.

**Remark: the self-application is formalized.**  { This self-application is now fixed by machine as well. In the file `PrinciplesToERR.v` the E/R/R triad is written as an object `ERRSystem` (`err_meta_system`), and the theorem `err_self_well_formed` proves that it passes that very criterion of well-formedness from `ERRWellFormedness.v`[^16]: E/R/R satisfies its own criterion. What matters is precisely how: the theorem `self_application_not_self_membership` separates two senses of “E/R/R is applied to itself.” This is *self-application* (stratified self-description, one level down), *not* self-membership ($x \in x$, under which $\mathrm{level}(S) <
\mathrm{level}(S)$), which $P1$ rules out; and therefore it is $P1$-*compatible*, not an exception to it. The self-consistency of E/R/R is proved by a separate Rocq theorem, without axioms; the substantive analysis below unfolds what this theorem fixes.}

### E/R/R Applied to E/R/R: The Analysis

**Elements.**  In the E/R/R structure itself there are three distinguishable aspects: Elements, Roles, Rules. These three aspects are themselves the Elements in the E/R/R analysis of the E/R/R structure. That is, at the level of the Elements of the self-application we have:

- The element $E$: the category “Elements” (as an aspect of the structure).
- The element $R_1$: the category “Roles” (as an aspect).
- The element $R_2$: the category “Rules” (as an aspect).

Each of these three is determinate and distinguishable from the other two. By $L1$, each category is identical to itself: Elements are precisely Elements and nothing else; likewise for Roles and Rules.

**Roles.**  At the level of the Roles of the self-application, the functions that the three categories play in the system are at work. Each category *performs* a definite function:

- The category Elements plays the role of “bearer of the substrate of the system”: that through which *there is something* in the system.
- The category Roles plays the role of “bearer of functional positions”: that through which the elements receive significance.
- The category Rules plays the role of “bearer of the organizing laws”: that through which the system is held together as a system.

By $L4$, each assignment of a role is grounded: the category Elements plays the role of the substrate *because* any system requires a substrate, and it is precisely the category “what there is” that takes on this function; likewise for Roles and Rules.

**Rules.**  At the level of the Rules of the self-application two layers are at work (“The Two Layers of Rules: The Universal and the Concrete”):

*The universal layer*—the laws $L1$–$L5$, which work here too, as in any system.
*The concrete layer*—the rules of the E/R/R structure itself:

- The rule “three categories—exactly three, no more and no fewer” (by the minimality of E/R/R, “Minimality: Two Elements, Two Roles, Two Rules”).
- The rule “the categories are distinguishable from one another” (hence a confusion of E/R/R categories is inadmissible—which is unfolded in “Paradoxes as a Confusion of E/R/R Categories”).
- The rule “they work in the generative order: Rules set Roles, Roles constrain Elements” (“Asymmetry and the Generative Order”).

**A remark on the selection of elements.**  In the self-application the selection of elements for roles works in a *limiting* form: *the categories* of E/R/R *themselves* play definite roles. This is the *only possible* distribution of roles, not “selection from an arbitrary set of candidates”: the category “Elements” cannot play the role of “bearer of the organizing laws,” since organization is a function of Rules, not of Elements. The distribution of roles in the self-application is set by the structure itself.

### Well-Formedness Check

**The criterion of well-formedness.**  The file `ERRWellFormedness.v` (in detail, in “Paradoxes as a Confusion of E/R/R Categories”) fixes the criterion: a system is *well-formed* if each of its components belongs to exactly one E/R/R category and there is no *self-reference* through the categories.[^17]

**The check for E/R/R itself.**  Let us apply the criterion to the self-application of E/R/R:

*Unambiguity of categories.* Each of the three categories—Elements, Roles, Rules—belongs to exactly one E/R/R category in the self-application (as an Element in our analysis). Unambiguity holds.

*Absence of self-reference.* The category Rules does not act as an element of itself; the category Elements does not act as a rule for itself; the category Roles does not act as an element of itself. In substance this agrees with $P1$ (Hierarchy): no self-relation across levels arises. No self-referential relation through the categories is found in this analysis.

**Consequence: the self-application reveals no violation.**  Let us formulate the conclusion cautiously, in accordance with the status of the analysis. In the current version of ToS the self-consistency of E/R/R is *not* a machine-checked theorem but a substantive check against the criterion formalized in `ERRWellFormedness.v` for the known paradoxical systems. Therefore the correct formulation is this: the self-application of E/R/R *reveals no structural violation* by the same signs (self-reference, confusion of categories) by which paradoxical systems are formally diagnosed. This is substantive evidence that E/R/R is fit to be the universal ontology of systems—but precisely substantive evidence, not a theorem of self-consistency proved in Rocq.

### The Parallel with the Self-Grounding of $L4$

**Structural content.**  The self-consistency of E/R/R is a structural phenomenon parallel to the self-grounding of $L4$ fixed in Chapter 3 ((see the corresponding chapter)). In both cases the formal apparatus of ToS *can be applied to itself*, and in both cases the result is consistency, not contradiction.

**The parallel.**  \;\;
*$L4$ applied to itself.* The Law of Sufficient Reason asserts that every existence has a ground. Applying $L4$ to $L4$ itself: the ground of $L4$ is the structural incompatibility of contradiction (the field `exclusive` in the record `Distinction`). The law grounds itself without appeal to anything external.

*E/R/R applied to itself.* The E/R/R structure asserts that every system can be analyzed into three aspects. Applying E/R/R to E/R/R itself: the structure can be analyzed into three categories (Elements, Roles, Rules) without self-reference and without confusion of categories. The structure grounds its applicability to itself.

**Consequence: self-consistency as a structural property of
ToS.**  From the self-grounding of $L4$ and the self-consistency of E/R/R it follows that the formal apparatus of ToS has an important methodological property: its central structures (the Law of Sufficient Reason and the E/R/R ontology) *do not depend* on anything external for their applicability. They work *through themselves*, which agrees with the established ontological primacy of the laws of logic and the E/R/R structure.

With the tenability of E/R/R checked through self-application, we have grounds to pass to its applications: first to the simplest system, the record `Distinction`, and then to the universal construction `distinction_of`.

## Application to `Distinction`

With the apparatus of E/R/R developed and the self-consistency of the structure checked, we can pass to its *working application*: the analysis of particular formal structures already introduced in the present work. The first such application is to the record `Distinction`, the simplest formal system, introduced in Chapter 2 and developed in Chapter 3.

The E/R/R analysis of `Distinction` gives two things: it shows how the methodology works on particular, simplest material, and it confirms that the simplest system—the act of distinction—has a full-fledged E/R/R structure.

### Setup

{

**What we analyze.**  The record `Distinction` with four fields `positive`, `negative`, `exclusive`, `exhaustive`, which formalizes the act of distinction. The structural analysis of the four fields was carried out in (see the corresponding chapter) of Chapter 2; the formal derivation of the laws from this record, in Chapter 3. Here we arrange the content of the act of distinction into the three E/R/R categories and check that the result is well-formed.
}

**The level of the system.**  In the substantive interpretation of the hierarchy of levels it is convenient to understand `Distinction` as a system of the ground level: the record contains no other systems as elements; it fixes the act of distinction directly. As in the case of `distinction_of` (“Application to distinction_of”), this is an interpretation in terms of the hierarchy, not a literal typing of `Distinction` in `Level`: formally, `Distinction` is a `Record`, not an object of `System L`.

**The order of analysis.**  In accordance with the ontological order (“The Order of Exposition”), the analysis proceeds in the direction Rules $\to$ Roles $\to$ Elements: first the rules are established, then the roles they define, and only then the elements that play these roles.

### The E/R/R Analysis of `Distinction`

**Rules: the universal laws and the fields `exclusive`,
`exhaustive`.**  At the level of Rules, two layers are at work in `Distinction` (“The Two Layers of Rules: The Universal and the Concrete”):

*The universal layer*—the laws $L1$–$L5$. They work in `Distinction` as the theorems derived in Chapter 3.

*The concrete layer*—two structural fields of the record itself, which formalize the rules by which the act of distinction works:

- The field `exclusive` ($\neg(`positive` \wedge `negative`)$): the rule fixing that the positive and the negative sides are incompatible.
- The field `exhaustive` ($`positive` \vee `negative`$): the rule fixing that there is no third between the sides.

These two fields are *concrete* rules, specific to the act of distinction. Together with the universal layer they set that `Distinction` is precisely an act of distinction and not some other two-component structure.

**Roles: the positive side and the negative side.**  The rules by which the act of distinction works define two positions that must be filled:

- The role of the *positive side*: the position of what is singled out—of that which, in the act of distinction, is presented as determinate content. In the record `Distinction` this role is set by the field `positive`.
- The role of the *negative side*: the position of the background—of that relative to which the presentation acquires determinacy. This role is set by the field `negative`.

By $L4$, both roles are necessary on structural grounds: without the positive side there is nothing to distinguish; without the negative, nothing to distinguish it against. Fewer than two roles: no distinction (“Minimality: Two Elements, Two Roles, Two Rules”); exactly two roles: the structural minimum realized in `Distinction`.

**Elements: the positive and the negative sides.**  At the level of Elements, the two sides of the distinction are at work in the act of distinction. For a particular instance $D : `Distinction`$ these are the values `positive` $D$ and `negative` $D$—exactly as `err_elements` is arranged in `ERRFromDistinction.v`. When the record is applied through the universal construction `distinction_of` $(A)$ ((see the corresponding chapter) of Chapter 2), these values are the proposition $A$ and its negation $\neg A$:

- The proposition $A$: the positive side, the element occupying the role of what is singled out.
- The proposition $\neg A$: the negative side, the element occupying the role of the background.

By $L1$, each of these elements is identical to itself: $A = A$, $\neg A = \neg A$. The multiplicity is exactly two elements, as was shown in “Minimality: Two Elements, Two Roles, Two Rules”: one element does not form a distinction, and two are exactly as many as are needed.

**Two levels of reading: instance and schema.**  In this analysis two levels must be explicitly distinguished; otherwise the E/R/R labeling of `Distinction` will come into contradiction with the formalization.

{
*The instance level.* For a particular $D : `Distinction`$ the elements are the *values* `positive` $D$ and `negative` $D$. This is exactly how the formalization is arranged: the file `ERRFromDistinction.v` defines the list of elements as

`err_elements D := [ positive D; negative D ]`,

that is, the positive and the negative sides of the instance are the *Elements* of the E/R/R analysis. At the instance level the arrangement is as follows: the Elements are `positive` $D$ and `negative` $D$; the Roles, “the singled-out” and “the background”; the Rules, `exclusive` and `exhaustive`.
}

*The level of the record schema.* At the level of the record schema `Distinction` itself, as a type, the field names `positive` and `negative` can be read differently—as *role slots*: “the positive side” and “the negative side,” two positions that a particular instance fills. This reading is substantively useful: it shows that the schema sets the *potential* of the act of distinction. But it must be understood precisely as a meta-level reading of the record schema, *not* as a literal E/R/R labeling coinciding with `ERRFromDistinction.v`. In the formalization the Elements are the values `positive` $D$ and `negative` $D$ of the instance, not the contents “inside” the role slots of the schema.

In other words, the arrangement “Elements $=$ the values of the fields” refers to the *instance* $D$ and coincides literally with the code; the reading “`positive`/`negative` $=$ role slots” refers to the *schema* `Distinction` and is a substantive meta-interpretation. Both readings are legitimate, but they must not be mixed.

**The correspondence between the fields of the record and the E/R/R categories.**  The final arrangement, with both levels of reading indicated explicitly:

| **Field** | **Level of the instance $D$** | **Schema level** |
|---|---|---|
| `positive` | Element: the value `positive` $D$ | role slot |
| `negative` | Element: the value `negative` $D$ | role slot |
| `exclusive` | Rule: incompatibility of the sides | Rule |
| `exhaustive` | Rule: exhaustiveness of the sides | Rule |

The left column is the literal E/R/R labeling of the instance, coinciding with the code of the file `ERRFromDistinction.v`: `positive` $D$ and `negative` $D$ are Elements. The right column is the meta-level reading of the schema, in which `positive` and `negative` are seen as role slots. The roles of the E/R/R analysis (“the singled-out” and “the background”) are, at the instance level, the positions that these two elements occupy; at the schema level they are the slots themselves.

### Well-Formedness Check

**The criterion.**  By the criterion of well-formedness (“Well-Formedness Check,” “Paradoxes as a Confusion of E/R/R Categories”): unambiguity of categories and absence of self-reference through the categories.

**The check for `Distinction`.**
*Unambiguity of categories.* At the level of the instance $D$: `positive` $D$ and `negative` $D$ are elements; the fields `exclusive` and `exhaustive` are rules; the roles “the singled-out”/“the background” are the positions the elements occupy. Each component belongs unambiguously to one E/R/R category; in the formalization `ERRWellFormedness.v` this unambiguity is built into the very representation—the category of a component is given by a function, so that one component cannot have two categories.

*Absence of self-reference.* The field `exclusive` is a rule about the relation of the roles `positive` and `negative`, not about itself. The field `exhaustive` likewise. By $P1$ such self-reference across levels is structurally impossible. The elements $A$ and $\neg A$ play their roles without referring to themselves as rules or roles.

**Consequence: `Distinction` is well-formed.**
{ The simplest formal structure of the present volume satisfies the criterion of E/R/R analysis—and now not only substantively. In the file `PrinciplesToERR.v`, `Distinction` is written as an object `ERRSystem` (`distinction_meta_system`), and the theorem `distinction_err_well_formed` confirms by machine that it passes the criterion `is_well_formed`; and `every_distinction_err_well_formed` extends this to every such analysis. The substantive justification of its legitimacy as a formal model of the act of distinction is backed by a separate Rocq theorem.}

### What the Analysis Yields

**Structural content.**  The E/R/R analysis of `Distinction` shows the following:

- The record `Distinction` itself, as a type in Rocq, fixes the *potential* of the act of distinction: the rules and roles are set, the elements not yet. The record is a structural template, not a particular act.
- A particular act of distinction is an actualization in which the roles `positive` and `negative` are filled by particular propositions $A$ and $\neg A$.
- The distinction between the *potential* and the *actual* modes of existence of a system (“Elements: The Actualization of Potential”) shows itself here with particular clarity: the type `Distinction` is the potential; the instance `mkDistinction` $A$ $\neg A$ … is the actualization.

**Consequence: the methodology works.**  The application of E/R/R to the simplest formal structure gives a consistent result: each field finds its place in the E/R/R categories, particular elements actualize the structure, and the well-formedness check passes. This is the first *working* confirmation of the applicability of the methodology to the particular formal objects of the present volume.

**Consequence: a basis for application to derived constructions.**
{
`Distinction` is the basic record on which the universal construction `distinction_of` is built (analyzed in (see the corresponding chapter) of Chapter 2). Since `Distinction` is well-formed, the construction `distinction_of` inherits E/R/R consistency—which we analyze in the next section.
}

## Application to `distinction_of`

After the analysis of `Distinction` as the simplest system of the base level, we pass to the second working application of the methodology: to the universal construction `distinction_of`, introduced in (see the corresponding chapter) of Chapter 2.

The E/R/R analysis of `distinction_of` yields something qualitatively new: this construction is a *mechanism for producing* acts of distinction for arbitrary propositions, not a separate act of distinction. It is the first *producer system* in the present work, as opposed to a mere bearer system.

### Setup

**What we analyze.**  The construction `distinction_of` $(P)$, which for any proposition $P : `Prop`$ builds an instance of the record `Distinction` with the following field values: `positive` $=P$, `negative` $=\neg P$; the field `exclusive` receives a constructive proof of the incompatibility of $P$ and $\neg P$; the field `exhaustive` receives a proof of $P \vee \neg P$ from the axiom `classic` (as discussed in (see the corresponding chapter) of Chapter 3).

**The level: a substantive interpretation.**
{
In the substantive E/R/R interpretation it is convenient to understand `distinction_of` as a construction of a higher level than `Distinction`: it takes a proposition and builds an instance of `Distinction`, and by the principle of hierarchy a producer construction stands above what it produces. This is a useful explanatory reading. But its status relative to the formalization must be stated at once. In the current formalization `Distinction` is a `Record`, and `distinction_of` is a `Definition` function that builds an instance from a proposition $P$; *neither is set up* as an object of type `System L` with a particular level. When we say below that `distinction_of` “belongs to the level $L_2$” and `Distinction` “is a record of level $L_1$,” this is an interpretation of the constructor function in terms of the hierarchy, *not* a literal typing in the type `Level` present in the code. In substance the interpretation is correct and useful; formally, however, the typing of `distinction_of` and `Distinction` in `Level` has not yet been carried out.
}

**The order of analysis.**  In accordance with the ontological order, the analysis proceeds in the direction Rules $\to$ Roles $\to$ Elements.

### The E/R/R Analysis of `distinction_of`

**Rules: the universal laws and the rules of the construction.**  At the level of Rules, two layers are at work in `distinction_of`:

*The universal layer*—the laws $L1$–$L5$, working at the level $L_2$. In particular, $P1$ (Hierarchy) provides that `distinction_of` as a function stands at a level above its values; $L4$ provides the groundedness of all the fields of the instance being built.

*The concrete layer*—the rules specific to the construction:

- The rule of applying `mkDistinction`: to build an instance of `Distinction`, the constructor requires four arguments—two propositions and two proofs.
- The rule of the constructive proof of `exclusive`: for an arbitrary $P$ the proof of $\neg(P \wedge \neg P)$ is built constructively (this is $L2$ for $P$, requiring no axioms).
- The rule of recourse to the axiom `classic`: to obtain `exhaustive` $= P \vee \neg P$, `classic` is used, since for an arbitrary proposition exhaustiveness is not constructively provable ((see the corresponding chapter) of Chapter 3).

**Roles: the input position and the output position.**  A producer construction has two specific positions that do not exist in the simple system `Distinction`:

- The *input* role: the position occupied by the parameter for which the instance is built. In `distinction_of` $(P)$ this position is occupied by the proposition $P$.
- The *output* role: the position occupied by the built result. This position is occupied by the built instance of `Distinction`.

By $L4$, both roles are grounded: the input is necessary because the construction is universal and must work for an arbitrary proposition; the output, because it is precisely the built instance that is the result of applying the construction. Without the input there would be nothing to build for; without the output, no result of building.

**Remark: the inner roles of the built instance.**  Besides the input and output roles, *within* the built instance of `Distinction` the same roles are at work that were analyzed in “The E/R/R Analysis of Distinction”: the positive side and the negative side. These roles are an inheritance from the record `Distinction`, working at the level $L_1$ *within* a result of level $L_2$.

**Elements: the proposition $P$ and the built instance.**  At the level of Elements the following are at work in `distinction_of`:

- The proposition $P$: the actual bearer of the input role. This is an arbitrary proposition of type `Prop`, passed to the construction.
- The built instance `Distinction` $(P, \neg P, …)$: the actual bearer of the output role. This is a particular object of the record `Distinction`, in which the roles are filled by the propositions $P$ and $\neg P$.

By $L1$, each of these elements is identical to itself: the given proposition $P$ remains the same proposition; the built instance remains the same instance.

**The correspondence between the components and the E/R/R categories.**

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| `mkDistinction` | Application of the constructor | Rule (concr. layer) |
| Constructive `exclusive` | Rule for $L2$ | Rule (concr. layer) |
| Use of `classic` | Rule for $L3$ | Rule (concr. layer) |
| Input position | Role of the parameter | Role |
| Output position | Role of the result | Role |
| Proposition $P$ | Actual input | Element |
| Instance of `Distinction` | Actual output | Element |

### Well-Formedness Check

**Unambiguity of categories.**  Each component of the construction belongs to exactly one E/R/R category. The rules (`mkDistinction`, the constructive proof, the recourse to `classic`) are precisely rules, not roles and not elements. The input and output positions are roles, not rules. The proposition $P$ and the built instance are elements that actualize these roles.

**Absence of self-reference.**  The construction `distinction_of` does not refer to itself as its own parameter: it takes an *arbitrary* proposition and does not *extend itself* to itself. By $P1$ such self-reference through the categories is structurally impossible: the construction stands at the level $L_2$, its values at the level $L_1$, and the passage back is impossible.

**Consequence: `distinction_of` is well-formed.**  The universal construction, inheriting E/R/R consistency from `Distinction` (“Well-Formedness Check”), itself satisfies the criterion of well-formedness.

### What the Analysis Yields

**Structural content.**  The E/R/R analysis of `distinction_of` shows the following:

- A producer construction has an E/R/R structure more complex than a simple record: *new* roles appear (input and output), specific to mechanisms of production.
- The hierarchy of levels works explicitly: `distinction_of` is at $L_2$, its values at $L_1$, and the passage $L_2 \to L_1$ is an *actualization* (the application of the construction to a particular proposition).
- The two layers of Rules show themselves: the concrete layer contains both constructive rules (the application of `mkDistinction`, the constructive proof of `exclusive`) and rules of recourse to an axiom (`classic` for `exhaustive`).

**Consequence: the methodology scales.**  The application of E/R/R to two structures of different complexity—the simple record `Distinction` and the universal construction `distinction_of`—shows that the methodology works beyond a single particular case. It is applicable to structures of different levels of the hierarchy, to simple bearer systems and to complex producer systems. This is a substantive justification of its applicability to all the subsequent structures of the present volume.

**Consequence: preparation for the diagnosis of paradoxes.**  In “Well-Formedness Check” we made sure that `distinction_of` does *not* lead to self-reference. But what if we tried to build a *self-referential* construction—for example, one that builds a `Distinction` for a proposition asserting something about the construction itself? Here begins the work of E/R/R as a *diagnostic instrument*, the subject of the next section.

## Paradoxes as a Confusion of E/R/R Categories

In § “Application to Distinction”–“Application to distinction_of” the E/R/R methodology worked as a *constructive* instrument: we analyzed well-built structures and made sure that they are well-formed. The present section reverses the direction: E/R/R is applied as a *diagnostic* instrument to structures in which something goes wrong—to the classical paradoxes.

The central observation: paradoxes are *diagnostic signals* that the E/R/R arrangement has been violated in the construction—not deep mysteries revealing the limits of reason. Under correct diagnosis a paradox is not *solved*: it is *laid open*—it becomes visible where exactly the construction violates the categorial arrangement, and the very question the paradox poses turns out to be ill-posed.

***Paradoxes are a confusion of E/R/R categories: one and the
same object attempts to play two different categorial
roles at once.***

### The Diagnostic Function of E/R/R

{

**Laying open, not solving.**  There is a difference in principle between two approaches to paradoxes: solving and laying open. To solve a paradox is to answer the question it poses: “is the lying sentence true?” or “does Russell’s set contain itself?” To *lay a paradox open* is to show that the question itself is ill-posed and has no meaningful content, since the construction underlying it violates the structure.
}

Laying open is not evasion. It is *exact diagnosis*: an indication of where exactly the construction goes beyond the bounds of a correct categorial labeling. Once the diagnosis has been made, the paradox receives no answer: it ceases to be a question.

**E/R/R as a universal diagnostic instrument.**  Since every correct system has an E/R/R structure, any construction claiming the status of a system must be analyzable through the three categories—Elements, Roles, Rules—unambiguously and without self-reference. Paradoxes are precisely those constructions for which such an analysis is *impossible*: one and the same entity attempts to occupy the places of different categories at once. This is a structural violation that is formalized in Rocq and checked by machine.[^18]

### The Place of Structural Paradoxes in the General Classification

In a broader work on the diagnosis of paradoxes[^19], paradoxes are classified by the type of violation:

- *Structural paradoxes* violate the vertical arrangement by confusing E/R/R categories; there is self-reference in the construction itself. These include the paradoxes of Russell, the Liar, Grelling, Cantor, Burali-Forti, Berry, Richard, Curry, Yablo, and others.
- *Defective paradoxes* contain a flaw in the premises (conceptual indeterminacy, a hidden contradiction, a false premise, a category mistake). These include, in particular, the sorites paradox, the paradox of the Ship of Theseus, Zeno’s paradoxes, and the paradoxes of infinity (Hilbert, Galileo, Banach–Tarski).
- *Non-paradoxes* are counterintuitive but correct results containing no contradiction (Monty Hall, the [[Birthday Paradox|birthday paradox]], [[Simpsons Paradox|Simpson’s paradox]]).

In the present section we analyze in detail the *structural* paradoxes—those that are resolved directly through E/R/R diagnosis. Defective paradoxes and non-paradoxes require other instruments, which lie beyond the scope of the present work.

### Russell’s Paradox: Element `=` Rule

**The construction.**  Consider the set $R$ of all sets that do not contain themselves. The question is: does $R$ contain itself? If $R \in R$, then by definition $R \notin R$; if $R \notin R$, then by definition $R \in R$. A contradiction.

**E/R/R diagnosis.**  In Russell’s construction one and the same entity—the set $R$—occupies two categories at once:

- As an Element: $R$ acts as a candidate for its own membership; the question “$R \in R$?” presupposes $R$ as an element.
- As a Rule: $R$ is defined by the rule “does not contain itself” and itself plays the role of the criterion by which its own membership is checked.

In other words: *Element `=` Rule*. The object attempts to be at once that which is classified and that which classifies.

**The violation of $P1$.**  In “: Hierarchy” it was shown that $P1$ (Hierarchy, $S \notin S$) is derived from $L1 + L5$. Applied to Russell’s paradox: a set cannot be its own element, since the organizer and the organized stand at different levels. The construction $R \in R$ requires $\text{Level}(R) < \text{Level}(R)$, which violates the irreflexivity of $L5$.

{

**Laid open formally.**  In the repository Russell’s construction is formalized as `russell_system` in `ERRWellFormedness.v` and checked for well-formedness—the result is `false`. This is established by machine by two theorems in two files: the lemma `russell_ill_formed` in `ERRWellFormedness.v` itself (directly about `russell_system`) and the lemma `russell_is_ill_formed` in `ParadoxDiagnosis.v` (through the map `paradox_system`, which assigns to a type of paradox its E/R/R system).[^20]
}

**The historical solution and its place in the E/R/R picture.**  The classical solution—Russell’s theory of types—distributes sets and elements over different types, making self-membership syntactically inexpressible. The Axiom of Regularity in ZFC formulates the same requirement by ruling out $\in$-cycles. Both solutions are particular cases of the general $P1$: the organizer and the organized are different levels.

### The Liar Paradox: An Element Applies a Rule to Itself

**The construction.**  The statement $L$: “This statement is false.”[^21] If $L$ is true, then $L$ is false; if $L$ is false, then $L$ is true. A contradiction.

**E/R/R diagnosis.**  The statement $L$ occupies two positions:

- As an Element: $L$ is the statement itself, toward which the truth-value evaluation is directed.
- As a Rule: $L$ applies the operation of truth-value evaluation to itself—it contains this very operation within itself.

This is a special case: *an Element applies a Rule to itself*. The self-referential application of evaluation leads to this: the statement must exist *before* its own evaluation (as an object) and at the same time *contain* this evaluation (as part of itself).

**The violation of $L5$.**  By $L5$, operations stand at a level above that to which they are applied. Truth-value evaluation is an operation working on a statement as on an object. Including the evaluation in the statement itself merges the levels of operation and operand, which is structurally impossible.

**Laid open formally.**  The Liar construction is formalized as `liar_system`; the theorem `liar_is_ill_formed` establishes its ill-formed status.

**The connection with Tarski’s hierarchy.**  Tarski separated the object language and the metalanguage: the truth-value evaluation of the statements of the object language is carried out in the metalanguage, at a level above. This is a particular case of the hierarchy of levels. The relation to our approach must be formulated precisely. Tarski builds an *open* hierarchy of languages and metalanguages, continuing upward without bound. In ToS the hierarchy of levels `Level` is arranged similarly in one respect and differently in another: each *particular* level has a finite depth relative to the ground (this is the content of $L5$ and of the theorem `L5_no_infinite_descent`), but the hierarchy itself *has no internal upper bound*—it continues upward without bound through the constructor of the next level. That is, the difference does not lie in “our hierarchy is finite, while Tarski’s is infinite”: it is true that each level is reachable in a finite number of steps from the ground, and at the same time there are unboundedly many levels.

### Grelling’s Paradox: Rule `=` Element

**The construction.**  A word is called *heterological* if it does not describe itself (for example, “long” is a short word and does not describe itself). Is the word “heterological” heterological? If yes, then by definition it does *not* describe itself, that is, it is not heterological; if no, then it describes itself, and hence it is heterological.

{

**E/R/R diagnosis.**  The word “heterological” occupies two positions:
}

- As a Rule: it is a property (a rule of the applicability of a predicate) working on words.
- As an Element: in the test for self-applicability it is itself considered as a word to which the rule is applied.

Here *Rule `=` Element*. The rule attempts to be its own operand.

**The violation of the hierarchy.**  A property (a predicate) and the object to which it is applied are different levels ($L5$). The property “heterological” is applied at the second-order level—to words themselves as objects of the first-order level. Applying the property *to itself* requires the property to be at two levels at once, which is impossible by $P1$.

**Laid open formally.**  `grelling_system` is ill-formed; the theorem `grelling_is_ill_formed`.

**A historical parallel.**  Russell’s stratification of types: predicates on words stand at a level above words; the application of a predicate to the predicate itself as to a word is blocked syntactically.

### [[Cantors Paradox|Cantor’s Paradox]] and the Burali-Forti Paradox

**Cantor’s paradox.**  The set of all sets $U$. It must contain all sets, including itself, which gives $U \in U$.

*E/R/R diagnosis*: $U$ occupies two positions—as a System (the whole system of all sets) and as an Element (a member of itself). This is *System `=` Element of itself*. A direct violation of $P1$.

**The Burali-Forti paradox.**  The set of all ordinal numbers. Its order type is an ordinal greater than all ordinals, which contradicts its own definition as the set of all of them.

*E/R/R diagnosis*: the totality of all ordinals $\Omega$ occupies two positions—as a Totality (the set itself) and as an Element (entering into this totality). Structurally the same error: *Totality `=` Element of itself*.

{

**Laid open formally.**  Both constructions are structurally equivalent to Russell’s construction: the self-membership of a totality. In the repository they are represented through `russell_system` (Cantor) and `grelling_system` (Burali-Forti) as concretizations of the general pattern of self-membership.[^22]
}

**The historical solution.**  In ZFC the renunciation of the universal set and the passage to proper classes (NBG, MK) formalize exactly the exclusion that $P1$ expresses: totalities cannot be their own elements.

### Unified Diagnosis

**The main theorem.**  All five paradoxes analyzed are structurally ill-formed. In Rocq this is fixed by a single theorem:

```coq
Theorem all_paradoxes_ill_formed : forall p : ParadoxType,
  is_well_formed (paradox_system p) = false.
```

where `ParadoxType` enumerates the five paradoxes and `paradox_system` assigns to each of them a formal construction.[^23]

**The unified table.**  All five structural paradoxes are brought together in a single table by the type of violation of the E/R/R categories:

| **Paradox** | **E/R/R violation** | **Hist. solution** |
|---|---|---|
| Russell | Element `=` Rule | Theory of types |
| Liar | Element applies Rule to itself | Tarski’s hierarchy |
| Grelling | Rule `=` Element | Stratification of types |
| Cantor | System `=` Element of itself | No univ. set |
| Burali-Forti | Totality `=` Element of itself | Proper classes |

{

**The contrapositive.**  If a system is well-formed, it cannot coincide with any of the paradoxical constructions. This is fixed by the theorem `well_formed_paradox_free`: well-formedness *excludes* paradoxicality.
}

**The connection with the principles $P1$–$P4$.**  The principles analyzed in “The Four Principles” work as structural blocks against paradoxes:

- $P1$ (Hierarchy) blocks the paradoxes of Russell, Cantor, and Burali-Forti by ruling out self-membership.
- $P2$ (Criterion Precedence) blocks the Liar by requiring that truth-value evaluation be defined before it is applied to a statement.
- $P3$ (Intensional Identity) distinguishes “empty” systems with different criteria—unlike ZFC, where there is a unique empty set.
- $P4$ (Finite Actuality) lays open the paradoxes of infinity (Hilbert, Galileo, Banach–Tarski), which the classification counts as *defective*: they arise from treating infinity as a completed object.

### Counterexamples: Well-Formed Systems

The diagnostic function of E/R/R works in both directions. Not only do paradoxes receive an exact diagnosis: well-formed systems are *verified* as correct.

**The natural numbers.**  The structure of the natural numbers is analyzed through E/R/R as follows:

- Elements: particular natural numbers $1, 2, 3, …$ as bearers.
- Roles: the position “one” (the beginning) and the position “successor” (for each number).
- Rules: the universal layer ($L1$–$L5$) and the concrete layer (the rules of construction—one and successor).

The categories are unambiguous; there is no self-reference.[^24] The natural numbers are a well-formed system.

**Chess.**  The game of chess is also analyzed through E/R/R:

- Elements: the particular pieces on the board and the squares of the board.
- Roles: the types of pieces (king, queen, bishop, and so on), the types of squares, the notions of position and move.
- Rules: the universal layer and the concrete layer (the rules of moves, the conditions of victory).

Each piece is precisely an element, not a rule; each rule is precisely a rule, not a piece. The categories do not mix; there is no self-reference. Chess is a well-formed system.[^25]

**Consequence: the criterion works both ways.**  E/R/R diagnosis distinguishes paradoxes from well-formed systems exactly and formally. Paradoxes are revealed as ill-formed automatically (Rocq compiles and checks); well-formed systems—from arithmetic to games—pass the check. This is a systematic criterion that does not depend on the particular features of the structure under consideration.

With the analysis of paradoxes as the diagnostic work of E/R/R we complete the substantive unfolding of the chapter. The unfolded structure—the record `Distinction`, the laws $L1$–$L5$, the principles $P1$–$P4$, the E/R/R arrangement, and the hierarchy of levels—becomes the basis for the following chapters, in which the formal apparatus will receive further technical refinements and will be applied to subtler questions of metamathematics.

---

[^1]: The formalization of the four principles and their derivation from the laws is contained in the file `PrinciplesFromLaws.v` of the ToS-Coq repository; the file rests on `Distinction.v`, `LawsFromDistinction.v`, and `TheoryOfSystems_Core_ERR.v`.
[^2]: The corresponding theorems of the file are `P1_concrete_L1_L2`, `P1_level_step`, `P1_asymmetry`.
[^3]: This result is fixed in the theorem `P1_blocks_russell`. A detailed discussion of the connection with paradoxes is in “Paradoxes as a Confusion of E/R/R Categories.”
[^4]: The corresponding theorem in the file is `four_principles_from_five_laws`. There is also the theorem `derivation_chain`, which explicitly indicates the source law for each principle: $P1$ from $L1 + L5$; $P2$ from $L5$; $P3$ from $L1 + L4$; $P4$ from $L5$.
[^5]: The file `ERRFromDistinction.v` of the ToS-Coq repository.
[^6]: A direct quotation from the comments of the file `ERRFromDistinction.v`.
[^7]: The corresponding functions of the file `ERRFromDistinction.v` are `err_element_count`, `err_role_count`, `err_rule_count`. There are also the theorems `distinction_has_two_elements`, `distinction_has_two_roles`, `minimum_two_roles`, which prove these equalities.
[^8]: The case in which an act of an operator is required in the absence of an algorithmic selection mechanism is closely connected with the Axiom of Choice in classical set theory. A detailed discussion is in Chapter 6, where both fundamental axioms of the ToS-Coq repository (`classic` and `L4_witness`) and their relation to the principle $P4$ are analyzed.
[^9]: Here, for the sake of illustration, we count the natural numbers starting from $1$. If one works with `nat` in Rocq, where the naturals start from $0$, then already $0^2 < 1$, and the set of bearers for small $c$ is nonempty; the example is then more conveniently taken with $c = 0$, where the condition $n^2 < 0$ holds for no $n$.
[^10]: The formal apparatus is in the file `FormationRules.v`, which rests on the type `System`, the field `sys_criterion` (the concrete criterion of a system), and the relation `HasType` (the typing of a system in a context). The key lemmas are `sys_form` (the formation rule of a system), `p1_check` (the check of the hierarchy), `l4_role_principle` (the check of the groundedness of roles), and `wf4_check` (the general check of well-formedness).
[^11]: The connection with the Axiom of Choice in classical set theory: the situation in which an element must be chosen from each of a family of nonempty sets without an algorithm for such a choice. In ToS the two situations are formally separated: automatic selection is realized through the constructive constructions of Rocq, operator-driven selection through the axiom `L4_witness`. A detailed discussion is in Chapter 6.
[^12]: “Nontrivial” in the sense of not degenerating into the simplest act of distinction. The simplest act of distinction is the limiting case of the hierarchy, in which the levels do not unfold further; see “Hierarchy as the Unfolding of E/R/R.”
[^13]: A detailed discussion of `Level` as a structure in its own right is in Chapter 6. Here its role in the formalization of the hierarchy is enough for us.
[^14]: Formally: the inductive definition of the natural numbers through one and the operation of adding one is the simplest E/R/R structure, with two elements at each step—“what is already built” and “the next.”
[^15]: This structure agrees with the metaphysical derivation of Volume I, where the Structure/Filling duality arises as $L4$ for $A = \exists$: the very fact of existence requires a meta-arrangement in which both roles are present.
[^16]: A detailed discussion of the criterion is in “Paradoxes as a Confusion of E/R/R Categories.”
[^17]: The exact formulations of `no_self_reference` and `rules_above_elements` are analyzed in “Paradoxes as a Confusion of E/R/R Categories.”
[^18]: The formal apparatus is in the files `ERRWellFormedness.v` (the criterion of well-formedness) and `ParadoxDiagnosis.v` (the unified analysis of five paradoxes). The main theorem `all_paradoxes_ill_formed` establishes that all the classical paradoxes are structurally ill-formed.
[^19]: The full classification of $46$ classical paradoxes into three classes (structural, defective, non-paradoxes) and a detailed method of domain analysis are in the author’s separate work on the diagnosis of paradoxes through the architecture of reasoning. In the present section we confine ourselves to structural paradoxes, since it is precisely they that are analyzed directly through E/R/R diagnosis.
[^20]: In `PrinciplesFromLaws.v` (“: Hierarchy”) there is also a separate theorem `P1_blocks_russell`, fixing that $P1$ blocks Russell’s construction.
[^21]: Formally: $L \Leftrightarrow \neg L$.
[^22]: The theorems `cantor_is_ill_formed` and `buraliforti_is_ill_formed` in the file `ParadoxDiagnosis.v` establish the ill-formed status of both constructions—through the map `paradox_system`, in which Cantor is assigned `russell_system` and Burali-Forti `grelling_system`.
[^23]: The full synthesis is in the theorem `paradox_diagnosis_synthesis`, which unites: (1) the ill-formed status of all the paradoxes; (2) the contrapositive `well_formed_paradox_free`; (3) the exact classification of violations for each paradox.
[^24]: This is fixed in `ERRWellFormedness.v` by the theorem `nat_well_formed`: the formal representation of the natural numbers as an `ERRSystem` passes the check `is_well_formed`.
[^25]: The theorem `chess_well_formed`.

---

Part: [[01 First Distinction and Laws of Logic|Part I. The First Distinction and the Laws of Logic]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]] · [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/03 Deriving the Laws of Logic from Distinction|Chapter 3. Deriving the Laws of Logic from Distinction]] · [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/05 Co Definition of A and Not A|Chapter 5. The Co-Definition of A and ¬A]] →
