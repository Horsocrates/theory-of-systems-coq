---
title: "Chapter 1. P4: Infinity as Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/04 Процессные действительные числа/01 P4 бесконечность как процесс.md"
sourceBlob: a9949f1ab0e316a873ca868fefb13579fbc1eba2
translated: 2026-10-20
status: draft
---

## The Principle of Finite Actuality

### Where the Volume Stands

Three parts lie behind us. Part I derived from a single starting point—from the fact that something is—the act of distinction and its five laws; Part II built the natural number series as the length of a list of distinctions; Part III unfolded the integers and the rational numbers from the natural series and showed that the rational numbers are enumerable, and then that behind the number-position there stands an object of another kind, the number-process. The last chapter of Part III analyzed the first such process, $\sqrt{2}$, and brought the exposition to a threshold: the process as an object in its own right has been named but not built.

Part IV crosses this threshold. It introduces the *process* as a full-fledged type—an object of formalization just as definite as a natural or a rational number—and carries all the consequences through this construction: for the ontology of number, for uncountability, for the question of the continuum, and for which familiar assumptions of classical mathematics turn out to be unnecessary along the way. Everything built in Part IV and beyond will be built *on processes*; Part IV therefore lays the foundation, and the foundation must be laid with care.

Before building the process as a type (the next chapter will do this), we must bring to full clarity the *principle* that justifies this type. The principle is called $P4$. It has been at work in the volume since the very construction of the natural number series, but at work without a developed exposition: it was mentioned where it was needed and applied, yet it did not receive a chapter of its own. The present chapter gives it such a chapter.

### $P4$: What It Asserts

Let us begin with what $P4$ *asserts*—and give the statement verbatim, in the formulation that the exposition of ToS gives it.[^1]
The principle bears the name *Finite Actuality* (so it is called in the original), and its statement consists of two sentences:

**$P4$ (Finite Actuality).**
*Every system is finite at any moment. Infinity is a property of process, not of object.*

Let us read closely. The first sentence is about *a system at a moment*: whatever we take—any system at all, at any stage of its unfolding—what is taken *at the given moment* is finite. Not “small,” not “bounded by a number we know,” but precisely finite: it consists of a finite number of distinguished elements. The second sentence says where infinity goes: it does not vanish, it *changes its bearer*. Infinity is a property of the *process*—of how the system unfolds, step by step, without a last step—and not a property of the *object*, not a characteristic of any system taken at a moment. The course is infinite; every frame of this course is finite.

From here—and only from here, as a *consequence*—we obtain what is usually put in place of the principle itself: “there is no completed infinity.” If every system at a moment is finite, and infinity belongs only to the process, then a “completed infinity”—an infinite system taken as a ready, existing object—is a combination of the uncombinable: infinity is ascribed to what, by $P4$, it cannot belong to, an object rather than a process. The chapter will return more than once to the formula “there is no completed infinity”; but it is important to see from the very beginning that this is a *conclusion* from $P4$, not $P4$ itself. The principle itself is *affirmative*: it says what there is (a finite system at every moment, infinity as a property of the course), not what there is not.

The distinction that $P4$ draws is ontological, not quantitative. The dispute is not about “how much” there is in all; the dispute is about *what* infinity belongs to—the object or the process. Standard mathematics accepts infinite sets as primary objects: Zermelo–Fraenkel axiomatics contains the Axiom of Infinity, which directly postulates an infinite set as an existing object. $P4$ places infinity in the unfolding of the object, not in the object itself. And from this alone, as the following sections will show, everything else follows—both which familiar assumptions turn out to be unnecessary and what a real number must be.

### The Plan of the Chapter

The chapter answers seven questions, and each following section takes one of them. What exactly $P4$ says and what its formal status is (§ 1.2). Where $P4$ comes from—from which starting points already introduced it follows (§ 1.3). Where $P4$ has already been at work in the preceding parts (§ 1.4). How $P4$ relates to the classical axioms—which of them it makes superfluous and with which it is incompatible, and this will require special precision (§ 1.5). What $P4$, on the contrary, leaves fully workable (§ 1.6). How $P4$ relates to Brouwer’s intuitionism, its nearest historical predecessor (§ 1.7). And finally, what $P4$ prepares for the construction of the process as a type—the bridge to Chapter 4.2 (§ 1.8).

A special caveat concerns § 1.5. ToS has a machine-checked formalization in the Rocq system, and this chapter, like the chapters of Part III, is checked against it line by line. The formalization shows that the relation of $P4$ to the standard axioms is arranged more *subtly* than a simple “$P4$ rules out the axiom.” Two different layers of statements are at work there, and the chapter will carefully separate them. A hasty formulation here would be an error, not a simplification.

## Exact Formulation and Formal Status

### From Formulation to Formalization

§ 1.1 gave the formulation of $P4$ verbatim: every system at a moment is finite; infinity is a property of process. This formulation is affirmative—it says what *is*. The present section shows how this statement looks in the machine-checked formalization of ToS and what its *status* is there: whether it is a definition or an axiom, something proved or something accepted.

To anticipate: in the formalization $P4$ also appears affirmatively—and even more sharply than in the prose. The formalization does not write “there is no completed infinite object”; that cannot even be written directly, since it is a statement about *nonexistence*. It writes the opposite—*what* exists: processes of a definite kind, which behave in a definite way. Let us examine this—first the formalization itself (§ 1.2.2), then its ontological reading (§ 1.2.3), then its logical ground (§ 1.2.4).

### $P4$ in the Formalization: What Is Built

In the ToS Rocq repository the four principles—$P1$, $P2$, $P3$, $P4$—are gathered in one file, `ProcessFourPrinciples.v`, and each receives a formal definition there.[^2]
In an explanatory comment the file itself characterizes $P4$ in one line: `P4: Process — everything is a process (nat -> Q)`—in mathematical notation, “$P4$: Process—everything is a process ($ℕ \to ℚ$).” Note that here too the formulation is *affirmative*: it says what everything *is* (a process), not what does not exist.

The definition of $P4$ in this file is built in agreement with this characterization—but is not equal to it. It is affirmative and consists of three parts. *First*, there exists a process that is a Cauchy process—an unfolding sequence of rational approximations, convergent in the operational sense that Chapter III.4 called the Cauchy property. *Second*, Cauchy processes are closed under multiplication: the product of two such processes is again a Cauchy process. *Third*, they are closed under addition: the sum of two Cauchy processes is again a Cauchy process. Formally, this is the predicate `P4_formalized`, the conjunction of these three statements; here it is, verbatim, in Rocq notation:

```coq
Definition P4_formalized : Prop :=
  (exists R : RealProcess, is_Cauchy R)
  /\ (forall R1 R2 : RealProcess, is_Cauchy R1 -> is_Cauchy R2 ->
        is_Cauchy (process_fst (process_product R1 R2)))
  /\ (forall R1 R2 : RealProcess, is_Cauchy R1 -> is_Cauchy R2 ->
        is_Cauchy (process_sum R1 R2)).
```

And the theorem `P4_holds_formalized` proves that `P4_formalized` is true. The witness for the first part is the constant process `const_process 0`, the simplest of the Cauchy processes; closure under product and sum is proved by separate lemmas of process arithmetic.

Precision is needed here—and the chapter insists on it from the very start of its account of the formalization. The file `ProcessFourPrinciples.v` does *not* formalize the whole ontological thesis of $P4$ in a single theorem. It fixes its *process core*: the existence of Cauchy processes and the closure of the basic arithmetic operations on them. The philosophical formula of $P4$—“every system at a moment is finite; infinity is a property of process”—is wider than this core. `P4_formalized` is a machine-checkable formal *trace* of this formula, not its full equivalent. What is proved—and proved honestly—is precisely the conjunction of three process statements; and when the chapter says below that “$P4$ is proved in Rocq,” this should be read in this exact sense: what is proved is the formal process trace of $P4$, the predicate `P4_formalized`.

Why is the formalization arranged as a statement about the presence of processes rather than as a direct record of “there is no completed infinity”? Not because a negative statement cannot be written in Rocq: it can be written—Rocq proves statements of the form “there is no $x$ with the property $P$” and “$P$ implies falsehood” in a perfectly ordinary way, and § 1.5 will show such a proof in the repository itself. The point is different: the bare phrase “there is no completed infinity” requires a precise formal *bearer*—a definition of what exactly is to count as a completed infinite object. That is why the formalization goes two ways: here, in `ProcessFourPrinciples.v`, it builds the affirmative core (Cauchy processes exist), while the incompatibility of completed infinity with $P4$ is proved separately, in the files of § 1.5, and is proved only *after* precise definitions of a completed infinite object and of stage-boundedness are introduced there.

The file goes further and lists named instances of processes. It declares the inductive type `ProcessInstance`—exactly twelve constructors, each named after a definite kind of process: the arithmetic process, the product process, the process of partial sums of a series, the process of the difference quotient (the derivative), the process of Riemann sums (the integral), the process of Picard iterations (the solution of an ordinary differential equation), and so on.[^3]
And here—precision again. `ProcessInstance` is an inductive type of *labels*: twelve label constructors, each of which *names* a kind of process pattern. The lemmas `twelve_instances` and `all_instances_nodup` prove exactly two things about the list of these labels—that it has length twelve and that it has no repetitions. This is *not* in itself a proof of the existence of twelve concrete Cauchy processes with all their analytic properties: the corresponding constructions and theorems—the derivative as a process, the integral as a process, and the rest—live in separate files of the process part of the repository. `ProcessInstance` fixes the *nomenclature* of the twelve patterns; their substantive development is the subject of other files and other chapters of the volume.

### $P4$ as an Ontological Thesis

The positive formalization of § 1.2.2 says that Cauchy processes exist and behave as a closed arithmetic domain. The ontological thesis of $P4$ adds to this a statement about *status*: the process is that through which the infinite enters mathematics—and the only thing through which it enters. Infinity *as a scheme*, not *as an object*. In the E/R/R labeling this means: infinity is a *rule*, not an element (the analysis of § 1.8.3).

Let us unfold this opposition. “Infinity as an object” means the thought that an infinite collection can be taken whole—that there is, for example, the *set* of all natural numbers, a ready object in which all the natural numbers are already gathered and present simultaneously. “Infinity as a scheme” means something else: there is a *rule*—“zero is a number; every number is followed by a number”—and this rule can be applied without end, but at no moment of its application does a ready, gathered “all” arise. Every concrete natural number is accessible—it can be built in a finite number of steps; “all the natural numbers at once,” as an existing object, are inaccessible, and not because there are too many of them, but because “at once” contradicts the very nature of a rule that acts *step by step*.

$P4$ as an ontological thesis asserts: infinity-as-a-scheme suffices for mathematics, and it alone is meaningful. The natural number series is a scheme (a rule of construction), not an object (a completed set). The process $\sqrt{2}$ is a scheme of rational approximations, not an object (a ready point). This is the same distinction of “data versus behavior” that Chapter III.3 introduced for countability: a completed object would be *data*, a finite ready record; a scheme is *behavior*, the capacity to answer the request “give step $n$.” $P4$ says: the infinite enters mathematics only as behavior.

Here it is worth pausing to bring together what the chapter has already distinguished several times along the way—for the confusion of these things is precisely the typical error to which $P4$ is especially exposed. $P4$ has *three* distinct levels, and they are not identical.

*The first level* is the ontological principle: every system at a moment is finite; infinity is a property of process, not of object. This is the philosophical-methodological thesis of ToS, the formulation from section 2.2.4 (§ 1.1).

*The second level* is the formal predicate `P4_formalized` from `ProcessFourPrinciples.v`: Cauchy processes exist, and the basic arithmetic operations preserve the Cauchy property. This is the machine-checkable process trace of the ontological principle, proved by the theorem `P4_holds_formalized`.

*The third level* consists of the prohibition theorems of the files `P4CompletedInfinity.v` and `P4Prohibits*`: under the special definitions `CompletedInfSet`, `P4_stage_bounded`, and `bridge`, completed infinity leads to a contradiction.

These three levels are connected—the second and the third are formal supports of the first—but they are not equal. The ontological principle is wider than any single Rocq theorem; `P4_formalized` proves the process core, not the whole thesis; the prohibition theorems prove incompatibility for *their own* definitions, not unconditionally. The chapter will hold to this distinction everywhere, and the reader will not go wrong in gathering it into one table:

| **Level** | **Content** | **Status** |
|---|---|---|
| Ontological $P4$ | Every system at a moment is finite; infinity is a property of process, not of object | Philosophical-methodological principle of ToS |
| `P4_formalized` | Cauchy processes exist; sum and product preserve the Cauchy property | Proved in `ProcessFourPrinciples.v` |
| Prohibition layer | `CompletedInfSet` ${}\land{}$ `P4_stage_bounded` ${}\land{}$ `bridge` ${}\to{}$ `False` | Proved in `P4CompletedInfinity.v` |

The formal levels—the second and the third—are not identical to the philosophical $P4$ of the first level; but together they give it strong machine-checkable support. It is precisely so—as support, not as a full equivalent—that all the chapter’s further references to the Rocq formalization should be understood.

### Formal Status: Which Axioms Stand behind $P4$

Since the chapter insists on checking against the formalization, it is obliged to answer precisely the question of the *logical ground* as well—on which axioms the Rocq formalization of ToS stands at all. The answer matters, because a principle of “no completed infinity” that secretly relied on the Axiom of Infinity would be strange.

In the intended-foundation layer of ToS, *two* logical axioms are singled out, and both are declared in one file, `ToS_Axioms.v`.[^4]
The first is $L3$, the Law of Excluded Middle: for every proposition $P$, $P \lor \lnot P$ holds. In Rocq this is the standard axiom `classic`; ToS borrows it from the standard library and re-exports it. The second is $L4$, the Law of Sufficient Reason in formalized form: from a proved existence a witness can be extracted. Formally, this is the axiom `L4_witness`: for every type $A$ and every predicate $P$ on it, if $\exists x, P(x)$, then a concrete $x$ can be presented together with a proof of $P(x)$.

The words “two axioms are singled out” refer to the intended-foundation layer—to the assumptions ToS *deliberately* lays at its foundation. Technically, individual files of the repository may contain local declarations and parameters—say, a local redeclaration of `classic` in one of the foundation files, or an uninterpreted parameter in the file on $\Pi^1_1$-comprehension (on which see § 1.5). These should be distinguished from the fundamental logical axioms of the theory: a local declaration of the already accepted `classic` adds nothing new, and a declared parameter is not a logical axiom of choice or of infinity. ToS has two fundamental logical axioms.

Special precision is needed here, because $L4$ is easily mistaken for the Axiom of Choice. `L4_witness` is *not* an axiom of choice in the set-theoretic sense in which choice is the simultaneous extraction of representatives from a *completed family* of sets: the Axiom of Choice takes a whole family of nonempty sets at once and gives each of its members its own representative; $L4$ extracts a witness from *one* existential statement. In the *ontological* sense of ToS this is precisely the distinction needed: $L4$ says that a single existence is determinate—if something is, it is something identifiable—and does not sanction a completed simultaneous choice over an arbitrary collection.

But it would be inaccurate to say that `L4_witness` “does not allow choice” or is “immeasurably weaker than the Axiom of Choice” in the usual technical sense. In its form—a polymorphic passage from `exists` to `sig`, from a proof of existence to the pair “witness plus proof”—`L4_witness` is a principle of indefinite description, and in the type-theoretic sense it has *choice-like* strength: given a family of existence proofs, one can build from it a function that outputs a witness for each index. The chapter therefore distinguishes two things. The ontological Axiom of Choice is a completed simultaneous choice over a completed family; $L4$ does not sanction such a choice, and in this sense ToS does not use it. The technical strength of `L4_witness` as a principle of indefinite description, however, is real, and it should not be passed off as something “immeasurably weaker than any choice.”

What is essential is something else: neither the Axiom of Infinity nor the set-theoretic Axiom of Choice is among the foundations of ToS. A separate file of the repository is devoted to this—`ProcessAxiomAudit.v`.[^5]
Here again honesty is needed about *what* this file does. `ProcessAxiomAudit.v` is *not* an automatic dependency crawler, not a theorem that mechanically runs through the whole repository. The file itself states that it relies on the results of the `Print Assumptions` command, run separately; inside Rocq it *records and formalizes the summary* of this audit—it classifies the dependencies of the key results and fixes meta-classifications. Its theorem `axiom_minimal` is formalized *documentation* of the conclusion “the formalization is axiomatically minimal: no Axiom of Infinity, no Axiom of Choice, no univalence axiom, no axiom of functional extensionality”—not a scanner that would itself verify this conclusion by enumeration. It should be read as a documented meta-audit based on `Print Assumptions`. With this caveat, the summary is as follows: the results of the process part of the formalization depend only on `classic`, and only rarely on $L4$, with $L4$ localized in one file devoted to the variational principle. So the ToS preprint that speaks of “the single axiom `classic`” and the file `ToS_Axioms.v`, which declares two axioms, do not contradict each other: the process part really does manage with $L3$ alone, while $L4$ belongs to the foundations and is hardly needed in process mathematics.

Let us sum up the formal status. $P4$ is not an axiom. In the file `ProcessFourPrinciples.v` the formal trace of $P4$ is *defined* (as the predicate `P4_formalized`) and *proved* (by the theorem `P4_holds_formalized`); the proof relies only on `classic` and process arithmetic. When the chapter says that $P4$ is “proved in Rocq,” exactly this is meant: what is proved is the machine-checkable process trace of the principle—the predicate `P4_formalized`—not the whole ontological thesis. To see *where* the principle comes from in substance—from which starting points of ToS it follows—let us pass to the next section.

## Where $P4$ Comes From

### Derivation from the Laws of Logic

$P4$ is *derived*—from starting points already accepted in Part I. The exposition of ToS gives this derivation a precise form: in the very section 2.2.4 from which the formulation of $P4$ is taken, the principle is derived from two laws of logic—$L1$ and $L5$—and the derivation takes six
steps.[^6]

Its course is as follows. By $L5$ (Order, the hierarchical dimension), every level must be completed before operations at the next level up begin: completion means that all the elements of level $n$ are determinate before the operations of level $n+1$ proceed. Distinction, as Part I established, is an *act*—not an instantaneous ready fact but an operation that is performed. Suppose now that some system at moment $t$ has infinitely many elements; this would mean that infinitely many distinctions have already been completed. But each distinction is an act; an infinite number of completed acts would require either an infinite elapsed time (which contradicts the words “at moment $t$”) or an infinite number of acts completed in finite time without sequential order (which contradicts $L5$). Consequently, at any moment $t$ only finitely many distinctions have been completed—every system at a moment is finite. And infinity enters as a quality of the *process*: the process of adding elements has no bound—for every $n$, $n+1$ is reachable—but at no moment is the process complete. This is $P4$, and this is exactly its formulation from § 1.1.

$P4$ is thus a *substantively derivable* consequence of starting points already accepted: the derivation of section 2.2.4 obtains it from $L1$ and $L5$, adding nothing to the foundations of ToS. But a caveat must be made at once, without which the word “derived” would mislead. This derivation is *substantive*, philosophical-methodological; it is carried out in the exposition of ToS, not in Rocq. The Rocq formalization does *not* reproduce the chain $L1 \land L5 \Rightarrow P4$ as a proved theorem. The file `ProcessFourPrinciples.v` does not derive $P4$ from the laws of logic—it proves the formal process predicate `P4_formalized` (through the constant process and the closure lemmas, § 1.2.2); moreover, in this file $P4$ is characterized as *independent*—the theorem `P4_independent` establishes the existence of a Cauchy process at any level regardless of the other principles. So “is derived” here and “is proved in Rocq” in § 1.2 are two different statements about two different levels (see the table of § 1.2.3): the first concerns the ontological derivation of the principle, the second the machine-checkable process trace. The chapter keeps them apart and does not pass one off as the other.

With this caveat, the present section does not repeat the formal derivation step by step—the substantive derivation is given above—but shows the same thing in another way: $P4$ is the application, to the case of the infinite, of three positions that the volume has developed from the very beginning—operational divisibility, the understanding of the set as a mode of consideration, and the principle of positive existence. The three positions are three facets of the same thing that the formal derivation extracts from $L1$ and $L5$. Let us examine each.

### Operational Divisibility: Atomicity Is Relative

The first position is operational divisibility. Part I, analyzing the structure of a system, showed that *atomicity is relative*: to be an element, something simple and indivisible, is not an absolute property of an object but its position relative to the existing state of the system of distinctions. One and the same object is taken as an element at one level of consideration and at another is opened up as a system of parts. Divisibility is not a property that an object possesses once and for all; it is performed—in an act that draws a new distinction within what was previously simple.

Let us apply this to infinite division. Completed infinity, in one of its guises, is the demand that *all* the distinctions within some object be drawn *at once*—that infinite divisibility be not a process but an existing fact, the ready result of all divisions together. But operational divisibility says precisely that divisibility is an act, not an existing fact. One cannot “have already drawn” an infinite number of distinctions; distinction is performed, and every concrete performed distinction is finite. $P4$ is the application of this position to the limit: absolute, completed infinite divisibility is impossible not because it is difficult, but because “completed” contradicts “divisibility as an act.”

### The Set as a Mode: The List Is Prior to the Set

The second position is the understanding of the set as a mode of consideration. Part I drew a distinction between the *list* and the *set*. The list is primary: it is a sequence of elements written out in order, as it was built. A set is a list taken in a special mode—a mode in which order and multiplicity are deliberately forgotten, in which the operator has agreed to look only at membership. A set is not a separate entity alongside the list; it is the list seen from a certain angle.

Completed infinity implies “an infinite list composed in its entirety.” But composing a list is a process: the elements are written out one after another. The position “the set as a mode” shows that an infinite set, too, is thinkable only as a mode of consideration of some list—and an infinite list is a process of writing out that does not complete. $P4$ is an application of this position as well: the process of composing an infinite list *never* completes, and therefore a “completed infinite set” is a mode of consideration of a nonexistent object—a ready infinite list.

### Positive Existence: To Be Is to Be Actualized

The third position is the principle of positive existence. ToS understands existence positively: to exist is to be actualized through an act—to be the result of a performed distinction, not to passively “be on hand” in a ready universe of objects. This principle has a direct consequence for the infinite. An infinite collection of acts “already actualized simultaneously” is impossible: acts are performed in a hierarchy, one after another, sequentially. “All acts at once” is not a big act—it is no act at all, but a refusal to understand existence as an act.

Here $P4$ is closest to its source. If to exist is to be actualized, and actualization proceeds step by step, then “completed infinity” demands the impossible: an infinite number of actualizations carried out not step by step but at once. $P4$ is a direct consequence of the positive understanding of existence, applied to infinite cases.

### $P4$ as a Specialization of the Accepted Starting Points

The three positions converge on one thing. Operational divisibility: divisibility is an act, and infinite divisibility-as-a-fact is impossible. The set as a mode: an infinite set is a mode of consideration of an infinite list, and that list is a never-completing process. Positive existence: to be is to be actualized, and an infinite collection of simultaneous actualizations is impossible. Each of the three, applied to the case of the infinite, yields one and the same: infinity enters mathematics as a scheme of construction, not as a completed object. This is $P4$.

$P4$ is thus a *specialization of three already accepted positions* to the case of infinity—and, in the substantive derivation of section 2.2.4, a consequence derivable from $L1$ and $L5$. The volume notes that the starting points laid down in Part I have a definite consequence concerning the infinite, and gives this consequence a name. At the same time—recall the caveat of § 1.3.1—two levels must be kept apart: *in substance*, $P4$ is derived from the three positions and from $L1, L5$; *formally*, what is proved in Rocq is not this derivation but the process predicate `P4_formalized` (§ 1.2.2). At neither level is $P4$ a separate axiom: it is either derived in substance or appears as a proved process trace. A principle that discloses what is already laid down in the foundations requires of the reader no separate trust beyond what has already been given to the laws of logic of Part I: $P4$ is in this sense *free*—it costs exactly as much as the starting points already accepted, and not a jot more.

## Where $P4$ Has Already Been at Work

### A Principle Recognized in Retrospect

$P4$ receives a developed formulation only in this chapter—but it began to work in the volume much earlier. This is a pedagogical move usual for ToS: a principle first acts in concrete analyses, on live material, and the reader sees it at work; and only when it has already been recognized in several independent places is it given an explicit definition. Thus the reader comes to the definition not empty-handed but with a stock of cases that the definition generalizes. Let us gather these cases.

### The Natural Number Series as an Inductive Type (Part II)

The earliest and purest appearance of $P4$ is in Part II, in the construction of the natural number series. The natural number series was introduced there not as a set but as an *inductive type*: a rule is given—zero is a number, and every number is followed by a number—and the natural numbers are exactly what this rule generates.

This is already $P4$ in action, though its name has not yet been spoken. An inductive type is a scheme of construction, not a completed object. Every concrete natural number—a hundred, a thousand, any given one—is accessible: it is built in a finite number of applications of the rule. “All the natural numbers as a ready, gathered set” do not figure in this picture at all—not because they have been forgotten, but because the inductive type does not presuppose them. Rocq realizes this directly: the natural number series `nat` is an inductive type, and every argument about all natural numbers—every sum, every limit, every check of convergence—goes through the induction principle, not through an appeal to “the set of all naturals.” The induction principle is a rule of inference; it does not require the natural numbers to be gathered together anywhere. Part II, in building counting, already stood on $P4$.

A precise caveat is needed, however. Formally, `nat` *exists*—as a type of the Rocq language, and one can quantify over this type: the notation “for every $n : \texttt{nat}$” is perfectly legitimate. ToS does not deny this formal fact: the type `nat` exists. ToS gives up only one *reading* of this type—the reading on which `nat` would be the completed actuality of all natural numbers, a ready, gathered set. Here `nat` is understood as an inductive scheme of generation and reasoning; the quantifier “for every $n$” is read as a reference to this scheme, to the induction principle, not to a survey of a ready infinite collection. This distinction—between a type as a scheme and a type as a completed set—will be important throughout Part IV.

### Non-Completion as Ontology (Part I)

Even earlier—in Part I—$P4$ was present in the form of a general ontological motif that can be called non-completion. Part I, analyzing the act of distinction and the hierarchy of levels, pursued the thought that a process does not have to complete into a ready object in order to be full-fledged—that non-completion is not a flaw, not a missing result, but a *positive* ontological feature. An object that unfolds and does not fold up into a point is not “worse” than a completed object; it is of another kind.

This directly prepared $P4$. If non-completion is a full-fledged way of existing, then infinity-as-a-scheme (which precisely does not complete) needs no justification by reference to a completed object. Part III already made explicit use of this: $\sqrt{2}$ was analyzed there as a process that does not fold up into a ready point and is full-fledged in this very not-folding-up. Non-completion, from an ontological motif of Part I, became a working instrument of Part III—and both rested on what is now called $P4$.

### Data versus Behavior (Part III)

The third return is to Chapter III.3, to the distinction between data and behavior. Analyzing the countability of the rational numbers, that chapter separated two things: *data*—a finite ready record that can be presented in its entirety—and *behavior*—the capacity to answer requests, which is never presented in its entirety but shows itself on demand. A rational number is data: a pair of integers, a finite record. A process is behavior: a rule that answers the request “the value at step
$n$.”

Chapter III.3 showed that countability is a property of data, not of behavior: finite records are enumerable, and the Calkin–Wilf traversal of the rational numbers enumerates precisely them. To the space of behaviors the notion of a traversal does not apply in the same sense in which it applies to finite data—and precision is needed here, because *computable* behaviors, given by programs, are precisely *enumerable*: they can be traversed as programs. Uncountability concerns not the computable processes but the *space of all process behaviors* $ℕ \to ℚ$ (or the corresponding class of Cauchy processes): it has a status different from that of finite data. This distinction is $P4$ taken from the side of epistemology: a completed object would be data, a finite ready thing; infinity-as-a-scheme is behavior. When Part IV, in the following chapters, proves the uncountability of processes, it will rely on exactly this—and Chapter 4.4 will draw the distinction between the enumerable computable processes and the uncountable space of process behaviors with all the necessary care. The root is here, in Chapter III.3, and this root is
$P4$.

### Irrationals as Processes (Part III)

The fourth and most direct return is to Chapter III.4, which immediately precedes this one. That chapter showed that $\sqrt{2}$ is not a position on the rational marking, not a ready point lying somewhere apart from the fractions approximating it, but a *process*: an unfolding sequence of rational approximations. Chapter III.4 analyzed this process into its composition—as a functional system with rules, roles, and elements—and showed, on the example of two different processes, that the process representation of $\sqrt{2}$ does not have to be unique: different rules of approximation can coincide in the first steps and diverge further on, behaving differently in the quality of approximation. The stronger thesis—that all the processes giving $\sqrt{2}$ form a single open class, equivalent with respect to some equivalence relation on processes—Chapter III.4 did not prove; it is a program of further formalization and will be expressed through the equivalence relation on processes in the subsequent chapters of Part IV.

This is $P4$ almost at full strength, but still on one particular example—on one irrationality. Chapter III.4 showed $P4$ at work; the present chapter formulates it; the next, Chapter 4.2, generalizes it—it builds the *process in general* as a type, for which $\sqrt{2}$ was only the first sample. So Chapter III.4 is the immediate bridge: it left the exposition exactly where the principle had to be named and the construction generalized.

### What the Returns Show

The four returns—to the inductive `nat` of Part II, to the non-completion of Part I, to the distinction of data and behavior in Chapter III.3, to the number-process of Chapter III.4—show one thing. $P4$ is not introduced in this chapter for the first time; it is only *named* here for the first time. The principle has worked in the volume since the very construction of the natural number series; it acted in four independent places, on different material, and every time in one and the same way: the infinite was taken as a scheme, not as an object. The chapter does not ask the reader to believe in a new assumption; it shows the reader that they have already seen $P4$ at work four times, and now only draws a line under what has been seen.

## $P4$ and the Classical Axioms

### Dispensability and Incompatibility

It is customary to say that $P4$ *cuts off* a number of axioms of standard mathematics—the Axiom of Infinity, the Axiom of Choice, and others. This is true, but the word “cuts off” is vague, and the vagueness is dangerous here. It can mean at least two different things: either “the formalization of ToS manages without this axiom—it is simply not needed,” or “$P4$ is *incompatible* with this axiom—one cannot accept both at once.” These are two different statements, and the second is strictly stronger than the first.

The Rocq formalization of ToS contains both layers—and contains them separately, as two generations of files. Moreover, it documents this difference itself: one of the files describes directly in its header *what changed* between the generations.[^7]
The present section analyzes both layers in order: first the early one, the layer of *dispensability* (§ 1.5.2–1.5.3), then the later one, the layer of *incompatibility* (§ 1.5.4–1.5.5), and in § 1.5.6 it shows how they relate. To say hastily “$P4$ rules out the Axiom of Choice” is to lump the two layers together and to lose the precision that the formalization actually achieves.

### The First Layer: The Axiom Is Not Needed

The early layer of the formalization is represented by a group of files with a common name of the form `P4_Eliminates_*`—one for each axiom.
Each such file proves a statement of one and the same kind: the work for the sake of which standard mathematics introduces the given axiom is performed in the $P4$ ontology *without* it—by means that $P4$ provides anyway. The axiom is not refuted; it turns out to be *superfluous*. Let us call this layer the layer of dispensability and analyze it on the example of four axioms.

*The Axiom of Infinity.* The file `P4_Eliminates_Infinity.v` shows that everything for the sake of which the Axiom of Infinity is introduced is done through the inductive type `nat`.[^8]
The file builds and proves the induction principle (as a built-in rule, not an axiom), partial sums, a convergence predicate, strong induction, the factorial, and the boundedness of a finite list. The final theorem `P4_eliminates_Infinity` is *not* a negation of the Axiom of Infinity; it is a *conjunction of four positive facts*: the induction principle works, every $n$ is finite, the factorial of five equals one hundred twenty, the partial sum of the first natural numbers is computed. The meaning of the theorem is exactly “here is a demonstration: all this works, and the Axiom of Infinity was not needed for it.” The axiom is not refuted—it is shown to be unnecessary.

*The Axiom of Choice.* The file `P4_Eliminates_AC.v` is arranged in the same
way.[^9]
In the $P4$ ontology every set at stage $N$ is a finite list—a process taken up to step $N$. Choosing a representative from a finite nonempty list requires no axiom: one can take the *first* element—the head of the list. This is the $L5$ resolution: canonical choice in the order of construction. The file proves lemmas of finite choice, a finite version of Zorn’s lemma (the maximum of a list), and a theorem on choice over a finite front: for a fixed finite $N$ and nonempty lists $F(n)$ with $n < N$, the choice function is built explicitly—as taking the head.[^10]
With this, choice at the level of dispensability is exhausted: for a finite front the axiom is not required. The same file also has a theorem without a restriction on $N$—for the family `family` indexed by *all* natural numbers; its status is subtler, and the chapter will return to it in § 1.5.5. Here let us fix what is beyond dispute: for the choice that the $P4$ ontology actually makes—choice from finite lists on a finite front—the Axiom of Choice is not needed.

*Transfinite recursion.* The file `P4_Eliminates_ATR.v` takes arithmetical transfinite recursion—in reverse mathematics, an axiom.[^11]
The file declares an inductive type of ordinals—with constructors for zero, successor, and limit—and transfinite recursion is defined as an ordinary `Fixpoint` function over this type. Rocq’s termination checker accepts it as structural recursion. The upshot: transfinite recursion is not an axiom but a *definition*. What reverse mathematics postulates is, in the $P4$ ontology, simply written down as a function.

*Comprehension by second-order formulas.* The file
`P4_Eliminates_Pi11.v` analyzes $\Pi^1_1$-comprehension—the scheme that separates out a subset by a formula with a quantifier over all functions from the natural numbers to the natural numbers.[^12]
The file introduces a $P4$-restricted *reading* of functional quantification: instead of a quantifier over all functions $ℕ \to ℕ$, a quantifier over program codes $c : ℕ$ is taken, and the function is recovered through the parameter `eval_program` (“run code $c$ on input
$n$”). Under this reading the quantifier “over all functions” reduces to the quantifier “over all codes $c$”—to ordinary arithmetical quantification over the natural numbers—and $\Pi^1_1$-comprehension yields an arithmetical analogue of the corresponding arguments.

A precise caveat is needed here, and the chapter insists on it. The file does *not* prove that every classical function $ℕ \to ℕ$ has a program code—there is no such statement in it. It *redefines the mode* of quantification over functions as quantification over codes; this is a $P4$-restricted reading, not a theorem that the class of all functions coincides with the class of programs. And `eval_program` here is neither a proved statement nor a defined function but an *uninterpreted declared parameter*: a constant without a definition, corresponding to a universal Turing machine and allowing one to speak of programs inside Rocq without building an interpreter. The chapter notes this for precision—and because the other three files of the layer of dispensability manage entirely without such declarations.

### What the Layer of Dispensability Has in Common

The four files are arranged on one pattern. None of them proves the negation of an axiom. Each takes the work for the sake of which the axiom is introduced—the generation of the natural numbers, the choice of a representative, transfinite recursion, the separation of a subset—and performs this work by the means of the $P4$ ontology: an inductive type, the head of a list, a `Fixpoint` function, a program code. The upshot in all four cases is the same: *the axiom is not needed*. This is the early layer—the layer of *reinterpretation* (as the formalization itself calls it): $P4$ provides an alternative, and the axiom becomes superfluous.

The layer of dispensability is valuable, but it has a limit. It says: “here is how to do without the axiom.” It does *not* say: “the axiom cannot be accepted together with $P4$.” Logically it leaves open the possibility that the axiom can nevertheless be added—there is simply no reason to. This remaining possibility is closed by the second layer.

### The Second Layer: The Axiom Is Incompatible

The later layer of the formalization is represented by files with names of the form
`P4Prohibits*` and the core common to them—the file `P4CompletedInfinity.v`.[^13]
This layer proves not dispensability but *incompatibility*: $P4$ and completed infinity together lead to a contradiction. Let us examine how exactly this is arranged—and where the boundary of what is proved runs.

The file `P4CompletedInfinity.v` introduces three definitions. A *completed infinite set* is a predicate $S$ on the natural numbers for which *every* $n$ is a member of $S$ (symbolically: $\forall n, S(n)$). *$P4$ stage-boundedness* is a property of “actuality”: at every stage the number of actual elements is bounded above by some ceiling. The *bridge* is a condition connecting these two pictures: if $n$ is a member of the completed set, then $n$ is actual already at stage zero.

And then the central theorem, `completed_inf_contradicts_P4`, states: a completed infinite set, $P4$ stage-boundedness, and the bridge together lead to a contradiction. The proof is short and transparent. $P4$ stage-boundedness gives a concrete ceiling for stage zero—some number $B$. The completed set, by definition, contains *every* natural number—in particular, the number $B+1$. The bridge makes $B+1$ actual at stage zero. But the ceiling says that everything actual at stage zero does not exceed $B$—that is, $B+1 \le B$. Contradiction.

### The Axiom of Choice in the Second Layer

How exactly the incompatibility extends to the Axiom of Choice is shown by the file `P4ProhibitsAC.v`.[^14]
The Axiom of Choice over the natural number series is the statement that for every family of nonempty lists indexed by the natural numbers there exists a choice function. The file observes: such a choice function is *itself* a completed infinite object—its graph (the collection of pairs “index, chosen value”) is total, defined for every natural index. The theorem `ac_implies_completed` proves this: from the Axiom of Choice over the natural number series follows the existence of a function whose graph is a completed infinite set. And then—by the theorem of the preceding paragraph—together with $P4$ stage-boundedness and the bridge, a contradiction results.

Precision is needed here, and the chapter insists on it. The file
`P4ProhibitsAC.v` does *not* prove the closed statement “the Axiom of Choice is false.” It proves: the Axiom of Choice yields a completed infinite object; and a completed infinite object *together with* $P4$ stage-boundedness *and* the bridge is contradictory. This is a *conditional* theorem: the contradiction arises when all three premises are present. Its strength lies in the fact that $P4$ stage-boundedness is a direct formalization of $P4$, and the bridge is a natural condition connecting “being a member” with “being actual.” But it is still a statement relative to the *internal definitions* of the formalization (“completed set,” “stage-boundedness,” “bridge”—as they are written in `P4CompletedInfinity.v`), not the statement “the Axiom of Choice is contradictory in Zermelo–Fraenkel theory.” The formalization proves a strictly defined, honest, and strong thing—and exactly that, no more.

Here too the apparent tension between the two files on choice—the early `P4_Eliminates_AC.v` and the later `P4ProhibitsAC.v`—is removed. The early one proves that choice is *not needed* (the head of the list); the later one, that choice is *incompatible* (it yields a completed infinity). Is this not a contradiction? No, and the resolution is subtle. The point lies in the *mode of reading* the choice function. The finite theorem `P4_eliminates_AC_finite` (§ 1.5.2) speaks of a finite front $N$: here the choice function is a finite object, and the question is settled. But `P4_Eliminates_AC.v` also contains a theorem for a family indexed by *all* natural numbers. Such a total choice function can be read in two ways. If it is read as a process *rule*—a prescription that outputs a choice for any *presented* index—it is $P4$-compatible: each request receives a finite answer, and there is no completed object. If it is read as a completed *graph*—a total collection of pairs $(i, f(i))$ for all $i$ at once, gathered into one—we land exactly in the mode of `P4ProhibitsAC.v`: such a graph is a completed infinity, and together with stage-boundedness and the bridge it yields a contradiction. The difference between the two files, then, does not reduce to “a finite list versus an infinite family”; it lies in the mode of reading the choice function itself: a process rule or a completed graph. $P4$ keeps the first and cuts off the second.

### How the Two Layers Relate

The formalization of ToS also records how the two layers relate—with the file
`P4ProhibitionSynthesis.v`.[^15]
In substance the relation is this: the layer of incompatibility is stronger than the layer of dispensability—if something is incompatible with $P4$, then $P4$ thereby already supplies an alternative to it, since the impossible has to be replaced by something; the converse is false—the presence of an alternative does not mean that the original is incompatible.

The file also contains a theorem with a telling name—`prohibition_implies_reinterpretation`. But here it is important not to overrate it. In its formulation it states: *if* completed infinity is incompatible with $P4$-boundedness given the bridge, *then* potential infinity holds. In its proof, however, it is arranged simply: it does *not use* the premise—it proves the conclusion directly, returning the lemma on the existence of potential infinity already proved in the repository (`potential_inf_exists`). Therefore `prohibition_implies_reinterpretation` is not a formalization of a *nontrivial logical dependence* “exclusion entails reinterpretation.” It is rather a synthetic *summary*: a documented record of the fact that the repository *has* a prohibition theorem and *separately* has a proved alternative (potential infinity). It should not be presented as a nontrivial proof of logical entailment; the substantive relation of the layers—the one stated in the previous paragraph—is true, but it is grounded in reasoning, not in this particular theorem.

Let us bring the two layers together. When the chapter says that $P4$ *cuts off* the Axiom of Infinity or the Axiom of Choice, it means exactly the following. First (the layer of dispensability): the work of these axioms is performed in the $P4$ ontology without them—by an inductive type, the head of a list, a `Fixpoint` function, a program code; this has been checked by the four files `P4_Eliminates_*` and confirmed by the audit `ProcessAxiomAudit.v`. Second (the layer of incompatibility): completed infinity—in the form in which it is formalized by the predicates of `P4CompletedInfinity.v`—is *incompatible* with $P4$ stage-boundedness in the presence of the bridge; and the Axiom of Choice over the natural number series yields precisely such a completed infinity. These are conditional theorems relative to the internal definitions of the formalization—strong and honest, but conditional all the same. What the chapter does *not* assert is that a closed “the Axiom of Choice is false,” in the sense of set theory, has been proved in Rocq. The cutting off is real and formally checked; its exact meaning is set by two layers, not by a slogan.

## What $P4$ Leaves

### Cutting Off and Preserving: Two Sides

§ 1.5 showed what $P4$ cuts off. It is natural to read this as an impoverishment: mathematics loses axioms, and therefore loses possibilities. The present section shows that this reading is wrong. $P4$ cuts off completed infinity—but everything done in mathematics *without* appeal to completed infinity, and that is the overwhelming part of it, remains in full force. And the same file of the formalization that proves incompatibility proves preservation right alongside: the theorem `P4_preserves_three` establishes that $P4$ is *compatible* with three things—potential infinity, finite choice, and inductive types. Cutting off and preserving are two sides of one principle, and the second must be presented as distinctly as the first.

### Natural Numbers, Integers, Rationals

First of all, $P4$ leaves the whole construction of Parts II and III in force. The natural number series is an inductive type, a scheme of construction; it is not only compatible with $P4$, it is the exemplary instance of what $P4$ allows infinity to be. The integers are a two-sided coordinate marking built over the natural number series; the rational numbers are a commensurable marking with a fractional step. None of these constructions appeals to completed infinity: every integer, every rational number is a finite record built in a finite number of steps. Everything Part III proved about the integers and the rational numbers—including their enumerability—stands unshaken under $P4$. Enumerability, moreover, is a property that $P4$ precisely clarifies: it speaks of the presence of a traversal procedure, that is, of a scheme, not of a ready, gathered set.

### Finite Collections and Induction

$P4$ leaves finite collections—entirely and without reservations. A finite list can be taken as a ready object: it *is* a ready object, and its construction completes. A set as a mode of consideration of a finite list is legitimate. Choosing a representative from a finite nonempty list is legitimate; it is taking the head (§ 1.5.2). $P4$ restricts the *completedness of the infinite*, not completedness as such; the finite completes by its very nature.

$P4$ also leaves induction—entirely. The induction principle is a rule of inference: to prove a statement for all natural numbers, it suffices to prove it for zero and to prove the step. This rule does not require the natural numbers to be gathered into a ready set; it requires only the scheme of their construction, and the scheme is the inductive type. Strong induction, recursion, definitions through `Fixpoint`—$P4$ leaves all of this, and the file `P4_Eliminates_Infinity.v` (§ 1.5.2) is a direct demonstration: induction, recursion, partial sums, the factorial—all work, and work without the Axiom of Infinity.

### Constructive Proofs of Existence

$P4$ leaves proofs of existence—but in a definite form. Under $P4$, to prove that something exists is to *present* this something: to point out a witness, give a construction, describe the rule by which the object is built. This is the content of $L4$ (§ 1.2.4): from a proved existence a witness is extracted. A proof of existence “by presentation” is fully compatible with $P4$, because the presented witness is a finite object or a finitely described scheme.

What $P4$ does not leave is proofs of existence “by the impossibility of absence” in the form in which the witness is not presented and cannot in principle be presented. But this restriction is milder than it seems: ToS keeps $L3$ (the Law of Excluded Middle) (§ 1.7 will analyze this in detail), and therefore reasoning by contradiction remains available. $P4$ touches not the Law of Excluded Middle but only the appeal to completed infinity as an *object* over which reasoning is conducted. The overwhelming majority of classical proofs of existence are either already constructive or translate into constructive form—and remain in force.

### Processes and Analysis

Finally—and this is the main thing for the whole rest of the volume—$P4$ leaves processes. A process is a function from the natural numbers to the rationals, a scheme unfolding step by step; it is the very form in which $P4$ allows the infinite to be. Everything built on processes, $P4$ does not merely tolerate—it is its foundation.

And analysis is built on processes. Chapter III.4 has already shown how $\sqrt{2}$ becomes a process and how convergence and the Cauchy property are defined operationally; the following parts of the volume will unfold differentiation, integration, series, and the solution of differential equations on this foundation. The ToS repository already has a considerable process corpus of analysis—files on the intermediate value theorem, the extreme value theorem, the Bolzano–Weierstrass and Heine–Borel theorems, and others. The detailed status of each of these results—what exactly is proved, which definitions it rests on, which logical means it uses—should be analyzed in the corresponding chapters of the volume, and the chapter will not run ahead here. For § 1.6 one thing is essential: the process ontology does not destroy analysis but gives it working material. The analysis that classical mathematics usually conducts over a completed continuum, the $P4$ ontology conducts over processes. One should not expect every formulation to carry over verbatim: some definitions and theorems take on a modified, operational form in process analysis—but in substance analysis remains analysis, and its material, by the analysis of § 1.5, becomes sturdier, not poorer.

### What the Cutting Off Costs

Let us draw up the balance. $P4$ leaves: the natural numbers, integers, and rationals; finite collections and operations on them; induction, recursion, strong induction; constructive proofs of existence; processes and the whole of analysis built on processes. This is not a remainder that survived the cutting off, but the *main body* of mathematics. $P4$ cuts off completed infinity—an object that on closer inspection (§ 1.5) turns out to be either unnecessary or incompatible with the accepted ontology. What is cut off, in other words, is not a working part of mathematics but a definite assumption about the nature of the infinite—an assumption without which the working part stands perfectly well. What exactly is lost in the process, and why the loss is not burdensome, is the subject not of the present chapter but of Chapter 4.6, which closes Part IV; here it is enough to say that the balance of cutting off and preserving comes out decisively in favor of preserving.

## $P4$ and Brouwer’s Intuitionism

### What the Comparison Is For

$P4$ has an important historical predecessor—the intuitionist program in the foundations of mathematics, begun by Luitzen Brouwer at the beginning of the twentieth century and developed afterward by Arend Heyting and others. The comparison with it is no tribute to erudition: it clarifies the place of ToS more precisely than any description from within. Intuitionism was the first in modern times to refuse to regard completed infinity as ontologically primary—and therefore, having seen *where* ToS converges with intuitionism and *where* it diverges, the reader will also see what is distinctive in the position of ToS.

### Where $P4$ Converges with Intuitionism

There are three points of convergence, and they are essential.

*The first is the refusal of completed infinity as primary.* Brouwer insisted that the infinity of mathematics is an infinity of becoming, not of being—a potential infinity, not an actual one. This is exactly the thesis of $P4$: infinity as a scheme, not as an object. In refusing the completed infinite, $P4$ and intuitionism coincide almost word for word.

*The second is constructivity.* Intuitionism requires a proof of existence to present the object: “exists” means “here it is, built.” ToS requires the same—this is the content of $L4$ and the general spirit of the $P4$ ontology (§ 1.6.4). To prove existence is to give a construction.

*The third is suspicion of the Axiom of Choice.* Intuitionism traditionally rejects the Axiom of Choice in its full form precisely because it postulates simultaneous choice over an infinite family—a completed infinity of choices. ToS comes to the same conclusion—and comes to it, as § 1.5 showed, through a formalized analysis: full choice yields a completed infinite object incompatible with $P4$.

On all three points ToS and intuitionism are allies. And the understanding of mathematics as an *activity*, as a process of construction rather than the description of a ready, eternal reality, is also common to them.

### Where $P4$ Diverges from Intuitionism

But there is also a divergence, and a deep one—so deep that the two positions are usually considered incompatible. The divergence concerns the attitude toward the *Law of Excluded Middle*.

Brouwer rejects the Law of Excluded Middle. For an intuitionist, the statement “$P$ or not-$P$” has no right to be considered true until $P$ is proved or not-$P$ is proved; as long as neither has been built, there is no ground for the disjunction. Intuitionistic logic is therefore nonclassical: neither the Law of Excluded Middle in its full scope nor double-negation elimination holds in it.

ToS *accepts* the Law of Excluded Middle. Moreover, it accepts it not as an additional axiom-concession but as one of the five laws of logic derived in Part I from a single starting point. Part I showed: the act of distinction that separates $A$ from not-$A$ is by its very nature *exhaustive*—it leaves no third region assigned neither to $A$ nor to not-$A$. This exhaustiveness of the completed act of distinction is the Law of Excluded Middle, $L3$. In Rocq it enters as the axiom `classic` (§ 1.2.4) precisely because the Rocq system is constructive by design, and $L3$ is built on top of it; but in ToS $L3$ is not arbitrary—it is a theorem about the arrangement of distinction.

### $P4$: Constructivism with Classical Logic

Hence the exact characterization of the position of ToS: *it is constructivism with classical logic*. With intuitionism ToS shares a constructive ontology: infinity is potential, existence requires a witness, there is no completed infinite. What distinguishes ToS from intuitionism is classical logic: the Law of Excluded Middle is kept.

This combination is rare—constructive ontology and classical logic are usually considered to pull in different directions. ToS shows how these two attitudes can be *separated by levels*. The key lies precisely in the distinction of levels. $L3$ is a law about the *completed act of distinction*: once the act is performed, $A$ is separated from not-$A$ exhaustively. $P4$ is a principle about *infinite collections*: infinity does not complete into an object. These two statements concern different things—one the act, the other the collection—and therefore need not collide. One can hold classical logic at the level of individual completed acts of distinction and at the same time hold a constructive, process ontology at the level of the infinite. Intuitionism rejected $L3$ because it tied it precisely to completed infinity—to “a survey of all cases.” ToS separates what intuitionism tied together, and can therefore take from intuitionism its constructive ontology without paying for it by giving up classical logic.

It is worth stating what this reasoning does *not* assert. It does not claim a metatheorem of consistency—that a formal system with classical logic and a process ontology is provably free of contradictions. Such a statement would be a strong metatheoretical result, and the chapter does not make it. What is said is more modest and more precise: *within* the ToS frame the two attitudes are assigned to different levels—logic answers for the completed act of distinction, ontology for infinite collections—and at these different levels they have nothing to conflict over.

In the landscape of the foundations of mathematics ToS therefore occupies a place of its own—between classical formalism, for which completed infinity is the primary material, and intuitionism, for which classical logic is unacceptable. ToS takes logic from the first and ontology from the second, and shows that such a combination is free of contradiction. A detailed placement of ToS among the other approaches to foundations is the subject of Chapter 4.6; here it is enough that this place exists and that it is distinctive.

## The Bridge to the Construction of the Process

### What Follows from $P4$

$P4$ has been formulated verbatim, derived in substance from $L1$ and $L5$, recognized in the earlier work of the volume, analyzed from the side of what it makes superfluous and what it is incompatible with, and related to intuitionism. It remains to ask: what *follows* from all this for the construction of number?

What follows is this. If every system at a moment is finite, and infinity is a property of process, then in the $P4$ ontology a real number should not be read as a ready point of a completed line. The familiar picture thinks of a real number as a point: $\sqrt{2}$, $\pi$, $e$—each is a ready point on the completed number line, and the decimal notation only approximately names this point. But the completed number line is a completed infinity—an uncountable set of ready points gathered into one—and $P4$ does not make such an object the original ontological bearer.

This is an *ontological* statement, and its boundaries are worth outlining at once. The chapter does not say that the point picture is false or that it must be expelled from mathematics. It says that the point cannot be the *original* bearer: what is originally given is the process, and the familiar point is recovered *later*—as an equivalence class of processes, as a mode of consideration into which the operator passes when there is a need to abstract from the differences between processes that give one and the same limit. The $P4$ ontology does not abolish the point but *rearranges* it: from a primary object it becomes a derived mode. How exactly this is arranged is the subject of Chapter 4.3; here it is only important that “a real number is not a ready point” does not rule out the point but indicates its true, derived place.

### What Is Possible Instead of the Point

What, then, is possible? Exactly what Chapter III.4 has already shown on $\sqrt{2}$: a *process*—a sequence of rational approximations unfolding according to a rule. A real number in the $P4$ ontology is a process, not a point; a scheme, not a completed object; behavior, not data. Chapter III.4 established this for one irrationality and analyzed it into its composition. Part IV must now take the general step: build the *process in general* as a full-fledged type of the formalization—one for which $\sqrt{2}$ was only the first sample, and the twelve patterns from `ProcessFourPrinciples.v` (§ 1.2.2) only the first twelve.

In the Rocq formalization of ToS this type is called `RealProcess` and is defined—extremely simply—as the type of functions from the natural numbers to the rationals, `nat -> Q`. To each step $n$ the process assigns a rational approximation. The simplicity of the definition is not accidental: it directly expresses $P4$. The natural numbers are an inductive type, a scheme; the rational numbers are finite records; a function between them is a rule that gives a finite answer to the request “step $n$.”

And here is the chapter’s last caveat about precision. Technically, `RealProcess := nat -> Q` is, in Rocq, a type of *total functions*: a term of this type assigns a value to *any* $n$, not only to those already requested. It would be wrong to say that there is “nothing completed at all” in `RealProcess`. ToS reads such a term *operationally*: as a rule that outputs a rational value for a presented $n$—and in this operational reading the process is a scheme, not a collection. The precise statement is therefore this: `RealProcess` is not a completed *set* of rational values in the set-theoretic sense—there is no completed infinity as a ZFC object in it; but in the formal language of Rocq it is precisely a functional object, a type of total functions, and the $P4$ ontology rests on the *operational reading* of this object, not on denying that it is a function type. It is with this caveat that the words about `RealProcess` being $P4$ written as a type definition should be understood: it is $P4$ under the operational reading of a function as a rule.

### E/R/R Analysis: Infinity as a Scheme, Not an Object

Before passing to the construction, let us consolidate by an E/R/R analysis (Part I) *how* $P4$ is arranged in the labeling of elements, roles, and rules. This chapter analyzes not a number system but a *principle*, and the analysis here is less about composition and more about which *level* of the labeling $P4$ holds. The caveat on status is stricter than usual and repeats the three levels of $P4$ (§ 1.2): the ontological thesis; its machine-checkable *trace* `P4_formalized` (proved); and the conditional
prohibition layer (theorems under precise definitions of completed infinity). We conduct the analysis in the ontological order
Rules $\to$ Roles $\to$ Elements.

*Rules* (the principle $P4$). $P4$ is the *constitution of the level of elements*: infinity enters mathematics *as a scheme*—the rule “zero is a number; every number is followed by a number,” applicable without end—and not *as an object*, a ready, gathered “all” (§ 1.2.3). In substance $P4$ is derived from $L1$ and $L5$ (§ 1.3), but precisely *in substance*: the chain
$L1\land L5\Rightarrow P4$ is not proved in Rocq, while the trace of $P4$ (`P4_formalized`: Cauchy processes exist and are closed under arithmetic) is proved independently. The prohibition layer adds: under a precise definition of a completed infinite object, such an object is incompatible with $P4$ (`P4_Eliminates_Infinity`: `nat` is a rule of induction, not a ready set), and the choice function *as a rule* is compatible with $P4$, while *as a completed graph* it is not
(§ 1.5).

*Roles—the significance of positions* (the law $L4$). Infinity receives the role of a *scheme*—a potentially extendable rule, not an existing collection. Every stage plays the role of a *finite actualization*. And the *point* (a ready real number) under $P4$ turns from a primary object into a *derived role*—an equivalence class of processes, a mode of consideration (Chapter 4.3): $P4$ does not abolish the point but moves it to its true, derived place.

*Elements—the bearers* (the law $L1$ and $P4$ itself). Only *finitely actualized* objects remain bearers: every natural number is constructible in a finite number of steps, every stage of a process is a finite rational record. There is no completed infinite object at the level of elements. A caveat of precision (§ 1.8.2): the type `RealProcess := nat -> Q` in Rocq is a type of *total* functions; $P4$ rests on the *operational* reading of the term (a rule giving an answer for a presented $n$), not on denying that this is a function type.

Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| $P4$: infinity as a scheme, not an object | constitution of the elements | Rule |
| the trace `P4_formalized` (Cauchy processes exist and are closed) | proved core | Rule |
| prohibition layer (`nat` is a rule, not a set) | conditional incompatibility | Rule |
| infinity is a scheme; the point is a derived mode | roles | Role |
| finite actualizations (stages, `nat`, records) | bearers (finite) | Element |
| laws $L1$–$L5$ (here $L1$, $L5$) | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous and here turns into the *root diagnostics* of the whole volume. To take infinity for an *object* (a completed set, a ready line) is a confusion of categories: a scheme-rule is read as an element-object. $P4$ is precisely the principle that rules out this confusion: it holds infinity at the level of *rules*, not of *elements*. And every particular diagnosis of the volume is a case of it: number is a role, not an object (Part II); the point is a class-mode, not an object (Chapter 4.3); uncountability is a rule about processes, not the size of a set (Chapter 4.4); a rational number is a class by `Qeq`, not a quotient object (Chapter III.2). The honest boundary: the three levels of $P4$ are not to be merged—what is proved is the *trace*
`P4_formalized`, while the full ontological thesis and the substantive derivation from $L1\land L5$ lie beyond any single Rocq theorem.

What the analysis yields. It lays the *foundation* of the whole of Part IV: since infinity is a rule-scheme, not an object, the real number is built as a *process* (Rule), not as a ready point (Element); and the point returns later as a derived role-class (Chapter 4.3). $P4$, analyzed by E/R/R, is the constitution under which the whole of process analysis unfolds—and the chapter now passes on to its plan.

### Where Part IV Is Going

Part IV is occupied with the construction and study of this type. Chapter 4.2 gives `RealProcess` a full definition—with arithmetic, with a metric, with the Cauchy condition that singles out the meaningful processes—and shows that this type arises not arbitrarily but as a structurally inevitable construction. Chapter 4.3 analyzes what a “point” is in the process ontology: the point turns out to be not an object but an equivalence class of processes—a mode of consideration into which the operator passes when there is a need to abstract from the differences between processes that give one and the same limit; the same chapter analyzes the famous equality of zero point nine repeating and one. Chapter 4.4 proves the uncountability of processes by a diagonal argument—and proves it as a consequence of the distinction of data and behavior, not as a riddle about the sizes of infinities. Chapter 4.5 reformulates the question of the continuum. Chapter 4.6 closes the part, drawing up the balance of what $P4$ cuts off and what it leaves, and placing ToS in the landscape of foundations.

The present chapter has been a philosophical-methodological introduction to all of this. It did not build the process—it justified the principle for the sake of which the process will be built. Now the principle $P4$ has been presented in full strength: formulated precisely, derived from the foundations, checked against the formalization, delimited from hasty readings. With this foundation Part IV can get down to work—and Chapter 4.2 begins it by giving the process the definition of a type.

*$P4$ is the principle of Finite Actuality: every system is finite at any moment, and infinity is a property of process, not of object. In substance it is derived from $L1$ and $L5$, and the three positions of the volume (operational divisibility, the set as a mode, positive existence) are its facets; that completed infinity “does not exist” is a conclusion from the principle, not the principle itself. In $P4$ three levels should be distinguished: the ontological principle; its formal process trace `P4_formalized`, proved in Rocq (Cauchy processes exist; sum and product preserve the Cauchy property); and the prohibition theorems, which show the incompatibility of completed infinity with $P4$ stage-boundedness under special definitions. These levels are a support of the principle, not its full equivalent. ToS has two fundamental logical axioms, $L3$ and $L4$; neither the Axiom of Infinity nor the set-theoretic Axiom of Choice is among them, which is recorded by a documented meta-audit. The formalization develops the relation of $P4$ to the classical axioms in two layers: dispensability (the work of an axiom can be done without it—shown for infinity, finite choice, transfinite recursion, and $\Pi^1_1$-comprehension) and incompatibility (completed infinity, as formalized, contradicts $P4$ stage-boundedness given the bridge—conditional but rigorous theorems). At the same time $P4$ leaves the main body of mathematics working: numbers, finite collections, induction, constructive proofs, processes, and process analysis. ToS is constructivism with classical logic—a combination possible because $L3$ speaks of the completed act of distinction, and $P4$ of an infinite collection; ToS separates these two attitudes into different levels. From $P4$ it follows that a real number is not originally a ready point—the point is recovered later as a mode of consideration of processes; what a real number is originally—a process—and how this process is built as a type is shown by Chapter 4.2.*

---

[^1]: The formulation of $P4$ is quoted from the work: Horsocrates, “Theory of Systems: A First-Principles Foundation for Mathematics” (PhilArchive, 2026), section 2.2.4. Quoted in the original English. The full derivation of the principle from the laws of logic, briefly set out below in § 1.3, is also given there.
[^2]: `ProcessFourPrinciples.v` of the ToS Rocq repository (directory `src/process/`); the file contains 25 proved statements, 0 `Admitted`, and inherits the single logical axiom `classic` (on which see § 1.2.4). The theorem names cited below come from this file.
[^3]: The type `ProcessInstance`, the list `all_instances`; the lemma `twelve_instances` proves that the list has length twelve, and the lemma `all_instances_nodup` that it has no repetitions.
[^4]: `ToS_Axioms.v` of the ToS Rocq repository (directory `src/`); 3 proved derived statements, 0 `Admitted`. The file is titled as declaring the fundamental logical axioms of the theory.
[^5]: `ProcessAxiomAudit.v` (directory `src/process/`), 13 proved statements.
[^6]: Horsocrates, “Theory of Systems” (PhilArchive, 2026), section 2.2.4, heading: “$P4$: Finite Actuality (derived from L1 $+$ L5)” and the six-step derivation that follows.
[^7]: `P4ProhibitionSynthesis.v` (directory `src/foundation/`); the introductory comment of the file contrasts the early layer (“$P4$ makes the axiom unnecessary”) with the later one (“$P4$ is incompatible with completed infinities”) and records that the second is stronger than the first.
[^8]: `P4_Eliminates_Infinity.v` (directory `src/foundation/`), 12 proved statements, 0 `Admitted`, 0 new axioms.
[^9]: `P4_Eliminates_AC.v` (directory `src/foundation/`), 0 `Admitted`, 0 new axioms.
[^10]: The theorem `P4_eliminates_AC_finite`: for every family `family` and every finite front $N$, if `family` $i$ is nonempty for $i < N$, then the choice of the head of the list lands in `family` $i$ for all $i < N$. This is a *finite*, stage-wise formulation of choice; it is precisely this formulation that is unconditionally compatible with $P4$.
[^11]: `P4_Eliminates_ATR.v` (directory `src/foundation/`), 15 proved statements, 0 `Admitted`, 0 new axioms.
[^12]: `P4_Eliminates_Pi11.v` (directory `src/foundation/`), 15 proved statements. Unlike the three preceding files, this file contains a declared parameter (see below).
[^13]: `P4CompletedInfinity.v` (directory `src/foundation/`), 12 proved statements, 0 `Admitted`, 0 new axioms. This is the core on which the files `P4ProhibitsAC.v` and `P4ProhibitsImpredicative.v` rely.
[^14]: `P4ProhibitsAC.v` (directory `src/foundation/`), 10 proved statements, 0 `Admitted`, 0 new axioms; it relies on `P4CompletedInfinity.v`.
[^15]: `P4ProhibitionSynthesis.v` (directory `src/foundation/`), 8 proved statements, 0 `Admitted`. The file proves `P4_prohibits_three` (incompatibility with three things: completed sets, the full Axiom of Choice, and [[Russells Paradox|Russell’s paradox]]) and `P4_preserves_three` (compatibility with three: potential infinity, finite choice, inductive types).

---

Part: [[04 Process Real Numbers|Part IV. Process Real Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/03 From Naturals to Rationals/04 From Position to Process|Chapter 4. From Position to Process—Part III]] · [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/02 RealProcess as a Type|Chapter 2. RealProcess as a Type]] →
