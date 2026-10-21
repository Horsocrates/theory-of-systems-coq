---
title: "Chapter 2. Counting as the Length of a List of Distinctions"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/02 Натуральные числа/02 Счёт как длина списка различий.md"
sourceBlob: db8369d8b0a0fb88f50629fcb485e18d3c7660dd
translated: 2026-10-20
status: draft
---

Chapter II.1 established by what one is primary: it is the number of the first act of distinction, the imprint of what has been performed. But the primacy of one is not yet the natural number series. To establish that counting begins with one, and to build the *whole* series of natural numbers from this one, are two different tasks. The first has been accomplished; the second is the subject of the present chapter and the three that follow.

ToS arrives at the natural number series by four paths, not one: the cardinal, the hierarchical, the informational, and the structural. That there are exactly four paths and that all of them lead to one and the same thing is no accident; the meaning of this multiplicity will be disclosed in Chapter II.5. The present chapter opens the first path, the *cardinal* one. It is the most direct: if one is one act of distinction, then the number $n$ is $n$ acts of distinction, and the form in which $n$ acts are taken as one number is the *list*. The cardinal path turns the intuition of § 1.6, counting as the recording of the number of performed distinctions, into a working formal construction.

## From One Act to Several

### What “Several Acts” Means

One is one act of distinction (§ 1.2). To build the number series from it, we must understand what *several* acts means, and understand it precisely, because a nontrivial step is hidden here.

“Two acts of distinction”: what is this? It is tempting to answer: two acts are simply an act and another act, placed side by side. But such an answer is insufficient, and its insufficiency is instructive. For us to have *two* acts rather than one, the first act and the second must be *distinguished*; otherwise they would merge into one, and the count would not move from one. And to distinguish the first act from the second is to perform *one more* distinction: the distinction between “the act already performed” and “the act being performed now.”

From this we see that counting is not a passive piling up of ready acts. Counting is itself an activity of distinction. To pass from one act to two, a new distinction is performed: the distinction of the acts themselves from one another. “Several acts” are possible *because* the act of distinction can be performed repeatedly, and each repetition, being a new act, can itself be told apart from the previous ones.

### The Repeatability of the Act

Let us name directly the property on which the whole cardinal path rests: the act of distinction is *repeatable*. Having performed the act, we can perform it again, and again. Nothing in the arrangement of the act limits the number of repetitions: the act of distinction is not “used up,” not “exhausted”; performing it does not close off the possibility of performing it once more.

Repeatability must be understood correctly; otherwise it gets distorted in one of two directions.

*Repeatability is not identical reproduction.* To repeat an act is not to obtain literally the very same act. The second act differs from the first already in that it is the *second*: it is performed relative to a state of affairs in which the first act *already* is. The repetition of the act of distinction itself creates a difference: a difference of order, the difference between “before” and “now.” If repetition yielded an identical act, no “two” would arise; it arises precisely because the repeated act occupies a *different* place in the order than the original one.

*Nor is repeatability the presence of a ready stock of acts.* To say “the act is repeatable” is not to say that all future repetitions already lie somewhere, an infinite stock of acts awaiting use. There is no ready stock. Repeatability is the *possibility of performing one more act*, not the *presence* of all acts at once. This distinction, between the possibility of continuation and the presence of something completed, is essential, and it will return in § 2.7 as the first working application of the principle $P4$. For now it suffices to note: “the act is repeatable” means “having performed $n$ acts, we can perform the $(n{+}1)$-th,” not “all acts have already been performed.”

### The Recursion of Counting

Putting together what has been said, we obtain the structure that lies at the foundation of counting.

There is the first act of distinction: one. It is repeatable: a second act can be performed. But the second act, in order to be the *second*, requires a distinction from the first, and this distinction is itself an act. And this act is repeatable too: we can pass to a third, which again will require a distinction from those already performed. The structure is *recursive*: each step of counting rests on the previous ones and generates the ground for the next.

This recursion is to be traced to its formal structure. The recursion of counting carries three features at once: there are *several* acts (multiplicity); they are *ordered*, there is a first, a second, an $n$-th (order, $L5$); and all of them together are taken as *one* number (unity). The structure in which these three features are joined is not chosen from a set of possible ones: it is *forced* by what the recursion of counting already is. Having traced where the recursion leads, the chapter will discover this structure; it will turn out to be the list. The chapter now passes to it, not choosing it but tracing the derivation up to it.

## The List as the Form of Multiplicity

### From Recursion to Structure

The chapter does not choose a form for the multiplicity of acts; it traces a derivation. The recursion of counting (§ 2.1.3) is already a certain structure; the task is to *recognize* it and give it a precise name, not to find a suitable container for it.

What the recursion of counting carries was established in § 2.1: the acts are performed *one after another* (repeatability, § 2.1.2); each next one is *ordered* relative to the previous ones, the second being second relative to the first ($L5$, § 2.1.1); and everything performed is taken as *one* number (§ 2.1.3). These features are what the recursion of counting *already is*, not wishes that a form ought to satisfy. The structure answering to them is therefore not chosen: it is *forced*. The chapter only reaches it along the derivation and names it.

The structure to which the derivation leads is the *list*. Below this is shown in several steps: first, that the set, the form of multiplicity familiar to mathematics, does not suit the primary cardinal path (§ 2.2.2); then, that the list *answers* to the derivation (§ 2.2.3); further, the same result is confirmed by analyzing both structures with the E/R/R apparatus (§ 2.2.4); finally, that the list answers to the derivation exactly, not approximately (§ 2.2.6). The analysis of the set here is a check, not a comparison of competitors from which the list emerges the winner: a check to make sure that what the derivation has discovered is precisely the list and nothing else.

### Why the Set Does Not Suit the Primary Path

The set is the form into which mathematics habitually gathers the many. To count a set is to find its cardinality; the natural number in the set-theoretic construction is precisely a cardinality, or a definite set (§ 1.1). Habit would suggest taking the set here as well. But for the *primary cardinal path* of ToS the set does not fit, and it does not fit on three independent grounds. Let us stress at once: the point is not that ToS banishes the set from mathematics. The set remains a fully legitimate mathematical object; it is *unsuited* only to the role of the *primary form* of the cardinal path, the structure in which counting is first carried out. What the set *is* in ToS (a mode of consideration derived from the list: the motif $M_3$, Chapter I.7) is said below; here we show why it cannot stand *at the foundation* of counting.

*The set is static.* A set is a gathering all of whose elements are given *at once*: $\{a, b, c\}$ is not “built” from $a$ to $c$; it is a ready collection. This is the ontology of the *ready-made*. But the derivation of ToS contains nothing ready-made at the primary level: at its foundation are the act and its repetition (Chapter I.7, processuality). The set would impose on the acts of distinction the status of a ready collection, which the derivation does not give them.

*The set carries no order.* In the set $\{a, b, c\}$ there is no first, second, or third element: $\{a, b, c\}$ and $\{c, a, b\}$ are one set. Order is indifferent to a set. But the recursion of counting (§ 2.1.1) is *ordered* by its very arrangement: the second act is second *relative to* the first, and without this “relative to” the very “two” does not arise. The structure to which the derivation leads carries order ($L5$); the set does not carry it, and therefore does not answer to the derivation.

*The set in ToS is derived.* Chapter I.7 introduced the motif $M_3$: sets in ToS are not primary; they are a *mode of consideration*, a way of taking something while abstracting from order and multiplicity. The natural number is an object that the derivation reaches *before* the mode; to build it through the set would be to place the derived before that from which it is derived. The order of justification would be violated.

The three grounds point to one thing: the set is not the structure in which the cardinal path can *begin*. This is because the recursion of counting carries order and processuality, while the set as a primary form carries neither, not because the set is “bad” (as a mode of consideration it is fully legitimate: § 1.8.5, $M_3$). The set is excluded *neither* from the mathematics of ToS *nor* as an admissible object; it is excluded only as the *primary form of the cardinal path*. Later, as a mode of consideration of the list, it legitimately arises in ToS; but it cannot stand at the *foundation* of counting.

### Why the Derivation Leads to the List

That the derivation excludes the set does not yet indicate where it leads. What indicates it is the following: the structure answering to the recursion of counting is free of all three mismatches, and this structure is the list.

*The list is sequential.* A list is not given at once; it is built: element by element, each attached to what has already been built. The empty list, the list of one, of two: these are stages of construction, not ready collections of different sizes. The list is an ontology of *process*, and therefore it is consistent with the processual nature of the act of distinction: as acts are performed one after another, so the elements of a list are added one after another.

*The list carries order.* A list has a first element, a second, an $n$-th; the list $[a, b, c]$ and the list $[c, a, b]$ are different lists. Order is not ascribed to a list from outside as an additional structure; it is part of what a list *is*. And this order is exactly $L5$: the law of order, derived in Chapter I.3, receives its working form here. When we say “three distinctions,” the list holds not only their number but also the fact that they come *first, second, third*, and this, as § 2.1 showed, is the condition of the very “three.”

*The list introduces no ready collection.* A list of $n$ elements does not presuppose a “set of all the elements” as a separate entity; it is simply the result of $n$ acts of attachment. There is no passage to the mode $M_3$, no appeal to what is derived. The list remains at the same level of primacy as the act whose imprint it is.

*The set is a static collection of the ready-made, indifferent to order and derived by $M_3$; for holding an ordered sequence of performed acts it carries the wrong structure. The list is sequential, ordered ($L5$), and introduces no ready collection. Therefore the form of the cardinal path is the list, not the set.*

### The List and the Set in the E/R/R Analysis

What has been said can be seen more distinctly if we analyze the list and the set with the apparatus that Chapter I.4 provided for every system: the E/R/R analysis. Chapter I.4 established that every system has three inseparable aspects, *Elements* (the substrate of the system), *Roles* (the positions that the elements occupy), and *Rules* (what holds the system together as a system), and that ontologically they are generated in the order Rules $\to$ Roles $\to$ Elements. Let us apply this analysis to the list and to the set; nothing new about E/R/R is introduced here; only what has already been given is applied.

**The list as an E/R/R system.** A list of distinctions, analyzed by the three aspects, gives the following. *Rules*—the rule of succession: every element except the first stands immediately after one definite element. This rule is precisely the working form of $L5$, the law of order. *Roles*—the positions that the rule of succession opens: “first,” “second,” “$n$-th”; the role here is articulated, there are as many positions as elements, and each differs from the others by its place in the succession. *Elements*—the distinctions themselves, occupying these positions. The three aspects are at hand and inseparable: a rule of succession without positions would be an empty scheme, positions without distinctions would be unfilled, distinctions without positions would be a heap without order. The list is a *complete* E/R/R system: all three aspects work in it.

**The set as an E/R/R system.** A set of the same distinctions, analyzed by the three aspects, gives something different. *Elements*—the same distinctions. *Roles*—but here the role is *single* and unarticulated: “member of the set”; all elements bear one and the same role, and no position differs from another. *Rules*—and here precision is needed. It would be wrong to say that a set has *no* Rules aspect at all: a set has its own rules, the rule of membership (what it is to be an element) and the rule of extensional identification (two sets are equal when they have the same elements), and in developed theories rules of formation as well. The Rules aspect does not vanish in a set. What vanishes is *one definite* rule, the *rule of succession*, the one that holds order in a list: “every element except the first stands after one definite element.” Comparing with the analysis of the list, we see exactly what has happened: *in the set it is precisely the rule of succession that is suppressed, not Rules in general; in its place remain the rules of membership and of extensional identification*. And together with the rule of succession, following the generating order Rules $\to$ Roles $\to$ Elements, the articulation of Roles disappears: with no rule of succession there are no ordered positions either; there remains one common role, “member,” and the substrate under it.

**What can be seen from this.** The set is not a system alien to the list. But it would be imprecise to say that the set is the *same* list: one and the same collection of values is obtained from *different* lists; $(a,b,c)$, $(c,b,a)$, $(a,a,b,c)$ all give one set $\{a,b,c\}$. It is more precise to say that the set is the *support* of a list: the result of forgetting what these lists differ in, namely order and multiplicity. The transition is conveniently presented in two steps:

$$
\text{List}(A) \;\longrightarrow\; \text{Multiset}(A)
  \;\longrightarrow\; \text{Set}(A).
$$

The first step forgets *order* (list $\to$ multiset), the second *multiplicity* (multiset $\to$ set). This is exactly what the motif $M_3$ meant (§ 1.8.5): the set as a mode of consideration of the list that abstracts from order and multiplicity. The E/R/R analysis gives the first step a precise form: the passage from list to multiset is the suppression of the rule of succession, of that aspect of Rules which held order.

And then it is clear why the derivation of counting leads precisely to the list. The recursion of counting (§ 2.1) *essentially* carries the rule of succession: the second act is second *in succession* after the first. The structure to which the derivation leads must have a rule of succession. The list has this rule; the set is the same structure with the *rule of succession* suppressed (the rules of membership and identification remain). A derivation that requires succession leads to the list, to a system in which the rule of succession works; the set cannot answer to it, because in the set exactly the rule that the derivation requires has been suppressed, not because it is “poorer” in general.

*In the E/R/R analysis the list is a complete system: Elements are distinctions, Roles are ordered positions, Rules is the rule of succession ($L5$). The set is the same list with the rule of succession suppressed, whereby the articulation of roles is reduced to one common role, “member”; this is precisely the mode $M_3$. The derivation of counting carries the rule of succession and therefore leads to the complete system, the list.*

### The List as the Imprint of the Repeatable Act

It is worth seeing how exactly the list answers to the recursion of counting from § 2.1.3: so exactly that the list can be called the direct *imprint* of the repeatable act.

The repeatability of the act (§ 2.1.2) says: having performed an act, we can perform one more. A list is arranged in the same way: having a list, we can attach one more element to it. The operation of attaching an element to a list is the formal analogue of performing one more act of distinction. To the first act corresponds the list of one element; to the second act, the attachment of a second element; and so on.

And the recursiveness coincides. Counting is recursive (§ 2.1.3): each step rests on the previous ones. A list is recursive by its very arrangement: a list is either the empty list or an element attached to a list, a definition in which the list refers to the list. The recursion of counting and the recursion of the list are one and the same recursion, and therefore the list is more than a *suitable* form: it is a form that exactly reproduces the structure of what is counted.

That the list is arranged recursively is a formal property as well as a substantive one: the induction principle, to which the chapter will come in § 2.6, is rooted in this recursiveness. For now let us note only that the derivation has been brought to its structure: the recursion of counting is the list. It remains to give the list a precise formal notation and, through it, to define what “the number $n$ is in the system” means. This is the subject of the next two sections.

## The Technical Predicate: `distinction`_`count`

### The List of Distinctions and Length as an Act of Tallying

The derivation has led to the list as the structure of the multiplicity of acts (§ 2.2). Let us give this a precise notation.

The act of distinction is recorded in ToS as `Distinction` (Chapter I.2). A list of acts of distinction is, accordingly, an object of type `list Distinction`: a list whose elements are distinctions. Such a list is the imprint of some number of performed acts: to a list of $n$ distinctions correspond $n$ performed distinctions, taken in their order.

The cardinal path leads to number through the *length* of such a list, and precision is needed here; otherwise a presupposition alien to ToS will slip into the construction. The length of a list is *not* a property inherent in the list as a ready object, something that “lies” in the list and only remains to be “read off.” At the primary level ToS knows nothing ready-made in which properties lie in advance (Chapter I.7, processuality; § 1.7.2: every characteristic is a performed distinction). The length of a list *is the result of an act*, the act of tallying: an act that goes through the list distinction by distinction and registers how many performed acts it has met in it. Length is not *inherent* in the list; it is *obtained* when the act of tallying has been performed.

This is a direct continuation of § 1.6: to count is to record the number of performed distinctions. The length of a list of distinctions is exactly this recorded number: how many performed acts the tally registers after going through the list. The concept of length thus brings nothing new into ToS: it is the application of counting-as-recording to the list. Formally the tally is written by the function `length`; but this function does not “read off a number inherent in the list”; it *produces* a number as the outcome of going through the list. It is through the length of a list of distinctions, through this outcome of the tally, that the first formal concept of the present chapter is introduced.

### The Definition of `distinction`_`count`

ToS introduces a predicate connecting a natural number $n$ with the lists of distinctions whose tally gives $n$. Formally it is written as follows:[^1]

```coq
Definition distinction_count (n : nat) : Prop :=
  exists Ds : list Distinction, length Ds = n.
```

Let us read the definition. `distinction`_`count` is a *predicate* on the natural numbers: to each $n$ it assigns a proposition (`Prop`). The proposition is this: *there exists a list of distinctions whose length equals* $n$. The predicate `distinction`_`count`\;$n$ is true if such a list exists, and false otherwise.

It is essential what this definition is *not*. It is not a redefinition of the natural number: $n$ here is an already available natural number of type `nat`, and the predicate only *asserts something about it*. Nor is it the statement “the number $n$ equals the length of a list”: the predicate does not equate $n$ with a length; it *asks about the existence* of a list of the required length. `distinction`_`count` is precisely a predicate: a characteristic that a number either has or does not have.

### Zero and the Empty List

Let us apply the definition to zero: an instructive case, and instructive precisely in how zero behaves in it.

Is `distinction`_`count`\;$0$ true? By the definition this means: does there exist a list of distinctions whose tally gives zero? Such a list exists: it is the empty list, the list without a single element. Formally this is witnessed:

```coq
Lemma zero_distinctions : distinction_count 0.
Proof. exists []. reflexivity. Qed.
```

The proof presents the empty list (`[]`). But here it is important to read correctly what exactly happens when it is tallied; otherwise zero will be misunderstood.

Tallying is the act of going through a list while registering the performed acts met (§ 2.3.1). And length is the outcome of a performed tally. Let us apply this to the empty list.

The query “what is the length of the empty list?” is a query about the outcome of a tally, and this query is *legitimate*: its object, the empty list, is a formed system (E/R/R, § 2.2.4), a full-fledged structure of type `list Distinction` to which tallying applies. A sufficient reason ($L4$) for the act of tallying *is* present here: the ground is that the object of the query is a list. The tally is legitimately performed, and in going through the empty list it meets not a single element. Therefore its outcome is $0$: not the positive length of a series of performed acts but the *boundary result* of a correctly performed tally, recording that no distinctions were met.

What, then, is zero? Zero here is not the number of what has been performed; it is the *value of a tally that ended without meeting an element*. The tally took place (there was a ground: the object is a list), went through the list to the end, and met not a single act, and its outcome was $0$. This is exactly the zero of Chapter II.1: a *boundary mark*, the result of a tally that makes manifest the absence of distinctions met (§ 1.3.2), neither an object nor a property nor a positive count of what has been performed. The empty list carries no “positive length”; it is the imprint of the fact that *nothing* has been performed, and zero is the outcome of the tally that registered this fact.

Here it is worth answering a question that arises by itself: why does a query for the length of the empty list give *zero* rather than an *error*? The difference between the two outcomes is not accidental, and it clarifies the nature of zero. A query ends in an error when it is *meaningless*: when it addresses a quality that the object lacks even in principle. To ask for the length of something that is not a list at all, an act or a number, is to ask a question that has no logical connection with its object; such a question has not merely “received no value”: it had no right to be asked, and the answer to it is an error. A query for the length of the empty list is *not of this kind*. The empty list *is* a list, a formed system for which tallying is defined. A query addressed to it is *meaningful* and *executable*: the tally is legitimately performed and runs to the end. Its outcome, $0$, is a full-fledged result, not a refusal: the tally went through the list and registered that no elements were met. That is why the empty list gives zero and not an error: the tally is defined and executed (hence not an error), but no distinctions were met (hence not a positive value but the boundary zero). An error would lie beyond the boundary of a meaningful query; zero stands *within* it, as the legitimate outcome of a tally that met not a single act.

Here it is useful to name directly the formal fact on which everything rests. The function `length` is *total*: to every list term, including `nil`, it assigns a term of type `nat`, and `length nil` reduces computationally to `0`; that is why `zero`_`distinctions` is provable. This is not a side circumstance that ontology has to “work around”; on the contrary, it is precisely the formal side of what has been said: the tally of the empty list is defined and its result is $0$. The ontological reading only *names* this $0$: as the boundary outcome of a tally that met no elements, not as a “measured positive length.” Syntax returns the term `0`; ontology reads this `0` as the boundary of the series of positive lengths, not as a positive count of what has been performed.

The three senses in which $0$ appears here are conveniently distinguished by a table:

| Level | What $0$ is |
|---|---|
| the type `nat` | the constructor `O`, the base point of the type |
| the function `length` | the result of tallying the empty list (`length nil` reduces to `0`) |
| the ontology of ToS | the boundary of positive counting: the outcome of a tally that met not a single performed act |

The first two levels are formal and indisputable; the third is an ontological reading that does not dispute the first two but only *names* the obtained $0$ a boundary, not a positive count.

From this we see that the fact that `distinction`_`count`\;$0$ is true does *not* mean that zero is the number of performed acts of distinction. Chapter II.1 (§ 1.3) established the opposite: zero is not a count of performed acts. There is no contradiction here, and seeing why matters for the whole chapter.

`distinction`_`count`\;$0$ is true, and legitimately true: the list `nil` exists, its tally is defined, and `length nil` is `0`. But *what* is witnessed by this is “there exists a list whose tally legitimately ended without meeting a single element, and the outcome of this tally is zero,” not “there exists a list whose tally gave the positive length zero.” To witness the *boundary outcome of a tally* is not the same as to *count what has been performed*. The empty list is a list in which *nothing has been performed*, not a list in which “zero acts have been performed” as some substantive event. It contains no performed distinction; there is only a tally that went through the list and met no elements, with the outcome zero. `distinction`_`count` honestly records this outcome, but what it records is precisely the boundary result of a tally, not a positive count of what has been performed.

### The Technical Layer

What has been said puts `distinction`_`count` in a quite definite place: on what Chapter I.6 called the *technical layer* of formal work.

`distinction`_`count` answers a technical question: for which $n$ does there exist a list of distinctions whose tally gives $n$? This is a question about lists and the outcomes of tallying them, about which outcomes of tallying are attainable at all. The question is legitimate and necessary: there is no doing without the tallying of lists. But it is *not* a question about the count of performed acts of distinction. `distinction`_`count` does not carry the ontological load of a count of what has been performed: it registers the outcome of a tally, including the outcome “nothing was met,” abstracting from the fact that a list of distinctions is the imprint of *performed* acts.

This is exactly why `distinction`_`count` alone, by itself, does not constitute the cardinal path. The cardinal path leads to the natural number series as the imprint of *performed distinctions*, and the count of what has been performed, as Chapter II.1 established, begins with one, and zero does not enter it. `distinction`_`count`, for which being true at zero is only the boundary outcome of tallying the empty list, does not fit this role: it answers a different question, about tallying in general, not about the count of performed acts.

*`distinction`_`count` is a technical predicate: it reports for which $n$ there exists a list of distinctions whose tally gives $n$. For zero it is true, but true because tallying the empty list legitimately gives the result $0$, not because zero is the number of performed acts. This is a registration of the form of data, not a count of what has been performed. The cardinal path requires a different predicate: one that counts performed acts and therefore begins with one.*

ToS introduces such a predicate; the chapter passes to it, and through it to the cardinal path proper, in the next section.

## The Ontological Predicate: `distinction`_`count`_`from`_`one`

### What the Technical Predicate Lacks

The technical predicate `distinction`_`count` (§ 2.3) reports for which numbers there exists a list of distinctions of the required length. For the cardinal path this is not enough, and the shortfall lies in exactly one thing: the technical predicate counts the *length of a list*, whereas the cardinal path must count *performed acts of distinction*.

The difference is not verbal. Tallying the empty list legitimately gives the result $0$ (§ 2.3.3): the tally is defined, went through the list, and met not a single element. There are no performed acts in the empty list: the empty list is the imprint of the fact that *nothing* has been performed. The technical predicate `distinction`_`count` credits zero as the boundary outcome of tallying the empty list; the cardinal path, counting *performed acts*, finds not a single performed act in the empty list and therefore begins with one, with the first performed distinction. Chapter II.1 (§ 1.3) established this as an ontological proposition; now it must receive a formal predicate that answers to it.

### The Definition of `distinction`_`count`_`from`_`one`

ToS introduces such a predicate, the predicate of the count of performed acts. Formally it is written as follows:[^2]

```coq
Definition distinction_count_from_one (n : nat) : Prop :=
  exists Ds : list Distinction, length Ds = n /\ 1 <= n.
```

The predicate `distinction`_`count`_`from`_`one` differs from the technical `distinction`_`count` by one added condition, $1 \le n$. Let us read it: a number $n$ satisfies the predicate if there exists a list of distinctions of length $n$ *and moreover* $n$ is not less than one. The first condition is the same as in the technical predicate: the existence of a list of the required length. The second, $1 \le n$, is precisely the formal record of the fact that the count of what has been performed begins with one.

Precision is needed here about what this predicate *formally* is. As written, `distinction`_`count`_`from`_`one` differs from the technical predicate *only* by the conjunct $1 \le n$, nothing more. It does *not* check that the elements of the list are precisely “performed acts”; it keeps no history of their performance; it does not distinguish stages; it does not require the acts to be pairwise distinct. Formally it is a *positivity filter*: a predicate that cuts off the zero boundary and lets through every $n \ge 1$ for which a list of the required length exists. Therefore its ontological meaning, the count of *performed acts of distinction*, is not contained in the formal record alone; it is set by the *interpretation* of the chapter, which reads a list of distinctions as the imprint of performed acts. The formal record and the ontological reading work together here: the record separates the positive count from the zero boundary, and the interpretation endows this positive count with the meaning of a count of what has been performed.

The added condition is small in appearance and essential in meaning. It draws the boundary established in Chapter II.1: zero is the boundary of the series, not a count of performed acts (§ 1.3). The technical predicate did not draw this boundary and credited zero; `distinction`_`count`_`from`_`one` draws it. This is what allows it to be read *ontologically*: as a predicate answering the question “how many acts of distinction have been performed,” not the question about the lengths of lists in general. Let us stress once more: this ontological reading itself is the work of interpretation, while the formal contribution of the predicate consists in the condition $1 \le n$, which separates the positive count from the zero boundary.

### Zero Drops Out, One Enters

Let us see what the predicate `distinction`_`count`_`from`_`one` says about two boundary cases, zero and one. About each, exactly what the ontology of Chapter II.1 requires is established; the formal record of these statements is given below.

**Zero is not a count.**

```coq
Theorem zero_not_a_count :
  ~ distinction_count_from_one 0.
Proof.
  intro H. destruct H as [_ [_ Hge]]. lia.
Qed.
```

The theorem `zero`_`not`_`a`_`count` asserts: the predicate `distinction`_`count`_`from`_`one` does *not* hold for zero. The proof is short: if zero satisfied the predicate, $1 \le 0$ would be among the conditions, and this is false, so the tactic `lia` closes the case. In substance the theorem says: zero is not a count of performed acts of distinction. Not “a list of length zero does not exist” (it does exist, § 2.3.3), but precisely this: zero is not the number of *what has been performed*, because in zero there is nothing performed.

**One is the first count.**

```coq
Theorem first_count_is_one :
  distinction_count_from_one 1.
Proof.
  exists [distinction_of True].
  split; [reflexivity | lia].
Qed.
```

{

The theorem `first`_`count`_`is`_`one` asserts: the predicate holds for one. The proof presents a list of one distinction, `[distinction_of True]`, a list with a single element, and checks two conditions: its length equals one (`reflexivity`), and $1 \le 1$ (`lia`). Both hold. One is the first count of performed acts: a list of one performed distinction corresponds to it.
}

Together the two results outline the beginning of the cardinal path exactly as Chapter II.1 described it: zero drops out of the count of what has been performed, and one is the first number of this count. What in § 1.3 was an ontological proposition has here become a proved pair of theorems.

The difference between the two predicates is conveniently summarized in a table:

| Predicate | Formal record | What it counts | Zero |
|---|---|---|---|
| `distinction_count` | `exists Ds,` `length Ds = n` | the technical length of a list | admits |
| `distinction_count_from_one` | `exists Ds,` `length Ds = n` `/\ 1 <= n` | the positive count of acts (under the ontological reading) | excludes |

The table makes the nature of the difference explicit: formally it reduces to a single conjunct, $1 \le n$, and in substance to the boundary between the tallying of lists in general and the count of what has been performed, which begins with one.

### What “the Number Is in the System” Means

The predicate `distinction`_`count`_`from`_`one` makes it possible to say precisely what the presence of a natural number means in ToS.

The number $n$ *is in the system* of ToS insofar as there exists a list of $n$ performed distinctions and $n \ge 1$. Not “the number $n$ is given as an element of a ready set” and not “the number $n$ is postulated by an axiom,” but: the number $n$ is, insofar as it is *realizable* as the imprint of $n$ performed acts of distinction.

This is an ontological move, and it is worth naming it directly. The being of a number in ToS is being *through realization*. A number does not lie ready-made; a number is insofar as a list of distinctions realizing it can be presented. The existence of a number is made dependent on the possibility of its realization by acts of distinction, exactly as the existence of everything in ToS is made dependent on the act ($A = \exists$, Chapter I.1).

From this we see in what sense the cardinal path is a *path to* the natural number series and not its postulation. The path does not declare $\mathbb{N}$ ready-made; it shows how each natural number *receives being* in ToS: through realization by a list of performed distinctions. It remains to show that this path can be traveled for *every* natural number, that there is no number that would fail to be realized. This is the content of the next section.

*`distinction`_`count`_`from`_`one` is the predicate of the cardinal path: formally it is a positivity filter (the existence of a list of length $n$ with $n \ge 1$), and under the ontological reading of the chapter it is the count of performed distinctions. A number $n$ satisfies it if there exists a list of $n$ distinctions and $n \ge 1$. Zero does not satisfy it (`zero`_`not`_`a`_`count`); one does (`first`_`count`_`is`_`one`). To be a number in ToS is to be realizable as the imprint of performed acts of distinction.*

## The Realizability of Every Number

### What Remains to Be Shown

The previous section established what the presence of a number in ToS means: the number $n$ is in the system insofar as it is realizable as the imprint of $n$ performed acts of distinction, as a list of $n$ distinctions for which $n \ge 1$ (§ 2.4.4). This is a definition of presence. But a definition by itself does not yet guarantee that the *whole* natural number series is present.

Indeed, the predicate `distinction`_`count`_`from`_`one` might turn out to hold only for *some* numbers. What was proved in § 2.4 so far covers one (`first`_`count`_`is`_`one`). And the rest? Is two realizable, that is, does there exist a list of exactly two distinctions? And the number one hundred? And a number written with a thousand digits? The cardinal path will be a path to the *natural number series* only when it has been shown that *no* natural number drops out: for every $n \ge 1$ a list of $n$ distinctions is realizable.

This is what is to be shown. The statement toward which the section is heading is this: for any $n \ge 1$ the predicate of counting from one holds. ToS establishes it as a theorem; formally it is written as follows:

```coq
Theorem positive_nat_is_distinction_count : forall n,
  (1 <= n)%nat -> distinction_count_from_one n.
```

Let us read it: whatever the natural number $n$, if $n \ge 1$, then $n$ satisfies the predicate of counting from one: a list of $n$ distinctions is realizable. The section analyzes *how* this is established and what follows from it.

### The Increment Step: One More Distinction

The realizability of every number rests on one simple step, the step of *increment*. It is the formal imprint of the repeatability of the act (§ 2.1.2): having performed some number of acts, we can perform one more.

ToS writes the attachment of a new distinction to a list as follows:

```coq
Definition add_distinction (Ds : list Distinction) (D : Distinction) :=
  D :: Ds.

Theorem add_distinction_increments : forall Ds D,
  length (add_distinction Ds D) = S (length Ds).
```

The first of the records given, `add`_`distinction`, places the new distinction $D$ at the *beginning* of the list $Ds$; technically this is `D :: Ds`, attachment at the head. This calls for a caveat about order. In the prose of the chapter the acts are performed “first, second, third” in the chronological sense; but `D :: Ds` puts the new act at the head of the list, not at its end. Therefore the list of distinctions is more conveniently read here as a *stack*: the head holds the *last* performed act, the tail the earlier ones. This does not affect the length, and the cardinal path needs precisely the length, but it matters for the interpretation of order: under this reading, “the first element of the list” is the act latest in time. If a chronological left-to-right reading is needed somewhere, it is given by the alternative operation of attachment at the end of the list (`snoc`); the cardinal path of the present chapter does not need it, since it rests on length, not on the direction of order.

The theorem `add`_`distinction`_`increments` checks something obvious and essential: tallying the incremented list gives one more than tallying the original. To attach a distinction is to increase the count by one. This is precisely the formal record of the fact that to perform one more act of distinction is to make the count larger by one.

**What distinguishes the repetitions of the act.** Here it is worth removing one possible puzzlement. In the formal proofs, lists of distinctions are built from *one and the same* canonical element: `first`_`count`_`is`_`one` presents `[distinction_of True]`, and `succ`_`is`_`new`_`distinction` attaches `distinction_of True` to an already available list. A list of three distinctions is thus `[distinction_of True; distinction_of True; distinction_of True]`: three *occurrences* of one value. Hence the novelty of an act is encoded here *not* by a difference of content: two elements of a list can be one and the same canonical distinction. Their difference as acts is given by *position*, the occurrence in the list: the first occurrence and the second occurrence are different repetitions of the act, even when their inner content coincides. This agrees with Chapter II.1 (§ 1.3, where the novelty of an act was given by repetition, not by a difference of value) and rests directly on the Law of Order $L5$: it is order and position, not the content of an element, that make a list of three repetitions a list *of three* rather than of one. Counting counts occurrences, and therefore it is the repeatability of one act, not a variety of contents, on which the cardinal path rests.

Hence the key step of the cardinal path: if the number $n$ is realizable, then the number $n + 1$ is realizable too. ToS establishes this as follows:

```coq
Theorem succ_is_new_distinction : forall n,
  distinction_count_from_one n ->
  distinction_count_from_one (S n).
```

`succ`_`is`_`new`_`distinction` says: the realizability of $n$ implies the realizability of $n + 1$. The proof is direct: take a list realizing $n$ and attach one more distinction to it; the incremented list realizes $n + 1$. In substance the theorem says what Chapter II.1 would call the passage to the next number: *the next number is the present one plus one more performed act*. The operation of succession is the performance of a new distinction, not an ascription from outside.

### From One to Every Number

Now both parts are at hand. One is realizable: this is `first`_`count`_`is`_`one` (§ 2.4.3); a list of one distinction has been presented. And every passage from $n$ to $n + 1$ preserves realizability: this is `succ`_`is`_`new`_`distinction` (§ 2.5.2). Joining these two gives the realizability of every number.

ToS establishes the joining by the theorem `positive`_`nat`_`is`_`distinction`
_`count`; its proof is arranged as follows. An arbitrary $n \ge 1$ is taken. If $n$ is one, realizability is given directly (`first`_`count`_`is`_`one`). If $n$ is greater than one, it is $n' + 1$ for some $n' \ge 1$; by the assumption $n'$ is realizable, and then by `succ`_`is`_`new`_`distinction` $n$ is realizable too. Thus realizability, having one as its beginning, *reaches* every $n \ge 1$.

*Every natural number is realizable: for every $n \ge 1$ there exists a list of $n$ performed distinctions. This rests on two propositions (one is realizable, and the passage from $n$ to $n + 1$ preserves realizability), whose joining carries realizability from one to any number.*

A caveat about the status of what has been proved is necessary here. The formal theorem `positive`_`nat`_`is`_`distinction`_`count` works *within* the already available type `nat`: it takes an arbitrary `n : nat` and shows that for $n \ge 1$ there exists a list of distinctions of length $n$. Therefore the theorem does *not* create the type of natural numbers anew and does not build `nat` from `Distinction`; it shows that every positive value of the *already given* type `nat` is *realizable* as the length of a list of distinctions. The result is a realization result, not a type-forming one: ToS does not claim to derive the type `nat` itself; it claims that the cardinal path can be traveled for every positive `nat`. This answers a possible objection, “you use `nat` to build `nat`”: `nat` as a type is taken ready-made from Rocq; the contribution of ToS is the ontological reading of its positive values as imprints of performed distinctions, not the construction of this type.

That the proof is arranged in just this way, a beginning plus a preserved passage, is no accident: this is the form of *induction*. Where induction comes from in ToS, and why here it grows out of the repeatability of the act rather than being brought in from outside, is analyzed in the next section. Here let us note only that the proved realizability of every number already rests on the inductive form, and thereby leads to the question about it.

### Every Number, but Not “All Numbers at Once”

The realizability of every number must be read precisely; otherwise more is read into it than there is. The theorem says: *for every* $n \ge 1$ a list of $n$ distinctions is realizable. It does *not* say that all these lists are realized *at once*, that somewhere there is a ready collection containing lists of all lengths together.

The difference here is essential, and it is directly connected with how ToS understands infinity. “Every number is realizable” means: whatever number we take, *for it* a list is realizable; the act of building it can be performed. This is a statement about *each individual* number, taken separately. “All numbers are realized at once” would mean something else: that all the lists have already been built and gathered into one completed object. ToS asserts the first; the second it does not assert, and not by accident.

*“Every number is realizable” is a statement about each individual number, taken separately: for it a list of distinctions can be built. It is not a statement that all the lists have been built and gathered into a ready collection. The cardinal path gives the first and does not give the second.*

Why ToS does not take the second step, does not gather all numbers into a ready completed collection, and why this refusal is a direct consequence of the principle $P4$ rather than a shortcoming, is analyzed in § 2.7. But first we must consider the inductive form on which the proof of the present section relied, and show that in ToS it is not an axiom but grows out of the arrangement of counting. This is the subject of § 2.6.

## Where Induction Comes From

### Induction as the Support of the Previous Section

The proof of the realizability of every number (§ 2.5.3) had a definite form: a beginning (one is realizable) and a preserved passage (the realizability of $n$ implies the realizability of $n + 1$). From these two a conclusion about *every* $n \ge 1$ was obtained. This form of reasoning, a beginning plus a passage yielding a conclusion about the whole series, is *mathematical induction*.

In mathematics induction is usually introduced as an *axiom*, one of the Peano axioms, accepted without derivation. The present section shows that in ToS matters stand differently: here induction *grows out of* the arrangement of counting, out of the repeatability of the act of distinction, rather than being postulated. This does not mean that ToS “proves the Peano axiom”: the point is a different one, namely that in ToS the induction principle need not be introduced as a separate postulate, for it is already contained in the way the number series is built.

### What Induction Asserts

Let us recall the form of the induction principle without reproducing its schoolbook presentation. The principle says: for some property to hold for *every* natural number, two things suffice: that it hold for the *first* number (the base), and that its holding for $n$ imply its holding for $n + 1$ (the step). The base and the step together entail the conclusion: the property holds for the whole series.

The force of the principle lies in this “together entail.” The base is one; the step is one; yet the conclusion concerns an infinite series of numbers. Where do two finite premises get power over the whole series? In the axiomatic presentation there is no answer: induction is *postulated*, and asking why it holds is not done. ToS answers this question.

### Induction Is the Form of the Repeatable Act

The answer of ToS is simple and consists in seeing that induction is not brought into the number series from outside: it is the *verbal record of how the series is arranged*.

The number series in ToS is not given ready-made (§ 2.5.4). It is *built*, by repetition of the act of distinction (§ 2.1). This construction has exactly two components and no others. The first: there is the *first* act, one (§ 1.2). The second: every performed act is *repeatable*; after it one more can be performed, and this is the passage from $n$ to $n + 1$ (§ 2.5.2, `succ`_`is`_`new`_`distinction`). The first act and repeatability: that is all the series is made of.

Let us compare this with the induction principle. The base of induction: the property holds for the first number. The first component of the construction: there is a first act. The step of induction: holding for $n$ implies holding for $n + 1$. The second component of the construction: the act is repeatable; after $n$, $n + 1$ is performed. *The base of induction answers to the first act; the step of induction answers to the repeatability of the act.* This is one and the same thing expressed in two ways, not a resemblance and not an analogy: induction says about the construction of the series the same thing that ToS says about it when analyzing the repetition of the act.

*The induction principle is not brought into the number series from outside. The base of induction is the first act of distinction; the step of induction is the repeatability of the act. Induction is the verbal record of that very construction of the series by repetition of the act which ToS has been tracing since § 2.1. That is why in ToS induction is not an axiom: it is contained in the arrangement of counting.*

A caveat about the formal layer is necessary here; otherwise what has been said may be understood more strongly than it is. The machine proof of the theorem `positive`_`nat`_`is`_`distinction`_`count` (§ 2.5.3) uses *standard induction on* `nat`, the tactic `induction`, which relies on the induction principle for the type `nat` built into Rocq. That is, in the formal layer ToS does *not* derive the induction principle itself from `Distinction`: the induction principle for `nat` is taken ready-made together with the type `nat`. The machine theorem shows something else: that *under* standard induction on `nat` the realizability of positive numbers through lists of distinctions is preserved at every step. The ontological explanation of the present section answers a substantive question, not a formal one: *why* precisely the inductive form, base plus preserved step, corresponds to the arrangement of counting in ToS. The answer (induction is the record of the construction of the series by repetition of the act) remains in force as the ontological justification of the *applicability* of the inductive form; it neither is nor claims to be a formal derivation of the induction principle from the act of distinction. The formal layer uses induction on `nat`; the ontological layer explains why this form is appropriate here.

### Why Two Premises Have Power over the Whole Series

Now the question of § 2.6.2 receives an answer too: where do the base and the step, two finite premises, get power over the whole infinite series?

This power comes from the same place as the series itself. The series is nothing other than the first act, repeated, and repeated again, and so on (§ 2.5.3). Every number of the series is *reached* from one by a finite number of repetitions; otherwise it would not be in the series. And the base and the step are exactly the first act and one repetition. Therefore what holds for the base (for the first act) and is preserved by the step (by one repetition) is preserved along every finite chain of repetitions as well, that is, it holds for every number reached. The base and the step have power over the whole series because *the whole series consists* of applications of the base and the step, not because of some special might of the principle. Induction “reaches” every number exactly as the construction itself reaches it (§ 2.5.3): step by step, and each number is reached in a finite number of steps.

It is also clear what induction does *not* give, and this matters for § 2.7. Induction allows a conclusion about *every* number of the series, for every number is reachable by a finite chain. It neither gives nor presupposes a *completed* traversal of the whole series at once: the conclusion “for every $n$” is obtained not by going through the infinite series to the end but by the fact that *for any presented* $n$ a finite chain base–step–…–step leads to it. Induction works “on request, for each,” not “at once, for all.” This distinction is the same as in § 2.5.4 (“every number, but not all at once”), and it leads directly to the principle $P4$.

### Induction and the Formal Record

It is worth saying how what has been said relates to the formal side of the matter.

In Rocq the natural numbers are the type `nat`, and the induction principle for it is available as `nat`_`ind`; it is part of the arrangement of the inductive type. It may seem that induction in ToS is thereby *accepted* together with the type `nat` after all, not derived. But this is a confusion of two layers, already distinguished in § 1.4 and § 2.3.3.

On the layer of the formal record, induction is indeed given together with the inductive type `nat`: that is how Rocq is arranged. On the layer of the ontology of ToS the question is different: not “is the principle available in Rocq” but “*why* does it hold, what in the subject matter itself answers to it.” And the answer has been given above: induction holds because the number series is built by repetition of the act, and the base and the step are the first act and a repetition. Rocq provides induction as a ready instrument; ToS *explains* why this instrument is applicable, why the number series is such that induction over it is legitimate. The inductive arrangement of the type `nat` in Rocq is the formal reflection of what ToS has established in substance: the series is generated by the first act and its repetition.

*That Rocq gives induction together with the type `nat` is a fact of the layer of the formal record. Why induction is legitimate is a question of ontology, and ToS answers it: the series is built by the first act and repetition, and induction is the record of this construction. The formal availability of the principle does not cancel the fact that in ToS it is justified, not postulated.*

With this the cardinal path is almost complete: it has been shown what the presence of a number means (§ 2.4), that every number is realizable (§ 2.5), and that the induction on which this rests grows out of the arrangement of counting (§ 2.6). One question remains, and it has already been postponed twice. *Every* number is realizable, but not “all at once”; induction has power over *every* number, but does not traverse the series in a completed way. What this means for the *infinity* of the natural number series, and why ToS speaks of it precisely in this way, is analyzed in the next section.

## $P4${P4} and Infinity

### The Postponed Question

Twice in the course of the chapter one and the same limitation has arisen, and twice its analysis has been postponed. § 2.5.4: *every* number is realizable, but not “all numbers at once.” § 2.6.4: induction has power over *every* number, but does not traverse the series in a completed way. In both cases ToS asserted something about any individual member of the series and refrained from asserting anything about the series *as a whole*.

This restraint requires explanation. The natural number series is infinite: anyone will say so, and ToS does not object. But what does “infinite” mean? If the cardinal path has built every number and has not built “all numbers at once,” is the series it has built infinite, and in what sense? The present section answers, and the answer rests on a principle that has not yet sounded explicitly in Part II: $P4$.

### The Objection: Is “for Every $n${n}” Not an Appeal to Completed Infinity?

Let us state the objection in full force, because it is natural and the whole construction is tested on it.

The cardinal path has proved a theorem of the form “for every $n \ge 1$ a list of $n$ distinctions is realizable” (§ 2.5). The words “for every $n$” seem to range over the *whole* natural number series. And to range over the whole series is to traverse an infinite collection of numbers. Does not the very statement “for every $n$” then mean that the infinite collection of all natural numbers is *already present* as a completed object, for otherwise over what would “every” range? And if so, then ToS, declaring in § 2.5.4 its refusal of “all numbers at once,” in fact breaks this refusal: the quantifier “for every” seems already to require completed infinity.

The objection is serious. If it is correct, the cardinal path is internally contradictory: it builds the series term by term, denying a ready collection, and at the same time seems to presuppose this collection by the quantifier “for every.” The answer of ToS shows that the objection rests on a confusion of two different things.

### Universal Quantification as a Scheme, Not as an Object

What is confused is the *quantifier* and the *collection*. The objection reads “for every $n$” as if it were a traversal of a present collection: as if, to assert “for every $n$, $P$ holds,” we had to have the collection of all $n$ and go through it. But universal quantification is not arranged this way.

In ToS, as in the strict constructive treatment in general, the statement “for every $n$, $P(n)$ holds” is a *scheme*, *not* a statement about a completed collection: an obligation that *for any presented* $n$ a proof of $P(n)$ can be presented. The statement “for every $n$” does not describe a traversed infinity; it *promises an answer to a request*: whatever $n$ you name, a proof of $P(n)$ will be built.

And ToS has shown exactly this (§ 2.6.4): for any presented $n$ a finite chain base – step – … – step leads to $P(n)$. There is no traversal of an infinite collection here; there is a *finite* chain, its own for each request. “For every $n$” is true because *for any request* a finite answer is guaranteed, not because an infinite collection has been gone through. The quantifier is a scheme “on request,” not an object “the whole collection.”

*The statement “for every $n$” neither describes nor requires a completed collection of all numbers. It is a scheme: for any presented $n$ a proof can be built, by a finite chain, its own for each $n$. The quantifier “for every” is a promise of an answer to a request, not a traversal of a present infinity.*

{
Precision is needed here about the formal side. In Rocq the statement `forall n : nat, P n` is a *dependent function type* over `nat`: its inhabitant is a function that, for an arbitrary input `n : nat`, returns a proof of `P n`. Therefore it would be imprecise to say that the quantifier *has no domain at all*: it does have a domain, the type `nat`, and `nat` as a type is already given in Rocq. The precise formulation is different: `forall n : nat, P n` does not require *enumerating* all `n` and does not presuppose `nat` as *gone through to the end as a completed collection*; it requires a *single construction*, a function, that works for an arbitrary *presented* `n`. The distinction “scheme versus object” drawn above is thus a distinction between the *traversal of a completed collection* and a *single procedure on request*, not a claim that the quantifier has no domain. The domain `nat` exists; what does not exist is a requirement to present `nat` as a traversed actual totality. The quantifier is the type of functions “for any $n$, build $P(n)$,” and precisely for this reason it is compatible with a term-by-term construction of the series that is never gone through to the end.
}

Thereby the objection of § 2.7.2 is answered. “For every $n$” does not presuppose “all numbers at once”: it is compatible with a term-by-term construction of the series, for it is itself only a promise that the construction will reach any requested member.

### Infinity as Possibility, Not as Collection: $P4${P4}

What has been said is a particular case of a general principle of ToS, and now it can be named. This is $P4$, derived in Chapter I.4 from the law $L5$.

Let us state $P4$ in its own formulation, without substituting a paraphrase for it. $P4$, the *principle of Finite Actuality*, says: by $L5$ every process has a sequential structure, stage after stage; at each stage a finite number of steps has been completed, and each step adds a finite number of elements, so that the outcome of every stage is finite. Applied to systems, this means: at each individual stage a *finite* number of elements is actually present. The principle speaks precisely about a *stage*, about what is present at each individual step; it does not speak about “the collection of all stages” and does not introduce it.

From $P4$, taken in this precise form, there follows, already as a *consequence* and not as the principle itself, what is essential for infinity. Since only what is present at an individual stage is actual, and every stage is finite, there is no *completed actually infinite object* in ToS: there is no stage at which the infinite would be present. Infinity remains, but as a *process*, not as an object: as an unbounded sequence of stages, none of which is the last. Thus $P4$ turns into a potential understanding of infinity: infinity is the possibility of the unbounded unfolding of a process, not a ready collection of everything unfolded at once.

The natural number series is infinite in this sense, and only in this sense. Its construction is a process in the sense of $P4$: every stage is a finite list of distinctions (§ 2.3), and at every stage a finite number of performed acts is present. There is no *last* stage (after every performed act one more can be performed, § 2.5.2), and therefore the construction of the series is unboundedly continuable. But “unboundedly continuable” does not mean “completed”: the possibility of taking one more step is always there, but a stage at which the whole series would be present is not, for every stage is finite.

Let us apply this to the results of the chapter. “Every number is realizable” (§ 2.5) now reads precisely: for any requested number the construction *can be brought* to it; at some finite stage it is actual. “Not all numbers at once” (§ 2.5.4) reads just as precisely: there is no stage at which the whole series would be present, for every stage is finite by $P4$. These two statements are not in contradiction, as might have seemed: they are two sides of one *potential* understanding of infinity. The series is infinite as an *inexhaustible possibility of counting*, not as its *exhausted outcome*.

It is worth specifying what exactly ToS denies when it speaks of the absence of completed infinity, and in what form this denial is formalized. ToS does *not* assert absolutely that “there is no collection of all natural numbers in any sense.” What is asserted is more precise: the natural number series is not a *completed actuality*; there is no stage at which the whole series would be actually presented. Formally, the incompatibility of completed infinity with $P4$ is analyzed in the repository file `P4CompletedInfinity.v`, and analyzed *conditionally*: the corresponding theorem derives a contradiction not from the mere existence of an infinite series but from *three* premises together: from the predicate of completed membership (`CompletedInfSet`, “every $n$ belongs to $S$”), from stage-boundedness by $P4$ (`P4_stage_bounded`), and from a *bridge* (`bridge`) that translates membership in the series into actual presentedness at a finite stage. In other words: completed infinity contradicts $P4$ *under the condition of a bridge* connecting membership with actuality at a stage. This is the precise form of the denial: what ToS rejects is precisely the *combination* of completed membership with stage-wise actuality, that is, the representation of the whole series as present at some stage, not the quantifier “for every $n$” (which, as shown in § 2.7.3, is legitimate without a completed collection).

*$P4$ is the principle of Finite Actuality: at every individual stage of a process a finite number of elements is actual. From this the potential understanding of infinity follows as a consequence: there is no completed infinite object; infinity is a process, unbounded continuability, not a ready collection. The natural number series is infinite in exactly this way: “every number is realizable” and “all numbers are not given at once” are two sides of this; the series is inexhaustible as a possibility of counting and therefore not completed as its outcome.*

### What Follows for What Comes Next

The potential understanding of infinity is a feature that will run through the whole of Part II and beyond, not a reservation of the cardinal path; it is worth indicating where it leads.

First of all, it explains why the natural number series in ToS is the series $1, 2, 3, …$ and nothing beyond it. It contains no “number $\infty$,” no final member, no collection-as-a-whole present *as an actuality* over the numbers. The infinity of the series is not one more object of it; it is a *property of the construction*: its unbounded continuability. This is a direct consequence of $P4$, and it sets ToS apart from constructions in which the natural number series is taken as a *completed actuality*, as a collection actually presented in its entirety (§ 1.1).

Further, the potential understanding of infinity is the very thing that allowed Chapter II.1 to analyze the notation $0{,}999…$ (§ 1.8). There $0{,}999…$ was analyzed as a *process*, a continuable scheme of approximations, not a completed object; and the agreement of this with $P4$ was noted, but $P4$ had not yet been named. Now it has been named: $0{,}999…$ as a process and the natural number series as a potential infinity stand on one principle. Let us stress, as in Chapter II.1, the precise sense of this. ToS does *not* deny the standard equality $0{,}999… = 1$ in the mode of real numbers, where the notation by definition means a limit or an equivalence class. What is at issue is the distinction of *modes*: the raw process of approximations, the constant process, and the equivalence class of processes are different modes, and an unconditional equality is appropriate only after the passage to a common mode. Part IV will unfold this formally through the type `RealProcess` (the file `ProcessCore.v`: `RealProcess` $:=`nat`\toℚ$) and the relation `process_equiv`, the equivalence of processes *by limit*, proved to be an equivalence relation and not reducible to pointwise equality. Infinity as process is a common feature of the numbers of ToS, not a peculiarity of one contested case.

With this the cardinal path is complete. The chapter has shown: counting is the recording of the number of performed distinctions; the form of multiplicity is the list; the presence of a number is its realizability by a list of distinctions; every number is realizable; induction grows out of the repeatability of the act; and the infinity of the series is the potential infinity of the construction, by $P4$. One last thing remains: to see that the path traveled here independently by ToS coincides with a long-standing line of thought about number as a multiplicity of one. With this the chapter concludes.

## The Multiplicity of One

### The Dual Nature of Number in the Cardinal Path

The cardinal path has been built (§ 2.1–2.7). Before closing the chapter, it is worth looking closely at one feature of what has been built, a feature that remained implicit in the course of the work and can now be named.

The number $n$ in the cardinal path is a list of $n$ performed distinctions (§ 2.4). Two seemingly opposite indications are joined in this definition. On the one hand, the number $n$ is a *multiplicity*: $n$ distinctions, $n$ performed acts, $n$ elements of a list, the many. On the other hand, the number $n$ is a *unity*: *one* number, one imprint, one system-list taken as a whole. The number of the cardinal path is dual: it is the many gathered into one.

This duality is neither a contradiction nor a stretch. It follows directly from how the path has been built. Multiplicity, because a number is a list of *several* distinctions (§ 2.2). Unity, because all these distinctions are repetitions of *one* act (§ 2.1.2) and are gathered into *one* list as one E/R/R system (§ 2.2.4). The many of a number is the many of repetitions; the unity of a number is the unity of the repeated act and the unity of the gathering list. Number is the *multiplicity of one*: one taken so many times, and these times gathered back into one.

### E/R/R Analysis: Number-as-List as a System

{
The chapter has already carried out the E/R/R analysis of this path, in § 2.2.4, for the list as a system: *Rules*—the rule of succession ($L5$); *Roles*—ordered positions; *Elements*—distinctions. Let us now gather it into a table, adding the proved counting predicates (§ 2.3–2.4) and potential infinity (§ 2.7), and check well-formedness. A caveat on status: the “system” here is a substantive interpretation over the standard list; the formal predicates `distinction`_`count` and `distinction`_`count`_`from`_`one` are proved (`Distinction.v`, `PrimalityOfOne.v`), but the ontological reading is carried by the prose.}

| Component | What it determines | E/R/R |
|---|---|---|
| the rule of succession ($L5$); the recursion of counting | the constitution of the list | Rule |
| length = act of tallying; `distinction`_`count` ($+$ filter $1\le n$) | counting and positivity | Rule |
| $P4$: the series is potentially infinite | potentiality | Rule |
| length = number; positions “first,” “$n$-th” | role-quantity | Role |
| distinctions (repetitions of one act); the list | bearers (finite, $P4$) | Element |
| the laws $L1$–$L5$ (here $L5$) | the universal layer | Rule (univ.) |

{
*Well-formedness.* The labeling is unambiguous: the distinctions are elements, length and positions are roles, the rule of succession is a rule. $P1$ is observed: length counts *distinctions* (elements), not itself. The diagnosis of this chapter has already been carried out in § 2.2.4 and is a case of the general one: the *list* (a complete system with a rule of succession) versus the *set* (the same system with the rule of succession suppressed); the cardinal path requires precisely the list, for counting carries succession, which the set suppresses. And the boundary case is clean: the empty list gives length zero, the correct outcome of a tally that met no elements, not an “error” and not “unmanifestness” (§ 2.3.3). The honest boundary: `distinction`_`count`_`from`_`one` is a positivity filter ($1\le n$), not a check of the “performedness” of acts; the induction is the standard one on `nat`, not derived from distinction (§ 2.6).}

 What the analysis yields. This is the *first* of the four paths: number is a *role*-quantity, the length of a list of repeated distinctions, and the same role structure (beginning and succession) will recur on levels (Chapter II.3), bits (Chapter II.4), and positions (Chapter II.5), the chapter that will bring the four paths together. The cardinal path gives this structure its first embodiment and secures the duality of number, the *multiplicity of one* (§ 2.8.1): the many of repetitions gathered into one system-list.

### An Independent Convergence with Long-Standing Thought

The understanding of number as a multiplicity of one is not new for European thought, and here, as in § 1.5, a comparison is appropriate. It must be made precisely: ToS arrived at the multiplicity of one by its *own* path, from its own derivation (§ 2.1–2.7), and inherits nobody’s tradition. The coincidence that will be noted is a convergence of independent paths, not a descent of ToS from predecessors. And the status of this coincidence must be named directly: it is *heuristic support*, neither a proof nor a genealogy. That the motif of the multiplicity of one arises in several independent traditions raises the plausibility that the derivation of ToS itself has hit upon something inherent in the subject matter rather than an artifact of its own formalism; but such a convergence does not and cannot carry the strict weight of a proof.

**Leibniz.** In line with ToS stands a long-standing definition: number is that which relates to the unit as a line to a line, a multitude of units, a single gathering of the repeated one.[^3] This definition takes number as precisely dual: the unit as what is repeated, and number as the *gathered multiplicity* of its repetitions. ToS arrives at the same from its own ground: one is the first act (§ 1.2), number is the gathered multiplicity of its repetitions (§ 2.8.1). The coincidence is exact, and all the more telling because the paths to it are *different*: there, a definition of number through its relation to the unit; here, a derivation of number from the act of distinction.

**Brouwer.** Independently, a convergence with the intuitionist understanding of number also comes to light.[^4] In it, the natural number is a *construction*, not an object of a ready set: the result of a mental step repeated a definite number of times; and the whole number series is a *freely continuable* unfolding of these steps, not a completed collection. ToS, going its own way, arrives at the same: a number is *realizable* by the construction of a list (§ 2.4), and the series is infinite only potentially, as the continuability of the construction (§ 2.7). Here the convergence concerns not only the multiplicity of one but also the understanding of infinity, and again it is a convergence of independent paths: intuitionism proceeds from the arrangement of mathematical intuition, ToS from the arrangement of the act of distinction.

**Husserl.** One more convergence is with the description of how number *arises* for consciousness: number there is the outcome of an act of *collecting*, an act that grasps the many as one without abolishing the many.[^5] Multiplicity is not erased in unity, and unity does not fall apart into multiplicity: the act of collecting holds both sides. ToS arrives at the same through the composition of its list: a list is the many of distinctions gathered into one as a system (§ 2.2.4), and this gathering is an act, not a ready givenness. And again the roads are independent: there, a description of an act of consciousness; here, a derivation of the structure of the list.

*The understanding of number as a multiplicity of one, a duality of the many and unity, is found in Leibniz, in intuitionism, and in the description of the collecting act. ToS arrives at it independently, from the derivation of number as a list of repeated distinctions. ToS does not turn the coincidence of different paths into a proof: it is heuristic support; the derivation of ToS itself arrives at a structure that has already been recognized many times in the history of thought, and this raises the plausibility that the structure answers to the subject matter.*

It is also worth speaking of the *boundary* of the convergence, so that the comparison remains precise. What coincides is the understanding of the *structure* of number: the duality of the one and the many, number as a gathered multiplicity. No coincidence in everything is asserted: each of the approaches named has its own ground, its own system, its own further consequences, and ToS neither reduces itself to any of them nor appropriates any of them. What has been noted is exactly a convergence at one point, and it is valuable precisely because the paths to this point diverged in everything else.

### Summary of the Chapter

The chapter has traveled the first of the four paths of ToS to the natural number series, the cardinal path.

The path began with the passage from one act to several: “several acts” are possible because the act of distinction is repeatable, and counting is itself an activity of distinction (§ 2.1). The derivation of repeatable, ordered counting led, by necessity rather than by choice, to the list as the form of multiplicity: the set, lacking order and derived by $M_3$, does not answer to the derivation, whereas the list carries order ($L5$) and in the E/R/R analysis turns out to be a complete system, while the set is the same system with the rule of succession suppressed (§ 2.2). The length of a list of distinctions was defined as the outcome of an act of tallying, not as an inherent property; for the empty list the tally legitimately gives the result zero, the boundary outcome of a tally that met not a single element (§ 2.3). The technical predicate of tallying was separated from the ontological predicate of counting from one, `distinction`_`count`_`from`_`one`, for which zero is not a count and one is the first count (§ 2.4). It was shown that every natural number is realizable: one is realizable, and the passage from $n$ to $n + 1$ preserves realizability (§ 2.5). The induction principle on which this rests turned out to be the verbal record of the construction itself, not an axiom: the base answers to the first act, the step to repeatability (§ 2.6). And the infinity of the series, by the principle $P4$, is a potential infinity: the unbounded continuability of the construction, not a completed collection (§ 2.7). Finally, the number of the path built appeared as the multiplicity of one, a duality of the many of repetitions and the unity of what is repeated, in which ToS independently converges with a long-standing line of thought (§ 2.8).

Thus the cardinal path has been traveled: the natural number is the length of a list of performed distinctions, and the whole natural number series is generated by the repeatability of the first act.

But this is only *one* of the paths. ToS arrives at the natural number series four times, not once (§ 2.1), and the cardinal path is only the first. The next chapter opens the second, the *hierarchical* path: number as a level in a hierarchy, generated by ascent through the rungs of organization rather than by setting one more distinction alongside. The same natural number series will be obtained from a different derivation, from the law $L5$ and the structure of levels that it gives. That one and the same series is reachable by several independent paths is an indication of the stability of the subject matter, not redundancy; ToS will gather the meaning of this in Chapter II.5.

---

[^1]: The predicate `distinction`_`count`, like the type `Distinction` and the theorems about it (`zero`_`distinctions` and onward), is defined in the file `Distinction.v` of the ToS Rocq repository. Here and below, the names of repository files are given for reference.
[^2]: The predicate `distinction`_`count`_`from`_`one` and the theorems pertaining to it (`first`_`count`_`is`_`one`, `zero`_`not`_`a`_`count`, `add`_`distinction`, `succ`_`is`_`new`_`distinction`, `positive`_`nat`_`is`_`distinction`_`count`) are defined in the file `PrimalityOfOne.v` of the ToS Rocq repository. Here and below in the chapter, the names of repository files are given for reference.
[^3]: The definition of number through its relation to the unit goes back to the Euclidean tradition (*Elements*, Book VII, definitions 1–2: the unit, and number as a multitude of units); Leibniz develops the understanding of number as a collection of units in a number of works on the foundations of arithmetic and on combinatorics.
[^4]: L. E. J. Brouwer develops the understanding of the natural number as a mental construction and of the number series as a freely continuable unfolding in his works on the foundations of intuitionist mathematics, beginning with the dissertation “Over de grondslagen der wiskunde” (1907).
[^5]: E. Husserl analyzes the origin of the concept of number from the act of collective apprehension (kollektive Verbindung) in the *Philosophy of Arithmetic* (Philosophie der Arithmetik, 1891).

---

Part: [[02 Natural Numbers|Part II. Natural Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Order]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/02 Natural Numbers/01 Primacy of One|Chapter 1. The Primacy of One]] · [[Library/Branches/Mathematics/Volume/02 Natural Numbers/03 Hierarchical Path Number as Level|Chapter 3. The Hierarchical Path: Number as Level]] →
