---
title: "Chapter 4. The Binary Path: Number as the Count of Binary Choices"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/02 Натуральные числа/04 Бинарный путь число как количество двоичного выбора.md"
sourceBlob: 8cda5ff0fbb2049ac3b0b8f2fe32ac9e56da3400
translated: 2026-10-20
status: draft
---

## The Third Path

### Where the First Two Paths Looked

Part II has traversed two paths to the natural number series. The cardinal path (Chapter II.2) obtained the series from the repeatability of the act of distinction: a number is the length of a list of performed distinctions. The hierarchical path (Chapter II.3) obtained the same series from the Law of Order: a number is a level of the hierarchy. Both paths have been carried to the end, and both arrived at one series.

Before opening the third path, it is worth noting *what* each of the first two *looked at*—because the third path will look differently, and this different view is the whole point.

The cardinal path looked at the performed distinctions as a *list*: it asked *how many* there are, and a number was the length of this list. The hierarchical path looked at distinctions as *rungs*: it asked how high the hierarchy had risen, and a number was a level. Different questions—but in both cases the gaze is directed *outside* a single act: the act of distinction is taken as something *already performed*, as a ready unit, and one counts how many such units are in the list or on what rung they stand. What happens *inside* a single act, neither path asked.

### Where the Third Path Looks

The third path looks *inside* a single act of distinction.

It takes *one* act, rather than a list of acts or their hierarchy, and asks: how is it arranged? What happens when one distinction is performed? And the answer—which will be obtained in § 4.2 from the laws of logic—is this: every act of distinction is *a choice between two*. To distinguish $A$ is to posit $A$ against $\neg A$—and nothing third: nothing intermediate, nothing fourth. A single act of distinction is *binary*.

It is from this binarity that the third path to the natural number series will unfold. If one act is a binary choice, then to perform $n$ acts is to make $n$ binary choices; and a number will appear as *the count of binary choices*—as the length of a binary record. On this path the natural number will reveal its kinship with the concept that mathematics and modern science call *information*: for the unit of information—the bit—is exactly one binary choice.

### How the Third Path Differs from the First Two

The difference of starting points is worth naming directly, because the independence of the third path rests on it.

The cardinal and the hierarchical paths took the act of distinction as a *whole* and counted such wholes—in a list or in a hierarchy. The third path *opens up* the act: it looks at what *one* act is in its internal arrangement, not at how many acts have been performed. Its starting point is binarity; neither the cardinal path nor the hierarchical one says anything about binarity, just as the third path says nothing about the length of a list or about level.

This is a third independent derivation. It does not rest on the first two and is not derived from them: the list of distinctions and the hierarchy of levels take no part in it. And therefore, if the third path arrives at the same natural number series—and it will—this will be a third independent piece of evidence that the series $1, 2, 3, …$ is a structural inevitability rather than a peculiarity of a single device.

### What Lies Ahead in the Chapter

The chapter will traverse the binary path step by step. First the main thing will be established—that the act of distinction is binary—and established by derivation from the laws of logic $L2$ and $L3$ rather than by observation (§ 4.2). Then we show that one binary act is a unit of information, a bit, and that ToS arrives at the bit by its own path, independently of information theory (§ 4.3). Next comes the core of the path: number as the count of binary choices, as the length of a binary record (§ 4.4). Then we show that the growth of the binary record generates the natural number series (§ 4.5). After this the binary path will be compared with the two already traversed: three paths, one series (§ 4.6). It will be shown that here, too, induction is not an axiom (§ 4.7). And the chapter will close with the transition to the fourth and last path (§ 4.8).

*The binary path is the third path of ToS to the natural number series. The first two paths looked at the act of distinction from outside—as a ready unit that is counted in a list or placed in a hierarchy. The third path looks inside a single act and takes its binarity as the basis: every distinction is a choice between two. From the binarity of the act, number will unfold as the count of binary choices, and the natural number series will reveal its kinship with the concept of information.*

## The Binarity of the Act of Distinction

### What Is to Be Established

The third path stands on one ground: the act of distinction is binary. If this ground is firm, everything further will unfold from it; if it is shaky, the path will not stand either. Therefore the binarity of the act will be *derived* here—from the laws of logic already established in Part I—rather than declared or taken from observation.

Binarity means something definite: every act of distinction divides *into exactly two parts*. Into two, and exactly two—not into three, not into one, not into a continuous range of intermediate shades. It is this “exactly two” that must be grounded: we must show that there are *no fewer* than two parts and *no more* than two. The first will be given by the law $L2$, the second by the law $L3$.

### The Law $L2${L2}: No Fewer Than Two Parts

Let us state $L2$ in its formulation from Chapter I.3. The Law of Non-Contradiction is the statement that something cannot be itself and not itself at the same time in the same respect; formally, for an arbitrary proposition, $\neg (A \wedge \neg A)$. Ontologically, as Chapter I.3 established, $L2$ is *the structural condition of the very possibility of division*: without the mutual exclusion of the positive and the negative sides, division itself would fall apart, since the “positive” and the “negative” sides would merge into one.

Let us apply this to the act of distinction. To distinguish is to single out $A$ against $\neg A$. Precision is needed here about what exactly $L2$ does. The very *fact* of two sides is set by the *structure of distinction*, not by the law $L2$: the positive and the negative sides are already present as the two sides of the act—in the record `Distinction` these are the fields `positive` and `negative`, in the type `Side` from `Binarity.v` the two constructors `Marked` and `Unmarked`. The law $L2$ does *not create* these sides out of nothing; formally $L2$ is $\neg (A \wedge \neg A)$, and it speaks of *two already given* sides: it rules out their *merging*, their holding at once. What, then, does $L2$ give for binarity? It provides the *separateness* of the two sides, not “the appearance of two out of nothing”: what is posited as $A$ is not at the same time $\neg A$. Without this separateness binarity would fall apart—the “positive” and the “negative” sides would merge into one, and there would be no distinction at all. Therefore the exact role of $L2$ is this: it *keeps separate* the two sides given by the structure of the act, and thereby guarantees that the act of distinction has *no fewer than two* sides—for two separate sides cannot turn out to be one.

### The Law $L3${L3}: No More Than Two Parts

Let us state $L3$ in its formulation from Chapter I.3. The Law of Excluded Middle is the statement that in every division something is $A$ or $\neg A$, and no third is given; formally, for an arbitrary proposition, $P \vee \neg P$. Ontologically, as Chapter I.3 established, $L3$ is *the condition of the completeness of division*: in every act of distinction in which the identity of the sides ($L1$) and their exclusivity ($L2$) are already at work, there remains no room for a “third”—something that would be neither the positive nor the negative side.

Let us apply this to the act of distinction. The distinction has singled out $A$ and $\neg A$. The law $L3$ says that this singling out *exhausts everything*: there is no *third* side—nothing that would be neither $A$ nor $\neg A$. And here the same precision is needed as for $L2$. Formally $L3$ is $P \vee \neg P$: a statement about a proposition and its negation. Taken by itself, in an *empty* space, $P \vee \neg P$ does not rule out introducing *one more* syntactic label: it says that for every *$P$* either it or its negation holds—but it does not limit in advance how many “sides” there can be at all. The exact formulation is this: $L3$ acts *within the already given frame* of distinction, not in an empty space. If the sides of the act are represented by the type `Side` with the constructors `Marked` and `Unmarked`, then $L3$ *exhausts* precisely this given space: every element of the type `Side` is *either* `Marked` *or* `Unmarked`, and the type provides for nothing else. This is how the formal record fixes the absence of a third side: by the fact that the frame of distinction *already* has exactly two sides and $L3$ asserts their exhaustiveness—not by a decree “do not introduce a third label.” And since the space of sides is a frame of two from the start, and it is exhausted, the act of distinction has *no more than two* sides.

### Exactly Two: The Act of Distinction Is Binary

Let us put the two conclusions together. By $L2$, the two sides of the act *do not merge*—they are separate, and therefore there are no fewer than two of them. By $L3$, the given frame of two sides is *exhausted*—there is no third, and therefore there are no more than two of them. No fewer than two and no more than two means *exactly two*.

It is worth naming precisely how this is fixed formally, without attributing to the code more than it contains. In the file `Binarity.v` of the ToS Rocq repository the sides of distinction are represented by a *separate* type rather than derived from `Distinction`: `Inductive Side := Marked | Unmarked` is declared—a type with two constructors (`Marked` is the positive side, `Unmarked` the negative). The file `Binarity.v` does not import `Distinction.v` and does not build `Side` as a theorem from the fields `positive` / `negative` / 
`exclusive` / `exhaustive` of the record `Distinction`. Therefore the connection with $L2$ and $L3$ must be stated precisely: in the prose, binarity is *grounded* through $L2$ and $L3$—$L2$ keeps the sides separate, $L3$ exhausts the given frame; in `Binarity.v` this grounding is *fixed* through the separate type `Side` with two constructors and two lemmas about them: `L2_exclusive` (`Marked <> Unmarked`—the constructors are distinct) and `L3_exhaustive` (`forall s : Side,
s = Marked \/ s = Unmarked`—every element of the type
is exhausted by two cases). Binarity, therefore, is not *derived* in the code from the record `Distinction`—it is *given* by the type `Side` and *confirmed* by two lemmas corresponding to $L2$ and $L3$.[^1] Every act of distinction divides into exactly two parts: into $A$ and $\neg A$, and into nothing more.

*The act of distinction is binary, and this is grounded, not assumed. By the law $L2$, the positive and the negative sides do not merge—there are no fewer than two sides. By the law $L3$, the given frame of two sides is exhausted, no third is given—there are no more than two sides. No fewer and no more than two is exactly two: every distinction divides into $A$ and $\neg A$, and into nothing beyond. Formally this is fixed by the type `Side` from `Binarity.v`—two constructors and two lemmas corresponding to $L2$ and $L3$.*

This conclusion does not mean that ToS has *chosen* the binary numeral system among others—preferring binary to ternary or decimal. There is no choice here (the mode of ToS is derivation, not choice). The binarity of the act of distinction is not a system for writing numbers; it is *the arrangement of the act itself*, and this arrangement is compelled by the laws $L2$ and $L3$. Decimal, ternary, or any other notation for numbers is a later convention, a matter of convenience; the binarity of *the act of distinction* is how the act is arranged before any notation, not a convention. It is on this arrangement, and not on a chosen numeral system, that the third path stands.

### What Follows from This

The consequence of the binarity of the act lies close at hand, and the whole rest of the chapter will be occupied with it. If one act of distinction is a binary choice—a choice between $A$ and $\neg A$—then every distinction is an answer to one question of the form “$A$ or $\neg A$?”: a question with two possible answers and no third. To perform $n$ distinctions is to answer $n$ such questions. And on this path a number will appear as *the count of binary questions* answered—the count of binary choices.

But before counting binary choices, it is worth naming what *one* such choice is. One answer to the question “$A$ or $\neg A$?” has a name—and this name came from the science of information. The next section shows that one binary choice is a *bit*, and that ToS arrives at the bit by its own path.

## Distinction as a Bit

### One Binary Choice

The act of distinction is binary (§ 4.2): it is a choice between two—$A$ or $\neg A$, and nothing third. Let us now name what *one* such choice, taken by itself, is.

One act of distinction is an answer to one question of the form “$A$ or $\neg A$?”—a question that has exactly two possible answers. To perform a distinction is to *resolve* this question: to posit one of the two. Before the act the question is open—both possibilities are there; after the act it is closed—one possibility has become posited. One act of distinction removes *one* two-valued uncertainty.

Here it is worth separating three things that are easily merged, and whose merging would make what follows imprecise. The first is the *frame* of distinction: the very presence of two sides, $A$ and $\neg A$, given by the structure of the act. The second is the *outcome* of distinction: which of the two sides is posited in a given act. The third is the *bit*: one fixed outcome of the two possible ones. The frame $A/\neg A$ sets the *possibility* of a binary outcome; the outcome *resolves* this possibility; the bit corresponds to exactly one resolved binary outcome. When it is said below that “an act of distinction is a bit,” this bundle is meant: the act, taken with its binary frame and its resolved outcome, is one bit.

### The Bit

The removal of one two-valued uncertainty—the answer to one “yes or no” question—has an exact name in modern science. It is called a *bit*.

The bit is the unit of information introduced in information theory in the mid-twentieth century. In the strict information-theoretic sense, one bit of information corresponds to a binary choice *with equiprobable outcomes*: the amount of information in the answer to a “yes or no” question both of whose answers have probability one half. This is the bit in Shannon’s sense, and it presupposes a probability measure.

The bit at which ToS arrives must be introduced more precisely—and distinguished from Shannon’s. The act of distinction in ToS is not accompanied by a probability distribution: it is a structural choice between two sides, and on this path ToS asserts nothing about the probabilities of the sides. Therefore ToS primarily introduces a *structural* bit: one binary position, one act of choice between two sides, irrespective of probabilities. The structural bit and the Shannon bit coincide *under a condition*: when a probability measure with equiprobable outcomes is added to the binary position, one structural bit carries exactly one Shannon bit of information. Without this condition they differ—if one outcome is almost known in advance, the Shannon measure is less than one bit, whereas the structural bit remains one: one binary position is there regardless of probabilities.

Let us now set the *structural* bit specifically alongside the act of distinction. The act of distinction, as § 4.2 showed, is one binary choice: $A$ or $\neg A$. The structural bit is one binary position: yes or no. This is *one and the same*: the frame “$A$ or $\neg A$?” and the frame “yes or no?” are one binary frame, and one resolved outcome in it is one structural bit. One act of distinction is one structural bit.

### Independent Convergence, Not Borrowing

To say “an act of distinction is a bit” is easily read as borrowing: as if ToS took a ready concept from information theory and applied it to distinction. This reading is wrong, and it is important to correct it.

ToS does not borrow the bit. The bit is *derived* here anew, by a path of its own—from the laws $L2$ and $L3$ (§ 4.2). ToS did not presuppose a binary unit and did not look for one; it traced the arrangement of the act of distinction and discovered that the act is binary—and a binary choice is exactly what another tradition has named a bit. The coincidence was discovered, not laid down as a foundation.

And it is worth seeing in what way this coincidence goes deeper than mere consonance—but seeing it precisely, without injustice to information theory. Information theory *adopts* the binary choice as the natural minimal unit of a distinguishable message and builds the measure of information through the logarithm to base two. This is not an arbitrary postulate: the choice of a binary unit in information theory is well motivated—it corresponds to the minimal nontrivial distinction. But information theory comes to binarity *from the side of the task of measuring messages*; the question “why does the minimal act of distinction have two sides at all” is not one it poses—it lies outside its subject matter. ToS poses precisely this question and answers it: by $L2$ and $L3$ the act of distinction *cannot* be other than binary—a ternary “unit of distinction” would violate $L3$, and a one-part one would not be a distinction at all. Information theory comes to the binary choice from the task of measuring messages; ToS, from the structure of the act of distinction. This is the convergence of independent paths: two roads, different in their initial question, lead to one binary unit.

*One act of distinction is one structural bit—one binary position, one removal of a two-valued uncertainty. ToS does not borrow the bit from information theory: the bit is derived anew, from the laws $L2$ and $L3$. Information theory comes to the binary unit from the task of measuring messages; ToS, from the structure of the act of distinction. The coincidence of the two paths was discovered, not posited.*

### The Boundary of the Convergence

For the comparison to remain precise, its boundary is worth drawing.

What coincides is the *unit*: both information theory and ToS arrive at the binary choice as an indivisible unit—the bit. There the convergence ends. ToS takes over from information theory neither its further constructions nor its subject matter. Information theory measures *the transmission of messages over communication channels*; it speaks of coding, of channel capacity, of noise—none of this does ToS borrow from the coincidence, and none of it is introduced into Part II. The resemblance concerns one point—that the unit is a binary choice; everything that information theory builds *on top of* this unit is its own edifice, which has no bearing on the derivation of the natural number series.

ToS takes exactly one thing from the coincidence: the confirmation that the binary choice is a natural unit at which ToS is not alone in arriving. From here ToS will go its own way—counting binary choices and obtaining the natural number series from their count.

### A Bridge to the Physics Volume

The binarity of the act of distinction is the ground of more than the present chapter. Later in the work, in the volume devoted to physics, it is developed further, and this is worth indicating briefly—without unfolding it.

If every distinction is one bit, then the collection of performed distinctions is measurable in bits—a definite count of binary choices corresponds to it. Later in the work, in the volume devoted to physics, this line will be unfolded: the count of distinctions, expressed in bits, is linked there with the number of possible microstates of a system and with the entropic measure—with what physics calls the measure of disorder. The current repository already contains formal *preparatory work* for this bridge: the file `Binarity.v` contains the functions `two_pow` and `microstates` and lemmas stating that adding one more distinction *doubles* the number of possible states (the number of states grows as $2^K$). These are combinatorial lemmas about powers of two plus comments outlining the connection with entropy; a full physical derivation of the entropy laws is not yet contained in them and belongs to the physics volume.

Part II does not go into this further: entropy, physical systems, and the laws of their change are the subject of another volume, and here it is enough to indicate that the bridge is outlined and that its formal preparatory work exists in the repository. For the natural number series only what has already been established is essential: the act of distinction is binary, and one act is a structural bit.

One binary choice has been named—it is a bit. The main thing remains: to count binary choices and to see that their count is the natural number. This is the subject of the next section.

## Number as the Count of Binary Choices

### From One Bit to Number

One act of distinction is one bit—one binary choice (§ 4.3). This is enough to take the main step of the binary path: to show that a natural number is the *count* of binary choices.

The move is simple and follows the model of the cardinal path. The cardinal path (Chapter II.2) counted acts of distinction as elements of a list: a number is the length of the list. The binary path counts acts of distinction as binary choices: a number is the count of binary choices made. The difference lies in *what* the act is taken as: on the cardinal path, as an indecomposable unit of a list; on the binary path, as one bit, one “yes or no.” What is counted, however, is one and the same: the performed acts.

### A Number Is the Count of Bits

To perform a series of distinctions is to make a series of binary choices: the first, the second, the third. Each choice is one bit. The count of bits made is a natural number: one bit is one, two bits are two, three bits are three, and so on.

This can also be said through the record. To record the binary choices made is to write them out in a row—each with its own symbol, zero or one, according to which of the two sides is posited. The result is a *binary record*—a string of binary symbols. And on the binary path the natural number is *the length of this record*: the number of binary symbols in it, the number of positions. Three binary choices—a record of three symbols—the number three.

Let us stress that it is precisely the length. On the binary path the natural number is not the *value* of the binary record as a code—not the number that the record “denotes” in the binary numeral system. It is *the number of symbols* in the record, the length of the string of binary choice. The binary path counts choices; it does not interpret them as the digits of a code.

**On the formal status of the binary record.** 
Editorial precision is needed here about what the code already contains. The file `Binarity.v` contains the type `Side` (with the lemmas $L2$ / $L3$) and combinatorial lemmas about $2^K$. The layer of *binary records*—the definitions `Bit`, `BitString`, `bit_length`, `add_bit`, and the theorems about the length of a record and about positive binary counting—has now been built on top of it, in the separate file `BitString.v`. This is a direct transfer of the cardinal apparatus of Chapter II.2 to the type `Side`:

```coq
Definition Bit := Side.
Definition BitString := list Bit.
Definition bit_length (bs : BitString) : nat := length bs.

Definition add_bit (b : Bit) (bs : BitString) : BitString := b :: bs.

Lemma add_bit_increments_length : forall b bs,
  bit_length (add_bit b bs) = S (bit_length bs).
Proof. reflexivity. Qed.

Definition positive_bit_count (bs : BitString) : Prop :=
  (bit_length bs >= 1)%nat.

Lemma nonempty_positive_count :
  forall bs, bs <> [] -> positive_bit_count bs.
```

{
With this layer, “one bit is the first positive count” receives a direct anchor: the record `one_bit := [Marked]` with the lemma `one_bit_length` ($`bit_length one_bit` = 1$); and *the positivity of the count of every nonempty record* receives the lemma `nonempty_positive_count` (“a nonempty record has `bit_length` $\ge 1$”). The count here is taken from the side of the *record* (the predicate `positive_bit_count` on `BitString`) rather than indexed by a number; the number side (“for every $n \ge 1$ there is a record of length $n$”) is read off it directly and parallels the already proved `positive_nat_is_distinction_count` from `PrimalityOfOne.v`. The whole layer is 7 theorems, *without a single axiom*; the formal anchor of the binary path is now both the type `Side` with $L2$ / $L3$ and `BitString.v`, built on top of it.}

### The Fork: $K${K} Binary Choices, Not $2^K${2^K} Outcomes

Here the binary path passes a fork, and it is important to see which of the two directions it takes—because the second direction would lead aside rather than to the natural number series.

The binary choice is connected with the number two twice over, and these two connections are easily confused. On the one hand, there is the *count* of binary choices—how many bits have been made: $K$ bits. On the other hand, there is the *number of outcomes*—how many different strings of length $K$ can be composed of binary symbols: there are $2^K$ such strings. These are *different* quantities. With three bits, the count of choices is three, while the number of possible strings is $2^3$, that is, eight.

The binary path to the natural number series goes through the *first* quantity—through $K$, the count of binary choices made. It is $K$ that is the natural number of this path: three choices made—the number three. The quantity $2^K$—the number of outcomes—is *not* the number that the binary path extracts from the binary record. By itself, $2^K$ is of course also a natural number; the point is not that it is “not a number.” The point is that it answers a *different* question: “how many *distinguishable* strings of length $K$ are possible,” not “how many choices have been made.” This is a question about combinations, and ToS will take it up later, when building structures richer than the series out of natural numbers. Here, though, the path goes strictly through $K$: a number is the count of binary choices, not the number of their possible outcomes. In terms of E/R/R, this is the distinction between role and element: $K$ is a role-quantity, $2^K$ is the cardinality of another set (§ 4.8.2).

*On the binary path the natural number is the count of binary choices—the count of bits made, the length of the binary record. It is $K$—how many choices have been made—not $2^K$—how many strings they could yield. The path counts the choices themselves, not their possible outcomes.*

### One Bit Is the First Positive Number

The binary path, like the two previous ones, begins with one—and the beginning here is exactly the same.

The least that the binary path *counts* is *one* binary choice: one distinction, one bit. The same care is needed here as on the cardinal path (Chapter II.2, § 2.3.3). One should distinguish the *technical length* of the empty record from the *positive count* of choices made. The empty binary record—a record without a single bit—exists as a full-fledged object of the formal theory of lists, and its length is $0$: counting the empty record legitimately ends in zero. But the positive binary count—the count of binary choices *made*—begins with one bit: with the first binary choice made. Zero here is neither the first bit nor a positive count; it is the technical length of the empty record—a boundary, not the first number of counting. The first thing that the binary path counts as *made* is one binary choice, and *one* corresponds to it: the first positive number of the binary path.

Here the binary path converges with the cardinal and the hierarchical paths at the same point at which those converged with each other. The cardinal path began the series with one—with the first performed act (Chapter II.1, § 1.2). The hierarchical path began with one—with the base level (Chapter II.3, § 3.3.5). The binary path begins with one—with the first binary choice made. Here, too, zero is not the first number of counting: “zero bits” is the technical length of the empty record, not the first positive binary count. The primacy of one is confirmed from a third, independent side.

A natural number is the count of binary choices, and its counting begins with one. It remains to show how the growth of the binary record generates the whole natural number series. This is the subject of the next section.

## The Binary Record Generates the Series

### From Number to Series

A natural number is the count of binary choices—the length of a binary record (§ 4.4). This was established, so to speak, for a single number: a given record corresponds to a given number. Now we must show that the binary path gives *the whole series*, not separate numbers—that the growth of the binary record generates $1, 2, 3, …$ in full.

The move here is the same as the one the two previous paths made. The cardinal path generated the series by appending a distinction to a list; the hierarchical, by stacking a level. The binary path generates the series by *adding a bit*—one more binary choice to those already made.

### To Add a Bit Is to Pass to the Next Number

Suppose some number of binary choices has been made—there is a binary record of some length, and some natural number corresponds to it. Let us make one more binary choice—one more distinction, one more bit. The record has become one symbol longer.

What did this give the number? The length of the record increased by one: where there were $K$ symbols, there are now $K + 1$. And since a number is the length of the record (§ 4.4), adding one bit has increased the number by exactly one. To add a bit is to pass from a number to *the one following it*.

Adding a bit, then, is the operation of succession. What on the cardinal path was the appending of a distinction to a list, and on the hierarchical path the stacking of a level, is on the binary path *the lengthening of the binary record by one symbol*. Three operations, and all three are one operation of succession `S`, taken in three forms: `S` is “one more distinction in the list,” “one more level over a level,” “one more bit in the record.” On the binary path `S` is the adding of a bit.

It is worth specifying on which side the bit is added. For the *length* of the record this is immaterial: whether the new bit is added on the left (`b :: bs`, at the head) or on the right (`bs ++ [b]`, at the end), the length increases by exactly one in both cases—and it is precisely the length that the binary path needs. For the record *as a string of symbols*, by contrast, the side of addition is essential, and there are two natural readings here: if the record is read *chronologically*—the first choice, the second, the third from left to right—the new bit is conveniently added *on the right*, at the end; if the record is read as a *stack* of choices made, the new bit is added *on the left*, at the head, and the head holds the last choice made. The binary path to the natural number series rests on length and is therefore indifferent to the side of addition; but it is useful to name the side explicitly, so that the order of symbols in the record does not remain ambiguous.

### Growing the Record Generates the Series

Now the generation of the series is fully visible. We begin with the least—with one binary choice, a one-symbol record; one corresponds to it. We add a bit—a two-symbol record, the number two. We add another bit—a three-symbol record, the number three. Each addition of a bit lengthens the record by a symbol and increases the number by one; each length reached is the next natural number. The growth of the binary record, begun from a one-symbol record and continued without bound, generates the whole natural number series:

$$
[ \square ] \;\xrightarrow{\;+ \text{bit}\;}\;
[ \square \square ] \;\xrightarrow{\;+ \text{bit}\;}\;
[ \square \square \square ] \;\xrightarrow{\;+ \text{bit}\;}\;
\cdots
$$

$$
1 \;\xrightarrow{\;+1\;}\; 2 \;\xrightarrow{\;+1\;}\;
3 \;\xrightarrow{\;+1\;}\; \cdots
$$

Two lines, one motion. The growth of the binary record and counting along the natural number series are one and the same generation, written in two forms.

### The Third Manifestation of One Structure

Here the binary path arrives at the same place as the two previous paths—and it is worth naming exactly where.

The natural number series is arranged from two things: there is an initial element—one—and there is an operation of succession that generates the next number from each number (Chapter II.2, § 2.5; Chapter II.3, § 3.4). All three paths traversed gave exactly this arrangement, differing only in what the initial element and the operation of succession turned out to be on each. On the cardinal path: the initial element is the first distinction in the list, the operation of succession is the appending of a distinction. On the hierarchical path: the initial element is the base level, the operation of succession is the stacking of a level. On the binary path: the initial element is the first bit, the operation of succession is the adding of a bit.

Three paths—three manifestations of one and the same structure: an initial element plus an operation of succession. The binary path builds neither a *different* series nor a series arranged *differently*—it shows the same structure of the natural number series once more, in its third embodiment. In the E/R/R analysis (§ 4.8.2) this is one role structure of number on a third bearer.

*The growth of the binary record generates the natural number series: begun from a one-symbol record (to which one corresponds) and continued by adding bits (each addition increases the length, and with it the number, by one), it gives length after length—number after number. Adding a bit is the operation of succession `S`, taken on the binary path. This is the third manifestation of one structure of the natural number series—an initial element and an operation of succession.*

### The Infinity of the Series of Binary Lengths

About the infinity of the series generated by the growth of the record one must say the same as Chapters II.2 and II.3 said about the infinity of the natural number series—and on the same grounds.

The growth of the record is unbounded: one more bit can be added to every binary record—one more binary choice can be made. There is no *last* record beyond which nothing could be added. But the unboundedness of growth is not the presence of a *completed collection of all binary records at once*. By the principle $P4$—the principle of Finite Actuality (Chapter II.2, § 2.7)—what is actual at every stage is only a finite record of finite length; the series of binary lengths is infinite *potentially*—as the unbounded continuability of growth, not as a ready collection of all lengths.

Here the binary path arrives at the same place as the cardinal and the hierarchical paths, and this is one and the same limitation, seen from a third side. The natural number series is the inexhaustible possibility of adding a bit, not the exhausted result of such adding. The binary path adds nothing new to the infinity of the natural number series; it confirms from a third side that the series is infinite potentially, by $P4$.

The natural number series has been generated a third time—by the growth of the binary record. It remains to compare the three paths traversed and to see that they gave one series. This is the subject of the next section.

## Comparison with the Two Paths Traversed

### How the Three Paths Differ

Three paths to the natural number series have been traversed: the cardinal in Chapter II.2, the hierarchical in Chapter II.3, the binary in § 4.1–4.5. The present section sets them side by side—in order to see what coincided and what this means, without choosing the best or checking one by another. We should begin with how the three paths differ.

They differ in their starting point—in what they look at, and by what operation they generate the series.

The cardinal path looks at the performed distinctions *as a list* and asks how many there are. A number is the length of the list; the operation of succession is the appending of a distinction to the list.

The hierarchical path looks at distinctions *as rungs* and asks how high the hierarchy is. A number is a level; the operation of succession is the stacking of a level over a level.

The binary path looks *inside* a single act and asks how it is arranged. A number is the count of binary choices, the length of a binary record; the operation of succession is the adding of a bit to the record.

The difference of starting points is essential. A list, a hierarchy, the binarity of an act are three different things; no path takes its *initial* unit of counting from what another rests on. The cardinal path derives the unit from the performed act-in-a-list, the hierarchical from a rung of the hierarchy, the binary from the internal binarity of a single act. These are three derivations independent in the *source* of the unit, and none is derived from the others.

Here, however, precision is needed, otherwise the independence will be exaggerated. The binary path is independent of the first two *in the source* of the unit of counting: it takes the unit from the binarity of the act, not from a list of acts and not from the hierarchy of levels. But as soon as the binary choices are *recorded* in a string, the passage from the string to the number again uses the *cardinal* mechanism—the length of the record. The length of a binary record is the same operation as the length of a list of distinctions in Chapter II.2: counting the elements of a sequence laid out in a row. Therefore the independence of the binary path is an independence in *where* the unit comes from (a bit, rather than an element of a list or a level), not in *how* the number is assembled from units. The operation of assembly—length—is shared by the binary and the cardinal paths. This does not weaken the binary path: it really does give a new, third source of the unit of counting; but it builds the series out of these units by the same mechanism of length, and it is more honest to say so directly.

### Where the Three Paths Coincided

For all the difference of starting points, the result of the three paths is *one*, and the coincidence is exact—in the very arrangement of the series.

Each path gave a series with a beginning—one—and an operation of succession generating the next number from each number. The cardinal: one is the first distinction, succession is the appending of a distinction. The hierarchical: one is the base level, succession is stacking. The binary: one is the first bit, succession is the adding of a bit. The beginnings of all three paths are one and the same number one; the operations of succession of all three are one and the same operation `S`, taken in three forms (§ 4.5.4). And the infinity in all three cases is one—potential, by $P4$.

The three paths diverge in their starting point and in what the operation of succession appears as—and converge completely in the result. Three different derivations led to an *identical* series: to one and the same
$1, 2, 3, …$.

### Three Paths, One Series

The coincidence of three independent paths strengthens the argument for the sake of which Part II traverses them.

Chapter II.3 (§ 3.6.5) already noted that the coincidence of two independent paths is an argument for the structural inevitability of the natural number series—that $ℕ$ was discovered, not invented. The third path strengthens this argument. Were there two paths, one could still suppose that they are implicitly related—that both derivations, for all their difference, somehow rest on a common, unnamed ground, and that the coincidence of their result is therefore not so surprising. The third path, starting from something quite different—from the arrangement of a single act—makes such a supposition less and less plausible. Three roads now lead to one and the same series $ℕ$, laid from three different places: from the list, from the hierarchy, from binarity. The more independent paths converge at one point, the clearer it is that this point is that to which the roads are *compelled* to come, not a crossroads of chance roads.

*Three independent paths—the cardinal, the hierarchical, and the binary—give an identical natural number series: the same number one at the beginning, one operation of succession in three forms, one potential infinity by $P4$. The coincidence of three paths strengthens the argument for the structural inevitability of $ℕ$: the more independent roads converge at one point, the clearer it is that the derivation of ToS is compelled to come to this point.*

### Groundwork for the Synthesis

The comparison of the three paths leads to a question that Part II leaves open for now—and it is worth naming it without resolving it here.

Three paths give one series. But *why* do they give one series? What exactly makes the list of distinctions, the hierarchy of levels, and the binary record *three forms of one thing*? To say that all three give the structure “an initial element plus an operation of succession” does not yet explain why such different derivations arrive at this structure. Behind the coincidence of the three paths there evidently stands something common—what makes the natural number series the inevitable result of each of them.

The binary path does not resolve this question: it is enough for it to show that the third path leads to $ℕ$ and arrives there. To resolve the question is the task of the synthesis with which Part II will conclude: to gather the four paths together and to name the common thing owing to which they converge. The binary path leaves this question as groundwork.

The three paths have been compared. It remains to show that on the binary path, too, induction is not an axiom, and to sum up the chapter. This is the subject of the following sections.

## Induction on Binary Records

### Induction on the Third Path as Well

The two previous paths showed that induction in ToS is not an axiom. The cardinal path grounded it in the repeatability of the act: the base is the first act, the step is one more act (Chapter II.2, § 2.6). The hierarchical path grounded it in the arrangement of the hierarchy: the base is the ground, the step is stacking (Chapter II.3, § 3.7). The binary path comes to the series by a third road—through the growth of the binary record—and induction must be grounded here anew, according to the arrangement of this path.

### Induction on Binary Records

The principle of induction for the natural number series was stated in Chapter II.2 (§ 2.6.2): for a property to hold for every number, it suffices that it hold for the first number (the base) and that its holding for $n$ imply its holding for $n + 1$ (the step).

Since on the binary path a number is the length of a binary record (§ 4.4), the same principle can be read on records. *Induction on binary records:* for a property to hold for every binary record, two things suffice—that it hold for a one-symbol record (the base), and that its holding for a record of length $K$ imply its holding for the record lengthened by one bit, of length $K + 1$ (the step). The base and the step together entail that the property holds for every binary record.

### The Base Is the First Bit, the Step Is the Adding of a Bit

Why induction on binary records is legitimate can be seen from how a record grows. The answer is of the same nature as on the two previous paths; only the components are different.

A binary record is composed of two things, and it has no others (§ 4.4, § 4.5). The first: there is a least record—a one-symbol record, one bit. The second: every record longer than one symbol is obtained from a shorter one by *adding* a bit. Let us compare this with induction. The base of induction: the property holds for a one-symbol record; the first component: there is a one-symbol record. The step of induction: holding for a record of length $K$ implies holding for a record of length $K + 1$; the second component: every record is obtained by adding a bit. *The base of induction corresponds to the first bit; the step of induction corresponds to the adding of a bit.*

Hence its legitimacy. Every binary record *either* is a one-symbol record *or* is obtained from a shorter one by finitely many additions of a bit. A property that holds for a one-symbol record (the base) and is preserved by the adding of a bit (the step) then holds along every finite chain of additions—that is, for every record. Induction on binary records holds sway over all records because every record consists of the first bit and the additions to it, not by some special power of the principle.

*Induction on binary records is not an axiom. Its base corresponds to the least record—one bit; its step, to the adding of a bit. Induction is a verbal record of how a binary record grows—from the first bit and additions; and it holds sway over all records because every record consists of them.*

Two clarifications are needed here—about the *base* and about the *form* of this induction.

**The base: one position or one content.** 
The statement “the base is a one-symbol record” is exact for properties that depend only on the *length* of the record: for them it does not matter which bit stands in the one-symbol record. But if the property being proved depends on the *contents* of the record—on which bits exactly stand in it—the base must be checked for *both* one-symbol records: for `[Marked]` and for `[Unmarked]`. Formally, the base of a content-dependent property is `forall b : Bit, P [b]`—$P$ for every one-symbol record—rather than “$P$ for one record.” The binary path to the natural number series uses properties that depend on length, and for them the base “a record of length one” suffices; but where a property touches the content of the record, the base should be taken in full form—over both one-symbol cases.

**The form: induction on nonempty records.** 
Induction on binary records with the base “one bit” is *not* ordinary induction on lists. Standard list induction has the empty list `[]` as its base, whereas here the base is a one-symbol record. Therefore the binary path corresponds not to the standard list principle but to a separate principle of induction on *nonempty* binary records—with the base over one-symbol records and a step that preserves nonemptiness. Formally it can be written as follows:

```coq
Lemma nonempty_bitstring_ind :
  forall (P : BitString -> Prop),
    (forall b : Bit, P [b]) ->
    (forall b bs, bs <> [] -> P bs -> P (b :: bs)) ->
    forall bs, bs <> [] -> P bs.
```

This formulation corresponds directly to the prose of the present section: the base is `forall b, P [b]` (every one-symbol record), and the step is that $P$ for a nonempty record implies $P$ for the record lengthened by a bit. Standard induction on `nat` (or the induction on records equivalent to it through the condition $1 \le `length`$) gives the same result; the principle `nonempty_bitstring_ind` merely writes it in a form that corresponds directly to the binary path.[^2]

### The Same Induction, a Third Grounding

Induction on binary records and induction on numbers are one principle. Since the series of binary lengths is the natural number series, induction on records and induction on numbers cannot be two principles: the principle of induction is a principle *for the natural number series*, and the series is one.

But the grounding of induction on the three paths is threefold—and that is the whole point. The cardinal path derived induction from the repeatability of the act; the hierarchical, from the arrangement of the hierarchy; the binary, from the growth of the binary record. One principle of induction receives three independent groundings on the three paths. And this is the same as what happened with the natural number series itself (§ 4.6): one principle, not three; three independent paths to one principle, not three retellings of one argument. The coincidence testifies here just as it testified for the series: induction is not an arbitrarily accepted axiom—it is that to which ToS comes in tracing the arrangement of the series, by whatever road one approaches this arrangement.

### Infinity

Infinity on the binary path has already been discussed (§ 4.5.5): the growth of the binary record is unbounded, but this unboundedness is potential, by $P4$—the inexhaustible possibility of adding a bit, not a completed collection of all records. There is no need to repeat this conclusion; it is only worth connecting it with induction.

The connection is this. Induction on binary records holds sway over *every* number of the series precisely because the series is not a completed collection. Induction does not survey all records at once—they cannot be surveyed at once, since there are potentially infinitely many of them. It is arranged differently: it gives the property for the first bit and carries it over by the adding of a bit—and thereby covers *any* record that growth will reach. Induction and potential infinity agree: induction is precisely the way of judging the whole series that does not require the series to be completed. What held for the cardinal and the hierarchical paths (Chapter II.2, § 2.7; Chapter II.3, § 3.5) holds here as well.

The binary path has been traversed: the natural number series has been obtained as the series of binary lengths and compared with the two previous paths, and induction on it has been grounded. It remains to sum up the chapter and pass to the fourth and last path. This is the subject of the concluding section.

## Summary

### What the Chapter Has Covered

The chapter has traversed the third of the four paths of ToS to the natural number series—the binary, or informational, path.

The path began with a different view of the act of distinction. The first two paths took the act as a ready unit and counted such units—in a list or in a hierarchy; the third path turned inside a single act and asked how it is arranged (§ 4.1). The answer was obtained by derivation from the laws of logic, not by observation: by the law $L2$ the positive and the negative sides do not merge—there are no fewer than two sides; by the law $L3$ no third side is given—there are no more than two sides; hence every act of distinction is binary and divides into exactly two parts (§ 4.2). One binary act was named a bit—and it was shown that ToS arrives at the bit by its own path, deriving binarity as necessary where information theory postulates it as convenient; the coincidence of the two traditions was discovered, not borrowed, and a bridge to the physics volume was indicated (§ 4.3). Then came the core of the path: a natural number is the count of binary choices, the length of a binary record; the path goes through $K$—the count of bits made—and not through $2^K$, the number of their possible outcomes (§ 4.4). This was gone through in motion: adding a bit lengthens the record by a symbol and increases the number by one, and the growth of the record, begun from one bit, generates the whole natural number series—the third manifestation of one structure, “an initial element plus an operation of succession” (§ 4.5). The three paths—the cardinal, the hierarchical, and the binary—were compared: different in their starting point, they give an identical series, and the coincidence of three independent paths strengthens the argument for the structural inevitability of $ℕ$ (§ 4.6). Finally, on the binary path, too, induction proved to be no axiom: its base corresponds to the first bit, its step to the adding of a bit (§ 4.7).

Thus the binary path has been traversed: a natural number is the count of binary choices, and the whole natural number series is generated by the growth of the binary record—by the adding of bits derived from the binarity of the act of distinction.

### E/R/R Analysis: The Number-Bit as a System

{
The path traversed has an E/R/R arrangement (Part I), and its analysis consolidates the result of the chapter. The header of the supporting file gives the labeling: *elements—the sides `Side`; rules—exclusion ($L2$), exhaustion ($L3$), growth*.[^3] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. A caveat on status: the “system” here is a substantive interpretation (the number-bit); the code fixes the type `Side` and the lemmas $L2$/$L3$ (`Binarity.v`), and the layer of the binary record (`Bit`, `BitString`, `bit_length`, `add_bit`, `nonempty_bitstring_ind`) is built on top of it in `BitString.v` (7 theorems, 0 axioms; § 4.4).}

*Rules* (the laws $L2$, $L3$).
The constitution of the system is two laws that give *exactly two* sides: $L2$ keeps them separate (`L2_exclusive`: `Marked` $\neq$ `Unmarked`), $L3$ exhausts the frame (`L3_exhaustive`: every side is one or the other). Together they constitute the bit—a structural one, one binary position (§ 4.3). The second rule is assembly: a number is the *count* of bits, and the adding of a bit is the operation of succession `S` (§ 4.5); assembly by length is shared with the cardinal path. Here, too, belongs the rule of growth: $K$ bits give $2^K$ outcomes (`two_pow`, `microstates`), but this is preparatory work for another task (§ 4.4.3). The universal $L1$–$L5$ act here as well; $L2$ and $L3$ are the distinctive ones.

*Roles—the significance of positions* (the law $L4$). The role of a bit is to be *one* binary position, one performed distinction; the role of a record is to carry the *count* of such positions. Number is precisely this role-quantity: $K$ bits—the number $K$. The role is constituted by a rule: since the bit is given by two laws, every record occupies a place according to the number of its bits. Three things must be distinguished here (§ 4.3.1): the *frame* (two sides), the *outcome* (which side is posited), and the *bit* (the fixed outcome).

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are the sides `Marked` and `Unmarked` and the records composed of them. By $L1$, each side is identical to itself (`Side` is a type with decidable equality). By $P4$, every record is finite—a finite number of bits—although the series of lengths is potentially infinite (§ 4.5.5). ToS gives the sides by a separate type `Side`, whose binarity is *grounded* by the laws $L2$/$L3$ (§ 4.2), rather than deriving them from distinction.

 Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| $L2$ (separateness) + $L3$ (exhaustiveness) | constitution (the bit) | Rule |
| number = count of bits; adding is `S` | the rule of counting | Rule |
| doubling `two_pow`/`microstates` ($2^K$) | preparatory work (growth) | Rule |
| bit = one position; a record of $K$ bits | role-quantity | Role |
| the sides `Marked`/`Unmarked`; a record | bearers (finite, $P4$) | Element |
| laws $L1$–$L5$ (here $L2$, $L3$) | universal layer | Rule (univ.) |

{
*Well-formedness.* The labeling is unambiguous: the sides are elements, the count of bits is the role, $L2$/$L3$ and assembly are rules; no layer stands in for another. The principle $P1$ is observed: a record is composed of sides *one level lower*, not of itself, and the frame, the outcome, and the bit are not mixed into one level (§ 4.3.1). And here the analysis turns into a *diagnosis*—the very fork of § 4.4.3. To mix up the *count* of choices made ($K$) with the *number* of their possible outcomes ($2^K$) is a confusion of categories: $K$ is a *role*-quantity, the answer of the path; $2^K$ is *the cardinality of another set of elements* (all strings of length $K$), a question about combinations, not about counting. The path takes the role-quantity and therefore goes through $K$. Likewise, the *structural* bit (one position) and the Shannon bit (equiprobable outcomes with a measure) differ: the first is a role-position, the second adds a probabilistic layer (§ 4.3.2).}

 What the analysis yields. It shows that the third path, too, carries the same role structure of number: a number is a *role*-quantity set by the initial element and succession, only the bearer is now different—a bit instead of an element of a list (Chapter II.2) or a level (Chapter II.3). This is the *third manifestation* of one structure (§ 4.5.4): one system of roles on a third bearer. And the analysis clarifies the kinship of number and information (§ 4.8.3): the bit and the unit of counting are two sides of one role—one performed distinction. The fourth path (Chapter II.5) will take number directly as *a position in a system*—that is, as a role in the E/R/R sense—and will bring all four together (§ 4.8.4).

### The Kinship of Number and Information

Beyond the natural number series, the binary path has given one more thing—and it deserves to be named separately.

The path has shown that the natural number and the concept of information are *akin* by their very origin. Both grow from one root—the binarity of the act of distinction. The bit, the unit of information, is one binary choice; a natural number is the count of such choices. Information and counting are two sides of one thing, not two unrelated domains linked only by chance through the binary record: where a distinction is performed, there are both a bit and a unit of counting, for distinction by its arrangement is both.

ToS neither postulates this kinship nor borrows it from information theory. It is *derived*: from the laws $L2$ and $L3$, which gave the binarity of the act. And it is groundwork for what lies ahead: on it, as § 4.3.5 indicated, the physics volume builds a bridge from the counting of distinctions to the physical measure of disorder. For Part II something more modest is essential: the natural number series obtained by the third path carries within it a kinship with information, as a trace of what the path started from.

### Transition to the Fourth Path

ToS counts four paths to the natural number series. Three have been traversed; one remains.

The fourth path is the *structural* one. The three paths traversed looked at distinctions: as a list, as rungs, as a binary choice inside an act. The fourth path looks at something else—at the *system* that distinctions form, taken as a whole. Its starting point is the arrangement of a system as a system, not a separate act or a series of acts: the fact that every system, by the laws $L5$ and $L4$, is an ordered collection of distinguishable places. From this arrangement the last approach to the natural number series will unfold: number as a *position* in a system, as a place in a structure.

With the fourth path the traversal of the paths will be complete. The chapter devoted to it will then bring all four paths together—it will name the common thing owing to which they converge on one series—and will thereby close Part II. The next and concluding chapter of Part II is devoted to the fourth path and the synthesis.

---

[^1]: The lemma `exactly_two_sides` available in `Binarity.v` coincides in formulation with `L3_exhaustive` (and is proved through it), and therefore fixes only exhaustiveness, not the distinctness of the sides. So that “exactly two” should receive a single formal carrier—the pair “distinct *and* exhausting”—these definitions have now been built: in the file `BitString.v` (on top of `Binarity.v`) the synthetic theorem `side_binarity := Marked <> Unmarked /\ (forall s, s = Marked \/ s = Unmarked)` is proved (from `L2_exclusive` and `L3_exhaustive`); and for the literal “count of sides $=2$” there is the list `all_sides := [Marked; Unmarked]` with lemmas of completeness (`all_sides_complete`) and length (`all_sides_length`: `length all_sides = 2`). See the summary of the chapter.
[^2]: The principle `nonempty_bitstring_ind`, like the whole layer of binary records (`Bit`, `BitString`, `bit_length`, `add_bit`), has now been built—in the file `BitString.v` on top of `Binarity.v` (the latter gives the type `Side` and the lemmas $L2$ / $L3$). The principle is proved there in exactly the form given; see the summary of the chapter.
[^3]: The E/R/R labeling is in the header of the file `Binarity.v` (objects `Side`, `two_pow`, `microstates`; lemmas $L2$/$L3$; growth). Here it is unfolded on the model of Part I.

---

Part: [[02 Natural Numbers|Part II. Natural Numbers]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Logic]]

Navigation: ← [[Library/Branches/Mathematics/Volume/02 Natural Numbers/03 Hierarchical Path Number as Level|Chapter 3. The Hierarchical Path: Number as Level]] · [[Library/Branches/Mathematics/Volume/02 Natural Numbers/05 Structural Path Number as Position in a System|Chapter 5. The Structural Path: Number as Position in a System]] →
