---
title: "Chapter 4. From Position to Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/03 От натуральных к рациональным/04 От позиции к процессу.md"
sourceBlob: 541430684dc4a7b979c33ff26447a21f091bd1c8
translated: 2026-10-20
status: draft
---

## A Square Equal to Two

### Where Part III Stands

Part III has come a long way. Starting from the natural number series
obtained in Part II, it unfolded the integers—a two-sided coordinate
marking (Chapter III.1); the rational numbers—a commensurable marking
with a fractional step (Chapter III.2); and it showed that the rational
numbers are enumerable (Chapter III.3). Along this whole path the number
was understood in one and the same way: as a *position*—a point of the
coordinate marking taken relative to the reference point.

The number-position is a simple and strong idea, and Part III has
developed it in full. A natural number is a position in counting; an
integer is a position in the two-sided marking; a rational number is a
position in the commensurable marking. The present chapter will show
that along this path one meets a role that a position—any position at
all—cannot bear, and that behind this role an object of another kind
unfolds. But first this role must be seen—on a concrete, simple problem.

### The Diagonal of the Unit Square

Take a square whose side is one unit and draw its diagonal. Let us ask:
what is the length of this diagonal?

The question is legitimate and ancient. The diagonal is a perfectly
definite segment; it has a length, and it can be laid off on the
coordinate marking. By a theorem known long before any theory of
numbers, the square of the length of the diagonal equals the sum of the
squares of the sides: $1 + 1$, that is, $2$. The length of the diagonal
is, therefore, a number which, taken twice as a factor, gives $2$.

Let us denote the number sought by $r$ and write down the condition it
must satisfy:

$$
r \cdot r = 2.
$$

The problem is posed. There is a segment—the diagonal of the unit
square; there is a condition on its length—$r \cdot r = 2$. It remains
to ask: which position of the commensurable marking satisfies this
condition?

### The Question to Be Analyzed

The commensurable marking is dense (Chapter III.2): between any two
positions there lies yet another, and the marking thickens without
limit. It is natural to expect that among this dense multitude of
positions there will also be one whose square equals two: after all, the
positions seem to come arbitrarily close to every place.

And yet there *is no* such position. No rational number squares to two.
This is a proved fact, not a conjecture, and Part III will prove it
rigorously in the next section. But first it is worth saying plainly
what this fact does *not* mean—so as not to misread it.

It does not mean that the commensurable marking has a defect, a hole,
that the rational numbers are deficient in some respect. Part III built
them as a full-fledged system—an ordered, dense commensurable marking
whose standard algebraic role is the role of a field and which has been
shown countable by an explicit traversal—and none of this is revoked. It
means something else: that the condition $r \cdot r = 2$ is a condition
of a special kind—one that no *position* can fulfill. And meeting such a
condition does not cut the path of Part III short; it turns it: behind a
condition that is beyond the power of a position, a number of another
kind unfolds. Which one, the chapter will show after first going through
the proof itself.

## No Fraction Gives Two

### What Must Be Proved

The statement that the preceding section arrived at is this: no rational
number, taken twice as a factor, gives two. In the language of
fractions: there is no fraction $p/q$ such that $(p/q) \cdot (p/q)$
equals $2$.

The fraction $p/q$ squared gives $p^2 / q^2$. The condition
$(p/q)^2 = 2$ therefore means $p^2 / q^2 = 2$, and this means
$p^2 = 2 q^2$. What must be proved, then, is the following: *there are
no integers $p$ and $q$, with $q$ not equal to zero, for which
$p^2 = 2 q^2$.* A technical detail of the notation should be noted at
once. In Rocq’s standard representation of a rational number, the
numerator is an integer, while the denominator is *positive* by the way
the type is arranged (the type `positive`, Chapter III.2, § 2.5). The
proof is therefore built in two moves: first an intermediate theorem is
proved for arbitrary integers $p$ and $q$ under the condition
$q \neq 0$, and then it is applied to a rational number whose
denominator has the form $q = \texttt{Z.pos}(d)$ with positive $d$.
What is proved will establish that the condition $r \cdot r = 2$ cannot
be fulfilled by any rational position.

ToS proves this rigorously and constructively.[^1]
The proof proceeds by a device known as *infinite descent*, and this
device is worth going through, for it is instructive in its own right.

### The Parity of a Number and the Parity of Its Square

The proof rests on one simple observation about parity.

*If the square of an integer is even, then the number itself is even.*
Indeed, a square is a number multiplied by itself. The product of two odd
numbers is odd; hence, if a number is odd, its square is odd too. Let us
turn this around: if the square is even—that is, not odd—then the number
is not odd either, that is, it is even. ToS proves this observation as a
separate lemma.[^2]

This observation is the lever of the whole proof. From it the key step
is derived: *if $p^2 = 2 q^2$, then $p$ and $q$ are both even.* Let us
see why. The equality $p^2 = 2 q^2$ says that $p^2$ is twice
something—hence $p^2$ is even, and then, by the observation, $p$ is even
as well. Since $p$ is even, it is twice some integer: $p = 2k$.
Substituting: $(2k)^2 = 2 q^2$, that is, $4 k^2 = 2 q^2$, whence
$q^2 = 2 k^2$. But this means that $q^2$ is even too—and then $q$ is
even as well. Thus from $p^2 = 2 q^2$ it follows that $p$ and $q$ are
both even.[^3]

### Infinite Descent

Now the device of descent. Suppose there are integers $p$ and $q$ for
which $p^2 = 2 q^2$. It has just been shown that both are even:
$p = 2 p'$ and $q = 2 q'$. Substitute into the equality and cancel:
$(2p')^2 = 2 (2q')^2$ gives $4 p'^2 = 8 q'^2$, that is,
$p'^2 = 2 q'^2$. The halves $p'$ and $q'$ satisfy *the very same*
equality.[^4]

But then $p'$, $q'$ are both even as well—by the same argument—and can
be halved, giving $p''$ and $q''$, again with the same equality. And
again. And again. The descent does not end: every pair of solutions
generates a pair half as large, and so on without limit.

Here lies a contradiction, and it is worth naming it exactly, as it is
carried out in the formalization. Take the *measure* of a pair of
solutions—the sum $|p| + |q|$, a non-negative integer. Every step of the
descent strictly decreases this measure: the halves $p'$, $q'$ have a
sum of absolute values half as large. But a chain of strictly decreasing
non-negative integers cannot be infinite—every such chain breaks off.
Formally, this is exactly *strong induction on the measure* $|p| + |q|$:
assuming the statement proved for all pairs of smaller measure, one
proves it for a pair of the given measure, and the only pair whose
measure the descent cannot decrease (since the measure is already the
least, zero) is the pair of zeros $p = 0$, $q = 0$. In this way Rocq
avoids informal reasoning about an “infinite process of division”:
instead of an appeal to “infinite descent” as such, the proof rests on a
rigorous principle—strong induction on a decreasing integer measure.
Conclusion: every solution of $p^2 = 2 q^2$ is the pair of zeros.[^5]
And the pair of zeros does not satisfy the conditions of the problem:
the denominator $q$ of a fraction cannot be zero (Chapter III.2,
§ 2.4). Hence no fraction satisfies the condition $p^2 = 2 q^2$.

*No rational number squares to two. If a fraction $p/q$ satisfied
$p^2 = 2 q^2$, then $p$ and $q$ would both be even, their halves would
satisfy the same equality, and so on without end. Formally, this
contradiction is carried out by strong induction on the measure
$|p| + |q|$: each step of the descent strictly decreases this measure,
and a strictly decreasing chain of non-negative integers cannot be
infinite—and the only solution is the pair of zeros. But zero cannot be
a denominator. ToS proves this constructively, without a single axiom
and without the law of excluded middle.*

### How to Read This Result

The result is proved; now it is important to read it correctly, for this
is where it is easiest to go astray.

What has been proved is a statement *negative* in form: there *is no*
such fraction. And the temptation is great to read it as news of a
deficiency: as if a hole had been discovered in the commensurable
marking, as if the rational numbers lacked something. That would be
wrong. The proof found no defect in $ℚ$. It established an exact fact
about *positions*: the condition $r \cdot r = 2$ is not fulfilled by any
position of the commensurable marking.

And the question that arises from this is not “how to patch the
marking” but an entirely different one: *if the condition
$r \cdot r = 2$ is beyond the power of any position, then what object is
it within the power of*? After all, the diagonal of the unit square
exists, it has a length, and the condition on this length is
legitimately posed. An object satisfying the condition must exist—but it
is not a position. What, then, is it? The chapter now turns to this
question, and the answer to it makes up the chapter’s substance.

## A Role That a Position Does Not Bear

### There Is a Condition, but No Object-Position

The previous section has left the chapter with a precisely outlined
state of affairs. There is a condition—$r \cdot r = 2$. There is a
segment to which it refers—the diagonal of the unit square. And it is
proved that no position of the commensurable marking satisfies this
condition.

This state of affairs is easy to read as a dead end—but there would be a
dead end in only one case: if *every* mathematical object were a
position. Then “there is no position” would mean “there is no object,”
and the path would break off. But why should every object be a
position? Part III worked with the number-position because it was
unfolding the coordinate marking, and for a marking the position is a
natural and sufficient kind of object. This does not mean that there are
no other kinds. What was proved in § 4.2 does not say “there is no
object”; it says something more exact: *the object satisfying the
condition $r \cdot r = 2$ is not a position*. What it is remains an open
question, and the chapter will answer it.

### Position and the Level of Consideration

To answer, we must return to the distinction introduced in Part I—the
distinction of *levels* of consideration.

Part I showed that objects line up by levels. At one level something is
taken as an *element*—as simple, indivisible for the given
consideration, as that of which systems consist. At the level above, a
*system* is taken—that which consists of elements linked by roles and
subordinate to a rule. One and the same object can be an element at its
own level and enter as a component into a system one level up; and
Part I gave this distinction an exact language—the language of rules,
roles, and elements, by which every system is described.

Let us apply this to numbers. A rational number—a position of the
commensurable marking—is an *element*. At the level of the marking it is
simple: a point taken relative to the reference point, with no inner
arrangement that the marking would need. Part III worked precisely at
this level—the level of rational numbers as elements. And what was
proved in § 4.2 is a fact *about this level*: at the level of
element-positions, the condition $r \cdot r = 2$ is not fulfilled.

But from the fact that the condition is not fulfilled at the level of
elements, it does not follow that it is not fulfilled at all. It may be
fulfilled at a *higher* level—the level of systems composed of these
elements. And the chapter will show that this is exactly how things
are: the condition $r \cdot r = 2$ is fulfilled not by an element but by
a *system* of elements—an object of the next level.

### Role as Belonging to a Level

What has been said is worth refining in terms of role—one of the three
concepts by which Part I described the structure of a system.

“Squaring to two” is a *role*. A role is what an object does, what it
serves as, what condition it fulfills—rather than the object itself. And
every role belongs to some level: there are roles within the power of an
element and roles within the power of a system alone. An integer in the
role of a position on the two-sided marking, a rational number in the
role of a position on the commensurable one—these are roles within the
power of an element: the element copes with them, and no higher level
is required.

The role “squaring to two” is beyond the power of an element—this is
exactly what § 4.2 proved. Let us say it more exactly, so that the word
“role” does not sound too vague. The condition $r \cdot r = 2$ is a
*predicate* on rational positions—a property that a position either
bears or does not; and what was proved in § 4.2 says precisely that this
predicate is *empty* on $ℚ$: no element of type $ℚ$ fulfills it.
Formally, this is the theorem `sqrt2_not_in_Q` of the file
`Sqrt2Irrational.v`: there is no rational $r$ for which $r \cdot r$
equals $2$.[^6]
But from the fact that the predicate is empty at the level of
element-positions, what follows is “the role belongs to another level,”
not “the role cannot be fulfilled at all.” Its bearer is a system rather
than an element: an object composed of rational elements linked by roles
and a rule. What this system is and how it is arranged, the chapter will
show in the next section, analyzing it directly, by its composition.

*From the fact that the condition $r \cdot r = 2$ is not fulfilled by
any position, it does not follow that it is not fulfilled at all. A
rational number—a position—is an element: something simple at the level
of the marking. Part III worked at the level of elements, and § 4.2 is a
fact about this level. “Squaring to two” is a role, and this role is
beyond the power of an element—but within the power of a system, an
object of a higher level composed of rational elements. The condition is
fulfilled not by a position but by a system of positions.*

### Toward the Analysis of the System

So the object satisfying the condition $r \cdot r = 2$ is a system
composed of rational numbers. To name it in one word is to name a
*process*. The next section will analyze this process directly: what it
consists of, by what roles its components are linked, and by what rule
it holds together.

## The Square Root of Two as a Process

### The Classical Name and What Stands behind It

Classical mathematics calls the object satisfying the condition
$r \cdot r = 2$ the *square root of two* and writes it $\sqrt{2}$. It is
also written as a decimal fraction—$1{,}41421…$—with an ellipsis that
refers to an infinite tail of digits never written out to the end.

ToS accepts the name $\sqrt{2}$ but asks what stands behind it. And here
its answer diverges from the customary one. Customarily, $\sqrt{2}$ is
thought of as *one number*—a single object-position that “is”
somewhere, while the decimal notation only names it approximately. ToS
sees it differently: $\sqrt{2}$ is a *process*—an unfolding sequence of
rational approximations—rather than a single numerical position. ToS
does not dispute that in standard mathematics $\sqrt{2}$ is a real
number; it says that the real number itself will be understood as a
process. And this process, unlike “a single position,” can be analyzed
by its composition—which is what the chapter does.

### A Process of Refining Approximations

Let us take a concrete process that gives $\sqrt{2}$.[^7]
We start with a rough rational approximation—say, with one. And we set a
rule that turns every approximation into a more accurate one: if $x$ is
the current approximation, then

$$
x' = \frac{x + 2/x}{2}
$$

is the next approximation. This rule—averaging $x$ with the number
$2/x$—is known as the Newton iteration. Applying it again and again, we
obtain a sequence of rational numbers:

$$
1, \quad \frac{3}{2}, \quad \frac{17}{12}, \quad \frac{577}{408},
\quad …
$$

Each term of the sequence is a rational number—an existing position of
the commensurable marking, a finite amount of data. In the first steps
one can see how sharply the process refines the approximation: the
square of the first term is $1$, of the second $9/4$, of the third
$289/144$, and the third is already only $1/144$ away from two. Here,
however, precision is needed about what exactly has been *proved*. The
file `RefinementSqrt.v` proves the concrete values of the first terms
and compares the quality of approximation at step $2$; but the
statement that *each* next step is strictly more accurate than the
previous one, and the statement that the process converges, are not
proved as theorems in this file. The chapter therefore speaks
cautiously: in the first steps the sharp refinement is visible by
direct computation, while the full statement about monotone improvement
and convergence requires a separate theorem about the given process
(§ 4.5).

To say “the process gives $\sqrt{2}$” rigorously—and to say it without
referring to $\sqrt{2}$ as a point that is already ready—let us
introduce a *predicate* on processes. A process $R \colon ℕ \to ℚ$
*gives $\sqrt{2}$* if two conditions hold: first, $R$ is a Cauchy
process (its terms draw arbitrarily close to one another); second, the
error of its square, $|R(n) \cdot R(n) - 2|$, becomes smaller than any
prescribed precision. Formally:

$$
\mathrm{sqrt2\_process}(R) \;:=\;
\mathrm{is\_Cauchy}(R)
\;\land\;
\forall  \varepsilon > 0\;\;
\exists  N\;\;
\forall  n \ge N \colon\;
|R(n) \cdot R(n) - 2| < \varepsilon.
$$

Thus $\sqrt{2}$ is given as a predicate on processes—a condition that a
process of rational approximations either satisfies or does not—and
*not* as a ready point toward which something tends. It is worth saying
at once what the status of this predicate in the repository is: the
definition `sqrt2_process` itself is a natural formalization, but
theorems of the form “`sqrt2_newton` satisfies `sqrt2_process`” have
not yet been proved in the current version of `RefinementSqrt.v`; the
chapter introduces this predicate as the exact formulation that the
formalization must arrive at, not as an already proved fact.

This unfolding sequence of approximations is one of the processes that
give $\sqrt{2}$. It is *the sequence itself*, the unfolding itself—not a
point toward which the sequence “tends” and which lies somewhere apart
from it, ready. $\sqrt{2}$ is given by a process—and, as § 4.5 will
show, there is more than one such process.

### The Square Root of Two as a Functional System

The process that gives $\sqrt{2}$ is a process, and ToS analyzes it in
an exact language, the language of the *functional system* introduced
in Part I.
Every functional system decomposes into three layers—rules, roles, and
elements. First let us decompose $\sqrt{2}$ into these three layers, to
see the system as a whole; then we will analyze each layer in order.

The decomposition gives the overall picture. The *rules* of the system
$\sqrt{2}$ are the law by which it unfolds and the criterion to which it
is subordinate. The *roles* are what each of its components serves as
in the system. The *elements* are the components themselves, the
existing rational numbers. Three layers—and $\sqrt{2}$ appears as a
system that has a task, a role arrangement, and material. Now let us
analyze the layers in order, beginning with the rules: for the rules are
the task of the system, and to understand a system means first of all to
understand what it is for.

*Rules.* The rules are the constitution of the system $\sqrt{2}$, and
the analysis begins with them, for they set *what* the system does.
There are two rules here. The first is the rule of *convergence*: the
requirement that the approximations draw together without bound, that
the error decrease to zero. This is the task of the system
$\sqrt{2}$—to converge, and to converge to that whose square is two. The
second is the rule of *generation*: the formula $x' = (x + 2/x)/2$, by
which the next approximation is built from each one. The first rule
sets *toward what* the system goes; the second, *how* it goes, step by
step. Together they are the constitution: $\sqrt{2}$ is the system whose
work is to converge by this law to this limit.

*Roles.* Since the task of the system is to converge, each of its
components receives a *role* determined by this task: to be an
approximation of such-and-such quality. The role does not come to the
component from outside—it is *constituted by the rule*: inasmuch as the
rule sets the criterion of convergence, each component occupies its own
place relative to this criterion, and this place is its role. The
quality is measured directly: how close the square of the approximation
is to two. The approximation $17/12$ squares to $289/144$, which is
$1/144$ away from two—and it plays the role “an approximation with error
$1/144$.” The next approximation plays the role of a more accurate one,
the one after it of a still more accurate one. The role of a component
is its *quality* as an approximation, and ToS measures this quality by
an explicit quantity—the absolute value of the difference between the
square and two.[^8]

*Elements.* Finally, the elements are what bears these roles. The
elements of the system $\sqrt{2}$ are the rational approximations: $1$,
$3/2$, $17/12$, $577/408$, and so on. Each of them is an existing
rational number, a position of the commensurable marking built by
Part III. The elements come last in the analysis because they are
determined by the role, not because they matter little—without them the
system would have nothing to be made of: a rational number enters the
system $\sqrt{2}$ insofar as it bears the role of an approximation, and
this role is set by the rule. The system $\sqrt{2}$ introduces no new,
unknown entities: its elements are rational numbers that already exist.
$\sqrt{2}$ as a process is not a rational position—this is proved
(§ 4.2)—but all its *stages* are fully rational. It does not add a new
rational element to the marking; it sets up a *system* composed of
rational elements and linking them by roles under a single rule.

Rules, roles, elements—the analyzed process is a functional system
described in all three layers. And it is described completely: nothing
beyond the two rules, the role quality, and the rational approximations
is needed for it. Such is one process that gives $\sqrt{2}$; the next
section will show that it is not the only one. (A summary of this
analysis in a table and a check of the well-formedness of the system are
given in § 4.8.2.)

### The Square Root of Two Exists Positively

Now one can see what is mistaken in the customary picture of $\sqrt{2}$
as a “missing number”—and why ToS rejects it.

To call $\sqrt{2}$ missing, a hole, what the rational numbers lack, is to
define it *through absence*, by a view from the side of the rational
numbers: $\sqrt{2}$ as “what is not there.” But this does not define
$\sqrt{2}$ at all—it only outlines the boundary of the rational numbers,
not $\sqrt{2}$ itself. ToS defines $\sqrt{2}$ *through what is*: there
are elements—the existing rational approximations; there are
roles—their qualities; there are rules—generation and convergence.
$\sqrt{2}$ exists *positively*, as a functional system: by presence at
the level above—the level of systems composed of rational numbers—rather
than by absence at the level of the rational numbers.

This completely removes the apparent dead end of § 4.2. The condition
$r \cdot r = 2$ is not fulfilled by a position—true; but it is fulfilled
by a *system*. The rational numbers are elements, the simple; the
process that gives $\sqrt{2}$ is a system of these elements, a whole one
level up. Not “a hole in the marking” but “a system above the marking.”
Part III did not run into a defect; it reached the level of elements and
thereby led up to the level of systems.

*$\sqrt{2}$ is a process of rational approximations, not a single
number-position in $ℚ$. This process is a functional system described by
three layers: its elements are the rational approximations ($1$, $3/2$,
$17/12$, $…$), existing positions of the commensurable marking; its
roles are the quality of approximation, measured by how close the square
is to two; its rules are generation (the formula for the next
approximation) and convergence (the decrease of the error to zero).
$\sqrt{2}$ exists positively: by presence at the level of systems
composed of rational numbers, not by absence at the level of the
rational numbers.*

### Toward the Multiplicity of Processes

The chapter has analyzed one process that gives $\sqrt{2}$—the Newton
process. But it is not the only one. $\sqrt{2}$ is also given by other
processes, arranged differently—and comparing them with one another
clarifies the nature of the number-process still more exactly. The
chapter turns to this in the next section.

## There Are Many Processes

### Not One Process but a Class of Processes

The chapter has analyzed $\sqrt{2}$ as a process—as a functional system
of refining approximations. But it was *one* process that was analyzed,
the Newton process. It is worth asking: is it the only one? Does
$\sqrt{2}$ have this one process—or several?

There are several—and not merely several, but as many as one likes.
$\sqrt{2}$ is given by a whole *class* of processes rather than by one:
every rule that builds more accurate approximations from rational
approximations and converges to two in the square sets up its own
process—and there are more than one or two such rules. And this is a
feature that clarifies the very nature of the number-process, not a side
circumstance. To see it, let us place beside the Newton process another
one, arranged by a different rule—and then show that even these two do
not exhaust the class.

### The Second Process: The Continued Fraction

Alongside the Newton process, $\sqrt{2}$ is given by the
*continued-fraction* process.[^9]
It is arranged differently. The Newton process generated each
approximation by averaging; the continued-fraction process builds its
approximations by its own rule—through pairs of numerators and
denominators growing by a special recurrence. The rule is different—and
so is the sequence of approximations:

$$
1, \quad \frac{3}{2}, \quad \frac{7}{5}, \quad \frac{17}{12},
\quad …
$$

This is another process. Another rule of generation, other elements:
other rational approximations line up in the sequence.

Let us compare the two sequences. The Newton process gives

$$
1, \quad \frac{3}{2}, \quad \frac{17}{12}, \quad \frac{577}{408},
\quad …
$$

and the continued-fraction process gives

$$
1, \quad \frac{3}{2}, \quad \frac{7}{5}, \quad \frac{17}{12},
\quad …
$$

At the first step both
give $1$; at the second, both give $3/2$; the processes coincide.[^10]
But at the third step they diverge: the Newton process gives $17/12$,
the continued-fraction process $7/5$. These are different rational
numbers, and ToS records their difference in a separate theorem.[^11]
The two processes, having coincided in the first steps, go their
separate ways further on.

### Processes Are Comparable in Quality

Since there are several processes and at one and the same step they give
different approximations, it is natural to ask: which of the
approximations is *better*? And this question has an exact answer, for
ToS measures the quality of approximation by an explicit quantity
(§ 4.4).

At the third step the Newton process gives $17/12$, the
continued-fraction process $7/5$. The quality of $17/12$ is
$|(17/12)^2 - 2| = 1/144$; the quality of $7/5$ is
$|(7/5)^2 - 2| = 1/25$. The quantity $1/144$ is less than $1/25$—so the
Newton approximation is *more accurate* at this step: its square is
closer to two. ToS proves this comparison as a theorem.[^12]

The two processes, then, are not merely different—their approximations
*can be compared* by an explicit quality function. And here again
precision about what is proved is needed. In the file `RefinementSqrt.v`
a *concrete* comparison has been formally checked—at step $2$: there the
Newton approximation is more accurate than the continued-fraction one.
The general statement—that at *every* step one approximation is
comparable with the other and one can say which is closer to the
goal—is not proved by this file; it would require a separate theorem. A
reservation about the word “comparable” itself should be added too: the
qualities of two approximations are comparable by the relation
$\le$—but if at some step the qualities are equal, one cannot say “which
is better”; one can only state the equality. The exact formulation is
this: the approximations of the processes can be set against each other
by an explicit measure of quality, and one concrete comparison, at step
$2$, is proved in the repository.

### What the Multiplicity of Processes Clarifies

The multiplicity of processes clarifies the nature of $\sqrt{2}$ and
finally removes what remains of the picture of the “missing number.”

If $\sqrt{2}$ were a single point, a single missing number, then it
would be meaningless to speak of “different $\sqrt{2}$”: the point is
one, and all paths to it merely grope for it in different ways. But
$\sqrt{2}$ is a process, not a point, and there *really* are several
processes: the Newton process and the continued-fraction process are
different systems—different rules, different elements, different
quality at each step. They are different ways of unfolding $\sqrt{2}$;
they do not “approximate one and the same number given in advance.”

Here it must be said exactly in what sense these different processes
give *one and the same* $\sqrt{2}$. Not in the sense that they are equal
as processes: the equality of processes “step by step” (in the
repository, the relation `process_eq` of the file
`ProcessRefinement.v`, which requires coincidence at *every* step) does
not hold for them—they diverge already at the third step. Their unity
is given by a weaker relation—the *equivalence relation of
processes*—and *not* by step-by-step equality: two processes are
equivalent if their mutual distance becomes smaller than any prescribed
precision—if $|R(n) - S(n)|$ goes to zero. Such a relation already
exists in the repository—it is `process_equiv` of the file
`ProcessCore.v`, defined as

$$
\mathrm{process\_equiv}(R, S) \;:=\;
\forall  \varepsilon > 0\;\;
\exists  N\;\;
\forall  n \ge N \colon\;
|R(n) - S(n)| < \varepsilon,
$$

and for it reflexivity, symmetry, and transitivity are proved
there—that is, it is a *genuine* equivalence relation.[^13]
And then $\sqrt{2}$, in the process reading of ToS, is a *class of
equivalent* processes of rational approximations—the class of all
processes that satisfy the condition $\mathrm{sqrt2\_process}$ (§ 4.4)
and are equivalent to one another by `process_equiv`—rather than a
separate rational position or one distinguished process.

The two analyzed processes are enough to see non-uniqueness—but it is
worth saying exactly what is *shown* here and what is *sketched*.
Formally, in the file `RefinementSqrt.v`, *two* concrete processes are
built and compared—the Newton process and the continued-fraction
process—and their difference at step $2$ is proved. These two alone are
enough to assert that the process representation of $\sqrt{2}$ is not
unique. The stronger statement—that there is an *open family* of such
processes—is natural and mathematically standard, but in the current
version of the repository it is not formalized, and the chapter presents
it as a substantive program, not as a proved fact. In substance, its
grounds are these: the Newton rule $x' = (x + 2/x)/2$ applies to any
initial rational approximation (the chapter started with one, but one
can start with $3/2$, with $2$, with another reasonable fraction—and
every choice of starting point gives its own process with the same
rule), and besides the Newton rule and the continued-fraction rule there
are other refinement rules as well. A full formalization of the open
family would require, for example, parametrized Newton processes with
different initial approximations and a proof of their convergence.

And one more reservation about words. Speaking of the collection of
processes that give $\sqrt{2}$, the chapter uses the words *class*,
*family*, *scheme*—but not the word *set* in the sense of a completed,
ready collection. This agrees with the principle $P4$: ToS does not take
the collection of all processes as a completed totality, as a ready,
gathered whole. $\sqrt{2}$ is an *open scheme* of processes given by
refinement rules—an open class of equivalent rational processes—rather
than a completed set of all its processes.

Here one can see how deceptive the metaphor of a *hole* would be. A hole
is a single empty place, a lack, an absence. In fact, in the place of
$\sqrt{2}$ there is *abundance*, not absence: a multitude of processes,
each a full-fledged functional system with rules, roles, and elements,
and all of them comparable with one another. Where the customary
picture saw emptiness, ToS discovers a richly arranged domain—a family
of processes. A surplus, not a lack.

*$\sqrt{2}$ is given by a class of processes, not by one process.
Alongside the Newton process, it is given by the continued-fraction
process—with a different rule of generation and different
approximations ($1, 3/2, 7/5, 17/12, …$). The two processes coincide in
the first steps and diverge further on; one comparison of their quality,
at step $2$, is proved in the repository. Different processes give one
$\sqrt{2}$ because they are equivalent—their mutual distance goes to
zero (`process_equiv`)—not because they are equal step by step.
$\sqrt{2}$, then, is an open class of equivalent convergent processes,
not a point and not a single process. The metaphor of a hole is
deceptive: in the place of $\sqrt{2}$ there is abundance, not absence.*

### Toward the Attainability of Approximations

The chapter has shown that $\sqrt{2}$ is given by a process and that
there is an open class of such processes. Among the rules of the process
(§ 4.4) was the rule of convergence—the requirement that the error
decrease to zero. The requirement itself is established; but whether it
can be fulfilled depends on the arrangement of the rational numbers. The
property of their arrangement that makes the rule of convergence
fulfillable is analyzed in the next section.

## Approximation Is Attainable: The Archimedean Property

### What the Rule of Convergence Requires

Analyzing $\sqrt{2}$ as a functional system (§ 4.4), the chapter named
among its rules the rule of *convergence*: the requirement that the
error of the approximations decrease to zero. This rule is already
established—it is part of the constitution of the system. Let us now ask
what in the arrangement of the rational numbers makes it *fulfillable*.

The question is not an idle one. The rule of convergence requires that
for any prescribed precision—however small—the process sooner or later
give an approximation of at least that precision. The rule by itself
only *requires* this; whether the requirement can be fulfilled depends
on the material over which the process unfolds—the rational
numbers—rather than on the rule. It could turn out that the process
refines and refines—and still does not come closer to the goal than
some line, getting stuck before it arrives. Then the rule of convergence
would remain empty: a requirement with nothing to satisfy it.

And in fact the rational numbers are arranged so that the rule of
convergence can be fulfilled. What exactly in their arrangement provides
this has an exact name: the *Archimedean property*. The chapter points
out, in what has already been built (Chapter III.2), the property of the
rational numbers that *fits* the rule of convergence and makes it
fulfillable; it neither introduces this property as a new assumption nor
checks a hidden premise after the fact.

### The Archimedean Property

The Archimedean property, in the form in which refinement processes need
it, speaks of halving.

Take the fraction $1/2$, then half of it—$1/4$, then half of the
half—$1/8$, and so on: $1/2$, $1/4$, $1/8$, $1/16$, $…$—fractions that
halve at each step. The Archimedean property asserts: *however small a
precision is set, there is an even smaller fraction in this sequence of
halving fractions.* However tight a measure $\varepsilon$ we take, there
is a number of steps $N$ such that the fraction $1/2^N$ is already less
than $\varepsilon$.

ToS proves this rigorously.[^14]
At the basis of the proof is the fact that the powers of two grow
without bound: $2^N$ will sooner or later exceed any prescribed number,
and hence the reciprocal $1/2^N$ will become smaller than any prescribed
fraction. The powers of two grow by a proved lemma, not by assumption:
ToS derives their unbounded growth from the arrangement of the natural
numbers themselves.

### Attainability as a Property of a Process

It is worth reading closely what exactly the Archimedean property
says—for it speaks of a *process*, and speaks in the language of ToS.

The Archimedean property asserts something more modest: for every given
precision, the halving process *attains* it in a finite number of steps.
It does not assert that some “infinitely small” quantity exists or that
the sequence of halving fractions “reaches zero.” Not “there is a
completed infinity of fractions” but “there is a procedure, and it gets
there”: set a precision, and the procedure will name the step $N$ at
which this precision is attained. This is the same operational
understanding with which Chapter III.3 endowed countability: a property
of a working procedure, not of a ready collection.[^15]

And here is what the Archimedean property gives to the processes of
§ 4.4 and § 4.5—but precision is needed here so as not to say more than
is proved. The Archimedean property by itself does *not* prove the
convergence of *each concrete* process. It supplies a general
*instrument*: it ensures the attainability of arbitrarily small rational
measures—for every precision there is a step at which the fraction
$1/2^N$ is already smaller than it. For this instrument to vouch for a
concrete process, one more thing is needed: an *error estimate* must be
obtained for the process in terms of decreasing fractions—say, an
estimate of the form $C/2^N$, or one through the width of shrinking
intervals. If such an estimate is proved for the process, then the
Archimedean property, applied to it, ensures that any precision is
attained. By itself, without an error estimate for the concrete process,
the Archimedean property does not give the convergence of that process.
Thus the file `Archimedean_ERR.v` proves not only `Archimedean`
but also `Archimedean_width` (attainability for a scaled
width) and `shrinking_interval_Cauchy`—the theorem that a
process held within intervals of decreasing width is a Cauchy process;
and it is the combination “width estimate $+$ Archimedean property” that
does vouch for convergence. The convergence of which the chapter spoke as
a rule of the process (§ 4.4) turns out, then, to be a requirement that
can be fulfilled—but fulfilled through an error estimate to which the
Archimedean property is applied, not through the Archimedean property
alone.

*The rule of convergence (§ 4.4) requires that the error of the
approximations decrease to zero; whether this requirement can be
fulfilled depends on the arrangement of the rational numbers. The
property of their arrangement that makes the rule fulfillable is the
Archimedean property: for any prescribed precision $\varepsilon$ there
is a step $N$ at which the fraction $1/2^N$ is already less than
$\varepsilon$. ToS proves it. This property speaks of a process: not
“there is a completed infinity of fractions” but “the halving procedure
attains any precision in a finite number of steps.” By itself it does
not prove the convergence of a concrete process—it gives an instrument:
applied to an error estimate of the process (through decreasing
fractions or the width of shrinking intervals), it vouches that the
process gets to any precision.*

### Toward the Convergence of the Process

The Archimedean property vouches that the process attains any
*individually taken* precision. But a process is something more than a
set of scattered attainments: its approximations must draw together
*among themselves*, converge in a single movement. What exactly this
inner convergence of the process means and how the Archimedean property
ensures it is analyzed in the next section.

## Shrinking Intervals: The Process Is Cauchy

### The Inner Convergence of a Process

The Archimedean property (§ 4.6) vouches that the process attains any
*individually taken* precision. But a process is a single movement, not
a set of scattered attainments, and its convergence lies in more than
its approaching the goal. The convergence of a process is first of all
its *inner* property: its own approximations, taken at sufficiently
distant steps, draw together *among themselves*.

The distinction is subtle but essential. One can speak of convergence by
pointing to the goal: the approximations approach $\sqrt{2}$. But the
goal—$\sqrt{2}$—is itself a process, and to define the convergence of a
process through approximation to a process would be to go in a circle.
ToS defines convergence *from within*, without referring to the goal: a
process converges if its own terms draw arbitrarily close to one
another. This is the property called the *Cauchy* property.

### The Cauchy Process

ToS defines the Cauchy property exactly.[^16]
A process is a *Cauchy* process if for any prescribed precision
$\varepsilon$ there is a step $N$ such that *any* two approximations
taken after it are less than $\varepsilon$ apart. Not “the
approximations approach the goal” but “the approximations, from some
step on, crowd together more tightly than any prescribed measure.”

This definition is operational, in the same sense in which countability
(Chapter III.3) and the Archimedean property (§ 4.6) are operational. It
does not speak of a completed infinity and does not point to a ready
limit. It describes the *behavior* of the process: set a measure
$\varepsilon$—and the process will indicate the step after which all its
terms fit within this measure in their mutual distance. The Cauchy
property is a characteristic of behavior, not of data—and in this it
matches the process itself, which is likewise behavior, not data
(Chapter III.3, § 3.7).

### Shrinking Intervals

Where does the process that gives $\sqrt{2}$ get the Cauchy property
from? From the way such a process is arranged—from the mechanism of
*shrinking intervals*.

The mechanism is this. Take an interval known to contain what is
sought—that toward which the process goes. Divide the interval and keep
the half within which what is sought still lies. Do the same with it:
divide, keep the needed half. Step by step—nested intervals, each half
as long as the previous one: their width decreases
$1, 1/2, 1/4, 1/8, …$—that is, it decreases in the way the halving
fractions of § 4.6 do.

And here is the connection with the Archimedean property. All
approximations of the process from step $N$ on lie inside the $N$-th
interval—and its width, by the Archimedean property, becomes smaller than
any prescribed measure. Hence any two approximations taken after step
$N$ are no farther apart than the width of this interval—that is, less
than any prescribed $\varepsilon$. And this is the Cauchy property. ToS
proves this connection as a theorem: the process of *shrinking
intervals* that defines $\sqrt{2}$ is a Cauchy process.[^17]

Precision is needed here so as not to say more than is proved. The
theorem `shrinking_interval_Cauchy` speaks of a process of a *special
kind*—a process of shrinking intervals that holds its approximations
within nested intervals whose width halves at each step. The Newton
process and the continued-fraction process of § 4.4 and § 4.5 are
processes of *another* type: they are generated by their own formulas
(averaging, a recurrence of numerators and denominators), not by halving
an interval. Therefore the theorem on shrinking intervals does *not*
automatically prove that the Newton process or the continued-fraction
process is a Cauchy process: for each of them the Cauchy property
requires an error estimate *of its own*. The exact picture is this: the
general mechanism of shrinking intervals shows that for a process to be
a number-process it is *sufficient* to have rational stages held within
nested intervals whose width goes to zero; and the process of shrinking
intervals that defines $\sqrt{2}$ is, by this mechanism, a Cauchy
process. For the Newton and continued-fraction processes, however, the
statement “this is a Cauchy process” needs convergence estimates of
their own—and these estimates are not proved in the current version of
`RefinementSqrt.v` (§ 4.5).[^18]

### Where the Boundary of Part III Lies

Here Part III reaches its limit—and it is worth saying exactly where
this limit lies.

Part III has established: $\sqrt{2}$ is given by a process—a functional
system of rational approximations (§ 4.4); there is an open class of
such processes (§ 4.5); every such process attains any precision
(§ 4.6) and is a Cauchy process (§ 4.7). Part III goes no further than
this—by the design of its plan, not for want of means. For behind what
has been analyzed rise questions of another order. The *process* as an
independent subject—not as a process that gives $\sqrt{2}$ in
particular, but as an object in its own right, with its own structure
and its own relations—requires a separate construction. And the
question posed back in Chapter III.3 (§ 3.7)—whether processes are
enumerable in the same way as the rational numbers are—remains
unresolved: the chapter on countability showed that a process is
behavior, not data, and that there are no grounds here for
enumerability, but Part III does not undertake to *prove* that processes
are not enumerable.

These questions make up the subject of Part IV. Part III has developed
the number-position in full and shown that behind it the number-process
unfolds; it has analyzed the first such process, $\sqrt{2}$, and
established the main thing about it. But the process as such, the real
numbers as processes, and the uncountability of processes—all this
Part IV builds anew and separately. The present chapter brings the
exposition to the threshold; crossing it is the task of the next part.

*The convergence of a process is its inner property: the approximations,
from some step on, draw arbitrarily close to one another. This is the
Cauchy property, defined operationally, as the behavior of the process.
The process of *shrinking intervals* that defines $\sqrt{2}$ provably
has it: nested intervals of halving width hold the approximations, and
the Archimedean property vouches that their mutual distance becomes
smaller than any measure. For processes of another type—the Newton and
continued-fraction processes—the Cauchy property requires convergence
estimates of their own. Here Part III reaches its limit: the process as
an independent subject and the uncountability of processes are the
subject of Part IV.*

## Summary of Part III. Transition to Part IV

### What the Chapter Has Covered

The chapter has traveled the path from the number-position to the
number-process.

It began with a concrete problem: a square equal to two—the length of
the diagonal of the unit square (§ 4.1). And it showed, by a rigorous
proof by infinite descent, that no position of the commensurable marking
answers this problem (§ 4.2). The chapter separated the levels—the level
of the element and the level of the system—and showed that the condition
$r \cdot r = 2$ is beyond the power of an element-position but within
the power of a system of elements (§ 4.3). It is such a system that the
chapter analyzed: $\sqrt{2}$ is a process—a functional system
decomposed into rules, roles, and elements (§ 4.4). Such processes
turned out to form an open class (§ 4.5); the chapter showed that the
process attains any precision—by the Archimedean property (§ 4.6)—and
that it is a Cauchy process: its approximations draw arbitrarily close
to one another (§ 4.7).

The result of the chapter: $\sqrt{2}$ is the name of a *class of
processes*—an open family of convergent functional systems that give a
square equal to two. This is a number-process: a number that exists
positively at the level of systems composed of rational positions.

### E/R/R Analysis: The Number-Process as a Functional System

The main transition of the chapter—from the number-position to the
number-process—is worth securing by an E/R/R analysis (Part I). The
chapter already decomposed the system $\sqrt{2}$ into its three layers
in § 4.4, in the ontological order, beginning with the
rules-constitution; let us now gather the analysis into a table—taking
into it also what was added in § 4.5–4.7—and check the well-formedness
of the system. The reservation about status is the same as before: the
“system” here is a substantive interpretation on the model of the
functional system of Part I, not an object `System` $L$ built
in the code; the unity of the processes is taken through the *weak*
relation `process_equiv`, and the predicate `sqrt2_process` is a target
formalization (§ 4.4–4.5).

| Component | What it determines | E/R/R |
|---|---|---|
| the rule of generation and the rule of convergence | the constitution of the system | Rule |
| unity of the processes: `process_equiv` (weak) | criterion of identity | Rule |
| Archimedean attainability; Cauchy process | conditions of convergence | Rule |
| quality `sqrt2_quality` $= |x \cdot x - 2|$ | the role of a component | Role |
| rational approximations $1, 3/2, 17/12, …$ | bearers (finite, $P4$) | Element |
| laws $L1$–$L5$ (here $L3$ for the limit) | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: the two rules are the
constitution, the quality of approximation is the role, the rational
approximations are the elements; no layer substitutes for another. The
principle $P1$ (no self-membership) is observed as well: the system
$\sqrt{2}$ is composed of elements *one level below*—existing rational
positions—and not of itself; the chapter separated the level of the
element and the level of the system back in § 4.3. And here the
analysis turns into *diagnostics*. The classical picture “$\sqrt{2}$ is
a missing number, a hole among the rationals” arises from a confusion of
categories: a role within the power of a *system* alone (“squaring to
two”) is sought among *element*-positions—and, not being found, is
declared a lack. In the correct labeling there is no lack: the role is
borne by a system of rational elements, and $\sqrt{2}$ exists positively
(§ 4.4). The honest boundaries are preserved here: `sqrt2_not_in_Q` is
proved constructively (without $L3$), whereas the theory of shrinking
intervals of § 4.7 rests on $L3$—these are different statuses, and they
should not be conflated.

What the analysis yields. It secures the whole path of Part III by a
single distinction of levels. The integer and the rational are
number-*positions*, roles within the power of an *element*; $\sqrt{2}$ is
the first number whose role is within the power of a *system* rather
than of an element: a number-process. E/R/R shows *why* the threshold
lies exactly here—what changes is the *level of the role’s bearer*, not
the material (the elements are still rational). With this, Part III
exhausts the number-position and hands the number-process over to
Part IV, where the process will be taken as an independent subject—with
its own equality, order, and structure.

### What Part III Has Covered

The present chapter completes Part III, and it is worth surveying its
whole path.

Part III began with the natural number series obtained in Part II and
asked what unfolds from it further. The answer was a succession of
coordinate markings. Chapter III.1 unfolded the *integers*—a two-sided
coordinate marking with a reference point and a unit step: the minus
sign was read as the opposite orientation of a displacement relative to
the reference point, not as negative existence, and both sides of the
marking turned out to be equally extendable. Chapter III.2 unfolded the
*rational numbers*—a commensurable marking with a fractional step,
dense, inheriting from the integers the coordinate sense of the sign.
Chapter III.3 showed that the rational numbers are *enumerable*—by
building an explicit constructive traversal. And the present chapter
showed that behind the rational numbers the *number-process* unfolds,
analyzing its first example—$\sqrt{2}$.

This whole path—from the natural number series to the rational
numbers—was the path of the *number-position*. The natural number, the
integer, the rational—all are positions of a coordinate marking, points
taken relative to the reference point. Part III developed this idea in
full: it built the markings, showed their arrangement, their asymmetry,
their enumerability—and reached the threshold at which the
number-position exhausts itself and beyond which the number-process
unfolds.

### A Positive Result

It is worth saying in what *mode* Part III traveled this path, for the
mode was sustained from the first chapter to the last.

Part III nowhere spoke of a lack. The integers did not “make up for a
deficiency” of the naturals; the rationals did not “patch the holes” of
the integers; $\sqrt{2}$ did not “compensate for a shortfall” of the
rationals. Each time something *new* unfolded—and unfolded from what
already was, by tracing what was laid down in it. The integers arose
when the act of distinction was taken in both directions from the
reference point; the rationals, when it was taken inside the step; the
number-process, when a role was found that is within the power of a
system, not of an element. No number system was deficient; each was
full at its own level, and each led up to the next level.

And $\sqrt{2}$—the last thing Part III arrived at—is a result that is
precisely positive. A richly arranged functional system, not an empty
place among the rational numbers: an open class of convergent
processes, each with its own rules, roles, and elements. Where the
customary view saw a shortfall, ToS discovered a surplus.

### Transition to Part IV

Part III has brought the exposition to the threshold beyond which the
subject of Part IV lies.

The chapter analyzed the number-process on one example—$\sqrt{2}$. But
$\sqrt{2}$ is only the first of the processes, and the process was taken
here as the process that gives this number in particular. Part IV will
take the *process as such*—as an independent subject, with its own
structure, its own relations, its own equality and order. It will build
the real numbers as processes, not as positions. And it will return to
the question left open back in Chapter III.3 and confirmed by the
present chapter: are processes enumerable? Here Part IV will have to
*specify which class of processes is meant*. Computable processes, given
by finite rules or programs, are enumerable precisely *as programs*—as
finite expressions over a countable alphabet (Chapter III.3). But
arbitrary process-behaviors, functions $ℕ \to ℚ$, do not reduce to the
collection of finite programs, and the corresponding space of process
behaviors has a different status. Part III showed that a process is
behavior, not data, and that there are no grounds for the enumerability
of *arbitrary* processes; Part IV will prove uncountability—and will
prove it for the space of process behaviors, carefully outlining which
class of processes is meant, not for “processes in general” in the sense
of programs.

With this, Part III comes to an end. It has traveled the path of the
number-position from the natural number series to the rational numbers,
developed it in full, and reached the threshold beyond which the
number-process unfolds. Crossing this threshold and building the real
numbers as processes is the task of Part IV.

---

[^1]: The proof set out in this section is formalized in the file `Sqrt2Irrational.v` of the ToS Rocq repository (directory `analysis`). The file contains 14 proved statements, rests on no axiom, and does not use the law of excluded middle.
[^2]: The lemma `sq_even_implies_even` of the file `Sqrt2Irrational.v`: if $n \cdot n$ is even, then $n$ is even.
[^3]: This is the lemma `sq_eq_2sq_both_even` of the file `Sqrt2Irrational.v`.
[^4]: The descent step is the lemma `descent_step` of the file `Sqrt2Irrational.v`: from $p^2 = 2 q^2$ one builds $p' = p/2$ and $q' = q/2$ with the same $p'^2 = 2 q'^2$.
[^5]: This is the lemma `descent_to_zero` of the file `Sqrt2Irrational.v`, proved by strong induction (Rocq: `lt_wf_ind`) on the measure $|p| + |q|$, more exactly on $\texttt{Z.to\_nat}(|p| + |q|)$: every solution of $p^2 = 2 q^2$ is $p = 0$, $q = 0$. Each step of the descent strictly decreases this measure, and there can be no infinitely decreasing chain of natural-number measures.
[^6]: `sqrt2_not_in_Q` of the file `Sqrt2Irrational.v`: $\lnot (\exists  r : ℚ,\; r \cdot r == 2)$. The predicate “the square equals two” is not realized by any element of type $ℚ$.
[^7]: The processes analyzed in this section and the next are formalized in the file `RefinementSqrt.v` of the ToS Rocq repository (directory `stdlib`). The file defines the processes `sqrt2_newton` and `sqrt2_cf` and proves their concrete values at the first steps; on the limits of what is proved, see § 4.5.
[^8]: In the file `RefinementSqrt.v` the quality of approximation is defined by the function `sqrt2_quality`, which assigns to a number $x$ the quantity $|x \cdot x - 2|$.
[^9]: Both processes—the Newton process and the continued-fraction process—and their comparison are formalized in the file `RefinementSqrt.v` of the ToS Rocq repository.
[^10]: The coincidence at steps $0$ and $1$ is proved in `RefinementSqrt.v` by the lemmas `agree_at_0` and `agree_at_1`.
[^11]: That the approximations of the two processes differ at step $2$ is proved by the lemma `differ_at_2` of the file `RefinementSqrt.v`.
[^12]: That at step $2$ the Newton approximation is more accurate—smaller in the quality measure `sqrt2_quality`—is proved by the lemma `newton_better_at_2`; the coincidence at the early steps and the divergence with Newton’s advantage at step $2$ are combined in the theorem `sqrt2_strict_refinement` of the file `RefinementSqrt.v`.
[^13]: `process_equiv` (notation `~~`) of the file `ProcessCore.v`; `process_equiv_refl`, `process_equiv_sym`, `process_equiv_trans` are proved there as well. Let us note for precision that in its current form the chapter *uses* `process_equiv` as a ready definition from the repository, but the theorem “the Newton process and the continued-fraction process are equivalent by `process_equiv`” has not yet been proved in the repository; the chapter points to this relation as the one by which the unity of the processes is to be expressed.
[^14]: The Archimedean property in this form is the theorem `Archimedean` of the file `Archimedean_ERR.v` of the ToS Rocq repository: for every $\varepsilon > 0$ there exists $N$ for which $1/2^N < \varepsilon$. The file contains 14 proved statements and introduces no axiom; in particular, no axiom of infinity is used.
[^15]: The file `Archimedean_ERR.v` states explicitly that the Archimedean property is a statement about processes: for every precision the halving process attains it, and no completed infinity is required for this.
[^16]: The definition `is_Cauchy` and the theorems of this section are in the file `ShrinkingIntervals_ERR.v` of the ToS Rocq repository. A reservation is in order: different files of the formalization use equivalent technical variants of the Cauchy condition—with indices $n > N$ (as in `ShrinkingIntervals_ERR.v` and `Archimedean_ERR.v`) or with indices $N \le n$ (as in the file `ProcessCore.v`). In substance they express one and the same thing—from some step on, all further terms of the process are mutually close—and they translate into each other by shifting the index by one; the chapter therefore speaks of one property in substance, written in equivalent forms, rather than of a *single* definition.
[^17]: The theorem `shrinking_interval_Cauchy` of the file `ShrinkingIntervals_ERR.v`: if the width of nested intervals decreases like the halving fractions, then a process that stays inside them satisfies the property `is_Cauchy`. The proof rests on the Archimedean property (§ 4.6).
[^18]: The difference in the logical environment of the files is also worth noting. The proof of the irrationality of $\sqrt{2}$ (§ 4.2, the file `Sqrt2Irrational.v`) is fully constructive—without the law of excluded middle. The general file `ShrinkingIntervals_ERR.v`, by contrast, works in the classical environment of ToS: it imports `ToS_Axioms` and classical logic (`Classical_Pred_Type`) for some limit arguments, and the comment in the file says so explicitly. This is the use of the already accepted formal layer of ToS—the law of excluded middle $L3$, which belongs to the foundations (Part I)—not a new axiom of the present chapter. The constructiveness of the proof of $\sqrt{2} \notin ℚ$ and the reliance on classical logic in the general theory of shrinking intervals are different statuses, and they should not be conflated.

---

Part: [[03 From Naturals to Rationals|Part III. From Naturals to Rationals]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/03 From Naturals to Rationals/03 Countability of the Rationals|Chapter 3. The Countability of the Rational Numbers]] · [[Library/Branches/Mathematics/Volume/04 Process Real Numbers/01 P4 Infinity as Process|Chapter 1. P4: Infinity as Process—Part IV]] →
