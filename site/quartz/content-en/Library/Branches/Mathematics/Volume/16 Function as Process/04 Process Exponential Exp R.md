---
title: "Chapter 4. The Process Exponential exp_ℝ"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/16 Функция как процесс/04 Процессная экспонента exp_ℝ.md"
sourceBlob: 92c35df94ed5233f41e383efaf6ef3825d5fbf57
translated: 2026-10-20
status: draft
---

## The Plan of the Chapter and the Change of Tier

The formal heart of Chapter 16.3—the identity $e^{-\ln(1-x)} = 1/(1-x)$—was obtained *on coefficients*: as an equality of formal series. To transfer it into an equality of *number*-processes (at every point $|x|<1$), we need a tool that we do not yet have: an exponential able to take as its argument a *whole process* rather than a rational number—the real exponential $\exp_{ℝ}\colon
\texttt{CauchySeq} \to \texttt{CauchySeq}$. This chapter builds it.

And here let us honestly note the *change of tier*. Chapters 16.1–16.3 lived on the 0-axiom, purely formal side: everything was finite arithmetic of coefficients. Starting with this chapter we enter the *analytic* layer—the layer of Cauchy reals, where limits are at work. The analytic *estimates* are axiom-free in themselves, but the whole construction of the real exponential rests on the Law of Excluded Middle, L3. This is the first tier of Part XVI where L3 appears, and we mark it directly: the notes here say “no new axioms, only L3,” not “0 axioms.”

The road is as follows. First, the engine: *Mertens’* theorem on the product of series, constructively over $ℚ$ (§ 16.4.2). On it, the *rational* exponential as a group homomorphism: the addition theorem, unit, invertibility (§ 16.4.3). Then the exponential *of a process*, $\exp_{ℝ}$, via a diagonal limit (§ 16.4.4). And finally its group homomorphism on the reals and *injectivity*, with two devices of our own (§ 16.4.5). The E/R/R analysis and the transition to the bridge of Chapter 16.5 complete the chapter (§ 16.4.6).

## The Engine: Mertens’ Theorem

For the exponential to be *multiplicative*—$\exp(u+v) = \exp(u)\exp(v)$—one must be able to multiply series as limits. Mertens’ general principle: the *Cauchy product* of two convergent series, at least one of which converges absolutely, converges to the product of their limits,

$$
\Bigl(\sum_i a_i\Bigr)\Bigl(\sum_j b_j\Bigr) = \sum_n \Bigl(\sum_{i+j=n} a_i b_j\Bigr).
$$

In the formalization we prove a form *sufficient* for our purpose rather than its most general form: a specialized rational version in which *both* series converge absolutely—their absolute partial sums are uniformly bounded—which is exactly the case of exponential series. This version suffices for all the multiplicativity that follows.

In our system it is built *constructively over $ℚ$*—without recourse to the Rocq library type of real numbers, as an equality of processes. “Constructively over $ℚ$” here means that the estimates themselves and the finite algebraic identities are carried out over rational thresholds and partial sums; the passage from them to an equality of Cauchy processes already uses L3. The substantive step is a difference identity that turns the unmanageable off-diagonal part $A_n B_n - C_n$ into a block sum that can be estimated by Cauchy tails; the capstone is an $\varepsilon/2$ argument over two thresholds. The library *did not have* this engine—the auxiliary splitting of the partial sum had once been left unproved by the author; here it is revived and carried through to a full theorem.[^1]

## The Rational Exponential: Addition and the Group Homomorphism

The first application of Mertens is the *addition theorem* of the exponential on a rational argument:

$$
\exp(u+v) \;\sim\; \exp(u)\cdot\exp(v)
$$

(here $\sim$ is the equality of number-processes). The proof reduces *all* the analysis to one coefficientwise identity: the convolution of the exponential series at the points $u$ and $v$ is the exponential series at the point $u+v$. And that identity is pure finite algebra: the *convolution recurrence* $(n+1) c_{n+1} = (u+v) c_n$, that is, the factorial form of the binomial identity *without* the binomial coefficients themselves.[^2]

With two companions the addition theorem turns the exponential into a *group homomorphism*. Unit: $\exp(0) \sim 1$. Invertibility: $\exp(-u)$ is the inverse of $\exp(u)$, since $\exp(u)\cdot\exp(-u) \sim
1$.[^3] The three process equalities together,

$$
\exp(u+v)\sim\exp(u)\cdot\exp(v),\quad \exp(0)\sim 1,\quad \exp(u)\cdot\exp(-u)\sim 1,
$$

say that the exponential behaves as a *homomorphism* from the additive group of the rationals $(ℚ,+,0,-)$ into the *multiplicative group of invertible Cauchy processes* (these are the positive reals $ℝ^{+}$ as a process structure)—addition passes into multiplication, zero into one, negation into inversion. This is the very canonical homomorphism that Part XI (algebra) knows abstractly; here it is built explicitly, over processes—as a set of proved group identities (we do not introduce a separate carrier $ℝ^{+}$ for this).

## The Exponential of a Process: $\exp_{ℝ}$

So far the exponential takes a *rational* number as its argument. But a real number in our system is a *process* $P\colonℕ\toℚ$ (Part IV). To take the exponential of a real, we need $\exp_{ℝ}$, whose argument is a whole process.

It is built by a *diagonal*. Each rational approximation $P n$ gives a number-process $\exp(P n)$; the result is a sequence of processes, and its diagonal

$$
\exp_{ℝ}(P) \;:=\; \operatorname{diag}_n \exp(P n)
$$

is again a single Cauchy process—provided that the sequence of processes is *meta-Cauchy*.

```coq
Definition exp_R (P : CauchySeq) : CauchySeq :=
  diagonal_limit (fun n => exp_limit (P n)) (exp_meta_cauchy P).
```

Meta-Cauchy rests on two *uniform* pillars (the process $P$ is bounded by a number $B$). The first is the *uniform tail* of the exponential series: for all arguments of modulus $\le B$ the tail of the series is uniformly small. The second is *Lipschitz continuity in the argument*: close arguments give close partial sums, because $|a^{k} - b^{k}| \le k B^{k-1} |a-b|$ (telescoping of powers). The analytic core of these estimates is *axiom-free*.[^4] This is the real exponential that the system did not have: the earlier $\exp$ could take only a rational argument. *The image of P4*: each $\exp(P n)$ is already a number-process, and $\exp_{ℝ}(P)$ takes the diagonal limit over these processes—that is, a role-limit of a *sequence* of role-limits (a process of processes), reduced by completeness to a single Cauchy process.

## The Homomorphism and Injectivity

The real exponential inherits the structure of the rational one—and adds injectivity to it.

The *addition theorem* holds on processes as well: $\exp_{ℝ}(P+R) \sim \exp_{ℝ}(P)\cdot
\exp_{ℝ}(R)$. It cannot be proved “by a product of diagonals”: on the completion there is no continuity of multiplication. The device is different—the *diagonal Mertens*: on the diagonal $n$ the difference $\Sigma\exp(P_n)\cdot
\Sigma\exp(R_n) - \Sigma\exp(P_n{+}R_n)$ *is* a Mertens block, bounded by uniform dominating functions. Together with unit and invertibility, this gives the full group homomorphism already on the reals.[^5]

*Injectivity*: $\exp_{ℝ}(A) \sim \exp_{ℝ}(B) \Rightarrow A \sim B$. Here there is a constructive subtlety: the partial sums of the exponential of a *negative* argument are not monotone, and the naive estimate does not go through. The device is *regime-free*: everything reduces to the kernel $\exp_{ℝ}(D)\sim 1 \Rightarrow D\sim 0$, and the kernel is settled without a quadratic tail—from $\exp_{ℝ}(D)\sim 1$ one also derives $\exp_{ℝ}(-D)\sim 1$ (via invertibility), then a sign splitting of $D$ with the *monotone lower bound* $1+t \le
\sum\exp\text{-term} t$ (for $t\ge 0$), applied to $D$ and to $-D$.[^6]

Injectivity is the last lever toward Chapter 16.5: it is precisely what will allow us to conclude the equality of the arguments from the equality of the exponentials, closing the functional equation of the logarithm.

## E/R/R Analysis, the Tier, and What the Chapter Prepares

| component of the chapter | role in the system | E/R/R layer |
|---|---|---|
| terms of the $\exp$-series and their partial sums | bearers, finite at stage $n$ | Element (P4) |
| $\exp_{ℝ}$—the exponential of a process | role-function (the real $\exp$) | Role |
| addition theorem, group homomorphism | role-homomorphism $({+})\to({\cdot})$ | Role |
| Mertens, diagonal Mertens, regime-free injectivity | process estimates | Rule (L3) |

**Elements.** At every stage $n$ there are finite rational partial sums of the exponential series and finite convolutions. The Element side is intact.

**Roles.** $\exp_{ℝ}$ plays the role of the *real exponential*; the addition theorem, the role of a *homomorphism* from the additive group $(ℚ,+)$ into the multiplicative group of invertible Cauchy processes; Mertens, the role of the *engine* that carries the coefficientwise convolution over into a limit equality.

**Rules.** The convolution recurrence, the diagonal Mertens, and regime-free injectivity are the rules by which process estimates are assembled into theorems.

**P4 diagnostics and the tier.** $\exp_{ℝ}(P)$ is a role-limit of a sequence of processes, reduced by completeness to a single Cauchy process: the real = a process, the exponential of the real = a role-limit of processes. And here is the honest mark of the tier: unlike the 0-axiom formal calculus of Chapters 16.1–16.3, this layer rests on L3 (the Law of Excluded Middle). The analytic *estimates* (the Lipschitz bound for powers, the uniform tail, Mertens’ difference identity) are *axiom-free*; but the whole construction of the real exponential and of the addition theorem is *only L3*, with no other axioms.[^7]

**What is new.** Mertens’ theorem, the addition theorem of the exponential, and its injectivity are classical analysis. What is new is their *constructive-over-$ℚ$* reading as equalities of processes (without recourse to the Rocq library type of real numbers), two devices of our own (the diagonal Mertens and regime-free injectivity), and the filling of a real gap in the system: there was previously neither a real process exponential nor a Mertens engine. The level is *new framing and methods*.

**What the chapter prepares.** We have the real exponential $\exp_{ℝ}$ with the addition theorem and injectivity—and the formal heart $e^{-\ln(1-x)}=1/(1-x)$ from Chapter 16.3. Chapter 16.5 connects them: the *evaluation* bridge transfers the coefficientwise identity into a number-process, *Tannery’s* theorem glues the diagonal of $\exp_{ℝ}$ to this evaluation, and the result is the key $\exp_{ℝ}(\text{ln-process})
\sim 1/(1-x)$—from which injectivity and the homomorphism close the functional equation of the logarithm.

---

[^1]: `src/CauchyProduct.v` (19 Qed, 0 Admitted): `mertens_cauchy_product`—no new axioms, only L3 (the difference identity `mertens_diff_eq` and the finite Fubini `partial_sum_conv_swap` are axiom-free). Machine-checked.
[^2]: `src/ExpFunctionalEquation.v` (17 Qed, 0 Admitted): `exp_add` (the addition theorem) via `exp_conv_rec` (the recurrence $(n+1)c_{n+1} = (u+v)c_n$). No new axioms, only L3. Machine-checked.
[^3]: Ibid.: `exp_limit_zero` ($\exp 0 \sim 1$), `exp_neg` ($\exp(u)\cdot \exp(-u)\sim 1$). No new axioms, only L3.
[^4]: `src/ProcessExp.v` (21 Qed, 0 Admitted): the core lemmas `Qpow_diff_bound` (the Lipschitz bound for powers), `exp_partial_lipschitz`, and `exp_partial_tail_bound` are *axiom-free*; the assembly `exp_meta_cauchy` and `exp_R` itself use no new axioms, only L3. Machine-checked.
[^5]: `src/ProcessExp.v`: `exp_R_add` (the diagonal Mertens), `exp_R_zero`, `exp_R_neg`, `exp_R_wd` (well-definedness on classes). No new axioms, only L3.
[^6]: Ibid.: `exp_R_inj` via `exp_R_inj_kernel` ($\exp_{ℝ}(D)\sim 1\Rightarrow D\sim 0$) and the monotone bound `exp_lower_bound`. No new axioms, only L3.
[^7]: Machine-checked: `Print Assumptions` for `mertens_cauchy_product`, `exp_add`, `exp_R`, `exp_R_add`, `exp_R_zero`, `exp_R_neg`, `exp_R_inj` gives exactly one axiom—`Classical_Prop.classic` (L3); neither choice nor functional extensionality.

---

Part: [[16 Function as Process|Part XVI. Function as Process]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/03 Composition Chain Rule and the Formal Heart E L|Chapter 3. Composition, the Chain Rule, and the Formal Heart E∘L]] · [[Library/Branches/Mathematics/Volume/16 Function as Process/05 Analytic Bridge Eval and Tannery Theorem Closing the Logarithm Equation|Chapter 5. The Analytic Bridge eval and Tannery’s Theorem: Closing the Logarithm Equation]] →
