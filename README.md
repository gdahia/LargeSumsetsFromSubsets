# Large sumsets from medium-sized subsets

Lean 4 formalization of Béla Bollobás, Imre Leader and Marius Tiba,
[*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366). In an abelian
group, a few random points of large subsets $A_0 \subseteq A$ and $B_0 \subseteq B$ already have
a sumset of almost the size of $A_0 + B_0$ (Theorem 2). In $\mathbb{Z}_p$, for sets of comparable
sizes with $|A| + |B|$ bounded away from $p$, subsets with $c_1$ and $c_2$ elements reach the
Cauchy–Davenport bound $|A| + |B| - 1$ as soon as $c_1 c_2 \ge c \max(|A|, |B|)$ (Theorem 1).

Theorem 2 is proved without the theorem of Shao that the paper uses. The proof instead applies
the arithmetic removal lemma to the sets of a minimizing pair of subsets, and both the removal
lemma and the cleanup theorem it gives are proved here. The paper quotes its Theorems 4 and 5,
used for Theorems 1, 6 and 8, from other works. They come from the Lean formalization
[LargeSumsetsFromSmallSubsets](https://github.com/gdahia/LargeSumsetsFromSmallSubsets) of
Bollobás, Leader and Tiba, [*Large sumsets from small subsets*](https://arxiv.org/abs/2204.07559),
a dependency of this project. Theorem 4 is Corollary 24 there. Theorem 5 is Theorem 31 there,
which that formalization proves in a weaker form: the subsets of $B$ may depend on the set $A$.
The proof of Theorem 8 is adapted to this form, as explained in
[simplified_proof.pdf](simplified_proof.pdf).

## Results

All sets are finite, $|A|$ is the number of elements of $A$, and $\mathbb{Z}_p$ is `ZMod p` for a
prime $p$. All names below are in the namespace `LargeSumsetsFromSubsets`.

Theorem numbers are those of the paper.

**Theorem 1** (`exists_subset_card_eq_card_add_card_sub_one_le_card_add`). For
$\alpha, \beta > 0$ there is $c > 0$ such that if
$A, B \subseteq \mathbb{Z}_p$ are nonempty with $\alpha |B| \le |A| \le \alpha^{-1} |B|$ and
$|A| + |B| \le (1 - \beta) p$, then for all integers $1 \le c_1 \le |A|$ and $1 \le c_2 \le |B|$
with $c_1 c_2 \ge c \max(|A|, |B|)$ there are $A' \subseteq A$ and $B' \subseteq B$ with
$|A'| = c_1$, $|B'| = c_2$ and

$$|A' + B'| \ge |A| + |B| - 1.$$

**Theorem 2** (`exists_forall_exists_subset_min_lt_expect_card_add`). For
$\sigma, \varepsilon > 0$ there is $c$ such that for nonempty subsets $A$ and $B$ of an abelian
group and integers $1 \le c_1 \le |A|$, $1 \le c_2 \le |B|$ with $c_1 c_2 > c \max(|A|, |B|)$
there are $A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon) |A|$ and
$|B_0| > (1 - \varepsilon) |B|$ such that, if $A'$ and $B'$ are the sets of $c_1$ and $c_2$
points of $A_0$ and $B_0$ chosen independently and uniformly at random,

$$\mathbb{E} |A' + B'| > \min\bigl((1 - \varepsilon) |A_0 + B_0|, \sigma |A_0|, \sigma |B_0|\bigr).$$

**Theorem 6** (`exists_arithProg_card_symmDiff_le_of_expect_card_add_le`). For
$\beta, \gamma > 0$ there is $\varepsilon > 0$ such that for $\alpha > 0$ there is $c$ with the
following property. If $A, B \subseteq \mathbb{Z}_p$ have at least two
elements, $\alpha |B| \le |A| \le \alpha^{-1} |B|$, $|A| + |B| \le (1 - \beta) p$,
$1 \le c_1 \le |A|$, $1 \le c_2 \le |B|$, $c_1 c_2 \ge c \max(|A|, |B|)$, and uniformly random
subsets $A'$ and $B'$ of $A$ and $B$ with $c_1$ and $c_2$ elements satisfy

$$\mathbb{E} |A' + B'| \le |A| + |B| - 1 + \varepsilon \min(|A|, |B|),$$

then there are arithmetic progressions $P$ and $Q$ with the same nonzero common difference and
$|A \mathbin{\triangle} P|, |B \mathbin{\triangle} Q| \le \gamma \min(|A|, |B|)$.

**Theorem 8** (`exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range`).
There is $\gamma > 0$ such that for $\alpha > 0$ there is $c$ with the following property. Let $X \subseteq I$ and $Y \subseteq J$, where $I$ and $J$ are intervals of
$\mathbb{Z}_p$ with $m$ and $n$ elements, $m + n \le p$, $\alpha n \le m \le \alpha^{-1} n$ and
$|I \setminus X|, |J \setminus Y| \le \gamma \min(m, n)$. For $1 \le c_1 \le |X|$ and
$1 \le c_2 \le |Y|$ with $c_1 c_2 \ge c \max(|X|, |Y|)$ there are $X' \subseteq X$ and
$Y' \subseteq Y$ with $c_1$ and $c_2$ elements and $|X' + Y'| \ge |X| + |Y| - 1$.

**Arithmetic removal lemma in a set of small doubling**
(`exists_forall_exists_subset_card_sdiff_le_forall_add_ne`). For $K \ge 0$ and $\varepsilon > 0$
there is $\delta > 0$ such that if $|X + X| \le K |X|$, $A, B, C \subseteq X$ and $a + b = c$ has
at most $\delta |X|^2$ solutions with $a \in A$, $b \in B$, $c \in C$, then one can remove at most
$\varepsilon |X|$ elements from each of $A$, $B$ and $C$ so that no solution remains.

**Cleanup theorem** (`exists_forall_exists_subset_card_sdiff_le_card_add_le`). For
$D \ge 1$ and $\rho > 0$ there is $\delta > 0$ such that if $X$ and $Y$ are nonempty,
$|X + Y| \le D \min(|X|, |Y|)$ and at most $\delta |X| |Y|$ pairs of $X \times Y$ have their sum
outside a set $P$, then one can remove at most $\rho \min(|X|, |Y|)$ elements from each of $X$ and
$Y$ so that the remaining sets $X_0$ and $Y_0$ satisfy
$|X_0 + Y_0| \le |P| + \rho \min(|X|, |Y|)$.

[Challenge.lean](LargeSumsetsFromSubsetsPalomar/Challenge.lean) states these six results under
the library names with a prime, with `sorry` placeholders, in terms of Mathlib alone.
[Solution.lean](LargeSumsetsFromSubsetsPalomar/Solution.lean) proves each statement by the
library theorem. The library and the solution contain no `sorry`, and the theorems depend on no
axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library has further statements. The main ones are the following.

| Declaration | Statement |
| --- | --- |
| `exists_subset_min_lt_expect_card_add` | Theorem 2 with the explicit constant `originalBltConstant σ ε` |
| `exists_subset_min_le_expectSumset` | Theorem 2 for $K \ge 1$ and $0 < \varepsilon \le 1$, with the constant `bltSampleConst K ε` and subsets containing all but an $\varepsilon / 4$ proportion of $A$ and $B$ |
| `exists_subset_card_le_mul_sqrt_min_le_card_add` | A deterministic form of Theorem 2 with $c_1 = c_2$ of order $\sqrt{\max(\|A\|, \|B\|)}$ and the constant `bltConstant σ ε` |
| `ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne` | The removal lemma with the threshold `removalConst K ε`, a multiple of Mathlib's `triangleRemovalBound` |
| `Cleanup.exists_subset_card_sdiff_le_card_add_le` | The cleanup theorem with the threshold `removalConst (16 * D ^ 7) (ρ / D)` |
| `exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico` | Theorem 8 of the paper for intervals of integers |
| `exists_interval_ends` | Lemma 9 of the paper: the decomposition of $\mathbb{Z}_p$ into end and middle intervals |
| `exists_subset_two_mul_card_le_card_add_sdiff`, `exists_subsets_min_le_card_biUnion_add_sdiff` | Lemma 10 and Corollary 11 of the paper |
| `exists_lt_disjoint_image_add_arithProg` | Lemma 12 of the paper, for one point |
| `exists_eq_arithProg_one_of_card_inter_arithProg_one` | An arithmetic progression of $\mathbb{Z}_p$ with at most $11L/10$ elements sharing $9L/10$ points with an interval of length $L$, $20 \le L \le p / 8$, is an interval |
| `exists_subset_arithProg_card_sdiff_le_of_card_add_le` | Theorem 4 of the paper, from Corollary 24 of *Large sumsets from small subsets* |
| `exists_fewTranslatesInt` | Theorem 5 of the paper for intervals of integers, with the subset of $B$ depending on $A$, from Theorem 31 of *Large sumsets from small subsets* |
| `mul_expect_card_add_le_expect_powersetCard` | Uniformly random $c$-subsets dominate $c/2$ independent samples from a subset containing all but a $\mu$ proportion, up to the factor $(1 - 2\mu)^2$ |

The proofs of Theorems 1 and 6 follow the paper. The proof of Theorem 8 follows the paper except
in the sample of $Y$: the paper takes, in each dense residue class $y$ of $Y$, a random member of a
family of subsets given by Theorem 5 that works for every class of $X$ at once. Here, for each
dense class $x$ of $X$ in the sample and each dense class $y$ of $Y$, the subset of the class $y$
given by the weaker form of Theorem 5 for the class $x$ is added to the sample of $Y$. With $t$
random classes of $X$ besides the largest one, the sample of $Y$ grows by the factor $t + 1$,
which only changes the constant $c$. Several steps that the paper states without proof are proved
here: the comparison of random subsets with independent samples, the fact that a progression close
to an interval is an interval, the reduction of the residue classes in the proof of Theorem 8 to
sets containing the endpoints of their intervals, as Theorem 5 requires, and the passage from
intervals of $\mathbb{Z}_p$ to intervals of integers.
The paper's proof of Theorem 2 iterates Shao's theorem on a decreasing sequence of pairs of
subsets. Here one pair of subsets minimizes `min |X + Y| (D |X|) (D |Y|) + Λ (|A \ X| + |B \ Y|)`;
if the conclusion failed for it, the popular sums would be few, and the cleanup theorem, or an
elementary covering bound when $|X + Y|$ is large, would give a pair with a smaller value. The
removal lemma is proved by the argument of Král, Serra and Vena from the triangle removal lemma of
Mathlib, so the constants of Theorems 2 and 5 are of tower type.

## Files

| Files in `LargeSumsetsFromSubsets/` | Contents |
| --- | --- |
| `ArithmeticRemoval/TripartiteGraph.lean`, `ArithmeticRemoval.lean` | The tripartite graph of $a + b = c$ and the removal lemma |
| `Cleanup.lean` | The cleanup theorem and the covering bound |
| `MediumSizedSubsets/Constants.lean`, `MediumSizedSubsets/Sampling.lean`, `MediumSizedSubsets/Potential.lean` | The constants of Theorem 2, the probability that a sum is sampled, the minimizing pair |
| `MediumSizedSubsets.lean` | Theorem 2 |
| `ArithmeticProgression.lean` | Arithmetic progressions and intervals of `ZMod p` |
| `ArithmeticProgression/NearInterval.lean` | Progressions close to an interval |
| `SubsetSampling.lean` | Random subsets against independent samples |
| `ZModStability.lean` | Theorem 4 and Theorem 6 |
| `IntervalSumsets/FewTranslates.lean` | Theorem 5 for intervals of integers, with the subset depending on $A$ |
| `IntervalSumsets/Fibers.lean`, `IntervalSumsets/Sampling.lean` | Residue classes and the samples of Theorem 8 |
| `IntervalSumsets.lean` | Theorem 8 |
| `IntervalEnds.lean` | Lemma 9 |
| `Stickout.lean` | Lemma 10 and Corollary 11 |
| `IntervalCovering.lean` | Lemma 12 |
| `CauchyDavenportBound.lean` | Theorem 1 |

| Other files | Contents |
| --- | --- |
| `LargeSumsetsFromSubsetsPalomar/Challenge.lean`, `LargeSumsetsFromSubsetsPalomar/Solution.lean` | The statements with `sorry` and their proofs from the library |
| `simplified_proof.tex`, `simplified_proof.pdf` | A note on the proof of Theorem 8 from the weaker form of Theorem 5 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib, defines nothing, and states
`exists_forall_exists_subset_min_lt_expect_card_add'`,
`exists_forall_exists_subset_card_sdiff_le_forall_add_ne'`,
`exists_forall_exists_subset_card_sdiff_le_card_add_le'`,
`exists_arithProg_card_symmDiff_le_of_expect_card_add_le'`,
`exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range'` and
`exists_subset_card_eq_card_add_card_sub_one_le_card_add'` with `sorry`. `comparator.json` names
these six theorems, no definition holes, `LargeSumsetsFromSubsetsPalomar.Challenge` and
`LargeSumsetsFromSubsetsPalomar.Solution` as the modules to compare, and `propext`,
`Classical.choice` and `Quot.sound` as the permitted axioms.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
statements; its `sorry` warnings are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
