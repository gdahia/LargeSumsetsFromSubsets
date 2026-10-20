# Large sumsets from medium-sized subsets

Lean 4 formalization of Béla Bollobás, Imre Leader and Marius Tiba,
[*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366). In an abelian
group, a few random points of large subsets $A_0 \subseteq A$ and $B_0 \subseteq B$ already have
a sumset of almost the size of $A_0 + B_0$ (Theorem 2). In $\mathbb{Z}_p$, for sets of comparable
sizes with $|A| + |B|$ bounded away from $p$, subsets with $c_1$ and $c_2$ elements reach the
Cauchy–Davenport bound $|A| + |B| - 1$ as soon as $c_1 c_2 \ge c \max(|A|, |B|)$ (Theorem 1).

Theorem 2 is proved without the theorem of Shao that the paper uses. The proof instead applies
the arithmetic removal lemma to the sets of a minimizing pair of subsets, and both the removal
lemma and the cleanup theorem it gives are proved here. Theorems 1, 6 and 8 are proved from
Theorems 4 and 5 of the paper, which the paper quotes from other works. These two theorems are
not formalized: they are the hypotheses `CauchyDavenportStability` and
`FewTranslatesNearIntervals` of the statements.

## Results

All sets are finite, $|A|$ is the number of elements of $A$, and $\mathbb{Z}_p$ is `ZMod p` for a
prime $p$. All names below are in the namespace `LargeSumsetsFromSubsets`.

Theorem numbers are those of the paper.

**Theorem 1** (`exists_subset_card_eq_card_add_card_sub_one_le_card_add`, assuming Theorems 4
and 5). For $\alpha, \beta > 0$ there is $c > 0$ such that if
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

**Theorem 6** (`exists_arithProg_card_symmDiff_le_of_expect_card_add_le`, assuming Theorem 4). For $\beta, \gamma > 0$ there is $\varepsilon > 0$ such that for $\alpha > 0$
there is $c$ with the following property. If $A, B \subseteq \mathbb{Z}_p$ have at least two
elements, $\alpha |B| \le |A| \le \alpha^{-1} |B|$, $|A| + |B| \le (1 - \beta) p$,
$1 \le c_1 \le |A|$, $1 \le c_2 \le |B|$, $c_1 c_2 \ge c \max(|A|, |B|)$, and uniformly random
subsets $A'$ and $B'$ of $A$ and $B$ with $c_1$ and $c_2$ elements satisfy

$$\mathbb{E} |A' + B'| \le |A| + |B| - 1 + \varepsilon \min(|A|, |B|),$$

then there are arithmetic progressions $P$ and $Q$ with the same nonzero common difference and
$|A \mathbin{\triangle} P|, |B \mathbin{\triangle} Q| \le \gamma \min(|A|, |B|)$.

**Theorem 8** (`exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range`,
assuming Theorem 5). There is $\gamma > 0$ such that for $\alpha > 0$ there is $c$ with the following
property. Let $X \subseteq I$ and $Y \subseteq J$, where $I$ and $J$ are intervals of
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

The hypotheses of Theorems 1, 6 and 8 are the following statements, quoted in the paper.

- `CauchyDavenportStability` is Theorem 4 of the paper, which the authors deduce from Theorem 21.8
  of Grynkiewicz, *Structural additive theory*. For $\beta, \gamma > 0$ there is $\varepsilon > 0$
  such that if $A, B \subseteq \mathbb{Z}_p$ have at least two elements,
  $|A| + |B| \le (1 - \beta) p$ and $|A + B| \le |A| + |B| - 1 + \varepsilon \min(|A|, |B|)$, then
  $A$ and $B$ lie in arithmetic progressions $P$ and $Q$ with the same common difference and
  $|P \setminus A|, |Q \setminus B| \le \gamma \min(|A|, |B|)$.
- `FewTranslatesNearIntervals` is Theorem 5 of the paper, Theorem 31 of Bollobás, Leader and
  Tiba, [*Large sumsets from small subsets*](https://arxiv.org/abs/2204.07559). For $\beta > 0$
  there is $\gamma > 0$ such that for $\alpha > 0$ there is $c$ with the following property. If
  $I$ and $J$ are intervals of $\mathbb{Z}_p$ with $m$ and $n$ elements,
  $\alpha n \le m \le \alpha^{-1} n$, $m + n \le (1 - \beta) p$, and $B \subseteq J$ contains the
  endpoints of $J$ and misses at most $\gamma \min(m, n)$ of its points, then there are sets
  $F_0, \dots, F_k \subseteq B$ with at most $c$ elements such that every $A$ with
  $|A \mathbin{\triangle} I| \le \gamma \min(m, n)$ satisfies
  $|A| + |B| - 1 \le \mathbb{E}_i |A + F_i|$. The definition states this inequality as
  $(k + 1)(|A| + |B| - 1) \le \sum_i |A + F_i|$ in $\mathbb{N}$.

[Challenge.lean](Challenge.lean) states these six results under the library names with a prime, with
`sorry` placeholders, in terms of Mathlib and of the definitions `CauchyDavenportStability` and
`FewTranslatesNearIntervals`. [Solution.lean](Solution.lean) proves each statement by the library
theorem. The library and the solution contain no `sorry`, and the theorems depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`.

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
| `exists_fewTranslates_int` | `FewTranslatesNearIntervals` for intervals of integers |
| `mul_expect_card_add_le_expect_powersetCard` | Uniformly random $c$-subsets dominate $c/2$ independent samples from a subset containing all but a $\mu$ proportion, up to the factor $(1 - 2\mu)^2$ |

The proofs of Theorems 1, 6 and 8 follow the paper. Several steps that the paper states without
proof are proved here: the comparison of random subsets with independent samples, the fact that a
progression close to an interval is an interval, the reduction of the residue classes in the proof
of Theorem 8 to sets containing the endpoints of their intervals, as Theorem 5 requires, and the
passage from intervals of $\mathbb{Z}_p$ to intervals of integers.
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
| `ZModStability.lean` | `CauchyDavenportStability` and Theorem 6 |
| `IntervalSumsets/FewTranslates.lean` | `FewTranslatesNearIntervals` and its form for integers |
| `IntervalSumsets/Fibres.lean`, `IntervalSumsets/Sampling.lean` | Residue classes and the samples of Theorem 8 |
| `IntervalSumsets.lean` | Theorem 8 |
| `IntervalEnds.lean` | Lemma 9 |
| `Stickout.lean` | Lemma 10 and Corollary 11 |
| `IntervalCovering.lean` | Lemma 12 |
| `CauchyDavenportBound.lean` | Theorem 1 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib. It defines `CauchyDavenportStability` and
`FewTranslatesNearIntervals`, with the same values as the library, and states
`exists_forall_exists_subset_min_lt_expect_card_add'`,
`exists_forall_exists_subset_card_sdiff_le_forall_add_ne'`,
`exists_forall_exists_subset_card_sdiff_le_card_add_le'`,
`exists_arithProg_card_symmDiff_le_of_expect_card_add_le'`,
`exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range'` and
`exists_subset_card_eq_card_add_card_sub_one_le_card_add'` with `sorry`. `comparator.json` names
these six theorems, no definition holes, so the two definitions are compared in full, `Challenge`
and `Solution` as the modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as
the permitted axioms.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
