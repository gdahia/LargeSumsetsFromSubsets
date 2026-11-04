# Large sumsets from medium-sized subsets

Lean 4 formalization of the main results of Béla Bollobás, Imre Leader and Marius Tiba,
[*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366). In
$\mathbb{Z}_p$, subsets with $c_1$ and $c_2$ elements of sets $A$ and $B$ of comparable sizes reach
the Cauchy–Davenport bound $|A| + |B| - 1$ as soon as $c_1 c_2 \ge c \max(|A|, |B|)$ (Theorem 1).
In an abelian group, a few random points of large subsets $A_0 \subseteq A$ and $B_0 \subseteq B$
already have a sumset of almost the size of $A_0 + B_0$ (Theorem 2).

All sets are finite, $|A|$ is the number of elements of $A$, and $\mathbb{Z}_p$ is `ZMod p` for a
prime $p$. Theorem numbers are those of the paper, and all names below are in the namespace
`LargeSumsetsFromSubsets`. The results that the paper quotes from the same authors'
[*Large sumsets from small subsets*](https://arxiv.org/abs/2204.07559) come from the Lean
formalization [LargeSumsetsFromSmallSubsets](https://github.com/gdahia/LargeSumsetsFromSmallSubsets),
a dependency of this project.

## Results

**Theorem 1** (`exists_subset_card_eq_card_add_card_sub_one_le_card_add`). Let
$\alpha, \beta > 0$. There is $c > 0$ with the following property. Let
$A, B \subseteq \mathbb{Z}_p$ be nonempty with $\alpha |B| \le |A| \le \alpha^{-1} |B|$ and
$|A| + |B| \le (1 - \beta) p$, and let $c_1, c_2$ be integers with $1 \le c_1 \le |A|$ and
$1 \le c_2 \le |B|$. If $c_1 c_2 \ge c \max(|A|, |B|)$, then there are $A' \subseteq A$ and
$B' \subseteq B$ with $|A'| = c_1$, $|B'| = c_2$ and

$$|A' + B'| \ge |A| + |B| - 1.$$

**Theorem 2** (`exists_forall_exists_subset_min_lt_expect_card_add`). Let
$\sigma, \varepsilon > 0$. There is $c$ with the following property. Let $A$ and $B$ be nonempty
subsets of an abelian group and let $c_1, c_2$ be integers with $1 \le c_1 \le |A|$ and
$1 \le c_2 \le |B|$. If $c_1 c_2 > c \max(|A|, |B|)$, then there are nonempty
$A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon) |A|$,
$|B_0| > (1 - \varepsilon) |B|$ and

$$\mathbb{E} |A' + B'| > \min\bigl((1 - \varepsilon) |A_0 + B_0|, \sigma |A_0|, \sigma |B_0|\bigr),$$

where $A'$ and $B'$ are the sets of $c_1$ points of $A_0$ and $c_2$ points of $B_0$ chosen
independently and uniformly at random, with repetition.

[Challenge.lean](LargeSumsetsFromSubsetsPalomar/Challenge.lean) states these two theorems under the
library names with a prime, with `sorry` placeholders, in terms of Mathlib alone.
[Solution.lean](LargeSumsetsFromSubsetsPalomar/Solution.lean) proves each statement by the library
theorem. The library and the solution contain no `sorry`, and the theorems depend on no axioms other
than `propext`, `Classical.choice` and `Quot.sound`.

## Files

| Files in `LargeSumsetsFromSubsets/` | Contents |
| --- | --- |
| `ArithmeticProgression/` | Arithmetic progressions and the intervals of `ZMod p` |
| `ArithmeticRemoval.lean`, `ArithmeticRemoval/TripartiteGraph.lean` | Removal of the solutions of `a + b = c` in a set of small doubling, from the triangle removal lemma of Mathlib |
| `Cleanup.lean` | Sets whose sums lie mostly in a small set have large subsets with a small sumset |
| `MediumSizedSubsets/` | The stages of the proof of Theorem 2 |
| `AddCommGroup.lean` | Theorem 2 |
| `SubsetSampling.lean` | Uniformly random subsets compared with independent random points |
| `CauchyDavenportStability.lean` | Sets of `ZMod p` with a sumset close to the Cauchy–Davenport bound |
| `IntervalSumsets.lean`, `IntervalSumsets/` | Small subsets of dense subsets of intervals whose sumset reaches the Cauchy–Davenport bound |
| `CauchyDavenportBound/` | The stages of the proof of Theorem 1 |
| `ZMod.lean` | Theorem 1 |

| Other files | Contents |
| --- | --- |
| `LargeSumsetsFromSubsetsPalomar/Challenge.lean`, `LargeSumsetsFromSubsetsPalomar/Solution.lean` | The statements with `sorry` and their proofs from the library |
| `simplified_proof.tex` | A note on the proof of Theorem 1 from the results of the dependency |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the scope,
and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib, defines nothing, and states
`exists_subset_card_eq_card_add_card_sub_one_le_card_add'` and
`exists_forall_exists_subset_min_lt_expect_card_add'` with `sorry`. `comparator.json` names these
two theorems, no definition holes, `LargeSumsetsFromSubsetsPalomar.Challenge` and
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
