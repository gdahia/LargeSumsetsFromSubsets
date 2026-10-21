# Large sumsets from subsets

Lean 4 proofs of two theorems on subsets with large sumset in an abelian group: Theorem 2 of
Bollobás, Leader and Tiba,
[*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366), and Theorem 1.1 of
Fox, Luo, Pham and Zhou,
[*Small subsets with large sumset: beyond the Cauchy–Davenport bound*](https://arxiv.org/abs/2210.07196).
The proof of the first uses an arithmetic removal lemma for sets of small doubling and a variant
of Shao's [almost-all Balog–Szemerédi–Gowers theorem](https://arxiv.org/abs/1811.10707), which
are also proved here. The first proof is copied from
[DenseSetsWithoutLargeSumsets](https://github.com/gdahia/DenseSetsWithoutLargeSumsets) and the
second from
[CountingSetsWithGivenDoublingViaDimension](https://github.com/gdahia/CountingSetsWithGivenDoublingViaDimension).

## Results

All sets are finite subsets of an abelian group, $|A|$ is the number of elements of $A$, and the
declarations are in the namespace `LargeSumsetsFromSubsets` or in one of its subnamespaces.

**Bollobás, Leader and Tiba, Theorem 2** (`exists_subset_min_lt_expect_card_add`). Let
$\sigma > 0$ and $\varepsilon > 0$, let $A$ and $B$ be nonempty, and let $1 \le c_1 \le |A|$ and
$1 \le c_2 \le |B|$ satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`. There are
$A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon)|A|$ and
$|B_0| > (1 - \varepsilon)|B|$ such that, for $c_1$ points of $A_0$ and $c_2$ points of $B_0$
chosen independently and uniformly at random, with repetitions allowed, the sets $A'$ and $B'$ of
chosen points satisfy

$$\mathbb{E} |A' + B'| > \min\bigl((1 - \varepsilon)|A_0 + B_0|, \sigma |A_0|, \sigma |B_0|\bigr).$$

The sets of chosen points are `Sampling.bltSample A₀ f` and `Sampling.bltSample B₀ g`, the sets of
values of `f : Fin c₁ → A₀` and `g : Fin c₂ → B₀`, and the expectation is Mathlib's
`Finset.expect` over all pairs $(f, g)$. There are two more forms:

- `exists_subset_min_le_expectSumset`, for $K \ge 1$ and $0 < \varepsilon \le 1$, with the
  constant `bltSampleConst K ε`, subsets containing at least
  $(1 - \varepsilon/4)|A|$ and $(1 - \varepsilon/4)|B|$ elements, and non-strict inequalities;
- `exists_subset_card_le_mul_sqrt_min_le_card_add`, which gives $A' \subseteq A'' \subseteq A$ and
  $B' \subseteq B'' \subseteq B$ with $|A''| \ge (1 - \varepsilon)|A|$,
  $|B''| \ge (1 - \varepsilon)|B|$, at most `bltConstant σ ε * √(max #A #B)` elements in each of
  $A'$ and $B'$, and $|A' + B'| \ge \min((1 - \varepsilon)|A'' + B''|, \sigma |A''|, \sigma |B''|)$.

The form with an unspecified constant is `exists_forall_exists_subset_min_lt_expect_card_add`.

**Arithmetic removal lemma** (`ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne`). Let
$|X + X| \le K|X|$ and $A, B, C \subseteq X$. If $a + b = c$ has at most $\delta |X|^2$ solutions
with $a \in A$, $b \in B$, $c \in C$, where `0 ≤ δ ≤ removalConst K ε`, then one can remove at
most $\varepsilon |X|$ elements from each of $A$, $B$ and $C$ so that no solution remains. The
form with an unspecified threshold is `exists_forall_exists_subset_card_sdiff_le_forall_add_ne`.

**Cleanup theorem** (`Cleanup.exists_subset_card_sdiff_le_card_add_le`). Let $X$ and $Y$ be nonempty
with $|X + Y| \le D \min(|X|, |Y|)$, where $D \ge 1$. If at most $\delta |X| |Y|$ pairs in
$X \times Y$ have their sum outside a set $P$, where
`0 ≤ δ ≤ removalConst (16 * D ^ 7) (ρ / D)`, then there are $X_0 \subseteq X$ and
$Y_0 \subseteq Y$, each missing at most $\rho \min(|X|, |Y|)$ elements, with
$|X_0 + Y_0| \le |P| + \rho \min(|X|, |Y|)$. The form with an unspecified threshold is
`exists_forall_exists_subset_card_sdiff_le_card_add_le`. Shao's theorem assumes that the pairs with
sum in $P$ have few distinct sums. The theorem here assumes in addition that $X + Y$ is small.

**Fox, Luo, Pham and Zhou, Theorem 1.1** (`FewTranslates.exists_subset_card_le_mul_le_card_add`).
Let $A$ be nonempty with $|A + A| = \kappa |A|$, and let $s \ge 1$. Some $T \subseteq A$ with at
most $s$ elements has $|A + T| \ge \min(\kappa^{1/3}, s)|A| / 14$.

## Proof and files

| Files in `LargeSumsetsFromSubsets/` | Contents |
| --- | --- |
| `ArithmeticRemoval/TripartiteGraph.lean` | The tripartite graph of the equation `a + b = c` |
| `ArithmeticRemoval.lean` | `removalConst` and the arithmetic removal lemma |
| `Cleanup.lean` | The cleanup theorem and the covering bound |
| `MediumSizedSubsets/Constants.lean` | The constants from `bltCap` to `bltSampleConst` |
| `MediumSizedSubsets/Sampling.lean` | `bltSample` and the probability that a sum is sampled |
| `MediumSizedSubsets/Potential.lean` | The minimizing pair `(X, Y)` |
| `MediumSizedSubsets.lean` | The three forms of the Bollobás–Leader–Tiba theorem |
| `FewTranslates.lean` | The Fox–Luo–Pham–Zhou theorem |

Bollobás, Leader and Tiba prove their theorem by applying Shao's theorem repeatedly. The proof
here follows DenseSetsWithoutLargeSumsets instead. [formalization.yaml](formalization.yaml) records the
differences from the sources, the scope, and the use of AI coding agents.

## Verification

[Challenge.lean](Challenge.lean) states the first form of the Bollobás–Leader–Tiba theorem, the
arithmetic removal lemma, the positivity of `removalConst`, the cleanup theorem and the
Fox–Luo–Pham–Zhou theorem with `sorry` placeholders. Its statements use Mathlib and seven
definitions copied from the library: `removalConst` and the six constants from `bltCap` to
`originalBltConstant`. [Solution.lean](Solution.lean) proves the five statements from the library.
The library and solution contain no `sorry`. In `comparator.json` the six constants are listed
under `definition_names`, so the comparator checks their types and takes their values from the
solution. It compares `removalConst` in full.

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
