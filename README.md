# Large sumsets from subsets

Lean 4 proofs of two theorems on subsets with large sumset in an abelian group: Theorem 2 of
Bollobás, Leader and Tiba,
[*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366), and Theorem 1.1 of
Fox, Luo, Pham and Zhou,
[*Small subsets with large sumset: beyond the Cauchy–Davenport bound*](https://arxiv.org/abs/2210.07196).
The proof of the first uses an arithmetic removal lemma for sets of small doubling and a variant
of Shao's [almost-all Balog–Szemerédi–Gowers theorem](https://arxiv.org/abs/1811.10707), which
are also proved here, with explicit thresholds.

Throughout, sets are finite subsets of an abelian group, $|A|$ is the number of elements of $A$,
and the declarations are in the namespace `LargeSumsetsFromSubsets`.

## Results

**Theorem 1** (`exists_subset_min_lt_expect_card_add'`). Let $\sigma > 0$ and $\varepsilon > 0$,
let $A$ and $B$ be nonempty, and let $c_1$ and $c_2$ be integers with $1 \le c_1 \le |A|$ and
$1 \le c_2 \le |B|$. If $c_1 c_2 > c(\sigma, \varepsilon) \max(|A|, |B|)$, then there are nonempty
$A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon)|A|$ and
$|B_0| > (1 - \varepsilon)|B|$ such that

$$\mathbb{E}\, |A' + B'| > \min\bigl((1 - \varepsilon)|A_0 + B_0|, \sigma |A_0|, \sigma |B_0|\bigr),$$

where $A'$ and $B'$ are the sets of $c_1$ points of $A_0$ and $c_2$ points of $B_0$ chosen
independently and uniformly at random, with repetitions allowed, and $c(\sigma, \varepsilon)$ is
the constant `originalBltConstant σ ε`,

$$c(\sigma, \varepsilon) = \frac{1296 K}{\varepsilon' \delta}, \qquad K = 2 \max(\sigma, 1), \qquad \varepsilon' = \tfrac{1}{2} \min(\varepsilon, 1),$$

with $\delta = \min\bigl(\tfrac{1}{2}, \tfrac{\rho}{8}, r(16 C^7, \rho / C)\bigr)$, $C = 100 K^3$ and
$\rho = \varepsilon'^2 / (1000 C)$. Here $r(L, \eta) = \tfrac{1}{2} \delta_\triangle(\eta / (36 (1 + L)^2))$
is the threshold `ArithmeticRemoval.removalConst L η`, where $\delta_\triangle$ is the bound
`SimpleGraph.triangleRemovalBound` of Mathlib's triangle removal lemma. The expectation is
Mathlib's `Finset.expect` over all pairs of functions $f : \mathrm{Fin}\ c_1 \to A_0$ and
$g : \mathrm{Fin}\ c_2 \to B_0$, and $A'$ and $B'$ are the sets of values of $f$ and $g$.

**Theorem 2** (`ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne'`). Let $K \ge 0$,
$\varepsilon > 0$ and $0 \le \delta \le r(K, \varepsilon)$, let $X$ be a set with
$|X + X| \le K |X|$, and let $A, B, C \subseteq X$. If the equation $a + b = c$ has at most
$\delta |X|^2$ solutions with $a \in A$, $b \in B$ and $c \in C$, then there are
$A' \subseteq A$, $B' \subseteq B$ and $C' \subseteq C$ with

$$|A \setminus A'| \le \varepsilon |X|, \qquad |B \setminus B'| \le \varepsilon |X|, \qquad |C \setminus C'| \le \varepsilon |X|$$

such that $a + b \ne c$ for all $a \in A'$, $b \in B'$ and $c \in C'$.

**Theorem 3** (`ArithmeticRemoval.removalConst_pos'`). Let $K \ge 0$ and $\varepsilon > 0$. Then

$$r(K, \varepsilon) > 0.$$

**Theorem 4** (`Cleanup.exists_subset_card_sdiff_le_card_add_le'`). Let $D \ge 1$, $\rho > 0$ and
$0 \le \delta \le r(16 D^7, \rho / D)$, let $X$ and $Y$ be nonempty with
$|X + Y| \le D \min(|X|, |Y|)$, and let $P$ be a set. If at most $\delta |X| |Y|$ pairs
$(x, y) \in X \times Y$ have $x + y \notin P$, then there are $X_0 \subseteq X$ and
$Y_0 \subseteq Y$ with $|X \setminus X_0| \le \rho \min(|X|, |Y|)$ and
$|Y \setminus Y_0| \le \rho \min(|X|, |Y|)$ such that

$$|X_0 + Y_0| \le |P| + \rho \min(|X|, |Y|).$$

Shao's theorem assumes only that the pairs with sum in $P$ have few distinct sums. Theorem 4
assumes in addition that $X + Y$ is small.

**Theorem 5** (`FewTranslates.exists_subset_card_le_mul_le_card_add'`). Let $A$ be nonempty and let
$s \ge 1$ be an integer. Then there is $T \subseteq A$ with $|T| \le s$ and

$$|A + T| \ge \tfrac{1}{14} \min(\kappa^{1/3}, s) |A|,$$

where $\kappa = |A + A| / |A|$.

[Challenge.lean](LargeSumsetsFromSubsetsPalomar/Challenge.lean) contains these five statements,
under the library names with a prime and with `sorry` placeholders, together with the
definitions of `ArithmeticRemoval.removalConst` and of the constants from `bltCap` to
`originalBltConstant`. [Solution.lean](LargeSumsetsFromSubsetsPalomar/Solution.lean) proves each
statement by the library theorem without the prime. The library and the solution contain no
`sorry`, and the theorems depend on no axioms other than `propext`, `Classical.choice` and
`Quot.sound`.

| Other library declarations | Meaning |
| --- | --- |
| `exists_forall_exists_subset_min_lt_expect_card_add` | Theorem 1 with a constant that exists |
| `exists_subset_min_le_expectSumset` | Theorem 1 for $K \ge 1$ and $0 < \varepsilon \le 1$, with the constant `bltSampleConst K ε`, subsets of at least $(1 - \varepsilon/4)\lvert A \rvert$ and $(1 - \varepsilon/4)\lvert B \rvert$ elements and non-strict inequalities |
| `exists_subset_card_le_mul_sqrt_min_le_card_add` | Subsets $A' \subseteq A'' \subseteq A$ and $B' \subseteq B'' \subseteq B$ with $\lvert A' \rvert, \lvert B' \rvert$ at most `bltConstant σ ε * √(max #A #B)` and $\lvert A' + B' \rvert \ge \min((1 - \varepsilon)\lvert A'' + B'' \rvert, \sigma \lvert A'' \rvert, \sigma \lvert B'' \rvert)$ |
| `exists_forall_exists_subset_card_sdiff_le_forall_add_ne` | Theorem 2 with a threshold that exists |
| `exists_forall_exists_subset_card_sdiff_le_card_add_le` | Theorem 4 with a threshold that exists |
| `bltSample` | The set of values of a sample `f : Fin k → A` |
| `Sampling.expectSumset` | The expected size of the sumset of two samples |

## Files

| Files in `LargeSumsetsFromSubsets/` | Contents |
| --- | --- |
| `ArithmeticRemoval/TripartiteGraph.lean` | The tripartite graph of the equation $a + b = c$ |
| `ArithmeticRemoval.lean` | `removalConst`, Theorems 2 and 3 |
| `Cleanup.lean` | Theorem 4 and the covering bound |
| `MediumSizedSubsets/Constants.lean` | The constants from `bltCap` to `bltSampleConst` |
| `MediumSizedSubsets/Sampling.lean` | `bltSample` and the probability that a sum is sampled |
| `MediumSizedSubsets/Potential.lean` | The minimizing pair $(X, Y)$ |
| `MediumSizedSubsets.lean` | Theorem 1 and its other forms |
| `FewTranslates.lean` | Theorem 5 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
challenge, and its five `sorry` warnings are expected.

## Verification

`Challenge.lean` imports only the Mathlib module `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`.
It defines `ArithmeticRemoval.removalConst`, `bltCap`, `bltRho`, `bltDelta`, `bltAlpha`,
`bltSampleConst` and `originalBltConstant` as the library does, with natural-number numerals so
that the definitions contain no proofs, and states the five theorems above with `sorry`.
[comparator.json](comparator.json) names these five theorems,
`LargeSumsetsFromSubsetsPalomar.Challenge` and `LargeSumsetsFromSubsetsPalomar.Solution` as the
modules to compare, no definition holes, so that the definitions of the solution must be those of
the challenge, and `propext`, `Classical.choice` and `Quot.sound` as the permitted axioms. The two
modules sit in `LargeSumsetsFromSubsetsPalomar/` rather than at the root, so that they do not
clash with the `Challenge` and `Solution` modules of the projects this one requires or is
required by.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
