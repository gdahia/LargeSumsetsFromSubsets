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

All sets are finite subsets of an abelian group, and `#A` is the number of elements of `A`. The
declarations are in the namespace `LargeSumsetsFromSubsets`.

**Bollobás, Leader and Tiba, Theorem 2.** Let `σ > 0` and `ε > 0`, let `A` and `B` be nonempty,
and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`.
There are `A₀ ⊆ A` and `B₀ ⊆ B` with `#A₀ > (1 - ε) * #A` and `#B₀ > (1 - ε) * #B` such that, for
`c₁` points of `A₀` and `c₂` points of `B₀` chosen independently and uniformly at random, with
repetitions allowed, the sets `A'` and `B'` of chosen points satisfy

```
𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀).
```

This is `exists_medium_sized_subsets_with_large_sumset_sample`. The sets of chosen points are
`bltSample A₀ f` and `bltSample B₀ g`, the sets of values of `f : Fin c₁ → A₀` and
`g : Fin c₂ → B₀`, and the expectation is Mathlib's `Finset.expect` over all pairs `(f, g)`. There
are two more forms:

- `exists_medium_sized_subsets_with_large_sumset_core`, for `K ≥ 1` and `0 < ε ≤ 1`, with the
  constant `bltSampleConst K ε`, subsets containing at least `(1 - ε / 4) * #A` and
  `(1 - ε / 4) * #B` elements, and non-strict inequalities;
- `exists_medium_sized_subsets_with_large_sumset_subsets`, which gives `A' ⊆ A'' ⊆ A` and
  `B' ⊆ B'' ⊆ B` with `#A'' ≥ (1 - ε) * #A`, `#B'' ≥ (1 - ε) * #B`, at most
  `bltConstant σ ε * √(max #A #B)` elements in each of `A'` and `B'`, and
  `#(A' + B') ≥ min ((1 - ε) * #(A'' + B'')) (σ * #A'') (σ * #B'')`.

**Arithmetic removal lemma.** Let `#(X + X) ≤ K * #X` and `A`, `B`, `C ⊆ X`. If `a + b = c` has at
most `δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `0 ≤ δ ≤ removalConst K ε`, then
one can remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no solution
remains. This is `ArithmeticRemoval.arithmetic_removal`.

**Cleanup theorem.** Let `X` and `Y` be nonempty with `#(X + Y) ≤ D * min #X #Y`, where `D ≥ 1`.
If at most `δ * #X * #Y` pairs in `X ×ˢ Y` have their sum outside a set `P`, where
`0 ≤ δ ≤ removalConst (16 * D ^ 7) (ρ / D)`, then there are `X₀ ⊆ X` and `Y₀ ⊆ Y`, each missing at
most `ρ * min #X #Y` elements, with `#(X₀ + Y₀) ≤ #P + ρ * min #X #Y`. This is
`Cleanup.exists_cleanup`. Shao's theorem assumes that the pairs with sum in `P` have few distinct
sums. The theorem here assumes in addition that `X + Y` is small.

**Fox, Luo, Pham and Zhou, Theorem 1.1.** Let `A` be nonempty with `#(A + A) = κ * #A`, and let
`s ≥ 1`. Some `T ⊆ A` with at most `s` elements has `#(A + T) ≥ min (κ ^ (1 / 3)) s * #A / 14`.
This is `exists_subset_card_add_ge`.

The constants are explicit:

- `ArithmeticRemoval.removalConst K ε` is `triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2`,
  where `triangleRemovalBound` is the constant of the triangle removal lemma in Mathlib. It is of
  tower type;
- `bltCap K` is `100 * K ^ 3` and `bltRho K ε` is `ε ^ 2 / (1000 * bltCap K)`;
- `bltDelta K ε` is the minimum of `1 / 2`, `bltRho K ε / 8` and
  `removalConst (16 * bltCap K ^ 7) (bltRho K ε / bltCap K)`;
- `bltAlpha K ε` is `bltDelta K ε / (36 * K)` and `bltSampleConst K ε` is
  `36 / (ε * bltAlpha K ε)`;
- `originalBltConstant σ ε` is `bltSampleConst (2 * max σ 1) (min ε 1 / 2)`;
- `bltConstant σ ε` is `8 * (max 1 (originalBltConstant σ ε) + σ + 1) ^ 2`.

[Challenge.lean](Challenge.lean) states the first form of the Bollobás–Leader–Tiba theorem, the
arithmetic removal lemma, the positivity of `removalConst`, the cleanup theorem and the
Fox–Luo–Pham–Zhou theorem with `sorry` placeholders. Its statements use Mathlib and eight
definitions copied from the library: `removalConst`, `bltSample` and the six constants from
`bltCap` to `originalBltConstant`. [Solution.lean](Solution.lean) proves the five statements from
the library. The library and solution contain no `sorry`. In `comparator.json` the six constants
are listed under `definition_names`, so the comparator checks their types and takes their values
from the solution. It compares `removalConst` and `bltSample` in full.

## Proof and files

*Arithmetic removal.* This is the argument of Král, Serra and Vena. Let `W = X ∪ (X + X)` and
form the tripartite graph on three copies of `W` whose triangles are the triples
`(u, u + a, u + c)` with `a ∈ A`, `c ∈ C` and `c - a ∈ B`. It has at most `#W` triangles for each
solution of `a + b = c`, so the triangle removal lemma deletes few edges and leaves no triangle.
An edge between two parts has a label, the difference of its endpoints. Remove from `A`, `B` and
`C` the labels for which more than `#X / 4` edges were deleted. A remaining solution would give
`#X` triangles, of which at most `3 * #X / 4` lose an edge.

*Cleanup.* Translate `X` and `Y` to contain `0` and let `Z` be the translate of `X + Y`. By the
Plünnecke–Ruzsa inequality `#(Z + Z) ≤ 16 * D ^ 7 * #Z`. The pairs of `X ×ˢ Y` with sum outside
`P` are the solutions of `a + b = c` with `a ∈ X`, `b ∈ Y` and `c ∈ (X + Y) \ P`. The arithmetic
removal lemma inside `Z` removes few elements from the three sets, and the remaining parts of `X`
and `Y` have all their sums in `P` or among the removed elements of `(X + Y) \ P`. The same file
proves a second bound, `Cleanup.exists_covering`, with no hypothesis on `#(X + Y)`: after
removing a `ρ` proportion of `X` and of `Y`, every remaining sum has at least `#X * #Y / 2`
representations `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`, so the remaining sumset has at most
`2 * #P ^ 3 / (#X * #Y)` elements.

*Bollobás, Leader and Tiba.* Let `K ≥ 1` and `0 < ε ≤ 1`, and put `D = bltCap K` and
`Λ = 4 * D / ε`. Choose nonempty `X ⊆ A` and `Y ⊆ B` minimizing
`min (#(X + Y)) (D * #X) (D * #Y) + Λ * (#(A \ X) + #(B \ Y))`. The second term shows that `X` and
`Y` contain all but an `ε / 4` proportion of `A` and `B`. A sum with `r` representations lies in
the sumset of the two samples with probability at least
`r * c₁ * c₂ / (9 * #X * #Y + r * c₁ * c₂)`, by a second-moment estimate. Suppose that the
expected size of the sumset of the samples is less than
`min ((1 - ε) * #(X + Y)) (K * #X) (K * #Y)`. Then the set `P` of sums with at least
`bltAlpha K ε * min #X #Y` representations has fewer than `(1 - ε / 2) * #(X + Y)` and fewer than
`2 * K * min #X #Y` elements, and at most `bltDelta K ε * #X * #Y` pairs have their sum outside
`P`. If `#(X + Y) ≤ D * min #X #Y`, the cleanup theorem gives a pair of subsets with smaller
value of the minimized quantity. Otherwise the covering bound does. Both contradict the choice of
`X` and `Y`. The theorem for `σ > 0` and `ε > 0` is the case `K = 2 * max σ 1` with `min ε 1 / 2`
in place of `ε`.

*Fox, Luo, Pham and Zhou.* Let `C = A + T` have fewer than `κ ^ (1 / 3) * #A / 14` elements.
Suppose that for every `b ∈ A` fewer than `#A / 14` elements `a ∈ A` have `a + b ∉ C`. Then for
all `x, y ∈ A` at least `11 * #A ^ 2 / 14` pairs `(a, a')` in `A ×ˢ A` have `a + x`, `a + a'` and
`a' + y` in `C`, and `x + y = (a + x) - (a + a') + (a' + y)`. Counting triples of elements of `C`
gives `#(A + A) * (11 * #A ^ 2 / 14) ≤ #C ^ 3`, which is false. So some `b ∈ A` has
`#(A + insert b T) ≥ #(A + T) + #A / 14`, and the theorem follows by induction on `s`.

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
