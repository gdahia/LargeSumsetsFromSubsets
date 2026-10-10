/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Large sumsets from subsets: statements

Four results on sumsets in an abelian group, in terms of Mathlib and the definitions below. The
proofs are supplied by the companion `Solution` module.

* `exists_subset_min_lt_expect_card_bltSample_add`: Theorem 2 of Bollobás, Leader and Tiba,
  *Large sumsets from medium-sized subsets*, arXiv:2206.09366.
* `exists_subset_card_sdiff_le_forall_add_ne`: the arithmetic removal lemma in a set of small
  doubling, with the threshold `removalConst`, which is positive by `removalConst_pos`.
* `exists_subset_card_sdiff_le_card_add_le`: a variant of Shao's almost-all
  Balog–Szemerédi–Gowers theorem, arXiv:1811.10707, for pairs of sets with small sumset.
* `exists_subset_card_le_mul_le_card_add`: Theorem 1.1 of Fox, Luo, Pham and Zhou, *Small subsets
  with large sumset: beyond the Cauchy–Davenport bound*, arXiv:2210.07196.

The constant of the first theorem is `originalBltConstant σ ε = bltSampleConst K ε'` with
`K = 2 * max σ 1` and `ε' = min ε 1 / 2`. It equals `1296 * K / (ε' * bltDelta K ε')`, where
`bltDelta` is the minimum of `1 / 2`, a multiple of `ε' ^ 2 / K ^ 3`, and a value of `removalConst`.
The threshold `removalConst` is a multiple of Mathlib's `SimpleGraph.triangleRemovalBound`.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

/-! ### Definitions -/

namespace ArithmeticRemoval

/-- The threshold for the proportion of solutions of `a + b = c` in the arithmetic removal lemma
for subsets of a set of doubling `K`, with at most an `ε` proportion of elements removed. -/
noncomputable def removalConst (K ε : ℝ) : ℝ :=
  SimpleGraph.triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2

end ArithmeticRemoval

noncomputable section

/-- The cap `100 * K ^ 3` on the doubling of the pairs of sets that are cleaned up. -/
def bltCap (K : ℝ) : ℝ := 100 * K ^ 3

/-- The proportion of elements that a cleanup may delete. -/
def bltRho (K ε : ℝ) : ℝ := ε ^ 2 / (1000 * bltCap K)

/-- The proportion of pairs allowed to have an unpopular sum. -/
def bltDelta (K ε : ℝ) : ℝ :=
  min (min (1 / 2) (bltRho K ε / 8))
    (ArithmeticRemoval.removalConst (16 * bltCap K ^ 7) (bltRho K ε / bltCap K))

/-- The popularity threshold: a sum of `X` and `Y` is popular when it has at least
`bltAlpha K ε * min #X #Y` representations. -/
def bltAlpha (K ε : ℝ) : ℝ := bltDelta K ε / (36 * K)

/-- The constant of the theorem for `K ≥ 1` and `0 < ε ≤ 1`. -/
def bltSampleConst (K ε : ℝ) : ℝ := 36 / (ε * bltAlpha K ε)

/-- The constant `c(σ, ε)` in Theorem 2 of Bollobás, Leader and Tiba. -/
def originalBltConstant (σ ε : ℝ) (_hσ : 0 < σ) (_hε : 0 < ε) : ℝ :=
  bltSampleConst (2 * max σ 1) (min ε 1 / 2)

end

section Sample

variable {G : Type*} [DecidableEq G]

/-- The set of values of a sequence `f` of `k` elements of `A`. -/
def bltSample (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : Finset G := univ.image fun i ↦ f i

end Sample

/-! ### Statements -/

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Large sumsets from medium-sized subsets** (Bollobás, Leader and Tiba, Theorem 2). Let `A`
and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
more than `(1 - ε) * #A` and `(1 - ε) * #B` elements such that, for `c₁` points of `A₀` and `c₂`
points of `B₀` chosen independently and uniformly at random, with repetitions allowed, the sets
`A'` and `B'` of chosen points satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
theorem exists_subset_min_lt_expect_card_bltSample_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) (c₁ c₂ : ℕ) (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : originalBltConstant σ ε hσ hε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
      (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
        𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀), (#(bltSample A₀ ab.1 + bltSample B₀ ab.2) : ℝ) :=
  sorry

/-- The threshold of the arithmetic removal lemma is positive. -/
theorem removalConst_pos {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < ArithmeticRemoval.removalConst K ε :=
  sorry

/-- **Arithmetic removal lemma in a set of small doubling.** Let `X` be a finite subset of an
abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C ⊆ X`. If `a + b = c` has at most
`δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `δ ≤ removalConst K ε`, then one can
remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no solution remains. -/
theorem exists_subset_card_sdiff_le_forall_add_ne {X A B C : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X) (hK : 0 ≤ K) (hXX : (#(X + X) : ℝ) ≤ K * #X)
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ' : δ ≤ ArithmeticRemoval.removalConst K ε)
    (hsol : (#{x ∈ A ×ˢ B ×ˢ C | x.1 + x.2.1 = x.2.2} : ℝ) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c :=
  sorry

/-- **Almost all sums in a small set.** Let `X` and `Y` be finite nonempty subsets of an abelian
group with `#(X + Y) ≤ D * min #X #Y`, and let `P` be a finite set. If at most `δ * #X * #Y` pairs
in `X ×ˢ Y` have their sum outside `P`, where `δ ≤ removalConst (16 * D ^ 7) (ρ / D)`, then one
can remove at most `ρ * min #X #Y` elements from each of `X` and `Y` so that the sumset of the
remaining sets has at most `#P + ρ * min #X #Y` elements. -/
theorem exists_subset_card_sdiff_le_card_add_le {X Y P : Finset G} (hX : X.Nonempty)
    (hY : Y.Nonempty) {D ρ δ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ)
    (hS : (#(X + Y) : ℝ) ≤ D * min (#X : ℝ) #Y) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ ArithmeticRemoval.removalConst (16 * D ^ 7) (ρ / D))
    (hbad : (#{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} : ℝ) ≤ δ * (#X * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y,
      (#(X \ X₀) : ℝ) ≤ ρ * min (#X : ℝ) #Y ∧ (#(Y \ Y₀) : ℝ) ≤ ρ * min (#X : ℝ) #Y ∧
        (#(X₀ + Y₀) : ℝ) ≤ #P + ρ * min (#X : ℝ) #Y :=
  sorry

/-- **Large sumsets from few translates** (Fox, Luo, Pham and Zhou, Theorem 1.1). A finite
nonempty subset `A` of an abelian group with `#(A + A) = κ * #A` has, for each `s ≥ 1`, a subset
`T` with at most `s` elements and `#(A + T) ≥ min (κ ^ (1 / 3)) s * #A / 14`. -/
theorem exists_subset_card_le_mul_le_card_add {A : Finset G} (hA : A.Nonempty) {s : ℕ}
    (hs : 1 ≤ s) :
    ∃ T ⊆ A, #T ≤ s ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T) :=
  sorry

end LargeSumsetsFromSubsets
