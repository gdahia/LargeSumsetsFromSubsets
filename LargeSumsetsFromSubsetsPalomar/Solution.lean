/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import LargeSumsetsFromSubsets.MediumSizedSubsets
import LargeSumsetsFromSubsets.Cleanup
import LargeSumsetsFromSubsets.FewTranslates

/-!
# Large sumsets from subsets

The statements of `Challenge.lean`, proved by the results of the library with the same names
without the prime.
-/

public section

open Finset
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Large sumsets from medium-sized subsets** (Bollobás, Leader and Tiba, Theorem 2). Let `A`
and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
more than `(1 - ε) * #A` and `(1 - ε) * #B` elements such that, for `c₁` points of `A₀` and `c₂`
points of `B₀` chosen independently and uniformly at random, with repetitions allowed, the sets
`A'` and `B'` of chosen points satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
theorem exists_subset_min_lt_expect_card_add' {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : originalBltConstant σ ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
      (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
        𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
          (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) :=
  exists_subset_min_lt_expect_card_add hσ hε hA hB hc₁ hc₁A hc₂ hc₂B hc

namespace ArithmeticRemoval

/-- The threshold of the arithmetic removal lemma is positive. -/
theorem removalConst_pos' {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : 0 < removalConst K ε :=
  removalConst_pos hK hε

/-- **Arithmetic removal lemma in a set of small doubling.** Let `X` be a finite subset of an
abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C ⊆ X`. If `a + b = c` has at most
`δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `0 ≤ δ ≤ removalConst K ε`, then one
can remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no solution remains. -/
theorem exists_subset_card_sdiff_le_forall_add_ne' {X A B C : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X) (hK : 0 ≤ K) (hXX : #(X + X) ≤ K * #X) (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : #{x ∈ A ×ˢ B ×ˢ C | x.1 + x.2.1 = x.2.2} ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C, #(A \ A') ≤ ε * #X ∧ #(B \ B') ≤ ε * #X ∧ #(C \ C') ≤ ε * #X ∧
      ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c :=
  exists_subset_card_sdiff_le_forall_add_ne hA hB hC hK hXX hε hδ hδ' hsol

end ArithmeticRemoval

namespace Cleanup

/-- **The cleanup lemma.** Let `X` and `Y` be finite nonempty subsets of an abelian group with
`#(X + Y) ≤ D * min #X #Y`, where `D ≥ 1`, and let `P` be a finite set. If at most
`δ * #X * #Y` pairs of `X ×ˢ Y` have their sum outside `P`, where
`0 ≤ δ ≤ removalConst (16 * D ^ 7) (ρ / D)`, then one can remove at most `ρ * min #X #Y`
elements from each of `X` and `Y` so that the sumset of the remaining sets has at most
`#P + ρ * min #X #Y` elements. -/
theorem exists_subset_card_sdiff_le_card_add_le' {X Y P : Finset G} (hX : X.Nonempty)
    (hY : Y.Nonempty) {D ρ δ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ)
    (hS : #(X + Y) ≤ D * min (#X : ℝ) #Y) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ ArithmeticRemoval.removalConst (16 * D ^ 7) (ρ / D))
    (hbad : #{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} ≤ δ * (#X * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, #(X \ X₀) ≤ ρ * min (#X : ℝ) #Y ∧ #(Y \ Y₀) ≤ ρ * min (#X : ℝ) #Y ∧
      #(X₀ + Y₀) ≤ #P + ρ * min (#X : ℝ) #Y :=
  exists_subset_card_sdiff_le_card_add_le hX hY hD hρ hS hδ hδ' hbad

end Cleanup

namespace FewTranslates

/-- **Large sumsets from few translates** (Fox, Luo, Pham and Zhou, Theorem 1.1). A finite
nonempty subset `A` of an abelian group has, for each `s ≥ 1`, a subset `T` with at most `s`
elements and `#(A + T) ≥ min (κ ^ (1 / 3)) s * #A / 14`, where `κ = #(A + A) / #A`. -/
theorem exists_subset_card_le_mul_le_card_add' {A : Finset G} (hA : A.Nonempty) {s : ℕ}
    (hs : 1 ≤ s) :
    ∃ T ⊆ A, #T ≤ s ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T) :=
  exists_subset_card_le_mul_le_card_add hA hs

end FewTranslates

end LargeSumsetsFromSubsets
