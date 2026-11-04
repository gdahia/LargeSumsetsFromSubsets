/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import LargeSumsetsFromSubsets.CauchyDavenportBound.Stability
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Basic

/-!
# Large sumsets from medium-sized subsets of `ZMod p`

Theorem 1 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*: for `α, β > 0`
there is `c > 0` such that if `A, B ⊆ ZMod p` are nonempty with `α * #B ≤ #A ≤ α⁻¹ * #B` and
`#A + #B ≤ (1 - β) * p`, then for all `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` with
`c * max #A #B ≤ c₁ * c₂` there are `A' ⊆ A` and `B' ⊆ B` with `c₁` and `c₂` elements and
`#A + #B - 1 ≤ #(A' + B')`.

The proof is that of the paper, in the stages of the directory `CauchyDavenportBound`. If no small
subsets reach `#A + #B - 1`, Theorem 6 places `A` and `B` near arithmetic progressions with the same
common difference, and after a dilation near intervals. Lemma 9 cuts `ZMod p` into the middle
intervals `I₂` and `J₂`, the end intervals `I₁, I₃, J₁, J₃` and the rest. The middle parts are
handled by Theorem 8, the end parts by Theorems 4 and 6, and the far parts by Lemma 12 and
Corollary 11. The resulting sumsets lie in disjoint regions and add up to `#A + #B - 1`.

## Main statements

* `exists_subset_card_eq_card_add_card_sub_one_le_card_add`: Theorem 1 of the paper.
-/

public section

open Finset
open scoped Pointwise

namespace LargeSumsetsFromSubsets

/-- **Theorem 1** of Bollobás, Leader and Tiba. For `α, β > 0` there is `c > 0` such that if
`A, B ⊆ ZMod p` are nonempty with `α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, then for all
`1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` with `c₁ * c₂ ≥ c * max #A #B` there are `A' ⊆ A` and `B' ⊆ B` with
`c₁` and `c₂` elements and `#(A' + B') ≥ #A + #B - 1`. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨c, hc, h⟩ := exists_subset_card_le_card_add_card_sub_one_le_card_add
    (lt_min hα one_pos) (min_le_right α 1) (lt_min hβ (by norm_num)) (min_le_right β (1 / 1024))
  refine ⟨c, hc, ?_⟩
  intro p hp A B hA hB hAB hBA hABp c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc
  refine exists_subset_card_eq_of_card_le hc₁A hc₂B (h p hp A B hA hB ?_ ?_ ?_ c₁ c₂ hc₁A hc₂B hcc)
  · grw [min_le_left α 1]
    exact hAB
  · grw [hBA, min_le_left α 1]
  · grw [hABp, min_le_left β (1 / 1024)]

end LargeSumsetsFromSubsets
