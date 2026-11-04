/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# Large sumsets from medium-sized subsets

Theorems 1 and 2 of Béla Bollobás, Imre Leader and Marius Tiba, *Large sumsets from medium-sized
subsets*, arXiv:2206.09366.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

/-- **Theorem 1** of Bollobás, Leader and Tiba. For `α, β > 0` there is `c > 0` such that if
`A, B ⊆ ZMod p` are nonempty with `α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, then for
all `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` with `c₁ * c₂ ≥ c * max #A #B` there are `A' ⊆ A` and
`B' ⊆ B` with `c₁` and `c₂` elements and `#(A' + B') ≥ #A + #B - 1`. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add' {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ #A + #B - 1 ≤ #(A' + B') :=
  sorry

/-- **Theorem 2** of Bollobás, Leader and Tiba. For `σ, ε > 0` there is `c` with the following
property. Let `A` and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A`
and `1 ≤ c₂ ≤ #B` satisfy `c₁ * c₂ > c * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
`#A₀ > (1 - ε) * #A` and `#B₀ > (1 - ε) * #B` such that, for `c₁` points of `A₀` and `c₂` points
of `B₀` chosen independently and uniformly at random, the sets `A'` and `B'` of chosen points
satisfy `𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (min (σ * #A₀) (σ * #B₀))`. -/
theorem exists_forall_exists_subset_min_lt_expect_card_add' {σ ε : ℝ} (hσ : 0 < σ)
    (hε : 0 < ε) :
    ∃ c : ℝ, ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G} {c₁ c₂ : ℕ},
      A.Nonempty → B.Nonempty → 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B →
      c * max (#A : ℝ) #B < c₁ * c₂ →
      ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
        (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
        min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
          𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
            (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) :=
  sorry

end LargeSumsetsFromSubsets
