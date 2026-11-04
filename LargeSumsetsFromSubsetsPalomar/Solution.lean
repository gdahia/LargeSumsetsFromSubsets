/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import LargeSumsetsFromSubsets.CauchyDavenportBound
import LargeSumsetsFromSubsets.Cleanup
import LargeSumsetsFromSubsets.IntervalSumsets
import LargeSumsetsFromSubsets.MediumSizedSubsets
import LargeSumsetsFromSubsets.ZModStability

/-!
# Large sumsets from medium-sized subsets

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime.
-/

public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

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
  exists_forall_exists_subset_min_lt_expect_card_add hσ hε

/-- **Arithmetic removal lemma in a set of small doubling.** For `K ≥ 0` and `ε > 0` there is
`δ > 0` with the following property. Let `X` be a finite subset of an abelian group with
`#(X + X) ≤ K * #X` and let `A, B, C ⊆ X`. If `a + b = c` has at most `δ * #X ^ 2` solutions with
`a ∈ A`, `b ∈ B` and `c ∈ C`, then one can remove at most `ε * #X` elements from each of `A`, `B`
and `C` so that no solution remains. -/
theorem exists_forall_exists_subset_card_sdiff_le_forall_add_ne' {K ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X A B C : Finset G},
      A ⊆ X → B ⊆ X → C ⊆ X → #(X + X) ≤ K * #X →
      #{x ∈ A ×ˢ B ×ˢ C | x.1 + x.2.1 = x.2.2} ≤ δ * #X ^ 2 →
      ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C, #(A \ A') ≤ ε * #X ∧ #(B \ B') ≤ ε * #X ∧ #(C \ C') ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c :=
  exists_forall_exists_subset_card_sdiff_le_forall_add_ne hK hε

/-- **Almost all sums in a small set.** For `D ≥ 1` and `ρ > 0` there is `δ > 0` with the
following property. Let `X` and `Y` be finite nonempty subsets of an abelian group with
`#(X + Y) ≤ D * min #X #Y`, and let `P` be a finite set. If at most `δ * (#X * #Y)` pairs in
`X ×ˢ Y` have their sum outside `P`, then one can remove at most `ρ * min #X #Y` elements from
each of `X` and `Y` so that the sumset of the remaining sets has at most `#P + ρ * min #X #Y`
elements. -/
theorem exists_forall_exists_subset_card_sdiff_le_card_add_le' {D ρ : ℝ} (hD : 1 ≤ D)
    (hρ : 0 < ρ) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X Y P : Finset G},
      X.Nonempty → Y.Nonempty → #(X + Y) ≤ D * min (#X : ℝ) #Y →
      #{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} ≤ δ * (#X * #Y) →
      ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, #(X \ X₀) ≤ ρ * min (#X : ℝ) #Y ∧ #(Y \ Y₀) ≤ ρ * min (#X : ℝ) #Y ∧
        #(X₀ + Y₀) ≤ #P + ρ * min (#X : ℝ) #Y :=
  exists_forall_exists_subset_card_sdiff_le_card_add_le hD hρ

/-- **Theorem 6** of Bollobás, Leader and Tiba. For `β, γ > 0` there is `ε > 0` such that for
`α > 0` there is `c` with the following property. Let `A, B ⊆ ZMod p` have at least two elements,
`α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ ≥ c * max #A #B`. If the sumset of uniformly random subsets of `A` and `B` with
`c₁` and `c₂` elements has expected size at most `#A + #B - 1 + ε * min #A #B`, then `A` and `B`
differ in at most `γ * min #A #B` points from arithmetic progressions with the same nonzero common
difference. -/
theorem exists_arithProg_card_symmDiff_le_of_expect_card_add_le' {β γ : ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) :
    ∃ ε > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (c₁ c₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ → 2 ≤ #A → 2 ≤ #B →
      α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      𝔼 A' ∈ powersetCard c₁ A, 𝔼 B' ∈ powersetCard c₂ B, (#(A' + B') : ℝ) ≤
        #A + #B - 1 + ε * min (#A : ℝ) #B →
      ∃ a b d : ZMod p, d ≠ 0 ∧ ∃ m n : ℕ,
        #(A ∆ (range m).image (fun i ↦ a + i • d)) ≤ γ * min (#A : ℝ) #B ∧
        #(B ∆ (range n).image (fun i ↦ b + i • d)) ≤ γ * min (#A : ℝ) #B :=
  exists_arithProg_card_symmDiff_le_of_expect_card_add_le hβ hγ

/-- **Theorem 8** of Bollobás, Leader and Tiba. There is `γ > 0` such that for `α > 0` there is
`c` with the following property. Let `X` and `Y` be subsets of intervals `I` and `J` of `ZMod p`
with `m` and `n` elements, where `m + n ≤ p` and `α * n ≤ m ≤ α⁻¹ * n`, each missing at most
`γ * min m n` points of its interval. If `1 ≤ c₁ ≤ #X` and `1 ≤ c₂ ≤ #Y` satisfy
`c₁ * c₂ ≥ c * max #X #Y`, there are `X' ⊆ X` and `Y' ⊆ Y` with `c₁` and `c₂` elements and
`#(X' + Y') ≥ #X + #Y - 1`. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range' :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (x y : ZMod p) (m n : ℕ) (X Y : Finset (ZMod p)) (c₁ c₂ : ℕ),
      X ⊆ (range m).image (fun i : ℕ ↦ x + i) → Y ⊆ (range n).image (fun i : ℕ ↦ y + i) →
      m + n ≤ p → α * n ≤ m → m ≤ α⁻¹ * n →
      #((range m).image (fun i : ℕ ↦ x + i) \ X) ≤ γ * min (m : ℝ) n →
      #((range n).image (fun i : ℕ ↦ y + i) \ Y) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') :=
  exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range

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
  exists_subset_card_eq_card_add_card_sub_one_le_card_add hα hβ

end LargeSumsetsFromSubsets
