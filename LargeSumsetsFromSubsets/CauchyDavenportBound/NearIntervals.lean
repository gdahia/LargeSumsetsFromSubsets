/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.EndParts
import LargeSumsetsFromSubsets.CauchyDavenportBound.FarParts
import LargeSumsetsFromSubsets.CauchyDavenportBound.MiddleParts

/-!
# Theorem 1 for sets near intervals

Theorem 1 of Bollobás, Leader and Tiba for sets `A` and `B` of `ZMod p` close to intervals. Lemma 9
cuts `ZMod p` into the middle intervals `I₂` and `J₂`, the end intervals `I₁, I₃, J₁, J₃` and the
rest. The end parts give a set `Z` of sums outside `I₂ + J₂`, the far parts a set `S` of sums
outside `Z` and `I₂ + J₂`, and the middle parts `#(A ∩ I₂) + #(B ∩ J₂) - 1` sums in `I₂ + J₂`.
These add up to `#A + #B - 1`.

## Main statements

* `exists_card_add_card_sub_one_le_card_add_of_near_intervals`: Theorem 1 for sets near intervals,
  with subsets of at most `(3 + 2 * ⌈192 / (α * β)⌉₊) * c₁` and
  `(3 + 2 * ⌈192 / (α * β)⌉₊) * c₂` elements.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {G : Type*} [DecidableEq G] [Add G]

/-- If `Z ⊆ A₁ + B₁`, `A₂ + B₂` and `S ⊆ A₃ + B₃` are pairwise disjoint, then the unions
`A₁ ∪ A₂ ∪ A₃` and `B₁ ∪ B₂ ∪ B₃` have at least `#Z + #(A₂ + B₂) + #S` sums. -/
lemma card_add_card_add_card_le_card_add {A₁ A₂ A₃ B₁ B₂ B₃ Z S : Finset G}
    (hZ : Z ⊆ A₁ + B₁) (hS : S ⊆ A₃ + B₃) (hZT : Disjoint Z (A₂ + B₂)) (hSZ : Disjoint S Z)
    (hST : Disjoint S (A₂ + B₂)) :
    #Z + #(A₂ + B₂) + #S ≤ #((A₁ ∪ A₂ ∪ A₃) + (B₁ ∪ B₂ ∪ B₃)) := by
  rw [← card_union_of_disjoint hZT,
    ← card_union_of_disjoint (disjoint_union_right.2 ⟨hSZ, hST⟩).symm]
  apply card_le_card
  grw [hZ, hS]
  refine union_subset (union_subset ?_ ?_) ?_
  · exact add_subset_add (subset_union_left.trans subset_union_left)
      (subset_union_left.trans subset_union_left)
  · exact add_subset_add (subset_union_right.trans subset_union_left)
      (subset_union_right.trans subset_union_left)
  · exact add_subset_add subset_union_right subset_union_right

variable {p : ℕ}

/-- If `α * #B ≤ #A ≤ α⁻¹ * #B` with `0 < α ≤ 1`, then `α * #A` and `α * #B` are at most
`min #A #B`. -/
lemma mul_card_le_min_card {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) {A B : Finset (ZMod p)}
    (hAB : α * #B ≤ #A) (hBA : #A ≤ α⁻¹ * #B) :
    α * #A ≤ min (#A : ℝ) #B ∧ α * #B ≤ min (#A : ℝ) #B :=
  ⟨le_min (mul_le_of_le_one_left (Nat.cast_nonneg _) hα₁) ((le_inv_mul_iff₀ hα).1 hBA),
    le_min hAB (mul_le_of_le_one_left (Nat.cast_nonneg _) hα₁)⟩

/-- **Theorem 1** of Bollobás, Leader and Tiba for sets near intervals. For `0 < α ≤ 1` and
`0 < β ≤ 1 / 1024` there are `γ > 0` and `K` with the following property. Let `A` and `B` be within
`γ * min #A #B` of intervals of `ZMod p`, with `α * #B ≤ #A ≤ α⁻¹ * #B` and
`#A + #B ≤ (1 - β) * p`, and let `c₁ ≤ #A` and `c₂ ≤ #B` satisfy `K ≤ c₁`, `K ≤ c₂` and
`K * max #A #B ≤ c₁ * c₂`. Then some subsets of `A` and `B` with at most
`(3 + 2 * ⌈192 / (α * β)⌉₊) * c₁` and `(3 + 2 * ⌈192 / (α * β)⌉₊) * c₂` elements have
`#A + #B - 1` sums. -/
lemma exists_card_add_card_sub_one_le_card_add_of_near_intervals {α β : ℝ} (hα : 0 < α)
    (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 1024) :
    ∃ γ > (0 : ℝ), ∃ K : ℝ, ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty →
      B.Nonempty → α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      ∀ (x y : ZMod p) (m n : ℕ), #(A ∆ arithProg x 1 m) ≤ γ * min (#A : ℝ) #B →
      #(B ∆ arithProg y 1 n) ≤ γ * min (#A : ℝ) #B →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → K ≤ c₁ → K ≤ c₂ → K * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ (3 + 2 * ⌈192 / (α * β)⌉₊) * c₁ ∧
        #B' ≤ (3 + 2 * ⌈192 / (α * β)⌉₊) * c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ₈, hγ₈, h₈⟩ := exists_card_inter_add_card_inter_sub_one_le_card_add
  obtain ⟨c₈, hc₈⟩ := h₈ α hα hα₁
  obtain ⟨cₑ, hcₑ⟩ := exists_card_eq_disjoint_of_interval_ends hβ
  obtain ⟨γ, hγ, hγβ, hγγ₈⟩ : ∃ γ > (0 : ℝ), 2 ^ 20 * γ ≤ β ∧ 400 * γ ≤ γ₈ :=
    ⟨min (β / 2 ^ 20) (γ₈ / 400), by positivity, by grind, by grind⟩
  obtain ⟨K, hKₑ, hK₈, hK⟩ : ∃ K : ℝ, cₑ ≤ K ∧ c₈ ≤ K ∧ 6400 ≤ α * β * K :=
    ⟨max (max cₑ c₈) (6400 / (α * β)), by grind, by grind,
      (div_le_iff₀' (by positivity)).1 (le_max_right _ _)⟩
  refine ⟨γ, hγ, K, ?_⟩
  intro p hp A B hA hB hAB hBA hABp x y m n hAx hBy c₁ c₂ hc₁A hc₂B hKc₁ hKc₂ hKc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hμ : 0 ≤ min (#A : ℝ) #B := by positivity
  obtain ⟨hαA, hαB⟩ := mul_card_le_min_card hα hα₁ hAB hBA
  obtain ⟨s, r, a₁, a₂, a₃, b₁, b₂, b₃, hL₁, hL₃, hL₁', hL₃', hsum, -, h₁, h₃, hA₂, hB₂, hf₁,
    hf₃⟩ := exists_interval_ends (x := x) (y := y) hp hβ₁ hγ hγβ hA hB hABp (min_le_right m p)
      (min_le_right n p) (by rwa [← arithProg_one_eq_min]) (by rwa [← arithProg_one_eq_min])
  obtain ⟨A₁, hA₁, B₁, hB₁, hA₁c, hB₁c, Z, hZ, hZc, hZ₂⟩ := hcₑ p hp A B s r a₁ a₂ a₃ b₁ b₂ b₃
    c₁ c₂ hsum hABp h₁ h₃ hf₁ hf₃ (hKₑ.trans hKc₁) (hKₑ.trans hKc₂)
    ((mul_le_mul_of_nonneg_right hKₑ (by positivity)).trans hKc)
  obtain ⟨A₂, hA₂', B₂, hB₂', hA₂c, hB₂c, hAB₂⟩ := hc₈ p hp A B (s + a₁) (r + b₁) a₂ b₂ c₁ c₂
    _ (min (#A : ℝ) #B) (by grind) (by linarith [mul_le_mul_of_nonneg_right hγγ₈ hμ])
    (by linarith [mul_le_mul_of_nonneg_right hγβ hμ, mul_le_mul_of_nonneg_right hβ₁ hμ])
    (min_le_left _ _)
    (min_le_right _ _) hαA hαB hA₂ hB₂ (hK₈.trans hKc₁) (hK₈.trans hKc₂) hc₁A hc₂B
    ((mul_le_mul_of_nonneg_right hK₈ (by positivity)).trans hKc)
  obtain ⟨A₃, hA₃, B₃, hB₃, hA₃c, hB₃c, S, hS, hZS, hSZ, hS₂⟩ :=
    exists_card_eq_card_sdiff_add_card_sdiff_disjoint hp hα hα₁ hβ (by linarith) (min_le_left _ _)
      (min_le_right _ _) hαA hαB
      (by linarith [min_le_left (#A : ℝ) #B, mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) p)])
      (le_min (hKc₁.trans (mod_cast hc₁A)) (hKc₂.trans (mod_cast hc₂B))) hK
      (by linarith [mul_le_mul_of_nonneg_right hγβ hμ, mul_nonneg hγ.le hμ]) hL₁ hL₃ hL₁' hL₃'
      hsum hA₂ hB₂ hZc hc₁A hc₂B hKc₁ hKc₂ hKc
  have hT : A₂ + B₂ ⊆ arithProg (s + (a₁ : ZMod p)) 1 a₂ + arithProg (r + (b₁ : ZMod p)) 1 b₂ :=
    add_subset_add (hA₂'.trans inter_subset_right) (hB₂'.trans inter_subset_right)
  refine ⟨A₁ ∪ A₂ ∪ A₃, union_subset (union_subset hA₁ (hA₂'.trans inter_subset_left)) hA₃,
    B₁ ∪ B₂ ∪ B₃, union_subset (union_subset hB₁ (hB₂'.trans inter_subset_left)) hB₃,
    ?_, ?_, ?_⟩
  · grw [card_union_le, card_union_le, hA₁c, hA₂c, hA₃c]
    linarith
  · grw [card_union_le, card_union_le, hB₁c, hB₂c, hB₃c]
    linarith
  grw [← card_add_card_add_card_le_card_add hZ hS (hZ₂.mono_right hT) hSZ (hS₂.mono_right hT),
    Nat.sub_le_iff_le_add]
  linarith [Nat.sub_le_iff_le_add.1 hAB₂,
    card_inter_add_card_sdiff A (arithProg (s + (a₁ : ZMod p)) 1 a₂),
    card_inter_add_card_sdiff B (arithProg (r + (b₁ : ZMod p)) 1 b₂)]

end LargeSumsetsFromSubsets
