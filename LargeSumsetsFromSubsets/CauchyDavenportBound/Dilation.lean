/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.NearIntervals
import Mathlib.Algebra.Field.ZMod

/-!
# Dilation of sets near arithmetic progressions

Multiplication by the inverse of `d ≠ 0` maps sets of `ZMod p` close to arithmetic progressions of
common difference `d` to sets equally close to intervals, and preserves sizes and sumsets. This
reduces Theorem 1 of Bollobás, Leader and Tiba for sets near arithmetic progressions with the same
common difference to the case of sets near intervals.

## Main statements

* `exists_card_add_card_sub_one_le_card_add_of_near_arithProg`: Theorem 1 for sets near arithmetic
  progressions with the same common difference.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {p : ℕ}

/-- Large sumsets of small subsets can be pulled back along the multiplication by a unit. -/
lemma exists_card_add_of_image_mul (hp : p.Prime) {u : ZMod p} (hu : u ≠ 0)
    {A B : Finset (ZMod p)} {k₁ k₂ : ℕ}
    (h : ∃ A' ⊆ A.image (u * ·), ∃ B' ⊆ B.image (u * ·), #A' ≤ k₁ ∧ #B' ≤ k₂ ∧
      #(A.image (u * ·)) + #(B.image (u * ·)) - 1 ≤ #(A' + B')) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ k₁ ∧ #B' ≤ k₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  have := Fact.mk hp
  obtain ⟨A', hA', B', hB', hA'k, hB'k, hAB⟩ := h
  obtain ⟨A'', hA'', rfl⟩ := subset_image_iff.1 hA'
  obtain ⟨B'', hB'', rfl⟩ := subset_image_iff.1 hB'
  have hadd : (A'' + B'').image (u * ·) = A''.image (u * ·) + B''.image (u * ·) :=
    image_add (AddMonoidHom.mulLeft u)
  simp only [← hadd, card_image_of_injective _ (mul_right_injective₀ hu)] at hA'k hB'k hAB
  exact ⟨A'', hA'', B'', hB'', hA'k, hB'k, hAB⟩

/-- Multiplication by the inverse of `d ≠ 0` maps a set close to an arithmetic progression of
common difference `d` to a set equally close to an interval. -/
lemma card_image_mul_symmDiff_arithProg (hp : p.Prime) {d : ZMod p} (hd : d ≠ 0)
    (A : Finset (ZMod p)) (a : ZMod p) (m : ℕ) :
    #(A.image (d⁻¹ * ·) ∆ arithProg (d⁻¹ * a) 1 m) = #(A ∆ arithProg a d m) := by
  have := Fact.mk hp
  have hinj : Function.Injective (d⁻¹ * ·) := mul_right_injective₀ (inv_ne_zero hd)
  rw [← inv_mul_cancel₀ hd, ← image_mul_arithProg, ← image_symmDiff _ _ hinj,
    card_image_of_injective _ hinj]

/-- **Theorem 1** of Bollobás, Leader and Tiba for sets near arithmetic progressions. The statement
of `exists_card_add_card_sub_one_le_card_add_of_near_intervals` for sets near arithmetic
progressions with the same common difference `d ≠ 0`, obtained by multiplying by `d⁻¹`. -/
lemma exists_card_add_card_sub_one_le_card_add_of_near_arithProg {α β : ℝ} (hα : 0 < α)
    (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 1024) :
    ∃ γ > (0 : ℝ), ∃ K : ℝ, ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty →
      B.Nonempty → α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      ∀ (a b d : ZMod p) (m n : ℕ), d ≠ 0 → #(A ∆ arithProg a d m) ≤ γ * min (#A : ℝ) #B →
      #(B ∆ arithProg b d n) ≤ γ * min (#A : ℝ) #B →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → K ≤ c₁ → K ≤ c₂ → K * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ (3 + 2 * ⌈192 / (α * β)⌉₊) * c₁ ∧
        #B' ≤ (3 + 2 * ⌈192 / (α * β)⌉₊) * c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ, hγ, K, hK⟩ := exists_card_add_card_sub_one_le_card_add_of_near_intervals hα hα₁ hβ hβ₁
  refine ⟨γ, hγ, K, ?_⟩
  intro p hp A B hA hB hAB hBA hABp a b d m n hd hAP hBQ c₁ c₂ hc₁A hc₂B hKc₁ hKc₂ hKc
  have := Fact.mk hp
  apply exists_card_add_of_image_mul hp (inv_ne_zero hd)
  refine hK p hp _ _ (hA.image _) (hB.image _) ?_ ?_ ?_ (d⁻¹ * a) (d⁻¹ * b) m n ?_ ?_ c₁ c₂ ?_ ?_
    hKc₁ hKc₂ ?_ <;>
    simpa [card_image_mul_symmDiff_arithProg hp hd,
      card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hd))]

end LargeSumsetsFromSubsets
