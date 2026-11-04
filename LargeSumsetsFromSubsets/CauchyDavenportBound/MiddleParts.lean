/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Basic.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.ConsecutiveIntervals
import LargeSumsetsFromSubsets.IntervalSumsets
import Mathlib.Tactic.Rify

/-!
# The middle parts

The middle parts of the proof of Theorem 1 of Bollobás, Leader and Tiba: the points of `A` and `B`
in the middle intervals `I₂` and `J₂` of Lemma 9. The sets `A` and `B` are within `δ` of `I₂` and
`J₂`, so `A ∩ I₂` and `B ∩ J₂` are dense subsets of intervals of comparable lengths, and Theorem 8
gives small subsets of them with `#(A ∩ I₂) + #(B ∩ J₂) - 1` sums.

## Main statements

* `exists_card_inter_add_card_inter_sub_one_le_card_add`: Theorem 8 for the middle parts.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {p : ℕ}

/-- Let `A` be within `δ` of `I = arithProg x 1 m` with `m ≤ p`, `3 * δ ≤ μ` and
`α * #A ≤ μ ≤ #A`. Then `2 * μ / 3 ≤ m`, `α * m ≤ 4 * μ / 3`, and the part `A ∩ I` has at least
`α / 2 * #A` elements. -/
lemma mul_le_card_inter_of_card_symmDiff_le {A : Finset (ZMod p)} {x : ZMod p} {m : ℕ}
    {α δ μ : ℝ} (hm : m ≤ p) (hα : 0 < α) (hα₁ : α ≤ 1) (hδμ : 3 * δ ≤ μ) (hμA : μ ≤ #A)
    (hαA : α * #A ≤ μ) (hA : #(A ∆ arithProg x 1 m) ≤ δ) :
    2 * μ / 3 ≤ m ∧ α * m ≤ 4 * μ / 3 ∧ α / 2 * #A ≤ #(A ∩ arithProg x 1 m) := by
  obtain ⟨hAm, hmA⟩ := abs_le.1 (abs_card_sub_le_of_card_symmDiff_le hm hA)
  have hδ : 0 ≤ δ := (Nat.cast_nonneg _).trans hA
  refine ⟨by linarith, by nlinarith [mul_le_of_le_one_left hδ hα₁], ?_⟩
  have hAI := card_inter_add_card_sdiff A (arithProg x 1 m)
  rify at hAI
  linarith [mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) #A) hα₁, (Nat.cast_le (α := ℝ)).2
    (card_le_card (symmDiff_subset_sdiff (s := A) (t := arithProg x 1 m)))]

/-- The condition of Theorem 8 for the subsets with `min c₁ x` and `min c₂ y` elements of sets of
sizes `x` and `y` with `α / 2 * a ≤ x ≤ a` and `α / 2 * b ≤ y ≤ b`. -/
lemma mul_max_le_min_mul_min_of_le {α c : ℝ} {a b x y c₁ c₂ : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hxa : x ≤ a) (hyb : y ≤ b) (hx : α / 2 * a ≤ x) (hy : α / 2 * b ≤ y) (hc₁ : c₁ ≤ a)
    (hc₂ : c₂ ≤ b) (hc : 4 * max c 0 / α ^ 2 * max (a : ℝ) b ≤ c₁ * c₂) :
    c * max (x : ℝ) y ≤ (min c₁ x : ℕ) * (min c₂ y : ℕ) := by
  have h₁ : α / 2 * c₁ ≤ min (c₁ : ℝ) x :=
    le_min (by nlinarith [Nat.cast_nonneg (α := ℝ) c₁])
      (by nlinarith [(Nat.cast_le (α := ℝ)).2 hc₁])
  have h₂ : α / 2 * c₂ ≤ min (c₂ : ℝ) y :=
    le_min (by nlinarith [Nat.cast_nonneg (α := ℝ) c₂])
      (by nlinarith [(Nat.cast_le (α := ℝ)).2 hc₂])
  push_cast
  calc c * max (x : ℝ) y ≤ max c 0 * max (a : ℝ) b := by
        gcongr
        exact le_max_left c 0
    _ = (α / 2) ^ 2 * (4 * max c 0 / α ^ 2 * max (a : ℝ) b) := by
        field_simp
        ring
    _ ≤ (α / 2) ^ 2 * (c₁ * c₂) := by gcongr
    _ = (α / 2 * c₁) * (α / 2 * c₂) := by ring
    _ ≤ min (c₁ : ℝ) x * min (c₂ : ℝ) y := by gcongr

/-- Theorem 8 for the middle parts. There is `γ₈ > 0` such that for `0 < α ≤ 1` there is `c` with
the following property. Let `A` and `B` be within `δ` of intervals `I` and `J` of total length at
most `p`, where `3 * δ ≤ min (γ₈ * μ) μ` and `α * #A, α * #B ≤ μ ≤ #A, #B`. If `c ≤ c₁ ≤ #A` and
`c ≤ c₂ ≤ #B` satisfy `c * max #A #B ≤ c₁ * c₂`, then some subsets of `A ∩ I` and `B ∩ J` with at
most `c₁` and `c₂` elements have `#(A ∩ I) + #(B ∩ J) - 1` sums. -/
lemma exists_card_inter_add_card_inter_sub_one_le_card_add :
    ∃ γ₈ > (0 : ℝ), ∀ α > (0 : ℝ), α ≤ 1 → ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (A B : Finset (ZMod p)) (x y : ZMod p) (m n c₁ c₂ : ℕ) (δ μ : ℝ), m + n ≤ p →
      3 * δ ≤ γ₈ * μ → 3 * δ ≤ μ → μ ≤ #A → μ ≤ #B → α * #A ≤ μ → α * #B ≤ μ →
      #(A ∆ arithProg x 1 m) ≤ δ → #(B ∆ arithProg y 1 n) ≤ δ →
      c ≤ c₁ → c ≤ c₂ → c₁ ≤ #A → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A ∩ arithProg x 1 m, ∃ B' ⊆ B ∩ arithProg y 1 n, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
        #(A ∩ arithProg x 1 m) + #(B ∩ arithProg y 1 n) - 1 ≤ #(A' + B') := by
  obtain ⟨γ₈, hγ₈, h₈⟩ :=
    exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg
  refine ⟨γ₈, hγ₈, ?_⟩
  intro α hα hα₁
  obtain ⟨c₈, hc₈⟩ := h₈ (α / 2) (by positivity)
  refine ⟨max (4 * max c₈ 0 / α ^ 2) 1, ?_⟩
  intro p hp A B x y m n c₁ c₂ δ μ hmn hδγ hδμ hμA hμB hαA hαB hA hB hcc₁ hcc₂ hc₁A hc₂B hc
  obtain ⟨hmμ, hαm, hAI⟩ :=
    mul_le_card_inter_of_card_symmDiff_le (by grind) hα hα₁ hδμ hμA hαA hA
  obtain ⟨hnμ, hαn, hBJ⟩ :=
    mul_le_card_inter_of_card_symmDiff_le (by grind) hα hα₁ hδμ hμB hαB hB
  obtain ⟨hc₁, hc₂⟩ : 1 ≤ c₁ ∧ 1 ≤ c₂ := ⟨Nat.one_le_cast.1 ((le_max_right _ _).trans hcc₁),
    Nat.one_le_cast.1 ((le_max_right _ _).trans hcc₂)⟩
  have hδ : δ ≤ γ₈ * min (m : ℝ) n := by
    nlinarith [mul_le_mul_of_nonneg_left (le_min hmμ hnμ) hγ₈.le, (Nat.cast_nonneg _).trans hA]
  obtain ⟨A', hA', B', hB', hA'c, hB'c, hAB'⟩ := hc₈ p hp x y m n (A ∩ arithProg x 1 m)
    (B ∩ arithProg y 1 n) (min c₁ #(A ∩ arithProg x 1 m)) (min c₂ #(B ∩ arithProg y 1 n))
    inter_subset_right inter_subset_right hmn (by linarith)
    ((le_inv_mul_iff₀ (by positivity)).2 (by linarith))
    (by grw [sdiff_inter_self_right, card_le_card symmDiff_subset_sdiff', hA, hδ])
    (by grw [sdiff_inter_self_right, card_le_card symmDiff_subset_sdiff', hB, hδ])
    (le_min hc₁ (Nat.cast_pos.1 (hAI.trans_lt'
      (mul_pos (half_pos hα) (Nat.cast_pos.2 (hc₁.trans hc₁A))))))
    (min_le_right _ _)
    (le_min hc₂ (Nat.cast_pos.1 (hBJ.trans_lt'
      (mul_pos (half_pos hα) (Nat.cast_pos.2 (hc₂.trans hc₂B))))))
    (min_le_right _ _)
    (mul_max_le_min_mul_min_of_le hα hα₁ (card_le_card inter_subset_left)
      (card_le_card inter_subset_left) hAI hBJ hc₁A hc₂B
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hc))
  exact ⟨A', hA', B', hB', hA'c ▸ min_le_left _ _, hB'c ▸ min_le_left _ _, hAB'⟩

end LargeSumsetsFromSubsets
