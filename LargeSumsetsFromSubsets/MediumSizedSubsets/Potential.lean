/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# The penalised minimality step

Among the pairs of nonempty subsets `X ⊆ A` and `Y ⊆ B` we minimise the potential
`min {#(X + Y), D * #X, D * #Y} + Λ * (#(A \ X) + #(B \ Y))`.
The minimiser is large, because the penalty term of `(A, B)` vanishes, and it is robust: passing to
subsets can only decrease the capped sumset term by less than the penalty incurred. Both facts are
recorded in `LargeSumsetsFromSubsets.exists_potential_minimiser`, which is the only interface
to the potential used later.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

open Finset

open scoped Pointwise

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The capped sumset term of the potential. -/
def cappedSumset (D : ℝ) (X Y : Finset G) : ℝ :=
  min (min (#(X + Y) : ℝ) (D * #X)) (D * #Y)

lemma cappedSumset_nonneg {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) : 0 ≤ cappedSumset D X Y := by
  unfold cappedSumset
  exact le_min (le_min (by positivity) (by positivity)) (by positivity)

lemma cappedSumset_le_card {D : ℝ} (X Y : Finset G) : cappedSumset D X Y ≤ #(X + Y) :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- **Penalised minimality.** -/
theorem exists_potential_minimiser (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    {D Λ : ℝ} (hD : 0 < D) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧
      Λ * (((#A : ℝ) - #X) + ((#B : ℝ) - #Y)) ≤ D * min (#A : ℝ) (#B : ℝ) ∧
      ∀ X' ⊆ X, ∀ Y' ⊆ Y, X'.Nonempty → Y'.Nonempty →
        cappedSumset D X Y ≤ cappedSumset D X' Y'
          + Λ * (((#X : ℝ) - #X') + ((#Y : ℝ) - #Y')) := by
  classical
  set Φ : Finset G × Finset G → ℝ := fun p =>
    cappedSumset D p.1 p.2 + Λ * ((#(A \ p.1) : ℝ) + #(B \ p.2)) with hΦ
  set cands : Finset (Finset G × Finset G) :=
    (A.powerset ×ˢ B.powerset).filter fun p => p.1.Nonempty ∧ p.2.Nonempty with hcands
  have hABmem : (A, B) ∈ cands := by
    simp [hcands, mem_filter, mem_product, mem_powerset, hA, hB]
  obtain ⟨⟨X, Y⟩, hmemXY, hmin⟩ := exists_min_image cands Φ ⟨(A, B), hABmem⟩
  obtain ⟨hXA, hYB, hXne, hYne⟩ : X ⊆ A ∧ Y ⊆ B ∧ X.Nonempty ∧ Y.Nonempty := by
    rw [hcands, mem_filter, mem_product, mem_powerset, mem_powerset] at hmemXY
    exact ⟨hmemXY.1.1, hmemXY.1.2, hmemXY.2.1, hmemXY.2.2⟩
  have hsdiff : ∀ {S T : Finset G}, T ⊆ S → (#(S \ T) : ℝ) = (#S : ℝ) - #T := by
    intro S T hTS
    rw [card_sdiff_of_subset hTS]
    exact_mod_cast Nat.cast_sub (card_le_card hTS)
  refine ⟨X, hXA, Y, hYB, hXne, hYne, ?_, ?_⟩
  · have hAB : Φ (A, B) ≤ D * min (#A : ℝ) (#B : ℝ) := by
      simp only [hΦ, sdiff_self, bot_eq_empty, card_empty, Nat.cast_zero, add_zero, mul_zero,
        cappedSumset]
      rw [mul_min_of_nonneg _ _ hD.le]
      exact min_le_min (min_le_right _ _) le_rfl
    have hXY := (hmin (A, B) hABmem).trans hAB
    simp only [hΦ] at hXY
    rw [hsdiff hXA, hsdiff hYB] at hXY
    linarith [cappedSumset_nonneg (D := D) hD.le X Y]
  · intro X' hX'X Y' hY'Y hX'ne hY'ne
    have hmem : (X', Y') ∈ cands := by
      simp only [hcands, mem_filter, mem_product, mem_powerset]
      exact ⟨⟨hX'X.trans hXA, hY'Y.trans hYB⟩, hX'ne, hY'ne⟩
    have h := hmin (X', Y') hmem
    simp only [hΦ] at h
    rw [hsdiff hXA, hsdiff hYB, hsdiff (hX'X.trans hXA), hsdiff (hY'Y.trans hYB)] at h
    linarith

end LargeSumsetsFromSubsets
