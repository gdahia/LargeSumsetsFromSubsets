/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.CastCard
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

/-- The capped sumset term is nonnegative. -/
lemma cappedSumset_nonneg {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) : 0 ≤ cappedSumset D X Y :=
  le_min (le_min (by positivity) (by positivity)) (by positivity)

/-- The capped sumset term is at most the size of the sumset. -/
lemma cappedSumset_le_card {D : ℝ} (X Y : Finset G) : cappedSumset D X Y ≤ #(X + Y) :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- The capped sumset term is the smaller of `#(X + Y)` and `D` times the size of the smaller
set. -/
lemma cappedSumset_eq_min {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) :
    cappedSumset D X Y = min (#(X + Y) : ℝ) (D * min (#X : ℝ) #Y) := by
  rw [cappedSumset, mul_min_of_nonneg _ _ hD, min_assoc]

/-- The capped sumset term is at most `D` times the size of the smaller set. -/
private lemma cappedSumset_le_mul_min {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) :
    cappedSumset D X Y ≤ D * min (#X : ℝ) (#Y : ℝ) :=
  (cappedSumset_eq_min hD X Y).trans_le (min_le_right _ _)

/-- The pairs of nonempty subsets of `A` and of `B`, among which the potential is minimised. -/
private def candidates (A B : Finset G) : Finset (Finset G × Finset G) :=
  {p ∈ A.powerset ×ˢ B.powerset | p.1.Nonempty ∧ p.2.Nonempty}

omit [DecidableEq G] [AddCommGroup G] in
/-- A pair belongs to `candidates A B` when it consists of nonempty subsets of `A` and of `B`. -/
private lemma mem_candidates {A B X Y : Finset G} :
    (X, Y) ∈ candidates A B ↔ X ⊆ A ∧ Y ⊆ B ∧ X.Nonempty ∧ Y.Nonempty := by
  simp [candidates, and_assoc]

/-- The potential of a pair of subsets of `A` and `B`: the capped sumset term plus `Λ` times the
number of deleted elements. -/
private def potential (D Λ : ℝ) (A B : Finset G) (p : Finset G × Finset G) : ℝ :=
  cappedSumset D p.1 p.2 + Λ * ((#(A \ p.1) : ℝ) + #(B \ p.2))

/-- The potential of a pair of subsets, with the deleted elements counted by subtraction. -/
private lemma potential_eq {D Λ : ℝ} {A B X Y : Finset G} (hX : X ⊆ A) (hY : Y ⊆ B) :
    potential D Λ A B (X, Y) = cappedSumset D X Y + Λ * (((#A : ℝ) - #X) + ((#B : ℝ) - #Y)) := by
  rw [potential, card_sdiff_of_subset hX, card_sdiff_of_subset hY,
    Nat.cast_sub (card_le_card hX), Nat.cast_sub (card_le_card hY)]

/-- **Penalised minimality.** There is a pair of nonempty subsets `X ⊆ A` and `Y ⊆ B` whose
penalty is at most `D * min #A #B`, and such that passing to nonempty subsets `X' ⊆ X` and
`Y' ⊆ Y` decreases the capped sumset term by at most `Λ` times the number of deleted elements. -/
lemma exists_potential_minimiser (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    {D Λ : ℝ} (hD : 0 < D) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧
      Λ * (((#A : ℝ) - #X) + ((#B : ℝ) - #Y)) ≤ D * min (#A : ℝ) (#B : ℝ) ∧
      ∀ X' ⊆ X, ∀ Y' ⊆ Y, X'.Nonempty → Y'.Nonempty →
        cappedSumset D X Y ≤ cappedSumset D X' Y' + Λ * ((#(X \ X') : ℝ) + #(Y \ Y')) := by
  have hAB := mem_candidates.2 ⟨subset_rfl, subset_rfl, hA, hB⟩
  obtain ⟨⟨X, Y⟩, hXY, hmin⟩ := exists_min_image (candidates A B) (potential D Λ A B) ⟨_, hAB⟩
  obtain ⟨hXA, hYB, hX, hY⟩ := mem_candidates.1 hXY
  refine ⟨X, hXA, Y, hYB, hX, hY, ?_, ?_⟩
  · have := hmin _ hAB
    rw [potential_eq hXA hYB, potential_eq subset_rfl subset_rfl] at this
    linarith [cappedSumset_nonneg hD.le X Y, cappedSumset_le_mul_min hD.le A B]
  · intro X' hX' Y' hY' hX'ne hY'ne
    have := hmin (X', Y') (mem_candidates.2 ⟨hX'.trans hXA, hY'.trans hYB, hX'ne, hY'ne⟩)
    rw [potential_eq hXA hYB, potential_eq (hX'.trans hXA) (hY'.trans hYB)] at this
    rw [cast_card_sdiff hX', cast_card_sdiff hY']
    linarith

end LargeSumsetsFromSubsets
