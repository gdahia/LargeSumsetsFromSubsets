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
# The penalized minimality step

Among the pairs of nonempty subsets `X ⊆ A` and `Y ⊆ B` we minimize the potential
`min (min #(X + Y) (D * #X)) (D * #Y) + Λ * (#(A \ X) + #(B \ Y))`. The minimizer is large, because
the penalty term of `(A, B)` vanishes, and it is robust: passing to subsets can only decrease the
capped sumset term by less than the penalty incurred.

## Main definitions

* `LargeSumsetsFromSubsets.cappedSumset D X Y`: the capped sumset term
  `min (min #(X + Y) (D * #X)) (D * #Y)`.

## Main statements

* `LargeSumsetsFromSubsets.exists_subset_cappedSumset_le_cappedSumset_add`: the minimizing pair and
  its two properties. It is the only interface to the potential used later.
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
  min_le_of_left_le (min_le_left _ _)

/-- The capped sumset term is the smaller of `#(X + Y)` and `D` times the size of the smaller
set. -/
lemma cappedSumset_eq_min {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) :
    cappedSumset D X Y = min (#(X + Y) : ℝ) (D * min (#X : ℝ) #Y) := by
  rw [cappedSumset, mul_min_of_nonneg _ _ hD, min_assoc]

/-- The capped sumset term is at most `D` times the size of the smaller set. -/
private lemma cappedSumset_le_mul_min {D : ℝ} (hD : 0 ≤ D) (X Y : Finset G) :
    cappedSumset D X Y ≤ D * min (#X : ℝ) #Y :=
  (cappedSumset_eq_min hD X Y).trans_le (min_le_right _ _)

/-- The pairs of nonempty subsets of `A` and of `B`, among which the potential is minimized. -/
private def candidates (A B : Finset G) : Finset (Finset G × Finset G) :=
  {X ∈ A.powerset | X.Nonempty} ×ˢ {Y ∈ B.powerset | Y.Nonempty}

omit [DecidableEq G] [AddCommGroup G] in
/-- A pair belongs to `candidates A B` when it consists of nonempty subsets of `A` and of `B`. -/
private lemma mem_candidates {A B X Y : Finset G} :
    (X, Y) ∈ candidates A B ↔ X ⊆ A ∧ X.Nonempty ∧ Y ⊆ B ∧ Y.Nonempty := by
  simp [candidates, and_assoc]

/-- The potential of a pair of subsets `X ⊆ A` and `Y ⊆ B`: the capped sumset term plus `Λ` times
the number of deleted elements. -/
private def potential (D Λ : ℝ) (A B X Y : Finset G) : ℝ :=
  cappedSumset D X Y + Λ * (#A - #X + (#B - #Y))

/-- **Penalized minimality.** There is a pair of nonempty subsets `X ⊆ A` and `Y ⊆ B` whose penalty
is at most `D * min #A #B`, and such that passing to nonempty subsets `X' ⊆ X` and `Y' ⊆ Y`
decreases the capped sumset term by at most `Λ` times the number of deleted elements. -/
lemma exists_subset_cappedSumset_le_cappedSumset_add {A B : Finset G} (hA : A.Nonempty)
    (hB : B.Nonempty) {D Λ : ℝ} (hD : 0 < D) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧
      Λ * (#(A \ X) + #(B \ Y)) ≤ D * min (#A : ℝ) #B ∧
      ∀ X' ⊆ X, ∀ Y' ⊆ Y, X'.Nonempty → Y'.Nonempty →
        cappedSumset D X Y ≤ cappedSumset D X' Y' + Λ * (#(X \ X') + #(Y \ Y')) := by
  have hAB := mem_candidates.2 ⟨subset_rfl, hA, subset_rfl, hB⟩
  obtain ⟨⟨X, Y⟩, hXY, hmin⟩ :=
    exists_min_image (candidates A B) (fun (X, Y) ↦ potential D Λ A B X Y) ⟨_, hAB⟩
  simp only [potential, Prod.forall] at hmin
  obtain ⟨hXA, hX, hYB, hY⟩ := mem_candidates.1 hXY
  refine ⟨X, hXA, Y, hYB, hX, hY, ?_, ?_⟩
  · rw [cast_card_sdiff hXA, cast_card_sdiff hYB]
    linarith [hmin A B hAB, cappedSumset_nonneg hD.le X Y, cappedSumset_le_mul_min hD.le A B]
  · intro X' hX' Y' hY' hX'ne hY'ne
    rw [cast_card_sdiff hX', cast_card_sdiff hY']
    linarith [hmin X' Y' (mem_candidates.2 ⟨hX'.trans hXA, hX'ne, hY'.trans hYB, hY'ne⟩)]

end LargeSumsetsFromSubsets
