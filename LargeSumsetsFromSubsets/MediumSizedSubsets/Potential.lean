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
# A capped sumset size with a deletion penalty

Let `A` and `B` be finite nonempty subsets of an abelian group and let `D ≥ 0` and `Λ` be reals.
Among the pairs of nonempty subsets `X ⊆ A` and `Y ⊆ B` we minimize the potential
`min #(X + Y) (D * min #X #Y) + Λ * (#(A \ X) + #(B \ Y))`. The potential of `(A, B)` is at most
`D * min #A #B`, so a minimizer deletes few elements. Minimality says that passing to nonempty
subsets `X' ⊆ X` and `Y' ⊆ Y` decreases the capped sumset size `min #(X + Y) (D * min #X #Y)` by at
most the penalty `Λ * (#(X \ X') + #(Y \ Y'))` of the deleted elements.

## Main statements

* `LargeSumsetsFromSubsets.MediumSizedSubsets.exists_subset_min_card_add_le_min_card_add_add`: the
  minimizing pair and its two properties.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets.MediumSizedSubsets

open Finset

open scoped Pointwise

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The pairs of nonempty subsets of `A` and of `B`, among which the potential is minimized. -/
private def candidates (A B : Finset G) : Finset (Finset G × Finset G) :=
  {X ∈ A.powerset | X.Nonempty} ×ˢ {Y ∈ B.powerset | Y.Nonempty}

omit [DecidableEq G] [AddCommGroup G] in
/-- A pair belongs to `candidates A B` when it consists of nonempty subsets of `A` and of `B`. -/
private lemma mem_candidates {A B X Y : Finset G} :
    (X, Y) ∈ candidates A B ↔ X ⊆ A ∧ X.Nonempty ∧ Y ⊆ B ∧ Y.Nonempty := by
  simp [candidates, and_assoc]

/-- The potential of a pair of subsets `X ⊆ A` and `Y ⊆ B`: the capped sumset size plus `Λ` times
the number of deleted elements. -/
private def potential (D Λ : ℝ) (A B X Y : Finset G) : ℝ :=
  min (#(X + Y) : ℝ) (D * min (#X : ℝ) #Y) + Λ * (#A - #X + (#B - #Y))

/-- **Penalized minimality.** There is a pair of nonempty subsets `X ⊆ A` and `Y ⊆ B` whose penalty
is at most `D * min #A #B`, and such that passing to nonempty subsets `X' ⊆ X` and `Y' ⊆ Y`
decreases `min #(X + Y) (D * min #X #Y)` by at most `Λ` times the number of deleted elements. -/
lemma exists_subset_min_card_add_le_min_card_add_add {A B : Finset G} (hA : A.Nonempty)
    (hB : B.Nonempty) {D : ℝ} (hD : 0 ≤ D) (Λ : ℝ) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧ Λ * (#(A \ X) + #(B \ Y)) ≤ D * min (#A : ℝ) #B ∧
      ∀ X' ⊆ X, ∀ Y' ⊆ Y, X'.Nonempty → Y'.Nonempty →
        min (#(X + Y) : ℝ) (D * min (#X : ℝ) #Y) ≤
          min (#(X' + Y') : ℝ) (D * min (#X' : ℝ) #Y') + Λ * (#(X \ X') + #(Y \ Y')) := by
  have hAB := mem_candidates.2 ⟨subset_rfl, hA, subset_rfl, hB⟩
  obtain ⟨⟨X, Y⟩, hXY, hmin⟩ :=
    exists_min_image (candidates A B) (fun (X, Y) ↦ potential D Λ A B X Y) ⟨_, hAB⟩
  simp only [potential, Prod.forall] at hmin
  obtain ⟨hXA, hX, hYB, hY⟩ := mem_candidates.1 hXY
  refine ⟨X, hXA, Y, hYB, hX, hY, ?_, ?_⟩
  · rw [cast_card_sdiff hXA, cast_card_sdiff hYB]
    linarith [hmin A B hAB, min_le_right (#(A + B) : ℝ) (D * min (#A : ℝ) #B),
      (by positivity : 0 ≤ min (#(X + Y) : ℝ) (D * min (#X : ℝ) #Y))]
  · intro X' hX' Y' hY' hX'ne hY'ne
    rw [cast_card_sdiff hX', cast_card_sdiff hY']
    linarith [hmin X' Y' (mem_candidates.2 ⟨hX'.trans hXA, hX'ne, hY'.trans hYB, hY'ne⟩)]

end LargeSumsetsFromSubsets.MediumSizedSubsets
