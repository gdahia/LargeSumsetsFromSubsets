/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Basic.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.Dilation
import LargeSumsetsFromSubsets.CauchyDavenportBound.EndParts
import LargeSumsetsFromSubsets.CauchyDavenportStability

/-!
# The stability step

The stability step of the proof of Theorem 1 of Bollobás, Leader and Tiba. Let `N` be the factor
by which the subsets of Theorem 1 for sets near arithmetic progressions exceed `c₁` and `c₂`. If no
subsets of `A` and `B` with at most `c₁ / N` and `c₂ / N` elements have `#A + #B - 1` sums, then
Theorem 6 places `A` and `B` close to arithmetic progressions with the same common difference, and
Theorem 1 for such sets gives subsets with at most `c₁` and `c₂` elements.

## Main statements

* `exists_subset_card_le_card_add_card_sub_one_le_card_add`: Theorem 1 for `α ≤ 1` and
  `β ≤ 1 / 1024`, with subsets of at most `c₁` and `c₂` elements.
* `exists_subset_card_eq_of_card_le`: such subsets can be enlarged to subsets of exactly `c₁` and
  `c₂` elements.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-- Subsets with at most `c₁` and `c₂` elements whose sumset is large can be enlarged to subsets
with exactly `c₁` and `c₂` elements. -/
lemma exists_subset_card_eq_of_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} {c₁ c₂ k : ℕ} (hc₁ : c₁ ≤ #A) (hc₂ : c₂ ≤ #B)
    (h : ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧ k ≤ #(A' + B')) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ k ≤ #(A' + B') := by
  obtain ⟨A', hA', B', hB', hA'c, hB'c, hk⟩ := h
  obtain ⟨A'', hA'A'', hA'', rfl⟩ := exists_subsuperset_card_eq hA' hA'c hc₁
  obtain ⟨B'', hB'B'', hB'', rfl⟩ := exists_subsuperset_card_eq hB' hB'c hc₂
  exact ⟨A'', hA'', B'', hB'', rfl, rfl, hk.trans (card_le_card (add_subset_add hA'A'' hB'B''))⟩

/-- Dividing `c` by `N ≤ c` loses at most a factor `2`: `c ≤ 2 * N * (c / N)`. -/
lemma le_two_mul_mul_div {c N : ℕ} (hN : 0 < N) (h : N ≤ c) : c ≤ 2 * N * (c / N) := by
  nlinarith [Nat.lt_div_mul_add (a := c) hN, Nat.div_pos h hN]

/-- If `4 * N ^ 2 * C * M ≤ c₁ * c₂` with `c₁, c₂ ≤ M`, `0 < M` and `1 ≤ C`, then the quotients
`q₁ = c₁ / N` and `q₂ = c₂ / N` satisfy `C * M ≤ q₁ * q₂`, `C ≤ q₁` and `C ≤ q₂`, and `c₁` and
`c₂` are at least `2`. -/
lemma mul_le_div_mul_div_of_four_mul_sq_mul_le {c₁ c₂ N : ℕ} {C M : ℝ} (hN : 0 < N) (hC : 1 ≤ C)
    (hM : 0 < M) (hc₁M : c₁ ≤ M) (hc₂M : c₂ ≤ M) (hc : 4 * N ^ 2 * C * M ≤ c₁ * c₂) :
    C * M ≤ (c₁ / N : ℕ) * (c₂ / N : ℕ) ∧ C ≤ (c₁ / N : ℕ) ∧ C ≤ (c₂ / N : ℕ) ∧ 2 ≤ c₁ ∧
      2 ≤ c₂ := by
  have hNC : 1 ≤ (N : ℝ) ^ 2 * C := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by exact_mod_cast hN)) hC
  obtain ⟨h₁, h₂⟩ : 4 * N ^ 2 * C ≤ c₁ ∧ 4 * N ^ 2 * C ≤ c₂ := ⟨by nlinarith, by nlinarith⟩
  have hq := (Nat.cast_le (α := ℝ)).2 (Nat.mul_le_mul
    (le_two_mul_mul_div (c := c₁) hN ((Nat.cast_le (α := ℝ)).1 (by nlinarith)))
    (le_two_mul_mul_div (c := c₂) hN ((Nat.cast_le (α := ℝ)).1 (by nlinarith))))
  push_cast at hq
  have hCM : C * M ≤ (c₁ / N : ℕ) * (c₂ / N : ℕ) :=
    le_of_mul_le_mul_left (a := 4 * (N : ℝ) ^ 2) (by linarith) (by positivity)
  refine ⟨hCM, le_of_mul_le_mul_right (hCM.trans (mul_le_mul_of_nonneg_left
      (((Nat.cast_le (α := ℝ)).2 (Nat.div_le_self c₂ N)).trans hc₂M) (Nat.cast_nonneg _))) hM,
    le_of_mul_le_mul_right ((hCM.trans_eq (mul_comm _ _)).trans (mul_le_mul_of_nonneg_left
      (((Nat.cast_le (α := ℝ)).2 (Nat.div_le_self c₁ N)).trans hc₁M) (Nat.cast_nonneg _))) hM,
    (Nat.cast_le (α := ℝ)).1 (by push_cast; linarith),
    (Nat.cast_le (α := ℝ)).1 (by push_cast; linarith)⟩

variable {p : ℕ}

/-- **Theorem 6** of Bollobás, Leader and Tiba at the threshold `#A + #B - 1`. There is `c` such
that if no subsets of `A` and `B` with at most `c₁` and `c₂` elements have `#A + #B - 1` sums, then
`A` and `B` are within `γ * min #A #B` of arithmetic progressions with the same nonzero common
difference. -/
lemma exists_arithProg_of_forall_card_add_lt_card_add_sub_one {α β γ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (c₁ c₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      2 ≤ #A → 2 ≤ #B → α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      (∀ A' ⊆ A, ∀ B' ⊆ B, #A' ≤ c₁ → #B' ≤ c₂ → #(A' + B') < #A + #B - 1) →
      ∃ a b d : ZMod p, d ≠ 0 ∧ ∃ m n : ℕ, #(A ∆ arithProg a d m) ≤ γ * min (#A : ℝ) #B ∧
        #(B ∆ arithProg b d n) ≤ γ * min (#A : ℝ) #B := by
  obtain ⟨ε, hε, h₆⟩ := exists_arithProg_card_symmDiff_le_of_expect_card_add_le hβ hγ
  obtain ⟨c, hc⟩ := h₆ α hα
  refine ⟨c, ?_⟩
  intro p hp A B c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc hA hB hAB hBA hABp hlt
  have hE := expect_card_add_le_of_forall_card_add_lt hlt
  rw [min_eq_left hc₁A, min_eq_left hc₂B, Nat.cast_sub (by grind)] at hE
  push_cast at hE
  exact hc p hp A B c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc hA hB hAB hBA hABp
    (le_add_of_le_of_nonneg (hE.trans (by linarith)) (by positivity))

/-- **Theorem 1** of Bollobás, Leader and Tiba for `α ≤ 1` and `β ≤ 1 / 1024`, with subsets of at
most `c₁` and `c₂` elements. -/
lemma exists_subset_card_le_card_add_card_sub_one_le_card_add {α β : ℝ} (hα : 0 < α)
    (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 1024) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ, hγ, K, hK⟩ :=
    exists_card_add_card_sub_one_le_card_add_of_near_arithProg hα hα₁ hβ hβ₁
  obtain ⟨c₆, hc₆⟩ := exists_arithProg_of_forall_card_add_lt_card_add_sub_one hα hβ hγ
  obtain ⟨C, hC, hKC, hc₆C⟩ : ∃ C : ℝ, 1 ≤ C ∧ K ≤ C ∧ c₆ ≤ C :=
    ⟨max (max K c₆) 1, by grind, by grind, by grind⟩
  have hN : 0 < 3 + 2 * ⌈192 / (α * β)⌉₊ := by positivity
  generalize 3 + 2 * ⌈192 / (α * β)⌉₊ = N at hK hN
  refine ⟨4 * N ^ 2 * C, by positivity, ?_⟩
  intro p hp A B hA hB hAB hBA hABp c₁ c₂ hc₁A hc₂B hc
  have hmax : 0 < max (#A : ℝ) #B := lt_max_of_lt_left (by exact_mod_cast hA.card_pos)
  obtain ⟨hCq, hCq₁, hCq₂, h2₁, h2₂⟩ := mul_le_div_mul_div_of_four_mul_sq_mul_le hN hC hmax
    (le_max_of_le_left (mod_cast hc₁A)) (le_max_of_le_right (mod_cast hc₂B)) hc
  by_cases hsmall : ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ / N ∧ #B' ≤ c₂ / N ∧ #A + #B - 1 ≤ #(A' + B')
  · obtain ⟨A', hA', B', hB', h₁, h₂, h₃⟩ := hsmall
    exact ⟨A', hA', B', hB', h₁.trans (Nat.div_le_self _ _), h₂.trans (Nat.div_le_self _ _), h₃⟩
  push Not at hsmall
  obtain ⟨a, b, d, hd, m, n, hAP, hBQ⟩ := hc₆ p hp A B _ _ (Nat.one_le_cast.1 (hC.trans hCq₁))
    ((Nat.div_le_self _ _).trans hc₁A) (Nat.one_le_cast.1 (hC.trans hCq₂))
    ((Nat.div_le_self _ _).trans hc₂B) ((mul_le_mul_of_nonneg_right hc₆C hmax.le).trans hCq)
    (h2₁.trans hc₁A) (h2₂.trans hc₂B) hAB hBA hABp hsmall
  obtain ⟨A', hA', B', hB', h₁, h₂, h₃⟩ := hK p hp A B hA hB hAB hBA hABp a b d m n hd hAP hBQ
    _ _ ((Nat.div_le_self _ _).trans hc₁A) ((Nat.div_le_self _ _).trans hc₂B) (hKC.trans hCq₁)
    (hKC.trans hCq₂) ((mul_le_mul_of_nonneg_right hKC hmax.le).trans hCq)
  exact ⟨A', hA', B', hB', h₁.trans (Nat.mul_div_le _ _), h₂.trans (Nat.mul_div_le _ _), h₃⟩

end LargeSumsetsFromSubsets
