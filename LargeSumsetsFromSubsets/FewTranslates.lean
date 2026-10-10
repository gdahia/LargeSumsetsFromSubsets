/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Large sumsets from few translates of a set with large doubling

Theorem 1.1 of Fox, Luo, Pham and Zhou, *Small subsets with large sumset: beyond the
Cauchy–Davenport bound*, with the constant `1 / 14` of their proof: a finite nonempty subset `A`
of an abelian group with `|A + A| = κ * |A|` has, for each `s ≥ 1`, a subset `T` of at most `s`
elements with `|A + T| ≥ min (κ ^ (1 / 3)) s * |A| / 14`.
-/

public section

open Finset
open scoped Pointwise

namespace LargeSumsetsFromSubsets

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A C T : Finset G} {x y : G}

private def walks (A C : Finset G) (x y : G) : Finset (G × G) :=
  {p ∈ A ×ˢ A | p.1 + x ∈ C ∧ p.1 + p.2 ∈ C ∧ p.2 + y ∈ C}

private lemma card_walks_le_card_fiber (A C : Finset G) (x y : G) :
    #(walks A C x y) ≤ #{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = x + y} := by
  refine card_le_card_of_injOn (fun p ↦ (p.1 + x, p.1 + p.2, p.2 + y)) (fun p hp ↦ ?_)
    fun p _ q _ h ↦ ?_
  · obtain ⟨-, h₁, h₂, h₃⟩ := mem_filter.1 hp
    simpa [h₁, h₂, h₃] using by abel
  · simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2.2

private lemma sum_card_fiber_le (A C : Finset G) :
    ∑ z ∈ A + A, #{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = z} ≤ #C ^ 3 := by
  rw [sum_card_fiberwise_eq_card_filter]
  exact (card_filter_le _ _).trans_eq (by simp [pow_succ, mul_assoc])

private lemma card_add_mul_le_card_pow {w : ℝ}
    (h : ∀ x ∈ A, ∀ y ∈ A, w ≤ #(walks A C x y)) : #(A + A) * w ≤ (#C : ℝ) ^ 3 :=
  calc #(A + A) * w
    _ = ∑ _z ∈ A + A, w := by simp
    _ ≤ ∑ z ∈ A + A, (#{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = z} : ℝ) := by
      refine sum_le_sum fun z hz ↦ ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
      exact (h x hx y hy).trans (mod_cast card_walks_le_card_fiber A C x y)
    _ ≤ (#C : ℝ) ^ 3 := mod_cast sum_card_fiber_le A C

private lemma card_filter_add_notMem_le {m : ℕ} (hm : ∀ b ∈ A, #{a ∈ A | a + b ∉ C} ≤ m) :
    #{p ∈ A ×ˢ A | p.1 + p.2 ∉ C} ≤ #A * m := by
  simp only [card_filter, sum_product_right]
  simpa only [card_filter, smul_eq_mul] using sum_le_card_nsmul _ _ _ hm

private lemma product_subset_walks_union (A C : Finset G) (x y : G) :
    A ×ˢ A ⊆ walks A C x y ∪ ({a ∈ A | a + x ∉ C} ×ˢ A ∪
      ({p ∈ A ×ˢ A | p.1 + p.2 ∉ C} ∪ A ×ˢ {a ∈ A | a + y ∉ C})) := by
  intro p hp
  have := mem_product.1 hp
  simp only [walks, mem_union, mem_filter, mem_product]
  tauto

private lemma card_mul_card_le_card_walks_add (hx : x ∈ A) (hy : y ∈ A) {m : ℕ}
    (hm : ∀ b ∈ A, #{a ∈ A | a + b ∉ C} ≤ m) :
    #A * #A ≤ #(walks A C x y) + 3 * (#A * m) := by
  have h := card_le_card (product_subset_walks_union A C x y)
  have h₁ := Nat.mul_le_mul_right #A (hm x hx)
  have h₂ := card_filter_add_notMem_le hm
  have h₃ := Nat.mul_le_mul_left #A (hm y hy)
  rw [card_product] at h
  grw [card_union_le, card_union_le, card_union_le, card_product, card_product] at h
  linarith

private lemma card_pow_three_lt (hA : A.Nonempty)
    (hC : (#C : ℝ) < 1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) :
    (#C : ℝ) ^ 3 < (1 / 14) ^ 3 * (#(A + A) * (#A * #A)) := by
  have hn : (0 : ℝ) < #A := mod_cast hA.card_pos
  have hκ : (0 : ℝ) ≤ #(A + A) / #A := by positivity
  have e : (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) ^ 3 = #(A + A) / #A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ]
    norm_num
  have h := pow_lt_pow_left₀ hC (by positivity) three_ne_zero
  rw [mul_pow, mul_pow, e] at h
  exact h.trans_eq (by field_simp)

private lemma exists_card_filter_add_notMem_ge (hA : A.Nonempty)
    (hC : (#C : ℝ) < 1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) :
    ∃ b ∈ A, 1 / 14 * (#A : ℝ) ≤ #{a ∈ A | a + b ∉ C} := by
  by_contra! h
  have hn : (0 : ℝ) < #A := mod_cast hA.card_pos
  have hK : (0 : ℝ) < #(A + A) := mod_cast (hA.add hA).card_pos
  have hm : (⌊1 / 14 * (#A : ℝ)⌋₊ : ℝ) ≤ 1 / 14 * #A := Nat.floor_le (by positivity)
  have hw : ∀ x ∈ A, ∀ y ∈ A, (#A * #A - 3 * (#A * ⌊1 / 14 * (#A : ℝ)⌋₊) : ℝ) ≤
      #(walks A C x y) := fun x hx y hy ↦ by
    have := card_mul_card_le_card_walks_add hx hy fun b hb ↦ Nat.le_floor (h b hb).le
    rw [sub_le_iff_le_add]
    exact_mod_cast this
  have h₁ := card_add_mul_le_card_pow hw
  have h₂ := card_pow_three_lt hA hC
  nlinarith [mul_nonneg (mul_pos hK hn).le (sub_nonneg.2 hm), mul_pos hK (mul_pos hn hn)]

private lemma card_add_insert (A T : Finset G) (b : G) :
    #(A + insert b T) = #(A + T) + #{a ∈ A | a + b ∉ A + T} := by
  have h : (A + {b}) \ (A + T) = {a ∈ A | a + b ∉ A + T}.image (· + b) := by
    have hb : A + {b} = A.image (· + b) := image₂_singleton_right
    rw [hb, sdiff_eq_filter, filter_image]
  rw [insert_eq, add_union, ← card_sdiff_add_card, h,
    card_image_of_injective _ (add_left_injective b), add_comm]

private lemma exists_subset_card_add_ge_succ (hA : A.Nonempty) {s : ℕ} (hT : T ⊆ A)
    (hTs : #T ≤ s)
    (h : 1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T)) :
    ∃ T ⊆ A, #T ≤ s + 1 ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) (s + 1 : ℕ) * #A ≤ #(A + T) := by
  obtain hC | hC := le_or_gt (1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) #(A + T)
  · refine ⟨T, hT, by lia, le_trans ?_ hC⟩
    gcongr
    exact min_le_left _ _
  obtain ⟨b, hb, hbad⟩ := exists_card_filter_add_notMem_ge hA hC
  refine ⟨insert b T, insert_subset hb hT, (card_insert_le _ _).trans (by lia), ?_⟩
  have hmin : min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) (s + 1) ≤
      min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s + 1 := by
    rw [← min_add_add_right]
    exact min_le_min (by linarith) le_rfl
  rw [card_add_insert]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg' (n := #A) (α := ℝ))]

/-- **Fox–Luo–Pham–Zhou**: some `T ⊆ A` with at most `s` elements has
`|A + T| ≥ min (κ ^ (1 / 3)) s * |A| / 14`, where `κ = |A + A| / |A|`. -/
theorem exists_subset_card_add_ge {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    (hA : A.Nonempty) {s : ℕ} (hs : 1 ≤ s) :
    ∃ T ⊆ A, #T ≤ s ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T) := by
  induction s, hs using Nat.le_induction with
  | base =>
    obtain ⟨a, ha⟩ := hA
    refine ⟨{a}, singleton_subset_iff.2 ha, by simp, ?_⟩
    rw [card_add_singleton]
    have := min_le_right (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) ((1 : ℕ) : ℝ)
    nlinarith [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg' (n := #A) (α := ℝ))]
  | succ s _ ih =>
    obtain ⟨T, hT, hTs, h⟩ := ih
    exact exists_subset_card_add_ge_succ hA hT hTs h

end LargeSumsetsFromSubsets
