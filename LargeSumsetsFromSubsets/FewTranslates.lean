/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Large sumsets from few translates

This file proves Theorem 1.1 of Fox, Luo, Pham and Zhou, *Small subsets with large sumset: beyond
the Cauchy–Davenport bound*, with the constant $1/14$ of their proof. A finite nonempty subset $A$
of an abelian group with $|A + A| = \kappa |A|$ has, for each $s \ge 1$, a subset $T$ with at
most $s$ elements and $|A + T| \ge \min(\kappa^{1/3}, s) |A| / 14$.

This is `LargeSumsetsFromSubsets.FewTranslates.exists_subset_card_le_mul_le_card_add`.

The proof is by induction on $s$. Let $C = A + T$ with $|C| < \kappa^{1/3} |A| / 14$. If every
$b \in A$ had fewer than $|A| / 14$ elements $a \in A$ with $a + b \notin C$, then for all
$x, y \in A$ most pairs $(a, a')$ of $A \times A$ would have $a + x$, $a + a'$ and $a' + y$ in
$C$. Since $x + y = (a + x) - (a + a') + (a' + y)$, counting triples of $C$ would give
$|A + A| \cdot \frac{11}{14} |A|^2 \le |C|^3$, which is false. So some $b \in A$ adds at least
$|A| / 14$ elements to $A + T$.
-/

public section

open Finset
open scoped Pointwise

namespace LargeSumsetsFromSubsets.FewTranslates

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A C T : Finset G} {x y : G}

/-- The pairs `(a, a')` of `A ×ˢ A` for which `a + x`, `a + a'` and `a' + y` lie in `C`. -/
private def walks (A C : Finset G) (x y : G) : Finset (G × G) :=
  {p ∈ A ×ˢ A | p.1 + x ∈ C ∧ p.1 + p.2 ∈ C ∧ p.2 + y ∈ C}

/-- A pair of `walks A C x y` gives a triple of `C` with alternating sum `x + y`. -/
private lemma card_walks_le_card_filter (A C : Finset G) (x y : G) :
    #(walks A C x y) ≤ #{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = x + y} := by
  refine card_le_card_of_injOn (fun p ↦ (p.1 + x, p.1 + p.2, p.2 + y)) (fun p hp ↦ ?_)
    fun p _ q _ h ↦ ?_
  · obtain ⟨-, h₁, h₂, h₃⟩ := mem_filter.1 hp
    simpa [h₁, h₂, h₃] using by abel
  · simp only [Prod.mk.injEq, add_left_inj] at h
    grind

/-- Counting the triples of `C` by their alternating sum. -/
private lemma sum_card_filter_le (A C : Finset G) :
    ∑ z ∈ A + A, #{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = z} ≤ #C ^ 3 := by
  rw [sum_card_fiberwise_eq_card_filter]
  exact (card_filter_le _ _).trans_eq (by simp [pow_succ, mul_assoc])

/-- If every pair `x, y ∈ A` has at least `w` walks, then `#(A + A) * w ≤ #C ^ 3`. -/
private lemma card_add_mul_le_card_pow {w : ℝ}
    (h : ∀ x ∈ A, ∀ y ∈ A, w ≤ #(walks A C x y)) : #(A + A) * w ≤ (#C : ℝ) ^ 3 := by
  rw [← nsmul_eq_mul, ← sum_const]
  refine (sum_le_sum ?_).trans (b := ∑ z ∈ A + A,
    ((#{t ∈ C ×ˢ C ×ˢ C | t.1 - t.2.1 + t.2.2 = z} : ℝ)))
    (mod_cast sum_card_filter_le A C)
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
  exact (h x hx y hy).trans (mod_cast card_walks_le_card_filter A C x y)

/-- Few pairs of `A ×ˢ A` have their sum outside `C` if each translate `A + b` misses `C` in
few points. -/
private lemma card_filter_add_notMem_le {m : ℕ} (hm : ∀ b ∈ A, #{a ∈ A | a + b ∉ C} ≤ m) :
    #{p ∈ A ×ˢ A | p.1 + p.2 ∉ C} ≤ #A * m := by
  simp only [card_filter, sum_product_right]
  simpa only [card_filter, smul_eq_mul] using sum_le_card_nsmul _ _ _ hm

/-- A pair of `A ×ˢ A` that is not a walk misses `C` at one of its three sums. -/
private lemma product_subset_walks_union (A C : Finset G) (x y : G) :
    A ×ˢ A ⊆ walks A C x y ∪ ({a ∈ A | a + x ∉ C} ×ˢ A ∪
      ({p ∈ A ×ˢ A | p.1 + p.2 ∉ C} ∪ A ×ˢ {a ∈ A | a + y ∉ C})) := by
  rintro ⟨a, a'⟩ h
  simp only [walks, mem_union, mem_filter, mem_product] at h ⊢
  tauto

/-- If each translate `A + b` misses `C` in at most `m` points, then any `x, y ∈ A` have at
least `#A * #A - 3 * (#A * m)` walks. -/
private lemma card_mul_card_le_card_walks_add (hx : x ∈ A) (hy : y ∈ A) {m : ℕ}
    (hm : ∀ b ∈ A, #{a ∈ A | a + b ∉ C} ≤ m) :
    #A * #A ≤ #(walks A C x y) + 3 * (#A * m) := by
  have h := card_le_card (product_subset_walks_union A C x y)
  grw [card_product, card_union_le, card_union_le, card_union_le, card_product, card_product] at h
  linarith [Nat.mul_le_mul_right #A (hm x hx), card_filter_add_notMem_le hm,
    Nat.mul_le_mul_left #A (hm y hy)]

/-- If each translate `A + b` misses `C` in at most `m` points, then
`#(A + A) * (#A * #A - 3 * (#A * m)) ≤ #C ^ 3`. -/
private lemma card_add_mul_sub_le_card_pow {m : ℕ} (hm : ∀ b ∈ A, #{a ∈ A | a + b ∉ C} ≤ m) :
    #(A + A) * (#A * #A - 3 * (#A * m) : ℝ) ≤ (#C : ℝ) ^ 3 := by
  apply card_add_mul_le_card_pow
  intro x hx y hy
  rw [sub_le_iff_le_add]
  exact_mod_cast card_mul_card_le_card_walks_add hx hy hm

/-- The cube of the bound `#C < κ ^ (1 / 3) * #A / 14`. -/
private lemma card_pow_three_lt (hA : A.Nonempty)
    (hC : (#C : ℝ) < 1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) :
    (#C : ℝ) ^ 3 < (1 / 14) ^ 3 * (#(A + A) * (#A * #A)) := by
  have e : (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) ^ 3 = #(A + A) / #A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h := pow_lt_pow_left₀ hC (by positivity) three_ne_zero
  rw [mul_pow, mul_pow, e] at h
  exact h.trans_eq (by field_simp [hA.card_pos.ne'])

/-- If `#(A + T) < κ ^ (1 / 3) * #A / 14`, some translate `A + b` with `b ∈ A` misses `A + T`
in at least `#A / 14` points. -/
private lemma exists_card_filter_add_notMem_ge (hA : A.Nonempty)
    (hC : (#C : ℝ) < 1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) :
    ∃ b ∈ A, 1 / 14 * (#A : ℝ) ≤ #{a ∈ A | a + b ∉ C} := by
  by_contra! h
  have hn : (0 : ℝ) < #A := mod_cast hA.card_pos
  have hK : (0 : ℝ) < #(A + A) := mod_cast (hA.add hA).card_pos
  nlinarith [card_pow_three_lt hA hC,
    card_add_mul_sub_le_card_pow fun b hb ↦ Nat.le_floor (h b hb).le, mul_pos hK (mul_pos hn hn),
    mul_nonneg (mul_pos hK hn).le
      (sub_nonneg.2 (Nat.floor_le (by positivity) : (⌊1 / 14 * (#A : ℝ)⌋₊ : ℝ) ≤ 1 / 14 * #A))]

/-- Adding `b` to `T` adds to `A + T` the points `a + b` with `a ∈ A` outside `A + T`. -/
private lemma card_add_insert (A T : Finset G) (b : G) :
    #(A + insert b T) = #(A + T) + #{a ∈ A | a + b ∉ A + T} := by
  have h : (A + {b}) \ (A + T) = {a ∈ A | a + b ∉ A + T}.image (· + b) := by
    have hb : A + {b} = A.image (· + b) := image₂_singleton_right
    rw [hb, sdiff_eq_filter, filter_image]
  rw [insert_eq, add_union, ← card_sdiff_add_card, h,
    card_image_of_injective _ (add_left_injective b), add_comm]

/-- The induction step of `exists_subset_card_le_mul_le_card_add`. -/
private lemma exists_subset_card_le_succ_mul_le_card_add (hA : A.Nonempty) {s : ℕ} (hT : T ⊆ A)
    (hTs : #T ≤ s)
    (h : 1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T)) :
    ∃ T ⊆ A, #T ≤ s + 1 ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) (s + 1 : ℕ) * #A ≤ #(A + T) := by
  obtain hC | hC := le_or_gt (1 / 14 * ((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ) * #A) #(A + T)
  · refine ⟨T, hT, by grind, le_trans ?_ hC⟩
    gcongr
    exact min_le_left _ _
  obtain ⟨b, hb, hbad⟩ := exists_card_filter_add_notMem_ge hA hC
  refine ⟨insert b T, insert_subset hb hT, (card_insert_le _ _).trans (by grind), ?_⟩
  have hmin : min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) (s + 1) ≤
      min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s + 1 := by
    rw [← min_add_add_right]
    exact min_le_min (by linarith) le_rfl
  rw [card_add_insert]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg' (n := #A) (α := ℝ))]

/-- **Large sumsets from few translates** (Fox, Luo, Pham and Zhou, Theorem 1.1). A finite
nonempty subset $A$ of an abelian group has, for each $s \ge 1$, a subset $T$ with at most $s$
elements and $|A + T| \ge \min(\kappa^{1/3}, s) |A| / 14$, where $\kappa = |A + A| / |A|$. -/
theorem exists_subset_card_le_mul_le_card_add (hA : A.Nonempty) {s : ℕ} (hs : 1 ≤ s) :
    ∃ T ⊆ A, #T ≤ s ∧
      1 / 14 * min (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ)) s * #A ≤ #(A + T) := by
  induction s, hs using Nat.le_induction with
  | base =>
    obtain ⟨a, ha⟩ := hA
    refine ⟨{a}, singleton_subset_iff.2 ha, by simp, ?_⟩
    rw [card_add_singleton]
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right (((#(A + A) : ℝ) / #A) ^ (1 / 3 : ℝ))
      ((1 : ℕ) : ℝ)) (Nat.cast_nonneg' (n := #A) (α := ℝ))]
  | succ s _ ih =>
    obtain ⟨T, hT, hTs, h⟩ := ih
    exact exists_subset_card_le_succ_mul_le_card_add hA hT hTs h

end LargeSumsetsFromSubsets.FewTranslates
