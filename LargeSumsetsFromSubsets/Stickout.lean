/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Sums that stick out of a set

Lemma 10 and Corollary 11 of Bollobás, Leader and Tiba: if `Y` is much larger than `X` and than
a set `W`, then a few elements of `X` and of `Y` already have `2 * #X` sums outside `W`. Here the
lemma is proved greedily, adding at each step the element of `Y` with the most new sums, under
the hypotheses `2 * #W + 4 * #X ≤ #Y`, `cY ≤ #Y` and `16 * #X ≤ min cX #X * cY`. The paper asks
for `8 * #X, 8 * #W ≤ #Y < p / 2` instead, and samples at random.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

/-- Adding `B` to `A` adds the points of `B` outside `W ∪ A` to the points of `A` outside `W`. -/
lemma card_union_sdiff {α : Type*} [DecidableEq α] (A B W : Finset α) :
    #((A ∪ B) \ W) = #(A \ W) + #(B \ (W ∪ A)) := by
  rw [← card_union_of_disjoint (disjoint_left.2 (by simp_all))]
  congr 1
  ext
  simp only [mem_union, mem_sdiff]
  tauto

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- Counting the pairs `(x, y) ∈ X × Y` with `x + y ∉ V` along `y`: the translates `X + {y}`,
`y ∈ Y`, have together at least `#X * (#Y - #V)` points outside `V`. -/
lemma card_mul_card_le_sum_card_add_singleton_sdiff (X Y V : Finset G) :
    #X * #Y ≤ ∑ y ∈ Y, #((X + {y}) \ V) + #X * #V := by
  have hsum : ∑ y ∈ Y, #((X + {y}) \ V) = ∑ x ∈ X, #{y ∈ Y | x + y ∉ V} := by
    simp_rw [card_filter]
    rw [sum_comm]
    congr with y
    rw [← card_filter, ← card_image_of_injective {x ∈ X | x + y ∉ V} (add_left_injective y)]
    congr 1
    ext z
    simp [mem_add, ← eq_sub_iff_add_eq, sub_eq_add_neg]
  rw [hsum, ← sum_const_nat (fun _ _ ↦ rfl), ← sum_const_nat (fun _ _ ↦ rfl), ← sum_add_distrib]
  gcongr with x
  rw [← card_filter_add_card_filter_not (fun y ↦ x + y ∈ V), add_comm]
  exact Nat.add_le_add_left (card_le_card_of_injOn (x + ·) (by intro; simp_all)
    (add_right_injective x).injOn) _

/-- If `2 * #V ≤ #Y` and `Y` is nonempty, some translate `X + {y}`, `y ∈ Y`, has at least
`#X / 2` points outside `V`. -/
lemma exists_card_le_two_mul_card_add_singleton_sdiff {X Y V : Finset G} (hY : Y.Nonempty)
    (hV : 2 * #V ≤ #Y) : ∃ y ∈ Y, #X ≤ 2 * #((X + {y}) \ V) := by
  refine exists_le_of_sum_le hY ?_
  rw [sum_const_nat (fun _ _ ↦ rfl), ← mul_sum]
  grind [card_mul_card_le_sum_card_add_singleton_sdiff X Y V, Nat.mul_le_mul_left #X hV]

/-- The greedy step of Lemma 10, iterated `j ≤ #Y` times: if `2 * #W + 2 * k ≤ #Y`, then at most
`j` elements of `Y` give at least `min (2 * k) (j * #X) / 2` sums with `X` outside `W`. -/
lemma exists_subset_min_le_two_mul_card_add_sdiff (X Y W : Finset G) {k j : ℕ} (hj : j ≤ #Y)
    (hY : 2 * #W + 2 * k ≤ #Y) :
    ∃ Y' ⊆ Y, #Y' ≤ j ∧ min (2 * k) (j * #X) ≤ 2 * #((X + Y') \ W) := by
  induction j with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨Y', hY'Y, hY'j, hY'⟩ := ih (by grind)
    by_cases hk : 2 * k ≤ 2 * #((X + Y') \ W)
    · exact ⟨Y', hY'Y, by grind, by grind⟩
    obtain ⟨y, hy, hXy⟩ := exists_card_le_two_mul_card_add_singleton_sdiff (X := X)
      (card_pos.1 (by grind)) (by grind [card_union_le, union_sdiff_self_eq_union] :
        2 * #(W ∪ (X + Y')) ≤ #Y)
    refine ⟨Y' ∪ {y}, union_subset hY'Y (by simpa), by grind [card_union_le, card_singleton], ?_⟩
    rw [add_union, card_union_sdiff]
    grind

/-- **Lemma 10** of Bollobás, Leader and Tiba. If `cY ≤ #Y`, `16 * #X ≤ min cX #X * cY` and
`2 * #W + 4 * #X ≤ #Y`, then some `X' ⊆ X` and `Y' ⊆ Y` with at most `cX` and `cY` elements have
at least `2 * #X` sums outside `W`. -/
lemma exists_subset_two_mul_card_le_card_add_sdiff {X Y W : Finset G} {cX cY : ℕ}
    (hcY : cY ≤ #Y) (hc : 16 * #X ≤ min cX #X * cY) (hY : 2 * #W + 4 * #X ≤ #Y) :
    ∃ X' ⊆ X, #X' ≤ cX ∧ ∃ Y' ⊆ Y, #Y' ≤ cY ∧ 2 * #X ≤ #((X' + Y') \ W) := by
  obtain ⟨X', hX'X, hX'⟩ := exists_subset_card_eq (min_le_right cX #X)
  obtain ⟨Y', hY'Y, hY'c, hY'⟩ :=
    exists_subset_min_le_two_mul_card_add_sdiff X' Y W (k := 2 * #X) hcY (by grind)
  refine ⟨X', hX'X, by grind, Y', hY'Y, hY'c, ?_⟩
  rw [hX', mul_comm] at hY'
  grind

/-- **Corollary 11** of Bollobás, Leader and Tiba. For pairs `(X i, Y i)`, `i ∈ s`, each
satisfying the hypotheses of Lemma 10 with `W` enlarged by `M` points, there are `X' i ⊆ X i` and
`Y' i ⊆ Y i` with at most `cX` and `cY` elements whose sumsets have together at least
`min M (2 * ∑ i ∈ s, #(X i))` elements outside `W`. -/
lemma exists_subsets_min_le_card_biUnion_add_sdiff {ι : Type*} (s : Finset ι)
    (X Y : ι → Finset G) (W : Finset G) {cX cY M : ℕ} (hcY : ∀ i ∈ s, cY ≤ #(Y i))
    (hc : ∀ i ∈ s, 16 * #(X i) ≤ min cX #(X i) * cY)
    (hY : ∀ i ∈ s, 2 * (#W + M) + 4 * #(X i) ≤ #(Y i)) :
    ∃ X' Y' : ι → Finset G,
      (∀ i ∈ s, X' i ⊆ X i ∧ #(X' i) ≤ cX ∧ Y' i ⊆ Y i ∧ #(Y' i) ≤ cY) ∧
      min M (2 * ∑ i ∈ s, #(X i)) ≤ #((s.biUnion fun i ↦ X' i + Y' i) \ W) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ ∅, fun _ ↦ ∅, by simp, by simp⟩
  | insert a s has ih =>
    obtain ⟨X', Y', hXY, hM⟩ := ih (fun i hi ↦ hcY i (mem_insert_of_mem hi))
      (fun i hi ↦ hc i (mem_insert_of_mem hi)) (fun i hi ↦ hY i (mem_insert_of_mem hi))
    set U := s.biUnion fun i ↦ X' i + Y' i
    obtain ⟨Xa, hXa, hXac, Ya, hYa, hYac, hcard⟩ : ∃ Xa ⊆ X a, #Xa ≤ cX ∧ ∃ Ya ⊆ Y a,
        #Ya ≤ cY ∧ min M (2 * ∑ i ∈ insert a s, #(X i)) ≤ #(U \ W) + #((Xa + Ya) \ (W ∪ U)) := by
      by_cases hU : M ≤ #(U \ W)
      · exact ⟨∅, empty_subset _, by simp, ∅, empty_subset _, by simp, by grind⟩
      obtain ⟨Xa, hXa, hXac, Ya, hYa, hYac, hXYa⟩ := exists_subset_two_mul_card_le_card_add_sdiff
        (hcY a (mem_insert_self a s)) (hc a (mem_insert_self a s))
        (by grind [card_union_le, union_sdiff_self_eq_union, mem_insert_self] :
          2 * #(W ∪ U) + 4 * #(X a) ≤ #(Y a))
      refine ⟨Xa, hXa, hXac, Ya, hYa, hYac, ?_⟩
      rw [sum_insert has]
      grind
    refine ⟨Function.update X' a Xa, Function.update Y' a Ya, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.1 hi with rfl | hi
      · simp [hXa, hXac, hYa, hYac]
      · simpa [ne_of_mem_of_not_mem hi has] using hXY i hi
    · rw [biUnion_insert, Function.update_self, Function.update_self,
        biUnion_congr (t₂ := fun i ↦ X' i + Y' i) rfl
          (fun i hi ↦ by simp [ne_of_mem_of_not_mem hi has]), union_comm,
        card_union_sdiff]
      exact hcard

end LargeSumsetsFromSubsets
