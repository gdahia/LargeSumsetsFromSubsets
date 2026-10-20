/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Ring.RingNF

/-!
# Blocks of an interval whose translates avoid a sumset

The pointwise form of Lemma 12 of Bollobás, Leader and Tiba. Let `I = arithProg u 1 m` and
`J = arithProg v 1 n` be intervals of `ZMod p` with `m + n + L ≤ p`, and cut `J` into the
consecutive blocks `arithProg (v + i * l) 1 l`, `i < n / l`. If `x` lies at distance at least `L`
beyond both ends of `I`, then some block `J'` satisfies `(x + J') ∩ (I + J) = ∅`, as long as
`2 * l ≤ n` and `2 * l ≤ L`. Indeed `x + J` meets `I + J` only in an initial and a final segment,
and the points in between form an interval of at least `min n L` points.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace LargeSumsetsFromSubsets

section AddCommMonoid

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The sumset of two arithmetic progressions with the same common difference lies in the
progression of their combined length. -/
lemma add_arithProg_subset (a b d : G) (m n : ℕ) :
    arithProg a d m + arithProg b d n ⊆ arithProg (a + b) d (m + n - 1) := by
  intro z hz
  obtain ⟨_, hy, _, hy', rfl⟩ := mem_add.1 hz
  obtain ⟨i, hi, rfl⟩ := mem_arithProg.1 hy
  obtain ⟨j, hj, rfl⟩ := mem_arithProg.1 hy'
  exact mem_arithProg.2 ⟨i + j, by grind, by rw [add_nsmul, add_add_add_comm]⟩

/-- The sumset of two nonempty arithmetic progressions with the same common difference is the
progression of their combined length. -/
lemma arithProg_add_arithProg (a b d : G) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    arithProg a d m + arithProg b d n = arithProg (a + b) d (m + n - 1) := by
  refine (add_arithProg_subset a b d m n).antisymm ?_
  intro z hz
  obtain ⟨k, hk, rfl⟩ := mem_arithProg.1 hz
  obtain ⟨i, j, rfl, hi, hj⟩ : ∃ i j, k = i + j ∧ i < m ∧ j < n :=
    ⟨min k (m - 1), k - min k (m - 1), by grind, by grind, by grind⟩
  rw [add_nsmul, add_add_add_comm]
  exact add_mem_add (mem_arithProg.2 ⟨i, hi, rfl⟩) (mem_arithProg.2 ⟨j, hj, rfl⟩)

end AddCommMonoid

/-- A point `u + w`, with `w < p`, at distance at least `L` beyond both ends of the interval
`arithProg u 1 m` satisfies `m + L ≤ w` and `w + L < p`. -/
private lemma le_and_lt_of_add_notMem_arithProg {p : ℕ} [NeZero p] {u : ZMod p} {w m L : ℕ}
    (hwp : w < p) (hx : u + w ∉ arithProg (u - L) 1 (m + 2 * L)) : m + L ≤ w ∧ w + L < p := by
  refine ⟨?_, ?_⟩ <;> by_contra! h
  · exact hx (mem_arithProg.2 ⟨w + L, by grind, by simp⟩)
  · exact hx (mem_arithProg.2 ⟨w + L - p, by grind, by simp [Nat.cast_sub h]⟩)

/-- **Lemma 12** of Bollobás, Leader and Tiba, for one point. If `x` is not within `L` of the
interval `I = arithProg u 1 m`, some block `arithProg (v + i * l) 1 l`, `i < n / l`, of
`J = arithProg v 1 n` has its translate by `x` disjoint from `I + J`. -/
lemma exists_lt_disjoint_image_add_arithProg {p : ℕ} [NeZero p] {u v x : ZMod p}
    {m n L l : ℕ} (hmnL : m + n + L ≤ p) (hl : 1 ≤ l) (hln : 2 * l ≤ n) (hlL : 2 * l ≤ L)
    (hx : x ∉ arithProg (u - L) 1 (m + 2 * L)) :
    ∃ i < n / l, Disjoint ((arithProg (v + (i * l : ℕ)) 1 l).image (x + ·))
      (arithProg u 1 m + arithProg v 1 n) := by
  obtain ⟨w, hwp, rfl⟩ : ∃ w < p, x = u + w := ⟨(x - u).val, ZMod.val_lt _, by simp⟩
  obtain ⟨hmw, hwL⟩ := le_and_lt_of_add_notMem_arithProg hwp hx
  obtain ⟨a, ha⟩ : ∃ a, a = m + n - 1 - w := ⟨_, rfl⟩
  have hal := Nat.lt_div_mul_add (a := a) hl
  have hla := Nat.div_mul_le_self a l
  refine ⟨a / l + 1, (Nat.le_div_iff_mul_le hl).2 (by grind), ?_⟩
  rw [disjoint_left]
  intro z hz hzIJ
  obtain ⟨_, hy, rfl⟩ := mem_image.1 hz
  obtain ⟨k, hk, rfl⟩ := mem_arithProg.1 hy
  have := (mem_arithProg_one_iff (by grind)).1 (add_arithProg_subset u v 1 m n hzIJ)
  rw [(by simp; ring : u + w + (v + ((a / l + 1) * l : ℕ) + k • 1) - (u + v) =
    ((w + (a / l + 1) * l + k : ℕ) : ZMod p)), ZMod.val_natCast_of_lt (by grind)] at this
  grind

end LargeSumsetsFromSubsets
