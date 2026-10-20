/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Arithmetic progressions close to an interval

An arithmetic progression of `ZMod p` that shares nine tenths of the points of an interval `Q`
of length `L`, with `20 ≤ L ≤ p / 8`, and has at most `11 * L / 10` elements is itself an interval.
The proof of Lemma 9 of Bollobás, Leader and Tiba uses this fact without proof.

Let `P = arithProg a d n` with `n = #P`, and let `T` be the set of indices `i < n` with
`a + i • d ∈ Q`. For every `k < 2 * #T - n` some `i` and `i + k` both lie in `T`, so `k • d` is a
difference of two points of `Q`: it is the cast of an integer `s` with `|s| < L`. Writing
`d = δ` with `|δ| < L`, the integers `k * δ` cannot jump over the gaps between the copies of
`(-L, L)` in `ℤ`, so `|k * δ| < L` for all these `k`. Taking `k` close to `7 * L / 10` gives
`|δ| = 1`, and the progression is an interval.
-/

@[expose] public section

open Finset

namespace LargeSumsetsFromSubsets

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Reversing an arithmetic progression changes the sign of its common difference. -/
lemma arithProg_neg (a d : G) (n : ℕ) : arithProg a (-d) n = arithProg (a - (n - 1) • d) d n := by
  ext x
  simp only [mem_arithProg]
  constructor <;>
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
    refine ⟨j, by grind, ?_⟩
    rw [(by grind : i + j + 1 - 1 = j + i), add_nsmul, smul_neg]
    abel

/-- The terms of `arithProg a d n` in a set `Q` are at most as many as their indices. -/
private lemma card_arithProg_inter_le_card_filter (a d : G) (n : ℕ) (Q : Finset G) :
    #(arithProg a d n ∩ Q) ≤ #{i ∈ range n | a + i • d ∈ Q} := by
  refine (card_le_card ?_).trans (card_image_le (f := fun i ↦ a + i • d))
  intro x hx
  obtain ⟨hxP, hxQ⟩ := mem_inter.1 hx
  obtain ⟨i, hi, rfl⟩ := mem_arithProg.1 hxP
  exact mem_image_of_mem _ (mem_filter.2 ⟨mem_range.2 hi, hxQ⟩)

end AddCommGroup

/-- A set of indices below `n` with more than `(n + k) / 2` elements contains two indices at
distance `k`. -/
lemma exists_mem_add_mem_of_add_lt {T : Finset ℕ} {n k : ℕ} (hT : T ⊆ range n)
    (hk : k + n < 2 * #T) : ∃ i ∈ T, i + k ∈ T := by
  obtain ⟨j, hj⟩ := inter_nonempty_of_card_lt_card_add_card (s := range (n + k)) (t := T)
    (u := T.image (· + k)) (hT.trans (range_subset_range.2 (by grind)))
    (image_subset_iff.2 fun i hi ↦ by simpa using hT hi)
    (by rw [card_range, card_image_of_injective _ (add_left_injective k)]; grind)
  simp only [mem_inter, mem_image] at hj
  obtain ⟨hjT, i, hi, rfl⟩ := hj
  exact ⟨i, hi, hjT⟩

section ZMod

variable {p : ℕ}

/-- The difference of two points of an interval of length `L` is the cast of an integer of
absolute value less than `L`. -/
lemma exists_intCast_eq_sub_of_mem_arithProg_one {q x y : ZMod p} {L : ℕ}
    (hx : x ∈ arithProg q 1 L) (hy : y ∈ arithProg q 1 L) :
    ∃ s : ℤ, |s| < L ∧ y - x = s := by
  rw [mem_arithProg] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  refine ⟨j - i, by rw [abs_lt]; grind, ?_⟩
  simp

/-- If every multiple `k • d` with `k < K` is the cast of an integer of absolute value less than
`L`, and `d` is the cast of `δ` with `|δ| < L`, then `|k * δ| < L` for all `k < K`: the
integers `k * δ` cannot jump over the gaps between the copies of `(-L, L)`. -/
lemma abs_mul_lt_of_forall_exists_intCast_eq {d : ZMod p} {δ : ℤ} {L K : ℕ} (hLp : 3 * L ≤ p)
    (hδ : (δ : ZMod p) = d) (hδL : |δ| < L)
    (h : ∀ k < K, ∃ s : ℤ, |s| < L ∧ k • d = s) : ∀ k < K, |k * δ| < L := by
  intro k hk
  induction k with
  | zero => simpa using hδL.trans_le' (abs_nonneg δ)
  | succ k ih =>
    obtain ⟨s, hsL, hs⟩ := h (k + 1) hk
    have hks : (k + 1 : ℤ) * δ = s := by
      rw [← sub_eq_zero]
      refine Int.eq_zero_of_abs_lt_dvd (m := p) ?_ ?_
      · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ← hs, ← hδ, nsmul_eq_mul]
        push_cast
        rfl
      · have := ih (by grind)
        rw [abs_lt] at *
        constructor <;> linarith
    push_cast
    rwa [hks]

/-- If `d ≠ 0` and every multiple `k • d` with `k < K` is the cast of an integer of absolute value
less than `L`, where `L + 2 ≤ 2 * K`, then `d = 1` or `d = -1`. -/
lemma eq_one_or_eq_neg_one_of_forall_exists_intCast_eq {d : ZMod p} {L K : ℕ} (hL : 0 < L)
    (hLp : 3 * L ≤ p) (hLK : L + 2 ≤ 2 * K) (hd : d ≠ 0)
    (h : ∀ k < K, ∃ s : ℤ, |s| < L ∧ k • d = s) : d = 1 ∨ d = -1 := by
  obtain ⟨δ, hδL, hδ⟩ := h 1 (by grind)
  rw [one_smul] at hδ
  subst hδ
  have hK := abs_mul_lt_of_forall_exists_intCast_eq hLp rfl hδL h (K - 1) (by grind)
  rw [abs_mul, Nat.abs_cast] at hK
  have hδ1 : |δ| = 1 := by
    refine le_antisymm ?_ (Int.one_le_abs (by rintro rfl; simp at hd))
    by_contra! hδ
    have hLK' : L ≤ 2 * (K - 1) := by grind
    generalize K - 1 = K' at hK hLK'
    linarith [mul_le_mul_of_nonneg_left (Int.add_one_le_of_lt hδ) (Nat.cast_nonneg' (α := ℤ) K'),
      (by exact_mod_cast hLK' : (L : ℤ) ≤ 2 * K')]
  obtain rfl | rfl := (abs_eq zero_le_one).1 hδ1 <;> simp

/-- If more than `(n + k) / 2` terms of `arithProg a d n` lie in an interval of length `L`, then
`k • d` is the cast of an integer of absolute value less than `L`. -/
lemma exists_intCast_eq_nsmul_of_add_lt_card_inter {a d q : ZMod p} {n L k : ℕ}
    (hk : k + n < 2 * #(arithProg a d n ∩ arithProg q 1 L)) :
    ∃ s : ℤ, |s| < L ∧ k • d = s := by
  obtain ⟨i, hi, hik⟩ := exists_mem_add_mem_of_add_lt (k := k)
    (filter_subset (fun i ↦ a + i • d ∈ arithProg q 1 L) (range n))
    (by grind [card_arithProg_inter_le_card_filter a d n (arithProg q 1 L)])
  obtain ⟨-, hi⟩ := mem_filter.1 hi
  obtain ⟨-, hik⟩ := mem_filter.1 hik
  obtain ⟨s, hsL, hs⟩ := exists_intCast_eq_sub_of_mem_arithProg_one hi hik
  refine ⟨s, hsL, ?_⟩
  rw [← hs, add_nsmul]
  abel

/-- In `ZMod p` with `p` prime, a progression of nonzero common difference with at most `p` terms
has as many elements as terms. -/
private lemma card_arithProg_of_le (hp : p.Prime) (a : ZMod p) {d : ZMod p} {m : ℕ} (hd : d ≠ 0)
    (hm : m ≤ p) : #(arithProg a d m) = m := by
  have : Fact p.Prime := ⟨hp⟩
  rw [arithProg, card_image_of_injOn, card_range]
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio, nsmul_eq_mul, add_right_inj] at hi hj hij
  rw [← Nat.mod_eq_of_lt (by grind : i < p), ← Nat.mod_eq_of_lt (by grind : j < p),
    ← ZMod.natCast_eq_natCast_iff']
  exact mul_right_cancel₀ hd hij

/-- In `ZMod p` with `p` prime, a progression of nonzero common difference with fewer than `p`
elements has as many elements as terms. -/
lemma card_arithProg_eq_of_card_lt (hp : p.Prime) {a d : ZMod p} {n : ℕ} (hd : d ≠ 0)
    (hn : #(arithProg a d n) < p) : #(arithProg a d n) = n := by
  refine card_arithProg_of_le hp a hd ?_
  by_contra! hpn
  grind [card_le_card (arithProg_mono a d hpn.le), card_arithProg_of_le hp a hd le_rfl]

end ZMod

/-- An arithmetic progression of `ZMod p` with at most `11 * L / 10` elements that shares at
least `9 * L / 10` points with an interval of length `L`, where `20 ≤ L` and `8 * L ≤ p`, is an
interval. -/
lemma exists_eq_arithProg_one_of_card_inter_arithProg_one {p : ℕ} (hp : p.Prime)
    {a d q : ZMod p} {n L : ℕ} (hL : 20 ≤ L) (hLp : 8 * L ≤ p)
    (hPQ : 9 * L ≤ 10 * #(arithProg a d n ∩ arithProg q 1 L))
    (hP : 10 * #(arithProg a d n) ≤ 11 * L) :
    ∃ (a' : ZMod p) (n' : ℕ), arithProg a d n = arithProg a' 1 n' := by
  have hcard := card_le_card (inter_subset_left (s₁ := arithProg a d n) (s₂ := arithProg q 1 L))
  have hd : d ≠ 0 := by
    rintro rfl
    grind [card_le_card (by simp [arithProg, subset_iff] : arithProg a 0 n ⊆ {a}), card_singleton]
  have hn := card_arithProg_eq_of_card_lt (a := a) (n := n) hp hd (by grind)
  obtain rfl | rfl := eq_one_or_eq_neg_one_of_forall_exists_intCast_eq
    (L := L) (K := 2 * #(arithProg a d n ∩ arithProg q 1 L) - n) (by grind) (by grind) (by grind) hd
    (fun k hk ↦ exists_intCast_eq_nsmul_of_add_lt_card_inter (a := a) (q := q) (n := n)
      (by grind))
  · exact ⟨a, n, rfl⟩
  · exact ⟨a - (n - 1) • 1, n, arithProg_neg a 1 n⟩

end LargeSumsetsFromSubsets
