/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSmallSubsets.NearCauchyDavenport.Progression
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring.RingNF

/-!
# Arithmetic progressions

The arithmetic progression `arithProg a d n = {a, a + d, …, a + (n - 1) • d}` in an additive monoid.
In a commutative ring it is the progression of the same name in `LargeSumsetsFromSmallSubsets`. In
`ZMod p` the progressions of common difference `1` are the intervals. This file proves the facts
about intervals of `ZMod p` used in the proof of Theorem 1 of Bollobás, Leader and Tiba: their
sizes, membership through `ZMod.val`, how they split into consecutive intervals, and their behavior
under translation, reflection and multiplication by a unit.

## Main definitions

* `arithProg a d n`: the arithmetic progression `{a, a + d, …, a + (n - 1) • d}`.

## Main statements

* `nearCauchyDavenport_arithProg_eq`: `arithProg` agrees with the progressions of
  `LargeSumsetsFromSmallSubsets`.
* `mem_arithProg_one_iff`: `x ∈ arithProg a 1 n ↔ (x - a).val < n` in `ZMod p`, for `n ≤ p`.
* `card_arithProg_one`: an interval of `ZMod p` of length `n ≤ p` has `n` elements.
* `disjoint_arithProg_one`: two consecutive intervals of total length at most `p` are disjoint.
* `image_add_arithProg`, `image_neg_arithProg`, `image_mul_arithProg`: translates, reflections and
  multiples of arithmetic progressions are arithmetic progressions.
* `ne_zero_of_two_le_card_of_subset_arithProg`: a set with at least two elements does not lie in a
  progression of common difference zero.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace LargeSumsetsFromSubsets

section AddCommMonoid

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The arithmetic progression `{a, a + d, …, a + (n - 1) • d}`. -/
def arithProg (a d : G) (n : ℕ) : Finset G := (range n).image fun i ↦ a + i • d

lemma mem_arithProg {a d x : G} {n : ℕ} : x ∈ arithProg a d n ↔ ∃ i < n, a + i • d = x := by
  simp [arithProg]

lemma card_arithProg_le (a d : G) (n : ℕ) : #(arithProg a d n) ≤ n :=
  card_image_le.trans (card_range n).le

@[simp]
lemma arithProg_zero (a d : G) : arithProg a d 0 = ∅ := by
  simp [arithProg]

lemma arithProg_one_right (a d : G) : arithProg a d 1 = {a} := by
  simp [arithProg]

lemma arithProg_mono (a d : G) {m n : ℕ} (h : m ≤ n) : arithProg a d m ⊆ arithProg a d n :=
  image_subset_image (range_subset_range.2 h)

lemma arithProg_add (a d : G) (m n : ℕ) :
    arithProg a d (m + n) = arithProg a d m ∪ arithProg (a + m • d) d n := by
  simp [arithProg, range_add_eq_union, image_union, map_eq_image, image_image, Function.comp_def,
    add_nsmul, add_assoc]

lemma image_add_arithProg (t a d : G) (n : ℕ) :
    (arithProg a d n).image (t + ·) = arithProg (t + a) d n := by
  simp [arithProg, image_image, Function.comp_def, add_assoc]

/-- A set with at least two elements does not lie in a progression of common difference zero. -/
lemma ne_zero_of_two_le_card_of_subset_arithProg {s : Finset G} {a d : G} {m : ℕ} (hs : 2 ≤ #s)
    (h : s ⊆ arithProg a d m) : d ≠ 0 := by
  rintro rfl
  grind [card_le_card (h.trans (by simp [arithProg, subset_iff] : arithProg a 0 m ⊆ {a})),
    card_singleton]

end AddCommMonoid

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Negation maps arithmetic progressions to arithmetic progressions. -/
lemma image_neg_arithProg (a d : G) (n : ℕ) :
    (arithProg a d n).image Neg.neg = arithProg (-a) (-d) n := by
  simp [arithProg, image_image, Function.comp_def, add_comm]

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

end AddCommGroup

/-- Multiplication by `u` maps arithmetic progressions to arithmetic progressions. -/
lemma image_mul_arithProg {R : Type*} [CommSemiring R] [DecidableEq R] (u a d : R) (n : ℕ) :
    (arithProg a d n).image (u * ·) = arithProg (u * a) (u * d) n := by
  simp [arithProg, image_image, Function.comp_def, mul_add, mul_left_comm]

/-- In a commutative ring, the progressions of *Large sumsets from small subsets*, written with
`i * d`, are the progressions `arithProg a d n`. -/
lemma nearCauchyDavenport_arithProg_eq {R : Type*} [CommRing R] [DecidableEq R] (a d : R) (n : ℕ) :
    LargeSumsetsFromSmallSubsets.NearCauchyDavenport.arithProg a d n = arithProg a d n := by
  simp [LargeSumsetsFromSmallSubsets.NearCauchyDavenport.arithProg, arithProg]

section ZMod

variable {p : ℕ}

/-- Membership in an interval of `ZMod p`, read off from `ZMod.val`. -/
lemma mem_arithProg_one_iff [NeZero p] {a x : ZMod p} {n : ℕ} (hn : n ≤ p) :
    x ∈ arithProg a 1 n ↔ (x - a).val < n := by
  rw [mem_arithProg]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rwa [add_sub_cancel_left, nsmul_one, ZMod.val_natCast_of_lt (by grind)]
  · intro h
    exact ⟨(x - a).val, h, by simp⟩

/-- An interval of `ZMod p` is the image of `range n` under `i ↦ a + i`. -/
lemma arithProg_one_eq_image_range (a : ZMod p) (n : ℕ) :
    arithProg a 1 n = (range n).image fun i : ℕ ↦ a + i := by
  simp [arithProg]

lemma card_arithProg_one (a : ZMod p) {n : ℕ} (hn : n ≤ p) : #(arithProg a 1 n) = n := by
  rw [arithProg, card_image_of_injOn, card_range]
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio, nsmul_one, add_right_inj] at hi hj hij
  rw [← ZMod.val_natCast_of_lt (n := p) (by grind : i < p),
    ← ZMod.val_natCast_of_lt (n := p) (by grind : j < p), hij]

/-- An interval splits into two consecutive intervals. -/
lemma arithProg_one_add_eq_union (a : ZMod p) (m n : ℕ) :
    arithProg a 1 (m + n) = arithProg a 1 m ∪ arithProg (a + m) 1 n := by
  rw [arithProg_add, nsmul_one]

/-- Two consecutive intervals of total length at most `p` are disjoint. -/
lemma disjoint_arithProg_one (a : ZMod p) {m n : ℕ} (h : m + n ≤ p) :
    Disjoint (arithProg a 1 m) (arithProg (a + m) 1 n) := by
  rw [← card_union_eq_card_add_card, ← arithProg_one_add_eq_union, card_arithProg_one _ h,
    card_arithProg_one _ (by grind), card_arithProg_one _ (by grind)]

/-- The reflection of an interval is an interval of the same length. -/
lemma image_neg_arithProg_one (a : ZMod p) (n : ℕ) :
    (arithProg a 1 n).image Neg.neg = arithProg (-(a + n) + 1) 1 n := by
  ext x
  simp only [mem_image, mem_arithProg, nsmul_one]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨n - (1 + i), by grind, ?_⟩
    push_cast [Nat.cast_sub (by grind : 1 + i ≤ n)]
    ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨_, ⟨n - (1 + j), by grind, rfl⟩, ?_⟩
    push_cast [Nat.cast_sub (by grind : 1 + j ≤ n)]
    ring

variable [NeZero p]

lemma arithProg_one_eq_univ (a : ZMod p) : arithProg a 1 p = univ := by
  ext x
  simp [mem_arithProg_one_iff le_rfl, ZMod.val_lt]

/-- An interval of length more than `p` is the interval of length `p`. -/
lemma arithProg_one_eq_min (a : ZMod p) (n : ℕ) : arithProg a 1 n = arithProg a 1 (min n p) := by
  rcases le_total n p with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, arithProg_one_eq_univ]
    exact eq_univ_of_forall fun x ↦ arithProg_mono a 1 h (by simp [arithProg_one_eq_univ])

end ZMod

end LargeSumsetsFromSubsets
