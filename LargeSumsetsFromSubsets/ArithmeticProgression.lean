/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic progressions

The arithmetic progression `arithProg a d n = {a, a + d, …, a + (n - 1) • d}` in an additive
monoid. In `ZMod p` the progressions of common difference `1` are the intervals. This file proves
the facts about intervals of `ZMod p` used in the proof of Theorem 1 of Bollobás, Leader and Tiba:
their sizes, membership through `ZMod.val`, and their behaviour under translation and under
multiplication by a unit.
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
  ext x
  simp only [mem_union, mem_arithProg]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases him : i < m
    · exact Or.inl ⟨i, him, rfl⟩
    · refine Or.inr ⟨i - m, by grind, ?_⟩
      rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' (by grind)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by grind, rfl⟩
    · exact ⟨m + i, by grind, by rw [add_nsmul, add_assoc]⟩

lemma image_add_arithProg (t a d : G) (n : ℕ) :
    (arithProg a d n).image (t + ·) = arithProg (t + a) d n := by
  simp [arithProg, image_image, Function.comp_def, add_assoc]

end AddCommMonoid

section ZMod

variable {p : ℕ}

/-- Membership in an interval of `ZMod p`, read off from `ZMod.val`. -/
lemma mem_arithProg_one_iff [NeZero p] {a x : ZMod p} {n : ℕ} (hn : n ≤ p) :
    x ∈ arithProg a 1 n ↔ (x - a).val < n := by
  rw [mem_arithProg]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [add_sub_cancel_left, nsmul_one, ZMod.val_natCast_of_lt (by grind)]
    exact hi
  · intro h
    exact ⟨(x - a).val, h, by rw [nsmul_one, ZMod.natCast_zmod_val, add_sub_cancel]⟩

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

lemma arithProg_one_eq_univ [NeZero p] (a : ZMod p) : arithProg a 1 p = univ := by
  ext x
  simp [mem_arithProg_one_iff le_rfl, ZMod.val_lt]

/-- Multiplication by `u` maps arithmetic progressions to arithmetic progressions. -/
lemma image_mul_arithProg (u a d : ZMod p) (n : ℕ) :
    (arithProg a d n).image (u * ·) = arithProg (u * a) (u * d) n := by
  simp [arithProg, image_image, Function.comp_def, mul_add, mul_left_comm]

end ZMod

end LargeSumsetsFromSubsets
