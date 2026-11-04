/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Basic.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.IntervalCovering
import LargeSumsetsFromSubsets.CauchyDavenportBound.IntervalEnds
import Mathlib.Tactic.Rify

/-!
# Consecutive intervals of `ZMod p`

Lemma 9 of Bollobás, Leader and Tiba cuts `ZMod p` into consecutive intervals
`I₁ = arithProg s 1 a₁`, `I₂ = arithProg (s + a₁) 1 a₂` and `I₃ = arithProg (s + (a₁ + a₂)) 1 a₃`,
and likewise `J₁`, `J₂` and `J₃` from `r` and `b₁`, `b₂`, `b₃`. This file proves the facts about
these intervals used in the proof of Theorem 1: inclusions and disjointness, the sizes of the parts
of a set in them, and the disjointness of the sumsets `I₁ + J₁`, `I₂ + J₂` and `I₃ + J₃`.

## Main statements

* `card_inter_ends_add_card_sdiff_eq`: the parts of `A` and `B` in the end intervals and outside
  `I = I₁ ∪ I₂ ∪ I₃` and `J = J₁ ∪ J₂ ∪ J₃` add up to the parts outside `I₂` and `J₂`.
* `disjoint_add_arithProg_of_add_le`: the sumsets `I₁ + J₁`, `I₂ + J₂` and `I₃ + J₃` are pairwise
  disjoint.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {p : ℕ}

/-- The interval `arithProg (a + k) 1 n` lies in `arithProg a 1 N` when `k + n ≤ N`. -/
lemma arithProg_add_natCast_subset (a : ZMod p) {k n N : ℕ} (h : k + n ≤ N) :
    arithProg (a + k) 1 n ⊆ arithProg a 1 N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_arithProg.1 hx
  exact mem_arithProg.2 ⟨k + i, by grind, by simp [add_assoc]⟩

/-- The intervals `arithProg x 1 m` and `arithProg y 1 n` are disjoint when `y = x + k` with
`m ≤ k` and `k + n ≤ p`. -/
lemma disjoint_arithProg_one_of_eq_add {x y : ZMod p} {k m n : ℕ} (hmk : m ≤ k) (h : k + n ≤ p)
    (hy : y = x + k) : Disjoint (arithProg x 1 m) (arithProg y 1 n) := by
  subst hy
  exact (disjoint_arithProg_one x h).mono_left (arithProg_mono _ _ hmk)

/-- The points within `L` of `arithProg (s + a₁) 1 a₂` lie in `arithProg s 1 (a₁ + a₂ + a₃)` when
`L ≤ a₁` and `L ≤ a₃`. -/
lemma arithProg_sub_subset (s : ZMod p) {a₁ a₂ a₃ L : ℕ} (h₁ : L ≤ a₁) (h₃ : L ≤ a₃) :
    arithProg (s + a₁ - L) 1 (a₂ + 2 * L) ⊆ arithProg s 1 (a₁ + a₂ + a₃) := by
  rw [add_sub_assoc, ← Nat.cast_sub h₁]
  exact arithProg_add_natCast_subset s (by grind)

/-- The size of a set `A` within `δ` of an interval of length `m ≤ p` differs from `m` by at most
`δ`. -/
lemma abs_card_sub_le_of_card_symmDiff_le {A : Finset (ZMod p)} {x : ZMod p} {m : ℕ} {δ : ℝ}
    (hm : m ≤ p) (h : #(A ∆ arithProg x 1 m) ≤ δ) : |(#A : ℝ) - m| ≤ δ := by
  obtain ⟨h₁, h₂⟩ : #A ≤ m + #(A ∆ arithProg x 1 m) ∧ m ≤ #A + #(A ∆ arithProg x 1 m) := by
    grind [card_symmDiff_add_two_mul_card_inter A (arithProg x 1 m), card_arithProg_one x hm,
      card_le_card (inter_subset_left : A ∩ arithProg x 1 m ⊆ A),
      card_le_card (inter_subset_right : A ∩ arithProg x 1 m ⊆ arithProg x 1 m)]
  rify at h₁ h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The sizes of the parts of `A` in three consecutive intervals of `ZMod p` and outside them. -/
lemma card_eq_card_sdiff_add_card_inter (A : Finset (ZMod p)) (s : ZMod p) {a₁ a₂ a₃ : ℕ}
    (h : a₁ + a₂ + a₃ ≤ p) :
    #A = #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(A ∩ arithProg s 1 a₁) +
      #(A ∩ arithProg (s + a₁) 1 a₂) + #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) := by
  rw [← card_sdiff_add_card_inter A (arithProg s 1 (a₁ + a₂ + a₃)), arithProg_one_add_eq_union,
    inter_union_distrib_left, card_union_of_disjoint, arithProg_one_add_eq_union,
    inter_union_distrib_left, card_union_of_disjoint]
  · grind
  · exact (disjoint_arithProg_one s (by grind)).mono inter_subset_right inter_subset_right
  · exact (disjoint_arithProg_one s h).mono inter_subset_right inter_subset_right

/-- The parts of `A` and `B` in the end intervals `I₁, I₃, J₁, J₃` and outside the intervals
`I = arithProg s 1 (a₁ + a₂ + a₃)` and `J = arithProg r 1 (b₁ + b₂ + b₃)` have together as many
elements as the parts outside the middle intervals `I₂` and `J₂`. -/
lemma card_inter_ends_add_card_sdiff_eq (A B : Finset (ZMod p)) (s r : ZMod p)
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (hA : a₁ + a₂ + a₃ ≤ p) (hB : b₁ + b₂ + b₃ ≤ p) :
    #(A ∩ arithProg s 1 a₁) + #(B ∩ arithProg r 1 b₁) +
        #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) + #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) +
        #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(B \ arithProg r 1 (b₁ + b₂ + b₃)) =
      #(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂) := by
  linarith [card_eq_card_sdiff_add_card_inter A s hA, card_eq_card_sdiff_add_card_inter B r hB,
    card_inter_add_card_sdiff A (arithProg (s + (a₁ : ZMod p)) 1 a₂),
    card_inter_add_card_sdiff B (arithProg (r + (b₁ : ZMod p)) 1 b₂)]

/-- For consecutive intervals `I₁, I₂, I₃` and `J₁, J₂, J₃` of `ZMod p` of total length at most `p`,
the sumsets `I₁ + J₁`, `I₂ + J₂` and `I₃ + J₃` lie in consecutive intervals, so they are pairwise
disjoint. -/
lemma disjoint_add_arithProg_of_add_le (s r : ZMod p) {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (h : a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p) :
    Disjoint (arithProg s 1 a₁ + arithProg r 1 b₁)
      (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) ∧
    Disjoint (arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ + arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃)
      (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) ∧
    Disjoint (arithProg s 1 a₁ + arithProg r 1 b₁)
      (arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ + arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Disjoint.mono (add_arithProg_subset _ _ _ _ _)
    (add_arithProg_subset _ _ _ _ _)
  · exact disjoint_arithProg_one_of_eq_add (k := a₁ + b₁) (by grind) (by grind) (by grind)
  · exact (disjoint_arithProg_one_of_eq_add (k := a₂ + b₂) (by grind) (by grind) (by grind)).symm
  · exact disjoint_arithProg_one_of_eq_add (k := a₁ + b₁ + (a₂ + b₂)) (by grind) (by grind)
      (by grind)

end LargeSumsetsFromSubsets
