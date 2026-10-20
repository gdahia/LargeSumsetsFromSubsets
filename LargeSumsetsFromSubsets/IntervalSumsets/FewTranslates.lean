/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Few translates of a set close to an interval

Theorem 5 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*, is Theorem 31
of their earlier paper *Large sumsets from small subsets*, arXiv:2204.07559v2. Let `A` be close to
an interval `I` of `ZMod p` and let `B` be contained in an interval `J`, contain its endpoints and
miss few of its points. Then there is a family of subsets of `B` of bounded size, depending only
on `I`, `J` and `B`, such that the sumset of `A` with a random member of the family has expected
size at least `#A + #B - 1`. The theorem is not proved here: it is the hypothesis
`FewTranslatesNearIntervals`.

This file deduces the same statement for intervals of integers, `exists_fewTranslates_int`, by
embedding a bounded window of `ℤ` into `ZMod q` for a large prime `q`.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-- Theorem 5 of Bollobás, Leader and Tiba, Theorem 31 of arXiv:2204.07559v2. For `β > 0` there
is `γ > 0` such that for `α > 0` there is `c` with the following property. Let
`I = {x, …, x + m - 1}` and `J = {y, …, y + n - 1}` be intervals of `ZMod p` with
`α * n ≤ m ≤ α⁻¹ * n` and `m + n ≤ (1 - β) * p`, and let `B ⊆ J` contain `y` and `y + n - 1` and
miss at most `γ * min m n` points of `J`. Then there are sets `F 0, …, F k ⊆ B` with at most `c`
elements each such that every `A` with `#(A ∆ I) ≤ γ * min m n` satisfies
`#A + #B - 1 ≤ 𝔼 i, #(A + F i)`, written as `(k + 1) * (#A + #B - 1) ≤ ∑ i, #(A + F i)`. -/
def FewTranslatesNearIntervals : Prop :=
  ∀ β > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℕ, ∀ p : ℕ, p.Prime →
    ∀ (x y : ZMod p) (m n : ℕ) (B : Finset (ZMod p)),
      α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n → (m + n : ℝ) ≤ (1 - β) * p →
      B ⊆ (range n).image (fun i : ℕ ↦ y + i) → y ∈ B → y + (n - 1 : ℕ) ∈ B →
      (#((range n).image (fun i : ℕ ↦ y + i) \ B) : ℝ) ≤ γ * min (m : ℝ) n →
      ∃ (k : ℕ) (F : Fin (k + 1) → Finset (ZMod p)), (∀ i, F i ⊆ B ∧ #(F i) ≤ c) ∧
        ∀ A : Finset (ZMod p),
          (#(A ∆ (range m).image (fun i : ℕ ↦ x + i)) : ℝ) ≤ γ * min (m : ℝ) n →
          (k + 1) * (#A + #B - 1) ≤ ∑ i, #(A + F i)

/-- A lower bound for a sum over `Fin (k + 1)` is a lower bound for the expectation. -/
lemma le_expect_of_mul_le_sum {k x : ℕ} {f : Fin (k + 1) → ℕ} (h : (k + 1) * x ≤ ∑ i, f i) :
    (x : ℝ) ≤ 𝔼 i, (f i : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, le_div_iff₀ (by positivity), mul_comm,
    ← Nat.cast_sum]
  exact_mod_cast h

/-- The cast `ℤ → ZMod q` is injective on any set inside an integer interval of length at most
`q`. -/
lemma injOn_intCast_of_subset_Ico {q : ℕ} {a b : ℤ} {s : Finset ℤ} (hs : s ⊆ Ico a b)
    (hb : b ≤ a + q) : Set.InjOn (Int.cast : ℤ → ZMod q) s := by
  intro u hu v hv huv
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at huv
  have hu' := mem_Ico.mp (hs hu)
  have hv' := mem_Ico.mp (hs hv)
  grind [Int.eq_zero_of_abs_lt_dvd huv (abs_lt.mpr ⟨by grind, by grind⟩)]

/-- The cast to `ZMod q` maps the integer interval `Ico a (a + n)` onto the interval of `ZMod q`
with `n` points starting at `a`. -/
lemma image_intCast_Ico (q : ℕ) (a : ℤ) (n : ℕ) :
    (Ico a (a + n)).image (Int.cast : ℤ → ZMod q) =
      (range n).image (fun i : ℕ ↦ (a : ZMod q) + i) := by
  ext z
  simp only [mem_image, mem_Ico, mem_range]
  constructor
  · rintro ⟨u, ⟨hau, hua⟩, rfl⟩
    refine ⟨(u - a).toNat, by grind, ?_⟩
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by grind)]
    simp
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a + i, by grind, by simp⟩

/-- The symmetric difference commutes with the image under a map injective on the union. -/
lemma image_symmDiff_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s t : Finset α} (hf : Set.InjOn f ↑(s ∪ t)) :
    (s ∆ t).image f = s.image f ∆ t.image f := by
  simp only [Set.InjOn, coe_union, Set.mem_union, mem_coe] at hf
  ext z
  simp only [mem_image, mem_symmDiff]
  grind

/-- A sumset of integers lies in the interval of sums of the endpoints. -/
lemma add_subset_Ico {s t : Finset ℤ} {a b c d : ℤ} (hs : s ⊆ Ico a b) (ht : t ⊆ Ico c d) :
    s + t ⊆ Ico (a + c) (b + d) := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hz
  grind [hs hu, ht hv]

/-- An additive map injective on `s + t` preserves the size of the sumset `s + t`. -/
lemma card_image_add_image_of_injOn {F α β : Type*} [DecidableEq α] [DecidableEq β] [Add α]
    [Add β] [FunLike F α β] [AddHomClass F α β] (f : F) {s t : Finset α}
    (hf : Set.InjOn f ↑(s + t)) : #(s.image f + t.image f) = #(s + t) := by
  rw [← image_add, card_image_of_injOn hf]

/-- If `B ⊆ Ico y (y + n)` with `n ≤ q`, the cast to `ZMod q` preserves the number of points of
`Ico y (y + n)` missed by `B`. -/
lemma card_image_add_range_sdiff_image_intCast {q n : ℕ} {y : ℤ} {B : Finset ℤ}
    (hB : B ⊆ Ico y (y + n)) (hn : n ≤ q) :
    #((range n).image (fun i : ℕ ↦ (y : ZMod q) + i) \ B.image Int.cast) =
      #(Ico y (y + n) \ B) := by
  have hinj := injOn_intCast_of_subset_Ico (q := q) (subset_refl (Ico y (y + n))) (by grind)
  rw [← image_intCast_Ico, ← image_sdiff_of_injOn hinj hB,
    card_image_of_injOn (hinj.mono sdiff_subset)]

/-- If `A ⊆ Ico (x - R) (x + m + R)` with `m + 2 * R ≤ q`, the cast to `ZMod q` preserves the
size of the symmetric difference of `A` and `Ico x (x + m)`. -/
lemma card_image_intCast_symmDiff_image_add_range {q m R : ℕ} {x : ℤ} {A : Finset ℤ}
    (hA : A ⊆ Ico (x - R) (x + m + R)) (hq : m + 2 * R ≤ q) :
    #(A.image Int.cast ∆ (range m).image (fun i : ℕ ↦ (x : ZMod q) + i)) =
      #(A ∆ Ico x (x + m)) := by
  have hinj := injOn_intCast_of_subset_Ico (q := q)
    (union_subset hA (Ico_subset_Ico (by grind) (by grind) : Ico x (x + m) ⊆ _)) (by grind)
  rw [← image_intCast_Ico, ← image_symmDiff_of_injOn hinj,
    card_image_of_injOn (hinj.mono symmDiff_subset_union)]

/-- `FewTranslatesNearIntervals` for intervals of integers, for sets `A` in a bounded window
around `I`. -/
lemma exists_fewTranslates_int (h : FewTranslatesNearIntervals) :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℕ, ∀ (x y : ℤ) (m n R : ℕ) (B : Finset ℤ),
      α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n →
      B ⊆ Ico y (y + n) → y ∈ B → y + n - 1 ∈ B →
      (#(Ico y (y + n) \ B) : ℝ) ≤ γ * min (m : ℝ) n →
      ∃ (k : ℕ) (F : Fin (k + 1) → Finset ℤ), (∀ i, F i ⊆ B ∧ #(F i) ≤ c) ∧
        ∀ A ⊆ Ico (x - R) (x + m + R), (#(A ∆ Ico x (x + m)) : ℝ) ≤ γ * min (m : ℝ) n →
          (#A + #B - 1 : ℝ) ≤ 𝔼 i, (#(A + F i) : ℝ) := by
  obtain ⟨γ, hγ, hγc⟩ := h (1 / 2) (by norm_num)
  refine ⟨γ, hγ, ?_⟩
  intro α hα
  obtain ⟨c, hc⟩ := hγc α hα
  refine ⟨c, ?_⟩
  intro x y m n R B hαm hmα hB hyB hyB' hmiss
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (2 * (m + n) + 2 * R + 1)
  have hBinj := injOn_intCast_of_subset_Ico (q := q) hB (by grind)
  obtain ⟨k, F', hF', hAF'⟩ := hc q hqp x y m n (B.image Int.cast) hαm hmα
    (by rify at hq; linarith)
    ((image_subset_image hB).trans (image_intCast_Ico q y n).le) (mem_image_of_mem _ hyB)
    (by simpa [(by grind [hB hyB] : 1 ≤ n), add_sub_assoc] using
      mem_image_of_mem (Int.cast : ℤ → ZMod q) hyB')
    (by rwa [card_image_add_range_sdiff_image_intCast hB (by grind)])
  choose hF'B hF'c using hF'
  choose F hFB hFF' using fun i ↦ subset_image_iff.mp (hF'B i)
  refine ⟨k, F, ?_, ?_⟩
  · intro i
    refine ⟨hFB i, ?_⟩
    rw [← card_image_of_injOn (hBinj.mono (hFB i)), hFF']
    exact hF'c i
  intro A hA hAI
  have hAF := hAF' (A.image Int.cast)
    (by rwa [card_image_intCast_symmDiff_image_add_range hA (by grind)])
  have hsum (i : Fin (k + 1)) : #(A.image Int.cast + F' i) = #(A + F i) := by
    rw [← hFF']
    exact card_image_add_image_of_injOn (Int.castAddHom (ZMod q)) <|
      injOn_intCast_of_subset_Ico (add_subset_Ico hA ((hFB i).trans hB)) (by grind)
  rw [card_image_of_injOn (injOn_intCast_of_subset_Ico hA (by grind)),
    card_image_of_injOn hBinj] at hAF
  simp only [hsum] at hAF
  rw [← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_sub (by grind [card_pos.2 ⟨y, hyB⟩])]
  exact le_expect_of_mul_le_sum hAF

end LargeSumsetsFromSubsets
