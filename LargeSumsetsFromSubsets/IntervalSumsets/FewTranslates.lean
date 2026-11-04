/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSmallSubsets.NearCauchyDavenport.Progression
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval

import LargeSumsetsFromSmallSubsets.FewTranslates.NearInterval
import LargeSumsetsFromSubsets.ArithmeticProgression
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic.Rify

/-!
# Few translates of a set close to an interval of integers

Theorem 5 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*, is Theorem 31 of
their earlier paper *Large sumsets from small subsets*, arXiv:2204.07559v2. Let `A` be close to an
interval `I` and let `B` be close to an interval `J` and contain its endpoints. Theorem 31 gives a
family of subsets of `B` of bounded size, depending only on `I`, `J` and `B`, such that the sumset
of `A` with a random member of the family has expected size at least `#A + #B - 1`.

The proof of Theorem 8 needs only one subset `F ⊆ B` of bounded size with `#A + #B - 1 ≤ #(A + F)`
for each `A`. This is the form of Theorem 31 proved in `LargeSumsetsFromSmallSubsets` as
`FewTranslates.exists_subset_card_le_add_le_card_add_of_card_sdiff_le`. This file deduces it for
intervals of integers by embedding a bounded window of `ℤ` into `ZMod q` for a large prime `q`.

## Main definitions

* `FewTranslatesInt γ α c`: for intervals `Ico x (x + m)` and `Ico y (y + n)` with
  `α * n ≤ m ≤ α⁻¹ * n`, every `A` and `B` within `γ * min m n` of them, with `B` inside its
  interval and containing its endpoints, have some `F ⊆ B` with at most `c` elements and
  `#A + #B - 1 ≤ #(A + F)`.

## Main statements

* `exists_subset_card_le_add_le_card_add_of_card_sdiff_le_int`: the form of Theorem 31 proved in
  `LargeSumsetsFromSmallSubsets`, for intervals of integers.
* `exists_fewTranslatesInt`: there is `γ > 0` such that for every `α > 0` some `c` satisfies
  `FewTranslatesInt γ α c`.
-/

@[expose] public section

open Finset LargeSumsetsFromSmallSubsets
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-! ### Intervals of integers in `ZMod q` -/

/-- The cast `ℤ → ZMod q` is injective on every set inside an integer interval of length at most
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

/-- The cast to `ZMod q` maps `Ico a (a + n)` onto the progression of difference `1` of
`LargeSumsetsFromSmallSubsets` starting at `a`. -/
lemma image_intCast_Ico_eq_arithProg (q : ℕ) (a : ℤ) (n : ℕ) :
    (Ico a (a + n)).image (Int.cast : ℤ → ZMod q) =
      LargeSumsetsFromSmallSubsets.NearCauchyDavenport.arithProg (a : ZMod q) 1 n := by
  rw [nearCauchyDavenport_arithProg_eq, arithProg_one_eq_image_range, image_intCast_Ico]

/-- The image of `s \ t` under a map injective on `s ∪ t` is the difference of the images. -/
lemma image_sdiff_of_injOn_union {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s t : Finset α} (hf : Set.InjOn f ↑(s ∪ t)) :
    (s \ t).image f = s.image f \ t.image f := by
  simp only [Set.InjOn, coe_union, Set.mem_union, mem_coe] at hf
  ext z
  simp only [mem_image, mem_sdiff]
  grind

/-- A map injective on `s ∪ t` preserves the size of `s \ t`. -/
lemma card_image_sdiff_image_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s t : Finset α} (hf : Set.InjOn f ↑(s ∪ t)) :
    #(s.image f \ t.image f) = #(s \ t) := by
  rw [← image_sdiff_of_injOn_union hf,
    card_image_of_injOn (hf.mono (coe_subset.2 (sdiff_subset.trans subset_union_left)))]

/-- A sumset of integers lies in the interval of sums of the endpoints. -/
lemma add_subset_Ico {s t : Finset ℤ} {a b c d : ℤ} (hs : s ⊆ Ico a b) (ht : t ⊆ Ico c d) :
    s + t ⊆ Ico (a + c) (b + d) := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hz
  grind [hs hu, ht hv]

/-- The cast to `ZMod q`, injective on `s + t`, preserves the size of the sumset `s + t`. -/
lemma card_image_intCast_add_image_intCast {q : ℕ} {s t : Finset ℤ}
    (h : Set.InjOn (Int.cast : ℤ → ZMod q) ↑(s + t)) :
    #(s.image (Int.cast : ℤ → ZMod q) + t.image Int.cast) = #(s + t) := by
  rw [← card_image_of_injOn h]
  exact congrArg card (image_add (f := Int.castAddHom (ZMod q))).symm

/-! ### Sets close to intervals of integers -/

/-- A set differs from `t` in at least as many points as it has outside `t`. -/
lemma card_sdiff_le_card_symmDiff {α : Type*} [DecidableEq α] (s t : Finset α) :
    #(s \ t) ≤ #(s ∆ t) :=
  card_le_card (le_sup_left.trans_eq (symmDiff_def s t).symm)

/-- If `s` and `t` differ in at most `c` points, each has at most `c` points outside the other. -/
lemma card_sdiff_le_and_card_sdiff_le_of_card_symmDiff_le {α : Type*} [DecidableEq α]
    {s t : Finset α} {c : ℝ} (h : #(s ∆ t) ≤ c) : #(s \ t) ≤ c ∧ #(t \ s) ≤ c := by
  rw [symmDiff_def, sup_eq_union] at h
  exact ⟨by grw [← h, ← subset_union_left], by grw [← h, ← subset_union_right]⟩

/-- A set `X ⊆ Ico a (a + m)` has at most `m` elements. -/
lemma card_le_of_subset_Ico {a : ℤ} {m : ℕ} {X : Finset ℤ} (hX : X ⊆ Ico a (a + m)) : #X ≤ m := by
  simpa using card_le_card hX

/-- A set `X ⊆ Ico a (a + m)` and the points of the interval it misses add up to `m`. -/
lemma card_Ico_sdiff_add_card {a : ℤ} {m : ℕ} {X : Finset ℤ} (hX : X ⊆ Ico a (a + m)) :
    (#(Ico a (a + m) \ X) : ℝ) + #X = m := by
  rw [← Nat.cast_add, card_sdiff_add_card_eq_card hX]
  simp

/-- The form of Theorem 31 of *Large sumsets from small subsets* proved in
`LargeSumsetsFromSmallSubsets`, for sets close to intervals of integers. Let
`A ⊆ Ico (x - R) (x + m + R)` and `B ⊆ Ico y (y + n)` have at least two elements, with `y` and
`y + n - 1` in `B`, let `α * #B ≤ μ` and `δ ≤ 1 / 800`, where `μ = min #A #B`, and let
`Ico x (x + m) \ A` and `A \ Ico x (x + m)` have at most `δ * μ` elements, `Ico y (y + n) \ B` at
most `5 * δ * μ`, `m ≤ #A + δ * μ` and `n ≤ #B + 5 * δ * μ`. Then some `F ⊆ B` with at most
`⌈64 / α⌉₊ ^ 2 + 2 * ⌈64 / α⌉₊ + 10` elements has `#A + n ≤ #(A + F) + 1`. -/
lemma exists_subset_card_le_add_le_card_add_of_card_sdiff_le_int {α δ : ℝ} (hα : 0 < α)
    (hδ : δ ≤ 1 / 800) {x y : ℤ} {m n R : ℕ} {A B : Finset ℤ} (hA : A ⊆ Ico (x - R) (x + m + R))
    (hB : B ⊆ Ico y (y + n)) (hyB : y ∈ B) (hyB' : y + n - 1 ∈ B) (hA₂ : 2 ≤ #A) (hB₂ : 2 ≤ #B)
    (hαB : α * #B ≤ min (#A : ℝ) #B) (hIA : #(Ico x (x + m) \ A) ≤ δ * min (#A : ℝ) #B)
    (hAI : #(A \ Ico x (x + m)) ≤ δ * min (#A : ℝ) #B)
    (hJB : #(Ico y (y + n) \ B) ≤ 5 * δ * min (#A : ℝ) #B) (hm : m ≤ #A + δ * min (#A : ℝ) #B)
    (hn : n ≤ #B + 5 * δ * min (#A : ℝ) #B) :
    ∃ F ⊆ B, #F ≤ ⌈64 / α⌉₊ ^ 2 + 2 * ⌈64 / α⌉₊ + 10 ∧ #A + n ≤ #(A + F) + 1 := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (2 * (#A + #B + m + n + 2 * R) + 1)
  have : Fact q.Prime := ⟨hqp⟩
  have hAq := injOn_intCast_of_subset_Ico (q := q)
    (union_subset hA (Ico_subset_Ico (by grind) (by grind) : Ico x (x + m) ⊆ _)) (by grind)
  have hJq := injOn_intCast_of_subset_Ico (q := q) (subset_refl (Ico y (y + n))) (by grind)
  have hcA : #(A.image (Int.cast : ℤ → ZMod q)) = #A := card_image_of_injOn (hAq.mono (by simp))
  have hcB : #(B.image (Int.cast : ℤ → ZMod q)) = #B := card_image_of_injOn (hJq.mono hB)
  have hp : (#(A.image (Int.cast : ℤ → ZMod q)) + #(B.image (Int.cast : ℤ → ZMod q)) : ℝ) ≤
      (1 - 1 / 2) * q := by
    rw [hcA, hcB]
    rify at hq
    linarith
  rw [← card_image_sdiff_image_of_injOn (s := Ico x (x + m)) (t := A) (by rwa [union_comm]),
    image_intCast_Ico_eq_arithProg] at hIA
  rw [← card_image_sdiff_image_of_injOn hAq, image_intCast_Ico_eq_arithProg] at hAI
  rw [← card_image_sdiff_image_of_injOn (s := Ico y (y + n)) (t := B)
    (by rwa [union_eq_left.2 hB]), image_intCast_Ico_eq_arithProg] at hJB
  rw [← hcA, ← hcB, ← Nat.cast_min] at hαB hIA hAI hJB hm hn
  obtain ⟨F', hF'B, hF'c, hF'⟩ :=
    FewTranslates.exists_subset_card_le_add_le_card_add_of_card_sdiff_le (d := 1) hα
      (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) one_ne_zero (hcA ▸ hA₂) (hcB ▸ hB₂) hαB hp
      (mem_image_of_mem _ hyB)
      (by simpa [add_sub_assoc] using mem_image_of_mem (Int.cast : ℤ → ZMod q) hyB')
      ((image_subset_image hB).trans (image_intCast_Ico_eq_arithProg q y n).le) hIA hAI hJB hm hn
  obtain ⟨F, hFB, rfl⟩ := subset_image_iff.1 hF'B
  rw [card_image_of_injOn (hJq.mono (coe_subset.2 (hFB.trans hB))),
    (by ring : 32 / (α * (1 / 2)) = 64 / α)] at hF'c
  rw [hcA, card_image_intCast_add_image_intCast
    (injOn_intCast_of_subset_Ico (add_subset_Ico hA (hFB.trans hB)) (by grind))] at hF'
  exact ⟨F, hFB, hF'c, hF'⟩

/-- Let `A` be within `γ * min m n` of `Ico x (x + m)` and let `B ⊆ Ico y (y + n)` miss at most
`γ * min m n` of its points, with `γ ≤ 1 / 1600`. Then `m ≤ #A + γ * min m n`,
`n ≤ #B + γ * min m n`, the sets have at least `min m n / 2` elements each, and
`γ * min m n ≤ min #A #B / 800`. -/
lemma le_card_add_mul_min_of_card_symmDiff_le {γ : ℝ} (hγ : γ ≤ 1 / 1600) {x y : ℤ} {m n : ℕ}
    {A B : Finset ℤ} (hB : B ⊆ Ico y (y + n)) (hJB : #(Ico y (y + n) \ B) ≤ γ * min (m : ℝ) n)
    (hAI : #(A ∆ Ico x (x + m)) ≤ γ * min (m : ℝ) n) :
    m ≤ #A + γ * min (m : ℝ) n ∧ n ≤ #B + γ * min (m : ℝ) n ∧
      min (m : ℝ) n / 2 ≤ min (#A : ℝ) #B ∧ γ * min (m : ℝ) n ≤ 1 / 800 * min (#A : ℝ) #B := by
  obtain ⟨-, hIA⟩ := card_sdiff_le_and_card_sdiff_le_of_card_symmDiff_le hAI
  have hm : (m : ℝ) ≤ #(Ico x (x + m) \ A) + #A := by
    simpa using (Nat.cast_le (α := ℝ)).2 (card_le_card_sdiff_add_card (s := Ico x (x + m)) (t := A))
  have h := le_min (by linarith [min_le_left (m : ℝ) n] : (1 - γ) * min (m : ℝ) n ≤ #A)
    (by linarith [min_le_right (m : ℝ) n, card_Ico_sdiff_add_card hB] :
      (1 - γ) * min (m : ℝ) n ≤ #B)
  refine ⟨by linarith, by linarith [card_Ico_sdiff_add_card hB], ?_, ?_⟩ <;>
    nlinarith [(by positivity : (0 : ℝ) ≤ min (m : ℝ) n)]

/-- **Cauchy–Davenport in `ℤ`.** Nonempty finite sets of integers have `#A + #B - 1 ≤ #(A + B)`. -/
lemma card_add_card_sub_one_le_card_add {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    #A + #B - 1 ≤ (#(A + B) : ℝ) := by
  rw [sub_le_iff_le_add]
  exact_mod_cast Nat.sub_le_iff_le_add.1 (cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB)

/-- Let `0 < α ≤ 1` and `α * n ≤ m`. Let `A ⊆ Ico (x - R) (x + m + R)` be within `min m n / 1600` of
`Ico x (x + m)`, and let `B ⊆ Ico y (y + n)` contain `y` and `y + n - 1`, miss at most
`min m n / 1600` points of the interval and have at least `64 / (α / 2)` elements. Then some `F ⊆ B`
with at most `⌈64 / (α / 2)⌉₊ ^ 2 + 2 * ⌈64 / (α / 2)⌉₊ + 10` elements satisfies
`#A + #B - 1 ≤ #(A + F)`. -/
lemma exists_subset_card_le_card_add_card_sub_one_le_card_add_of_card_symmDiff_le {α : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) {x y : ℤ} {m n R : ℕ} {A B : Finset ℤ} (hαn : α * n ≤ m)
    (hA : A ⊆ Ico (x - R) (x + m + R)) (hAI : #(A ∆ Ico x (x + m)) ≤ 1 / 1600 * min (m : ℝ) n)
    (hB : B ⊆ Ico y (y + n)) (hyB : y ∈ B) (hyB' : y + n - 1 ∈ B)
    (hJB : #(Ico y (y + n) \ B) ≤ 1 / 1600 * min (m : ℝ) n) (hBc : 64 / (α / 2) ≤ #B) :
    ∃ F ⊆ B, #F ≤ ⌈64 / (α / 2)⌉₊ ^ 2 + 2 * ⌈64 / (α / 2)⌉₊ + 10 ∧
      #A + #B - 1 ≤ (#(A + F) : ℝ) := by
  obtain ⟨hm, hn, hmin, hkey⟩ := le_card_add_mul_min_of_card_symmDiff_le le_rfl hB hJB hAI
  obtain ⟨hAI', hIA'⟩ := card_sdiff_le_and_card_sdiff_le_of_card_symmDiff_le (hAI.trans hkey)
  rw [div_le_iff₀ (by positivity)] at hBc
  have hBn : (#B : ℝ) ≤ n := by exact_mod_cast card_le_of_subset_Ico hB
  have hαB : α / 2 * #B ≤ min (#A : ℝ) #B := by
    linarith [mul_le_mul_of_nonneg_left hBn hα.le,
      le_min hαn (mul_le_of_le_one_left (Nat.cast_nonneg n) hα₁)]
  obtain ⟨hA₂, hB₂⟩ := le_min_iff.1 (by linarith : (2 : ℝ) ≤ min (#A : ℝ) #B)
  obtain ⟨F, hFB, hFc, hF⟩ := exists_subset_card_le_add_le_card_add_of_card_sdiff_le_int
    (by positivity) le_rfl hA hB hyB hyB' (by exact_mod_cast hA₂) (by exact_mod_cast hB₂) hαB hIA'
    hAI' (by linarith) (by linarith) (by linarith)
  refine ⟨F, hFB, hFc, ?_⟩
  rify at hF
  linarith

/-- For intervals `Ico x (x + m)` and `Ico y (y + n)` with `α * n ≤ m ≤ α⁻¹ * n`, every `A` and `B`
within `γ * min m n` of them, with `B` inside its interval and containing its endpoints, have some
`F ⊆ B` with at most `c` elements and `#A + #B - 1 ≤ #(A + F)`. The sets `A` are restricted to a
window `Ico (x - R) (x + m + R)`. -/
def FewTranslatesInt (γ α : ℝ) (c : ℕ) : Prop :=
  ∀ (x y : ℤ) (m n R : ℕ) (B : Finset ℤ),
    α * n ≤ m → m ≤ α⁻¹ * n → B ⊆ Ico y (y + n) → y ∈ B → y + n - 1 ∈ B →
    #(Ico y (y + n) \ B) ≤ γ * min (m : ℝ) n →
    ∀ A ⊆ Ico (x - R) (x + m + R), #(A ∆ Ico x (x + m)) ≤ γ * min (m : ℝ) n →
      ∃ F ⊆ B, #F ≤ c ∧ #A + #B - 1 ≤ (#(A + F) : ℝ)

/-- `FewTranslatesInt` still holds for a smaller `γ`. -/
lemma FewTranslatesInt.mono {γ γ' α : ℝ} {c : ℕ} (h : FewTranslatesInt γ α c) (hγ : γ' ≤ γ) :
    FewTranslatesInt γ' α c := by
  intro x y m n R B h₁ h₂ h₃ h₄ h₅ h₆ A hA₁ hA₂
  exact h x y m n R B h₁ h₂ h₃ h₄ h₅ (by grw [h₆, hγ]) A hA₁ (by grw [hA₂, hγ])

/-- Theorem 5 of Bollobás, Leader and Tiba in the form used for Theorem 8: there is `γ > 0` such
that for every `α > 0` some `c` satisfies `FewTranslatesInt γ α c`. If `B` has at most `c` elements,
`F = B` works by the Cauchy–Davenport theorem in `ℤ`. Otherwise
`exists_subset_card_le_card_add_card_sub_one_le_card_add_of_card_symmDiff_le` applies with `min α 1`
in place of `α`. -/
lemma exists_fewTranslatesInt : ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℕ, FewTranslatesInt γ α c := by
  refine ⟨1 / 1600, by norm_num, ?_⟩
  intro α hα
  refine ⟨⌈64 / (min α 1 / 2)⌉₊ ^ 2 + 2 * ⌈64 / (min α 1 / 2)⌉₊ + 10, ?_⟩
  intro x y m n R B hαn hαm hB hyB hyB' hJB A hA hAI
  by_cases hBc : #B ≤ ⌈64 / (min α 1 / 2)⌉₊ ^ 2 + 2 * ⌈64 / (min α 1 / 2)⌉₊ + 10
  · obtain ⟨hm, -, -, -⟩ := le_card_add_mul_min_of_card_symmDiff_le le_rfl hB hJB hAI
    have hn : 1 ≤ n := by grind [mem_Ico.1 (hB hyB)]
    refine ⟨B, subset_rfl, hBc, card_add_card_sub_one_le_card_add (card_pos.1 ?_) ⟨y, hyB⟩⟩
    rify at hn ⊢
    nlinarith [min_le_left (m : ℝ) n]
  refine exists_subset_card_le_card_add_card_sub_one_le_card_add_of_card_symmDiff_le
    (lt_min hα one_pos) (min_le_right α 1) (by grw [min_le_left α 1, hαn]) hA hAI hB hyB hyB' hJB ?_
  grw [Nat.le_ceil (64 / (min α 1 / 2))]
  norm_cast
  grind

end LargeSumsetsFromSubsets
