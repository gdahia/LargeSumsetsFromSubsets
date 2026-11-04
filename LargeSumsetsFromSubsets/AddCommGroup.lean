/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.MediumSizedSubsets.PopularSums

/-!
# Large sumsets from medium-sized subsets in abelian groups

Theorem 2 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*. Let `A` and `B`
be finite nonempty subsets of an abelian group, let `σ, ε > 0`, and let `1 ≤ c₁ ≤ #A` and
`1 ≤ c₂ ≤ #B` satisfy `c₁ * c₂ > c σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with more
than `(1 - ε) * #A` and `(1 - ε) * #B` elements such that the sets `A'` and `B'` of `c₁` points of
`A₀` and `c₂` points of `B₀` chosen independently and uniformly at random satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`.

The theorem follows from `MediumSizedSubsets.exists_subset_min_le_expectCardAdd` with
`K = 2 * max σ 1` and `min ε 1 / 2` in place of `ε`, which turn its inequalities into strict ones.
Choosing one good pair of samples of a common size of order `√(max #A #B)` gives a deterministic
form.

## Main definitions

* `LargeSumsetsFromSubsets.MediumSizedSubsets.c σ ε`: the constant `c(σ, ε)` of Theorem 2.

## Main statements

* `LargeSumsetsFromSubsets.exists_subset_min_lt_expect_card_add`: Theorem 2 with the constant
  `MediumSizedSubsets.c σ ε`.
* `LargeSumsetsFromSubsets.exists_forall_exists_subset_min_lt_expect_card_add`: Theorem 2 with a
  constant that exists.
* `LargeSumsetsFromSubsets.exists_subset_card_le_mul_sqrt_min_le_card_add`: subsets `A' ⊆ A₀` and
  `B' ⊆ B₀` with at most `8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max #A #B)` elements and
  `#(A' + B') ≥ min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

open Finset MediumSizedSubsets

open scoped BigOperators Pointwise

noncomputable section

/-- The constant `c(σ, ε)` of Theorem 2 of Bollobás, Leader and Tiba: the constant
`36 / (ε * alpha K ε)` of `MediumSizedSubsets.exists_subset_min_le_expectCardAdd` for
`K = 2 * max σ 1` and `min ε 1 / 2` in place of `ε`. -/
def MediumSizedSubsets.c (σ ε : ℝ) : ℝ :=
  36 / (min ε 1 / 2 * alpha (2 * max σ 1) (min ε 1 / 2))

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Large sumsets from medium-sized subsets** (Bollobás, Leader and Tiba, Theorem 2). Let `A` and
`B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` satisfy
`c₁ * c₂ > c σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with more than `(1 - ε) * #A` and
`(1 - ε) * #B` elements such that, for `c₁` points of `A₀` and `c₂` points of `B₀` chosen
independently and uniformly at random, with repetitions allowed, the sets `A'` and `B'` of chosen
points satisfy `𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
theorem exists_subset_min_lt_expect_card_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B) (hc : c σ ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
      (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
        𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
          (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) := by
  have hK : 1 ≤ 2 * max σ 1 := by linarith [le_max_right σ 1]
  have hε' : min ε 1 / 2 < ε := by linarith [min_le_left ε 1]
  have hσK : σ < 2 * max σ 1 := by linarith [le_max_left σ 1, le_max_right σ 1]
  rw [c, div_mul_eq_mul_div, div_lt_iff₀ (mul_pos (by positivity) (alpha_pos hK (by positivity)))]
    at hc
  obtain ⟨X, hXA, Y, hYB, hX, hY, hXcard, hYcard, hE⟩ :=
    exists_subset_min_le_expectCardAdd (ε := min ε 1 / 2) hK (by positivity)
      (by linarith [min_le_right ε 1]) hA hB hc₁ hc₁A hc₂ hc₂B (by linarith)
  refine ⟨X, hXA, Y, hYB, hX, hY, ?_, ?_, hE.trans_lt' ?_⟩
  · grw [← hXcard]
    gcongr
    linarith
  · grw [← hYcard]
    gcongr
    linarith
  · exact min_lt_min (min_lt_min (mul_lt_mul_of_pos_right (by linarith)
      (Nat.cast_pos.2 (hX.add hY).card_pos)) (mul_lt_mul_of_pos_right hσK
        (Nat.cast_pos.2 hX.card_pos))) (mul_lt_mul_of_pos_right hσK (Nat.cast_pos.2 hY.card_pos))

/-- **Theorem 2** of Bollobás, Leader and Tiba. For `σ, ε > 0` there is `c` with the following
property. Let `A` and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and
`1 ≤ c₂ ≤ #B` satisfy `c₁ * c₂ > c * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
`#A₀ > (1 - ε) * #A` and `#B₀ > (1 - ε) * #B` such that, for `c₁` points of `A₀` and `c₂` points of
`B₀` chosen independently and uniformly at random, the sets `A'` and `B'` of chosen points satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (min (σ * #A₀) (σ * #B₀))`. -/
theorem exists_forall_exists_subset_min_lt_expect_card_add {σ ε : ℝ} (hσ : 0 < σ)
    (hε : 0 < ε) :
    ∃ c : ℝ, ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G} {c₁ c₂ : ℕ},
      A.Nonempty → B.Nonempty → 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B →
      c * max (#A : ℝ) #B < c₁ * c₂ →
      ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
        (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
        min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
          𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
            (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) :=
  ⟨c σ ε, fun hA hB hc₁ hc₁A hc₂ hc₂B hc ↦
    exists_subset_min_lt_expect_card_add hσ hε hA hB hc₁ hc₁A hc₂ hc₂B hc⟩

/-! ### The deterministic form -/

/-- The common size `⌈√(max 1 (c σ ε) * M)⌉ + 1` of the two samples, where `M` is the size of the
larger set. -/
private def sampleSize (σ ε : ℝ) (M : ℕ) : ℕ :=
  ⌈√(max 1 (c σ ε) * M)⌉₊ + 1

/-- Some pair of samples attains the expectation of `exists_subset_min_lt_expect_card_add`. -/
private lemma exists_subset_card_le_min_le_card_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B) (hc : c σ ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, ∃ A' ⊆ A₀, ∃ B' ⊆ B₀,
      (1 - ε) * #A ≤ #A₀ ∧ (1 - ε) * #B ≤ #B₀ ∧ #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) ≤ #(A' + B') := by
  obtain ⟨A₀, hA₀A, B₀, hB₀B, hA₀, hB₀, hA₀card, hB₀card, hE⟩ :=
    exists_subset_min_lt_expect_card_add hσ hε hA hB hc₁ hc₁A hc₂ hc₂B hc
  have : Nonempty A₀ := hA₀.to_subtype
  have : Nonempty B₀ := hB₀.to_subtype
  obtain ⟨⟨f, g⟩, -, hfg⟩ := exists_lt_of_lt_expect univ_nonempty hE
  exact ⟨A₀, hA₀A, B₀, hB₀B, _, by simp [image_subset_iff], _, by simp [image_subset_iff],
    hA₀card.le, hB₀card.le, card_image_le.trans (by simp), card_image_le.trans (by simp), hfg.le⟩

private lemma one_le_sampleSize (σ ε : ℝ) (M : ℕ) : 1 ≤ sampleSize σ ε M := by
  simp [sampleSize]

/-- The two samples are large enough for `exists_subset_min_lt_expect_card_add`. -/
private lemma mul_lt_sampleSize_sq (σ ε : ℝ) (M : ℕ) : c σ ε * M < sampleSize σ ε M ^ 2 := by
  rw [sampleSize]
  push_cast
  nlinarith [le_max_left 1 (c σ ε), Real.sq_sqrt (by positivity : 0 ≤ max 1 (c σ ε) * M),
    Nat.le_ceil √(max 1 (c σ ε) * M), Real.sqrt_nonneg (max 1 (c σ ε) * M),
    mul_le_mul_of_nonneg_right (le_max_right 1 (c σ ε)) (Nat.cast_nonneg (α := ℝ) M)]

/-- The common sample size is at most `(max 1 (c σ ε) + 2) * √M`. -/
private lemma sampleSize_le_add_two_mul_sqrt (σ ε : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    sampleSize σ ε M ≤ (max 1 (c σ ε) + 2) * √M := by
  have hc := le_max_left 1 (c σ ε)
  rw [sampleSize, Real.sqrt_mul (by linarith)]
  push_cast
  linarith [Real.one_le_sqrt.2 (by exact_mod_cast hM : (1 : ℝ) ≤ M),
    Nat.ceil_lt_add_one (by positivity : 0 ≤ √(max 1 (c σ ε)) * √M),
    mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hc)) (Real.sqrt_nonneg M)]

/-- The common sample size is at most `8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √M`. -/
private lemma sampleSize_le_mul_sqrt {σ : ℝ} (hσ : 0 ≤ σ) (ε : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    sampleSize σ ε M ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √M := by
  grw [sampleSize_le_add_two_mul_sqrt σ ε hM]
  gcongr
  nlinarith [le_max_left 1 (c σ ε)]

/-- A set too small to be sampled already fits, with room to spare, under the bound
`8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √M`. -/
private lemma mul_add_one_le_mul_sqrt {σ : ℝ} (hσ : 0 ≤ σ) (ε : ℝ) {N M : ℕ} (hM : 1 ≤ M)
    (hN : N < sampleSize σ ε M) : σ * N + 1 ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √M := by
  have hc := le_max_left 1 (c σ ε)
  have hM' : 1 ≤ √M := Real.one_le_sqrt.2 (by exact_mod_cast hM)
  nlinarith [mul_le_mul_of_nonneg_left ((Nat.cast_le.2 hN.le).trans
      (sampleSize_le_add_two_mul_sqrt σ ε hM)) hσ,
    mul_le_mul_of_nonneg_right (by nlinarith : σ * (max 1 (c σ ε) + 2) + 1 ≤
      8 * (max 1 (c σ ε) + σ + 1) ^ 2) (Real.sqrt_nonneg M)]

/-- The unbalanced case of `exists_subset_card_le_mul_sqrt_min_le_card_add`: when `A` is too small
to be sampled, `A` itself serves as its own medium-sized subset and a subset of `B` of the size of
the target sumset serves as the other one. -/
private lemma exists_subset_card_le_mul_sqrt_min_le_card_add_of_lt {σ ε : ℝ} (hσ : 0 < σ)
    (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty) (hAB : #A < sampleSize σ ε (max #A #B)) :
    ∃ B' ⊆ B, #B' ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max (#A : ℝ) #B) ∧
      min (min ((1 - ε) * #(A + B)) (σ * #A)) (σ * #B) ≤ #(A + B') := by
  have hceil : ⌈σ * #A⌉₊ ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max (#A : ℝ) #B) := by
    rw [← Nat.cast_max]
    exact (Nat.ceil_lt_add_one (by positivity)).le.trans (mul_add_one_le_mul_sqrt
      hσ.le ε (hA.card_pos.trans_le (le_max_left _ _)) hAB)
  obtain hB | hB := le_or_gt ⌈σ * #A⌉₊ #B
  · obtain ⟨B', hB'B, hB'⟩ := exists_subset_card_eq hB
    refine ⟨B', hB'B, hB' ▸ hceil, min_le_of_left_le (min_le_of_right_le ?_)⟩
    grw [Nat.le_ceil (σ * #A), ← hB']
    exact_mod_cast card_le_card_add_left hA
  · refine ⟨B, subset_rfl, (Nat.cast_le.2 hB.le).trans hceil,
      min_le_of_left_le (min_le_of_left_le ?_)⟩
    exact mul_le_of_le_one_left (by positivity) (by linarith)

/-- **Large sumsets from medium-sized subsets**, deterministic form. There are `A₀ ⊆ A`,
`B₀ ⊆ B`, `A' ⊆ A₀` and `B' ⊆ B₀` such that `A₀` and `B₀` contain all but an `ε` proportion of `A`
and `B`, the sets `A'` and `B'` have at most `8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max #A #B)`
elements, and `#(A' + B') ≥ min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
lemma exists_subset_card_le_mul_sqrt_min_le_card_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, ∃ A' ⊆ A₀, ∃ B' ⊆ B₀, (1 - ε) * #A ≤ #A₀ ∧ (1 - ε) * #B ≤ #B₀ ∧
      #A' ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max (#A : ℝ) #B) ∧
      #B' ≤ 8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max (#A : ℝ) #B) ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) ≤ #(A' + B') := by
  have hr : sampleSize σ ε (max #A #B) ≤
      8 * (max 1 (c σ ε) + σ + 1) ^ 2 * √(max (#A : ℝ) #B) := by
    rw [← Nat.cast_max]
    exact sampleSize_le_mul_sqrt hσ.le ε (hA.card_pos.trans_le (le_max_left _ _))
  obtain hrA | hrA := le_or_gt (sampleSize σ ε (max #A #B)) #A
  · obtain hrB | hrB := le_or_gt (sampleSize σ ε (max #A #B)) #B
    · obtain ⟨A₀, hA₀, B₀, hB₀, A', hA', B', hB', hA₀card, hB₀card, hA'c, hB'c, hsum⟩ :=
        exists_subset_card_le_min_le_card_add hσ hε hA hB (one_le_sampleSize σ ε _) hrA
          (one_le_sampleSize σ ε _) hrB (by simpa [sq] using mul_lt_sampleSize_sq σ ε (max #A #B))
      exact ⟨A₀, hA₀, B₀, hB₀, A', hA', B', hB', hA₀card, hB₀card,
        (Nat.cast_le.2 hA'c).trans hr, (Nat.cast_le.2 hB'c).trans hr, hsum⟩
    · obtain ⟨A', hA'A, hA'bound, hsum⟩ :=
        exists_subset_card_le_mul_sqrt_min_le_card_add_of_lt hσ hε hB (B := A) (by rwa [max_comm])
      refine ⟨A, subset_rfl, B, subset_rfl, A', hA'A, B, subset_rfl,
        mul_le_of_le_one_left (by positivity) (by linarith),
        mul_le_of_le_one_left (by positivity) (by linarith), by rwa [max_comm (#B : ℝ)] at hA'bound,
        (Nat.cast_le.2 hrB.le).trans hr, ?_⟩
      simpa [add_comm, min_comm, min_left_comm, min_assoc] using hsum
  · obtain ⟨B', hB'B, hB'bound, hsum⟩ :=
      exists_subset_card_le_mul_sqrt_min_le_card_add_of_lt hσ hε hA hrA
    exact ⟨A, subset_rfl, B, subset_rfl, A, subset_rfl, B', hB'B,
      mul_le_of_le_one_left (by positivity) (by linarith),
      mul_le_of_le_one_left (by positivity) (by linarith), (Nat.cast_le.2 hrA.le).trans hr,
      hB'bound, hsum⟩

end

end LargeSumsetsFromSubsets
