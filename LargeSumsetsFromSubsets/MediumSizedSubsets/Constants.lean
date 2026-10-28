/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticRemoval

/-!
# The constants of the Bollobás–Leader–Tiba argument

For a doubling parameter `K ≥ 1` and an error `0 < ε ≤ 1` the proof of the medium-sized-subset
theorem uses six constants, defined here together with the handful of inequalities relating them:

* `bltCap K = 100 * K ^ 3` caps the sumset term of the potential function;
* `bltPenalty K ε` is the price of deleting one element;
* `bltRho K ε` is the proportion of elements the cleanup steps may delete;
* `bltDelta K ε` is the proportion of pairs allowed to have an unpopular sum; it is small enough
  for the arithmetic removal lemma at the parameters produced by `bltCap` and `bltRho`;
* `bltAlpha K ε` is the popularity threshold;
* `bltSampleConst K ε` is the constant of the theorem itself.

Each constant depends only on the previous ones, so the definitions are not circular. The numerals
in the definitions are natural numbers, so that the definitions contain no proofs.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

noncomputable section

/-- The cap on the sumset term of the potential function. -/
def bltCap (K : ℝ) : ℝ := (100 : ℕ) * K ^ 3

/-- The price, in the potential function, of deleting one element. -/
def bltPenalty (K ε : ℝ) : ℝ := 4 * bltCap K / ε

/-- The proportion of elements that the cleanup steps are allowed to delete. -/
def bltRho (K ε : ℝ) : ℝ := ε ^ 2 / ((1000 : ℕ) * bltCap K)

/-- The proportion of pairs allowed to have an unpopular sum. -/
def bltDelta (K ε : ℝ) : ℝ :=
  min (min (1 / (2 : ℕ)) (bltRho K ε / (8 : ℕ)))
    (ArithmeticRemoval.removalConst ((16 : ℕ) * bltCap K ^ 7) (bltRho K ε / bltCap K))

/-- The popularity threshold: a sum is popular when it has at least `bltAlpha K ε * min #X #Y`
representations. -/
def bltAlpha (K ε : ℝ) : ℝ := bltDelta K ε / ((36 : ℕ) * K)

/-- The constant of the medium-sized-subset theorem. -/
def bltSampleConst (K ε : ℝ) : ℝ := (36 : ℕ) / (ε * bltAlpha K ε)

variable {K ε : ℝ}

/-- The cap is at least `100`. -/
lemma hundred_le_bltCap (hK : 1 ≤ K) : 100 ≤ bltCap K := by
  unfold bltCap
  push_cast
  linarith [one_le_pow₀ (n := 3) hK]

/-- The cap is positive. -/
lemma bltCap_pos (hK : 1 ≤ K) : 0 < bltCap K := by
  linarith [hundred_le_bltCap hK]

/-- The deletion price is positive. -/
lemma bltPenalty_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < bltPenalty K ε :=
  div_pos (mul_pos (by norm_num) (bltCap_pos hK)) hε

/-- The deletion proportion is positive. -/
lemma bltRho_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < bltRho K ε :=
  div_pos (pow_pos hε 2) (mul_pos (by norm_num) (bltCap_pos hK))

/-- `bltRho` is far smaller than `ε`, which is what makes the cleanup steps cheap. -/
lemma bltRho_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) : bltRho K ε ≤ ε / 1000 := by
  unfold bltRho
  push_cast
  rw [div_le_div_iff₀ (by nlinarith [hundred_le_bltCap hK]) (by norm_num)]
  nlinarith [hundred_le_bltCap hK]

/-- The doubling constant handed to the arithmetic removal lemma is nonnegative. -/
private lemma removalDoubling_nonneg (hK : 1 ≤ K) : (0 : ℝ) ≤ 16 * bltCap K ^ 7 :=
  mul_nonneg (by norm_num) (pow_nonneg (bltCap_pos hK).le 7)

/-- The density parameter is positive. -/
lemma bltDelta_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < bltDelta K ε := by
  unfold bltDelta
  apply lt_min (lt_min (by norm_num) (div_pos (bltRho_pos hK hε) (by norm_num)))
  exact ArithmeticRemoval.removalConst_pos (removalDoubling_nonneg hK)
    (div_pos (bltRho_pos hK hε) (bltCap_pos hK))

/-- The density parameter is at most `1 / 2`. -/
lemma bltDelta_le_half : bltDelta K ε ≤ 1 / 2 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- The density parameter is at most an eighth of the deletion proportion. -/
lemma eight_mul_bltDelta_le_bltRho : 8 * bltDelta K ε ≤ bltRho K ε := by
  have : bltDelta K ε ≤ bltRho K ε / 8 := (min_le_left _ _).trans (min_le_right _ _)
  linarith

/-- The density parameter is below the threshold of the arithmetic removal lemma. -/
lemma bltDelta_le_removalConst :
    bltDelta K ε ≤ ArithmeticRemoval.removalConst (16 * bltCap K ^ 7) (bltRho K ε / bltCap K) :=
  min_le_right _ _

/-- The popularity threshold is positive. -/
lemma bltAlpha_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < bltAlpha K ε :=
  div_pos (bltDelta_pos hK hε) (by push_cast; linarith)

/-- The sampling constant is positive. -/
lemma bltSampleConst_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < bltSampleConst K ε :=
  div_pos (by norm_num) (mul_pos hε (bltAlpha_pos hK hε))

/-- The defining relation between the sampling constant and the popularity threshold. -/
lemma mul_bltSampleConst_mul_bltAlpha (hK : 1 ≤ K) (hε : 0 < ε) :
    ε * (bltSampleConst K ε * bltAlpha K ε) = 36 := by
  unfold bltSampleConst
  push_cast
  field_simp [(bltAlpha_pos hK hε).ne']

/-- A product `κ` of sample sizes above `bltSampleConst K ε * m` satisfies
`36 * m ≤ ε * bltAlpha K ε * κ`. -/
lemma thirtySix_mul_le_mul_bltAlpha_mul (hK : 1 ≤ K) (hε : 0 < ε) {m κ : ℝ}
    (hκ : bltSampleConst K ε * m ≤ κ) : 36 * m ≤ ε * (bltAlpha K ε * κ) := by
  rw [← mul_bltSampleConst_mul_bltAlpha hK hε]
  linarith [mul_le_mul_of_nonneg_left hκ (mul_pos hε (bltAlpha_pos hK hε)).le]

/-- The product of the sampling constant and the density parameter. -/
lemma mul_bltDelta_mul_bltSampleConst (hK : 1 ≤ K) (hε : 0 < ε) :
    ε * (bltDelta K ε * bltSampleConst K ε) = 1296 * K := by
  unfold bltSampleConst bltAlpha
  field_simp [(bltDelta_pos hK hε).ne', (by positivity : K ≠ 0)]
  ring

/-- Division-free form of the definition of `bltAlpha`. -/
lemma mul_bltAlpha_eq_bltDelta (hK : 1 ≤ K) : 36 * (K * bltAlpha K ε) = bltDelta K ε := by
  unfold bltAlpha
  push_cast
  field_simp [(by positivity : K ≠ 0)]

/-- The penalty of deleting a `bltRho` proportion of elements is a small multiple of `ε`. -/
lemma bltPenalty_mul_bltRho (hK : 1 ≤ K) (hε : 0 < ε) :
    bltPenalty K ε * bltRho K ε = ε / 250 := by
  unfold bltPenalty bltRho
  field_simp [(bltCap_pos hK).ne']
  ring

end

end LargeSumsetsFromSubsets
