/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.MediumSizedSubsets.Constants
public import LargeSumsetsFromSubsets.MediumSizedSubsets.Sampling
import LargeSumsetsFromSubsets.Cleanup
import LargeSumsetsFromSubsets.MediumSizedSubsets.Potential

/-!
# Large sumsets from medium-sized subsets

This file proves Theorem 2 of Bollobás, Leader and Tiba's *Large sumsets from medium-sized
subsets*, in four forms:

* `exists_subset_min_le_expectSumset`, the normalised form, for a doubling parameter `K ≥ 1` and
  an error `0 < ε ≤ 1`;
* `exists_subset_min_lt_expect_card_add`, the original form with the explicit constant
  `originalBltConstant σ ε`, deduced from the normalised form by replacing `σ` with
  `2 * max σ 1 ≥ 1` and `ε` with `min ε 1 / 2 ∈ (0, 1]`; the two replacements turn the
  inequalities of the normalised form into the strict ones asked for here;
* `exists_forall_exists_subset_min_lt_expect_card_add`, the original form with an unspecified
  constant;
* `exists_subset_card_le_mul_sqrt_min_le_card_add`, the symmetric square-root form, obtained by
  specialising to `c₁ = c₂ = bltSampleSize σ ε (max #A #B)`, of order `√(max #A #B)`, and
  replacing the expectation by a single good sample. Sampling requires this common size to be at
  most both `#A` and `#B`; when it is not, one of the two sets is already smaller than the bound
  asked for, and the whole of it, or a subset of the other set of exactly the required size, does
  the job.

The normalised form is proved by a penalised-minimality argument. Among all pairs of nonempty
subsets `X ⊆ A` and `Y ⊆ B` one minimises the potential of
`LargeSumsetsFromSubsets.exists_potential_minimiser`; the penalty forces the minimiser to be
large. Were the sampling estimate to fail for the minimiser, the popular sums, those with at
least `bltAlpha K ε * min #X #Y` representations, would be few and would still carry almost every
pair, so one of the two cleanup lemmas of `LargeSumsetsFromSubsets.Cleanup` would produce a
pair of strictly smaller potential.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

open Finset

open scoped BigOperators Pointwise

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-! ### Elementary inequalities -/

/-- The elementary inequality behind the estimate for a popular sum. -/
private lemma one_sub_div_four_le_div {ε xy t : ℝ} (hε : 0 < ε) (hxy : 0 < xy) (ht₀ : 0 ≤ t)
    (ht : 36 * xy ≤ ε * t) : 1 - ε / 4 ≤ t / (9 * xy + t) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The elementary inequality behind the estimate for the unpopular sums. -/
private lemma mul_add_le_mul {K α n m κ : ℝ} (hK : 0 ≤ K) (hn : 0 ≤ n) (hnm : n ≤ m)
    (hκ : 36 * m ≤ α * κ) :
    K * n * (9 * (n * m) + α * n * κ) ≤ 36 * (K * α) * (n * m) * κ := by
  have hKn : 0 ≤ K * n := mul_nonneg hK hn
  nlinarith [mul_le_mul_of_nonneg_left hnm (mul_nonneg hKn (by linarith : 0 ≤ α * κ)),
    mul_le_mul_of_nonneg_left (by linarith : 36 * n ≤ α * κ) (mul_nonneg hKn (hn.trans hnm)),
    mul_nonneg (mul_nonneg hKn (hn.trans hnm)) (by linarith : 0 ≤ α * κ)]

/-- The arithmetic of the covering bound: if `s * (x * y) ≤ 2 * p ^ 3` with
`0 ≤ p < 2 * K * min x y`, then `s < 16 * K ^ 3 * min x y`. -/
private lemma lt_of_mul_le_two_mul_pow_three {s x y p K : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hpK : p < 2 * K * min x y) (h : s * (x * y) ≤ 2 * p ^ 3) :
    s < 16 * K ^ 3 * min x y := by
  have hn : 0 < min x y := lt_min hx hy
  refine lt_of_mul_lt_mul_right ?_ (sq_nonneg (min x y))
  linarith [pow_lt_pow_left₀ hpK hp three_ne_zero, mul_le_mul_of_nonneg_left
    (mul_le_mul (min_le_left x y) (min_le_right x y) hn.le hx.le) hs]

/-- A set `X` with `(1 - ε / 4) * #A ≤ #X`, for `ε ≤ 1`, satisfies `3 * c ≤ 4 * #X` for every
`c ≤ #A`. -/
private lemma three_mul_le_four_mul {ε : ℝ} {a x c : ℕ} (hε1 : ε ≤ 1) (hca : c ≤ a)
    (hx : (1 - ε / 4) * a ≤ x) : 3 * c ≤ 4 * x := by
  have : (3 * c : ℝ) ≤ 4 * x := by
    linarith [mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) a),
      (Nat.cast_le.2 hca : (c : ℝ) ≤ a)]
  exact_mod_cast this

/-! ### Popular sums -/

open scoped Classical in
/-- The popular sums: those with at least `bltAlpha K ε * min #X #Y` representations. -/
noncomputable def popularSums (K ε : ℝ) (X Y : Finset G) : Finset G :=
  (X + Y).filter fun s => bltAlpha K ε * min (#X : ℝ) #Y ≤ Sampling.reprCount X Y s

/-- The popular sums lie in the sumset. -/
lemma popularSums_subset (K ε : ℝ) (X Y : Finset G) : popularSums K ε X Y ⊆ X + Y :=
  filter_subset _ _

/-- A sum is popular when it has at least `bltAlpha K ε * min #X #Y` representations. -/
lemma mem_popularSums {K ε : ℝ} {X Y : Finset G} {s : G} :
    s ∈ popularSums K ε X Y ↔
      s ∈ X + Y ∧ bltAlpha K ε * min (#X : ℝ) #Y ≤ Sampling.reprCount X Y s := by
  unfold popularSums
  exact mem_filter

/-- The bad pairs are counted by the representations of the sums outside `P`. -/
private lemma card_badPairs_eq_sum_reprCount (X Y P : Finset G) :
    #(Cleanup.badPairs X Y P) = ∑ s ∈ (X + Y) \ P, Sampling.reprCount X Y s := by
  rw [Sampling.sum_reprCount, Cleanup.badPairs]
  congr 1
  ext ⟨u, v⟩
  simp only [mem_filter, mem_product, mem_sdiff]
  exact ⟨fun ⟨⟨hu, hv⟩, hP⟩ ↦ ⟨⟨hu, hv⟩, add_mem_add hu hv, hP⟩, fun ⟨h, _, hP⟩ ↦ ⟨h, hP⟩⟩

/-- Every pair of `X ×ˢ Y` either has its sum in `P` or is bad. -/
private lemma sum_reprCount_add_card_badPairs (X Y P : Finset G) :
    ∑ s ∈ P, Sampling.reprCount X Y s + #(Cleanup.badPairs X Y P) = #X * #Y := by
  rw [Sampling.sum_reprCount, Cleanup.badPairs, card_filter_add_card_filter_not, card_product]

/-- If fewer than `2 * K * min #X #Y` sums carry all but a `δ ≤ 1 / 2` proportion of the pairs,
then the sizes of `X` and `Y` are within a factor `4 * K` of each other. -/
private lemma max_lt_four_mul_min {X Y P : Finset G} {K δ : ℝ} (hX : X.Nonempty)
    (hY : Y.Nonempty) (hδ : δ ≤ 1 / 2) (hP : (#P : ℝ) < 2 * K * min (#X : ℝ) #Y)
    (hbad : (#(Cleanup.badPairs X Y P) : ℝ) ≤ δ * (#X * #Y)) :
    max (#X : ℝ) #Y < 4 * K * min (#X : ℝ) #Y := by
  have hn : 0 < min (#X : ℝ) #Y := by positivity
  have hsum : (∑ s ∈ P, Sampling.reprCount X Y s : ℝ) ≤ #P * min (#X : ℝ) #Y := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun s _ ↦ le_min
      (by exact_mod_cast Sampling.reprCount_le_left X Y s)
      (by exact_mod_cast Sampling.reprCount_le_right X Y s)
  have hsplit : (∑ s ∈ P, Sampling.reprCount X Y s : ℝ) + #(Cleanup.badPairs X Y P) = #X * #Y := by
    exact_mod_cast sum_reprCount_add_card_badPairs X Y P
  refine lt_of_mul_lt_mul_left ?_ hn.le
  linarith [min_mul_max (#X : ℝ) #Y, mul_lt_mul_of_pos_right hP hn,
    mul_le_mul_of_nonneg_right hδ (by positivity : (0 : ℝ) ≤ #X * #Y)]

section Sampling

variable {K ε : ℝ} {X Y : Finset G} {c₁ c₂ : ℕ}

/-- A popular sum is seen by the two samples with probability at least `1 - ε / 4`. -/
private lemma one_sub_div_four_le_hitProb (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂) {s : G}
    (hs : s ∈ popularSums K ε X Y) : 1 - ε / 4 ≤ Sampling.hitProb X Y c₁ c₂ s := by
  obtain ⟨hs, hr⟩ := mem_popularSums.1 hs
  refine (one_sub_div_four_le_div hε (by positivity) (by positivity) ?_).trans
    (Sampling.div_le_hitProb hs hc₁ hc₂ hkX hkY)
  rw [← min_mul_max (#X : ℝ) #Y]
  linarith [mul_le_mul_of_nonneg_left (thirtySix_mul_le_mul_bltAlpha_mul hK hε hκ)
      (by positivity : (0 : ℝ) ≤ min (#X : ℝ) #Y),
    mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ ε * (c₁ * c₂))]

/-- The expected size of the sumset of the samples is at least `1 - ε / 4` times the number of
popular sums. -/
private lemma mul_card_popularSums_le_expectSumset (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂) :
    (1 - ε / 4) * #(popularSums K ε X Y) ≤ Sampling.expectSumset X Y c₁ c₂ := by
  rw [Sampling.expectSumset_eq_sum_hitProb, mul_comm, ← nsmul_eq_mul, ← sum_const]
  exact (sum_le_sum fun s hs ↦ one_sub_div_four_le_hitProb hK hε hX hY hc₁ hc₂ hkX hkY hκ hs).trans
    (sum_le_sum_of_subset_of_nonneg (popularSums_subset K ε X Y) fun s _ _ ↦
      Sampling.hitProb_nonneg X Y c₁ c₂ s)

/-- An unpopular sum `s ∈ X + Y` is seen by the two samples with probability at least its number
of representations times `c₁ * c₂ / (9 * #X * #Y + bltAlpha K ε * min #X #Y * c₁ * c₂)`. -/
private lemma reprCount_mul_div_le_hitProb (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) {s : G} (hs : s ∈ X + Y) (hsP : s ∉ popularSums K ε X Y) :
    Sampling.reprCount X Y s * (c₁ * c₂ / (9 * (#X * #Y) + bltAlpha K ε * min (#X : ℝ) #Y *
      (c₁ * c₂))) ≤ Sampling.hitProb X Y c₁ c₂ s := by
  have hα := bltAlpha_pos hK hε
  have hr : (Sampling.reprCount X Y s : ℝ) < bltAlpha K ε * min (#X : ℝ) #Y := by
    simpa [mem_popularSums, hs] using hsP
  refine le_trans ?_ (Sampling.div_le_hitProb hs hc₁ hc₂ hkX hkY)
  rw [← mul_div_assoc]
  gcongr

/-- The expected size of the sumset of the samples is at least the number of bad pairs times
`c₁ * c₂ / (9 * #X * #Y + bltAlpha K ε * min #X #Y * c₁ * c₂)`. -/
private lemma card_badPairs_mul_div_le_expectSumset (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) :
    #(Cleanup.badPairs X Y (popularSums K ε X Y)) * (c₁ * c₂ / (9 * (#X * #Y) +
      bltAlpha K ε * min (#X : ℝ) #Y * (c₁ * c₂))) ≤ Sampling.expectSumset X Y c₁ c₂ := by
  rw [card_badPairs_eq_sum_reprCount, Nat.cast_sum, sum_mul, Sampling.expectSumset_eq_sum_hitProb]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (sdiff_subset (t := popularSums K ε X Y))
    fun s _ _ ↦ Sampling.hitProb_nonneg X Y c₁ c₂ s)
  apply sum_le_sum
  intro s hs
  obtain ⟨hs, hsP⟩ := mem_sdiff.1 hs
  exact reprCount_mul_div_le_hitProb hK hε hX hY hc₁ hc₂ hkX hkY hs hsP

/-- If the sampling estimate fails, there are fewer than `2 * K * min #X #Y` popular sums. -/
private lemma card_popularSums_lt (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂)
    (hE : Sampling.expectSumset X Y c₁ c₂ < K * min (#X : ℝ) #Y) :
    (#(popularSums K ε X Y) : ℝ) < 2 * K * min (#X : ℝ) #Y := by
  have hKn : 0 < K * min (#X : ℝ) #Y := mul_pos (by linarith) (by positivity)
  by_contra! h
  linarith [mul_card_popularSums_le_expectSumset hK hε hX hY hc₁ hc₂ hkX hkY hκ,
    mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε / 4),
    mul_le_mul_of_nonneg_right hε1 hKn.le]

/-- If the sampling estimate fails, the popular sums do not exhaust the sumset. -/
private lemma card_popularSums_lt_mul_card_add (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂)
    (hE : Sampling.expectSumset X Y c₁ c₂ < (1 - ε) * #(X + Y)) :
    (#(popularSums K ε X Y) : ℝ) < (1 - ε / 2) * #(X + Y) := by
  have hS : (0 : ℝ) ≤ #(X + Y) := by positivity
  by_contra! h
  linarith [mul_card_popularSums_le_expectSumset hK hε hX hY hc₁ hc₂ hkX hkY hκ,
    mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε / 4), mul_nonneg hε.le hS,
    mul_nonneg (mul_nonneg hε.le hε.le) hS]

/-- If the sampling estimate fails, at most a `bltDelta K ε` proportion of the pairs have an
unpopular sum. -/
private lemma card_badPairs_popularSums_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂)
    (hE : Sampling.expectSumset X Y c₁ c₂ < K * min (#X : ℝ) #Y) :
    (#(Cleanup.badPairs X Y (popularSums K ε X Y)) : ℝ) ≤ bltDelta K ε * (#X * #Y) := by
  have hα := bltAlpha_pos hK hε
  by_contra! h
  refine hE.not_ge (le_trans ?_ (card_badPairs_mul_div_le_expectSumset hK hε hX hY hc₁ hc₂ hkX hkY))
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h.le (by positivity))
  rw [mul_div_assoc', le_div_iff₀ (by positivity), ← min_mul_max (#X : ℝ) #Y,
    ← mul_bltAlpha_eq_bltDelta hK]
  exact mul_add_le_mul (by linarith) (by positivity) min_le_max
    ((thirtySix_mul_le_mul_bltAlpha_mul hK hε hκ).trans
      (mul_le_of_le_one_left (by positivity) hε1))

end Sampling

/-! ### The two cleanup steps -/

omit [AddCommGroup G] in
/-- A subset `X₀ ⊆ X` missing fewer than `#X` elements of `X` is nonempty. -/
private lemma nonempty_of_card_sdiff_lt {X X₀ : Finset G} (h : (#(X \ X₀) : ℝ) < #X) :
    X₀.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at h

section Cleanup

variable {K ε : ℝ} {X Y P : Finset G}

/-- **The small-sumset case.** If `#(X + Y) ≤ bltCap K * min #X #Y` and the sums outside a set
`P` with `#P < (1 - ε / 2) * #(X + Y)` carry at most a `bltDelta K ε` proportion of the pairs,
then the cleanup lemma produces a pair of nonempty subsets of smaller potential. -/
private lemma exists_cappedSumset_add_lt_of_card_add_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : (#(X + Y) : ℝ) ≤ bltCap K * min (#X : ℝ) #Y)
    (hP : (#P : ℝ) < (1 - ε / 2) * #(X + Y))
    (hbad : (#(Cleanup.badPairs X Y P) : ℝ) ≤ bltDelta K ε * (#X * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, X₀.Nonempty ∧ Y₀.Nonempty ∧
      cappedSumset (bltCap K) X₀ Y₀ + bltPenalty K ε * ((#(X \ X₀) : ℝ) + #(Y \ Y₀)) <
        cappedSumset (bltCap K) X Y := by
  obtain ⟨X₀, hX₀, Y₀, hY₀, hdX, hdY, hsum⟩ :=
    Cleanup.exists_subset_card_sdiff_le_card_add_le hX hY (by linarith [hundred_le_bltCap hK])
      (bltRho_pos hK hε) hS (bltDelta_pos hK hε).le bltDelta_le_removalConst hbad
  have hn : 0 < min (#X : ℝ) #Y := by positivity
  have hρn := mul_le_mul_of_nonneg_right (bltRho_le hK hε hε1) hn.le
  refine ⟨X₀, hX₀, Y₀, hY₀, nonempty_of_card_sdiff_lt (hdX.trans_lt ?_),
    nonempty_of_card_sdiff_lt (hdY.trans_lt ?_), ?_⟩
  · linarith [min_le_left (#X : ℝ) #Y, mul_le_mul_of_nonneg_right hε1 hn.le]
  · linarith [min_le_right (#X : ℝ) #Y, mul_le_mul_of_nonneg_right hε1 hn.le]
  have hΛρ : bltPenalty K ε * (bltRho K ε * min (#X : ℝ) #Y) = ε / 250 * min (#X : ℝ) #Y := by
    rw [← mul_assoc, bltPenalty_mul_bltRho hK hε]
  rw [cappedSumset_eq_min (bltCap_pos hK).le X Y, min_eq_left hS]
  linarith [cappedSumset_le_card (D := bltCap K) X₀ Y₀, mul_pos hε hn,
    mul_le_mul_of_nonneg_left (add_le_add hdX hdY) (bltPenalty_pos hK hε).le,
    mul_le_mul_of_nonneg_left ((min_le_left (#X : ℝ) #Y).trans
      (by exact_mod_cast card_le_card_add_right hY : (#X : ℝ) ≤ #(X + Y))) hε.le]

/-- **The large-sumset case.** If `#(X + Y) > bltCap K * min #X #Y`, the sizes of `X` and `Y` are
within a factor `4 * K` of each other, and fewer than `2 * K * min #X #Y` sums carry all but a
`bltDelta K ε` proportion of the pairs, then the covering lemma produces a pair of nonempty
subsets of smaller potential. -/
private lemma exists_cappedSumset_add_lt_of_lt_card_add (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : bltCap K * min (#X : ℝ) #Y < #(X + Y))
    (hP : (#P : ℝ) < 2 * K * min (#X : ℝ) #Y) (hXY : max (#X : ℝ) #Y < 4 * K * min (#X : ℝ) #Y)
    (hbad : (#(Cleanup.badPairs X Y P) : ℝ) ≤ bltDelta K ε * (#X * #Y)) :
    ∃ X₁ ⊆ X, ∃ Y₁ ⊆ Y, X₁.Nonempty ∧ Y₁.Nonempty ∧
      cappedSumset (bltCap K) X₁ Y₁ + bltPenalty K ε * ((#(X \ X₁) : ℝ) + #(Y \ Y₁)) <
        cappedSumset (bltCap K) X Y := by
  have hρ : bltRho K ε < 1 := by linarith [bltRho_le hK hε hε1]
  obtain ⟨X₁, hX₁, Y₁, hY₁, hdX, hdY, hsum⟩ :=
    Cleanup.exists_subset_card_sdiff_le_card_add_mul_le hX hY (bltDelta_pos hK hε) hρ.le
      eight_mul_bltDelta_le_bltRho hbad
  refine ⟨X₁, hX₁, Y₁, hY₁,
    nonempty_of_card_sdiff_lt (hdX.trans_lt (mul_lt_of_lt_one_left (by positivity) hρ)),
    nonempty_of_card_sdiff_lt (hdY.trans_lt (mul_lt_of_lt_one_left (by positivity) hρ)), ?_⟩
  have hΛρ : bltPenalty K ε * (bltRho K ε * #X + bltRho K ε * #Y) = ε / 250 * (#X + #Y) := by
    rw [← mul_add, ← mul_assoc, bltPenalty_mul_bltRho hK hε]
  refine (add_le_add (cappedSumset_le_card X₁ Y₁) le_rfl).trans_lt ?_
  rw [cappedSumset_eq_min (bltCap_pos hK).le X Y, min_eq_right hS.le, bltCap]
  linarith [lt_of_mul_le_two_mul_pow_three (by positivity) (by positivity) (by positivity)
      (by positivity) hP hsum,
    mul_le_mul_of_nonneg_left (add_le_add hdX hdY) (bltPenalty_pos hK hε).le,
    le_max_left (#X : ℝ) #Y, le_max_right (#X : ℝ) #Y,
    mul_le_mul_of_nonneg_right hε1 (by positivity : (0 : ℝ) ≤ #X + #Y),
    mul_le_mul_of_nonneg_right (le_self_pow₀ hK three_ne_zero)
      (by positivity : (0 : ℝ) ≤ min (#X : ℝ) #Y)]

end Cleanup

/-! ### The normalised form -/

/-- If the sampling estimate fails for a pair `(X, Y)` with large enough samples, then some pair of
nonempty subsets of `X` and `Y` has smaller potential. -/
private lemma exists_cappedSumset_add_lt {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {X Y : Finset G} (hX : X.Nonempty) (hY : Y.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X) (hkY : 3 * c₂ ≤ 4 * #Y)
    (hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂)
    (h : Sampling.expectSumset X Y c₁ c₂ < min (min ((1 - ε) * #(X + Y)) (K * #X)) (K * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, X₀.Nonempty ∧ Y₀.Nonempty ∧
      cappedSumset (bltCap K) X₀ Y₀ + bltPenalty K ε * ((#(X \ X₀) : ℝ) + #(Y \ Y₀)) <
        cappedSumset (bltCap K) X Y := by
  rw [lt_min_iff, lt_min_iff] at h
  obtain ⟨⟨hES, hEX⟩, hEY⟩ := h
  have hEK : Sampling.expectSumset X Y c₁ c₂ < K * min (#X : ℝ) #Y := by
    rw [mul_min_of_nonneg _ _ (by linarith)]
    exact lt_min hEX hEY
  have hbad := card_badPairs_popularSums_le hK hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hEK
  obtain hS | hS := le_or_gt (#(X + Y) : ℝ) (bltCap K * min (#X : ℝ) #Y)
  · exact exists_cappedSumset_add_lt_of_card_add_le hK hε hε1 hX hY hS
      (card_popularSums_lt_mul_card_add hK hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hES) hbad
  · have hP := card_popularSums_lt hK hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hEK
    exact exists_cappedSumset_add_lt_of_lt_card_add hK hε hε1 hX hY hS hP
      (max_lt_four_mul_min hX hY bltDelta_le_half hP hbad) hbad

omit [DecidableEq G] [AddCommGroup G] in
/-- The penalty bound of the potential minimiser keeps all but an `ε / 4` proportion of each
set. -/
private lemma one_sub_div_four_mul_le_card {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε)
    {A B X Y : Finset G} (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (h : bltPenalty K ε * (((#A : ℝ) - #X) + ((#B : ℝ) - #Y)) ≤ bltCap K * min (#A : ℝ) #B) :
    (1 - ε / 4) * (#A : ℝ) ≤ #X ∧ (1 - ε / 4) * (#B : ℝ) ≤ #Y := by
  have hD := bltCap_pos hK
  have hΔ : ((#A : ℝ) - #X) + ((#B : ℝ) - #Y) ≤ ε / 4 * min (#A : ℝ) #B := by
    rw [bltPenalty, div_mul_eq_mul_div, div_le_iff₀ hε] at h
    nlinarith
  exact ⟨by linarith [mul_le_mul_of_nonneg_left (min_le_left (#A : ℝ) #B) hε.le,
      (Nat.cast_le.2 (card_le_card hYB) : (#Y : ℝ) ≤ #B)],
    by linarith [mul_le_mul_of_nonneg_left (min_le_right (#A : ℝ) #B) hε.le,
      (Nat.cast_le.2 (card_le_card hXA) : (#X : ℝ) ≤ #A)]⟩

/-- **Large sumsets from medium-sized subsets**, normalised form. For `K ≥ 1`, `0 < ε ≤ 1` and
`c₁ * c₂ > bltSampleConst K ε * max #A #B` there are `X ⊆ A` and `Y ⊆ B` with at least
`(1 - ε / 4) * #A` and `(1 - ε / 4) * #B` elements such that the expected size of the sumset of
`c₁` random points of `X` and `c₂` random points of `Y` is at least
`min ((1 - ε) * #(X + Y)) (K * #X) (K * #Y)`. -/
lemma exists_subset_min_le_expectSumset {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : bltSampleConst K ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧
      (1 - ε / 4) * (#A : ℝ) ≤ #X ∧ (1 - ε / 4) * (#B : ℝ) ≤ #Y ∧
      min (min ((1 - ε) * (#(X + Y) : ℝ)) (K * #X)) (K * #Y) ≤
        Sampling.expectSumset X Y c₁ c₂ := by
  obtain ⟨X, hXA, Y, hYB, hX, hY, hsize, hmin⟩ :=
    exists_potential_minimiser A B hA hB (Λ := bltPenalty K ε) (bltCap_pos hK)
  obtain ⟨hXcard, hYcard⟩ := one_sub_div_four_mul_le_card hK hε hXA hYB hsize
  refine ⟨X, hXA, Y, hYB, hX, hY, hXcard, hYcard, ?_⟩
  by_contra! h
  have hκ : bltSampleConst K ε * max (#X : ℝ) #Y ≤ c₁ * c₂ := by
    refine le_trans ?_ hc.le
    gcongr
    exact (bltSampleConst_pos hK hε).le
  obtain ⟨X₀, hX₀, Y₀, hY₀, hX₀ne, hY₀ne, hlt⟩ := exists_cappedSumset_add_lt hK hε hε1 hX hY
    hc₁ hc₂ (three_mul_le_four_mul hε1 hc₁A hXcard) (three_mul_le_four_mul hε1 hc₂B hYcard) hκ h
  linarith [hmin X₀ hX₀ Y₀ hY₀ hX₀ne hY₀ne]

/-! ### The original form -/

/-- The constant `c(σ, ε)` in Theorem 2 of Bollobás, Leader and Tiba. -/
def originalBltConstant (σ ε : ℝ) : ℝ :=
  bltSampleConst (2 * max σ 1) (min ε 1 / 2)

/-- **Large sumsets from medium-sized subsets** (Bollobás, Leader and Tiba, Theorem 2). Let `A`
and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
more than `(1 - ε) * #A` and `(1 - ε) * #B` elements such that, for `c₁` points of `A₀` and `c₂`
points of `B₀` chosen independently and uniformly at random, with repetitions allowed, the sets
`A'` and `B'` of chosen points satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
theorem exists_subset_min_lt_expect_card_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : originalBltConstant σ ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
      (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
      min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
        𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
          (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) := by
  have hε' : min ε 1 / 2 < ε := by linarith [min_le_left ε 1]
  have hσK : σ < 2 * max σ 1 := by linarith [le_max_left σ 1, le_max_right σ 1]
  obtain ⟨X, hXA, Y, hYB, hX, hY, hXcard, hYcard, hE⟩ :=
    exists_subset_min_le_expectSumset (by linarith [le_max_right σ 1]) (by positivity)
      (by linarith [min_le_right ε 1]) hA hB hc₁ hc₁A hc₂ hc₂B hc
  refine ⟨X, hXA, Y, hYB, hX, hY, ?_, ?_, lt_of_lt_of_le ?_ hE⟩
  · linarith [mul_lt_mul_of_pos_right (by linarith : 1 - ε < 1 - min ε 1 / 2 / 4)
      (Nat.cast_pos.2 hA.card_pos : (0 : ℝ) < #A)]
  · linarith [mul_lt_mul_of_pos_right (by linarith : 1 - ε < 1 - min ε 1 / 2 / 4)
      (Nat.cast_pos.2 hB.card_pos : (0 : ℝ) < #B)]
  exact min_lt_min (min_lt_min (mul_lt_mul_of_pos_right (by linarith)
    (Nat.cast_pos.2 (hX.add hY).card_pos)) (mul_lt_mul_of_pos_right hσK
      (Nat.cast_pos.2 hX.card_pos))) (mul_lt_mul_of_pos_right hσK (Nat.cast_pos.2 hY.card_pos))

/-- **Theorem 2** of Bollobás, Leader and Tiba. For $\sigma, \varepsilon > 0$ there is $c$ with
the following property. Let $A$ and $B$ be finite nonempty subsets of an abelian group and let
$1 \le c_1 \le |A|$ and $1 \le c_2 \le |B|$ satisfy $c_1 c_2 > c \max(|A|, |B|)$. There are
$A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon)|A|$ and
$|B_0| > (1 - \varepsilon)|B|$ such that, for $c_1$ points of $A_0$ and $c_2$ points of $B_0$
chosen independently and uniformly at random, the sets $A'$ and $B'$ of chosen points satisfy
$\mathbb{E} |A' + B'| > \min((1 - \varepsilon)|A_0 + B_0|, \sigma |A_0|, \sigma |B_0|)$. -/
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
  ⟨originalBltConstant σ ε, fun hA hB hc₁ hc₁A hc₂ hc₂B hc ↦
    exists_subset_min_lt_expect_card_add hσ hε hA hB hc₁ hc₁A hc₂ hc₂B hc⟩

/-! ### The symmetric square-root form -/

/-- An inflated BLT constant convenient for the symmetric square-root corollary. -/
def bltConstant (σ ε : ℝ) : ℝ :=
  8 * (max 1 (originalBltConstant σ ε) + σ + 1) ^ 2

/-- The common size of the two samples, of order `√M` where `M` is the size of the larger set. -/
private def bltSampleSize (σ ε : ℝ) (M : ℕ) : ℕ :=
  ⌈Real.sqrt (max 1 (originalBltConstant σ ε) * M)⌉₊ + 1

/-- The inflated constant is at least `1`. -/
lemma one_le_bltConstant {σ : ℝ} (hσ : 0 ≤ σ) (ε : ℝ) : 1 ≤ bltConstant σ ε := by
  rw [bltConstant]
  nlinarith [le_max_left 1 (originalBltConstant σ ε)]

/-- Some pair of samples attains the expectation of `exists_subset_min_lt_expect_card_add`. -/
private lemma exists_subset_card_le_min_le_card_add {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : originalBltConstant σ ε * max (#A : ℝ) #B < c₁ * c₂) :
    ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, ∃ A' ⊆ A₀, ∃ B' ⊆ B₀,
      (1 - ε) * (#A : ℝ) ≤ #A₀ ∧ (1 - ε) * (#B : ℝ) ≤ #B₀ ∧ #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
      min (min ((1 - ε) * (#(A₀ + B₀) : ℝ)) (σ * #A₀)) (σ * #B₀) ≤ #(A' + B') := by
  obtain ⟨A₀, hA₀A, B₀, hB₀B, hA₀, hB₀, hA₀card, hB₀card, hE⟩ :=
    exists_subset_min_lt_expect_card_add hσ hε hA hB hc₁ hc₁A hc₂ hc₂B hc
  have : Nonempty ↥A₀ := hA₀.to_subtype
  have : Nonempty ↥B₀ := hB₀.to_subtype
  obtain ⟨⟨a, b⟩, -, hab⟩ := exists_lt_of_lt_expect univ_nonempty hE
  exact ⟨A₀, hA₀A, B₀, hB₀B, bltSample A₀ a, bltSample_subset A₀ a, bltSample B₀ b,
    bltSample_subset B₀ b, hA₀card.le, hB₀card.le, card_bltSample_le A₀ a,
    card_bltSample_le B₀ b, hab.le⟩

/-- The common sample size is at least `1`. -/
private lemma one_le_bltSampleSize (σ ε : ℝ) (M : ℕ) : 1 ≤ bltSampleSize σ ε M := by
  simp [bltSampleSize]

/-- The two samples are large enough for `exists_subset_min_lt_expect_card_add`. -/
private lemma lt_bltSampleSize_sq (σ ε : ℝ) (M : ℕ) :
    originalBltConstant σ ε * M < (bltSampleSize σ ε M : ℝ) ^ 2 := by
  have hc := le_max_left 1 (originalBltConstant σ ε)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ max 1 (originalBltConstant σ ε) * M)
  rw [bltSampleSize]
  push_cast
  nlinarith [Nat.le_ceil (Real.sqrt (max 1 (originalBltConstant σ ε) * M)),
    Real.sqrt_nonneg (max 1 (originalBltConstant σ ε) * M),
    mul_le_mul_of_nonneg_right (le_max_right 1 (originalBltConstant σ ε))
      (Nat.cast_nonneg (α := ℝ) M)]

/-- The common sample size is at most `(max 1 (originalBltConstant σ ε) + 2) * √M`. -/
private lemma bltSampleSize_le_mul_sqrt (σ ε : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (bltSampleSize σ ε M : ℝ) ≤ (max 1 (originalBltConstant σ ε) + 2) * Real.sqrt M := by
  have hc := le_max_left 1 (originalBltConstant σ ε)
  have hM' : 1 ≤ Real.sqrt M := Real.one_le_sqrt.2 (by exact_mod_cast hM)
  rw [bltSampleSize, Real.sqrt_mul (by linarith)]
  push_cast
  linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.sqrt (max 1 (originalBltConstant σ ε)) *
      Real.sqrt M),
    mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hc)) (Real.sqrt_nonneg M)]

/-- The common sample size is at most `bltConstant σ ε * √M`. -/
private lemma bltSampleSize_le_bltConstant_mul_sqrt {σ : ℝ} (hσ : 0 ≤ σ) (ε : ℝ) {M : ℕ}
    (hM : 1 ≤ M) : (bltSampleSize σ ε M : ℝ) ≤ bltConstant σ ε * Real.sqrt M := by
  refine (bltSampleSize_le_mul_sqrt σ ε hM).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  rw [bltConstant]
  nlinarith [le_max_left 1 (originalBltConstant σ ε)]

/-- A set too small to be sampled already fits, with room to spare, under the bound asked of the
medium-sized subsets. -/
private lemma mul_add_one_le_bltConstant_mul_sqrt {σ : ℝ} (hσ : 0 ≤ σ) (ε : ℝ) {N M : ℕ}
    (hM : 1 ≤ M) (hN : N < bltSampleSize σ ε M) :
    σ * N + 1 ≤ bltConstant σ ε * Real.sqrt M := by
  have hc := le_max_left 1 (originalBltConstant σ ε)
  have hM' : 1 ≤ Real.sqrt M := Real.one_le_sqrt.2 (by exact_mod_cast hM)
  rw [bltConstant]
  nlinarith [mul_le_mul_of_nonneg_left ((Nat.cast_le.2 hN.le).trans
      (bltSampleSize_le_mul_sqrt σ ε hM)) hσ,
    mul_le_mul_of_nonneg_right (by nlinarith : σ * (max 1 (originalBltConstant σ ε) + 2) + 1 ≤
      8 * (max 1 (originalBltConstant σ ε) + σ + 1) ^ 2) (Real.sqrt_nonneg M)]

/-- The unbalanced case of `exists_subset_card_le_mul_sqrt_min_le_card_add`: when `A` is too small
to be sampled, `A` itself serves as its own medium-sized subset and a subset of `B` of the size
of the target sumset serves as the other one. -/
private lemma exists_subset_card_le_bltConstant_mul_sqrt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty) (hsmall : #A < bltSampleSize σ ε (max #A #B)) :
    ∃ B' ⊆ B, (#B' : ℝ) ≤ bltConstant σ ε * Real.sqrt (max (#A : ℝ) #B) ∧
      min (min ((1 - ε) * (#(A + B) : ℝ)) (σ * #A)) (σ * #B) ≤ #(A + B') := by
  have hceil : (⌈σ * #A⌉₊ : ℝ) ≤ bltConstant σ ε * Real.sqrt (max (#A : ℝ) #B) := by
    rw [← Nat.cast_max]
    exact (Nat.ceil_lt_add_one (by positivity)).le.trans (mul_add_one_le_bltConstant_mul_sqrt
      hσ.le ε (hA.card_pos.trans_le (le_max_left _ _)) hsmall)
  obtain hB | hB := le_or_gt ⌈σ * #A⌉₊ #B
  · obtain ⟨B', hB'B, hB'⟩ := exists_subset_card_eq hB
    refine ⟨B', hB'B, hB' ▸ hceil, (min_le_left _ _).trans ((min_le_right _ _).trans ?_)⟩
    exact (Nat.le_ceil _).trans (by exact_mod_cast hB' ▸ card_le_card_add_left hA)
  · refine ⟨B, subset_rfl, (Nat.cast_le.2 hB.le).trans hceil,
      (min_le_left _ _).trans ((min_le_left _ _).trans ?_)⟩
    exact mul_le_of_le_one_left (by positivity) (by linarith)

/-- **Large sumsets from medium-sized subsets**, in the symmetric square-root form. There are
`A' ⊆ A'' ⊆ A` and `B' ⊆ B'' ⊆ B` such that `A''` and `B''` contain all but an `ε` proportion of
`A` and `B`, the sets `A'` and `B'` have at most `bltConstant σ ε * √(max #A #B)` elements, and
`#(A' + B') ≥ min ((1 - ε) * #(A'' + B'')) (σ * #A'') (σ * #B'')`. -/
theorem exists_subset_card_le_mul_sqrt_min_le_card_add {σ ε : ℝ} {A B : Finset G}
    (hσ : 0 < σ) (hε : 0 < ε) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ A' A'' B' B'' : Finset G, A' ⊆ A'' ∧ A'' ⊆ A ∧ B' ⊆ B'' ∧ B'' ⊆ B ∧
      (1 - ε) * (#A : ℝ) ≤ #A'' ∧ (1 - ε) * (#B : ℝ) ≤ #B'' ∧
      (#A' : ℝ) ≤ bltConstant σ ε * Real.sqrt (max (#A : ℝ) #B) ∧
      (#B' : ℝ) ≤ bltConstant σ ε * Real.sqrt (max (#A : ℝ) #B) ∧
      min (min ((1 - ε) * (#(A'' + B'') : ℝ)) (σ * #A'')) (σ * #B'') ≤ #(A' + B') := by
  have hr : (bltSampleSize σ ε (max #A #B) : ℝ) ≤
      bltConstant σ ε * Real.sqrt (max (#A : ℝ) #B) := by
    rw [← Nat.cast_max]
    exact bltSampleSize_le_bltConstant_mul_sqrt hσ.le ε (hA.card_pos.trans_le (le_max_left _ _))
  obtain hrA | hrA := le_or_gt (bltSampleSize σ ε (max #A #B)) #A
  · obtain hrB | hrB := le_or_gt (bltSampleSize σ ε (max #A #B)) #B
    · obtain ⟨A₀, hA₀, B₀, hB₀, A', hA', B', hB', hA₀card, hB₀card, hA'c, hB'c, hsum⟩ :=
        exists_subset_card_le_min_le_card_add hσ hε hA hB (one_le_bltSampleSize σ ε _) hrA
          (one_le_bltSampleSize σ ε _) hrB
          (by simpa [sq] using lt_bltSampleSize_sq σ ε (max #A #B))
      exact ⟨A', A₀, B', B₀, hA', hA₀, hB', hB₀, hA₀card, hB₀card,
        (Nat.cast_le.2 hA'c).trans hr, (Nat.cast_le.2 hB'c).trans hr, hsum⟩
    · obtain ⟨A', hA'A, hA'bound, hsum⟩ :=
        exists_subset_card_le_bltConstant_mul_sqrt hσ hε hB (B := A) (by rwa [max_comm])
      refine ⟨A', A, B, B, hA'A, subset_rfl, subset_rfl, subset_rfl,
        mul_le_of_le_one_left (by positivity) (by linarith),
        mul_le_of_le_one_left (by positivity) (by linarith), by rwa [max_comm],
        (Nat.cast_le.2 hrB.le).trans hr, ?_⟩
      simpa [add_comm, min_comm, min_left_comm, min_assoc] using hsum
  · obtain ⟨B', hB'B, hB'bound, hsum⟩ := exists_subset_card_le_bltConstant_mul_sqrt hσ hε hA hrA
    exact ⟨A, A, B', B, subset_rfl, subset_rfl, hB'B, subset_rfl,
      mul_le_of_le_one_left (by positivity) (by linarith),
      mul_le_of_le_one_left (by positivity) (by linarith), (Nat.cast_le.2 hrA.le).trans hr,
      hB'bound, hsum⟩

end

end LargeSumsetsFromSubsets
