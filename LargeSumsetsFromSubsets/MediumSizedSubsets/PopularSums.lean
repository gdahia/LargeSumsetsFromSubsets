/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticRemoval
public import LargeSumsetsFromSubsets.MediumSizedSubsets.Sampling
import LargeSumsetsFromSubsets.Cleanup
import LargeSumsetsFromSubsets.MediumSizedSubsets.Potential
import Mathlib.Data.Finset.CastCard

/-!
# The popular sums of a minimizing pair

Let `K ≥ 1` and `0 < ε ≤ 1`, and let `A` and `B` be finite nonempty subsets of an abelian group.
This file proves that there are `X ⊆ A` and `Y ⊆ B` with at least `(1 - ε / 4) * #A` and
`(1 - ε / 4) * #B` elements such that `c₁` points of `X` and `c₂` points of `Y` chosen independently
and uniformly at random have a sumset of expected size at least
`min ((1 - ε) * #(X + Y)) (K * #X) (K * #Y)`, as soon as `c₁ * c₂` is a large multiple of
`max #A #B`.

The pair `(X, Y)` minimizes `min #(X + Y) (D K * min #X #Y) + Lambda K ε * (#(A \ X) + #(B \ Y))`,
so it is large. If the expected size were smaller, the popular sums, those with at least
`alpha K ε * min #X #Y` representations, would be few and would carry all but a `delta K ε`
proportion of the pairs of `X ×ˢ Y`. The cleanup theorem, when `#(X + Y) ≤ D K * min #X #Y`, or the
covering bound otherwise, would then give a pair of nonempty subsets of `X` and `Y` with a smaller
value.

## Main definitions

* `LargeSumsetsFromSubsets.MediumSizedSubsets.D K`: the cap `100 * K ^ 3` on the sumset term.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.Lambda K ε`: the price of deleting one element.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.rho K ε`: the proportion of elements that the cleanup
  steps may delete.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.delta K ε`: the proportion of pairs allowed to have an
  unpopular sum.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.alpha K ε`: the popularity threshold.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.popularSums K ε X Y`: the sums with at least
  `alpha K ε * min #X #Y` representations.

## Main statements

* `LargeSumsetsFromSubsets.MediumSizedSubsets.exists_subset_min_le_expectCardAdd`: the subsets `X`
  and `Y` above, for `36 * max #A #B < ε * alpha K ε * c₁ * c₂`.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets.MediumSizedSubsets

open Finset

open scoped Pointwise

noncomputable section

/-! ### The constants -/

/-- The cap `D` on the sumset term of the potential. -/
def D (K : ℝ) : ℝ := 100 * K ^ 3

/-- The price `Λ` of deleting one element. -/
def Lambda (K ε : ℝ) : ℝ := 4 * D K / ε

/-- The proportion `ρ` of elements that the cleanup steps may delete. -/
def rho (K ε : ℝ) : ℝ := ε ^ 2 / (1000 * D K)

/-- The proportion `δ` of pairs allowed to have an unpopular sum. It is at most the threshold of the
arithmetic removal lemma for the doubling `16 * D K ^ 7` and the error `rho K ε / D K`. -/
def delta (K ε : ℝ) : ℝ :=
  min (min (1 / 2) (rho K ε / 8))
    (ArithmeticRemoval.removalBound (16 * D K ^ 7) (rho K ε / D K))

/-- The popularity threshold `α`: a sum is popular when it has at least `alpha K ε * min #X #Y`
representations. -/
def alpha (K ε : ℝ) : ℝ := delta K ε / (36 * K)

variable {K ε : ℝ}

lemma hundred_le_D (hK : 1 ≤ K) : 100 ≤ D K :=
  le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hK)

lemma D_pos (hK : 1 ≤ K) : 0 < D K := by
  linarith [hundred_le_D hK]

lemma Lambda_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < Lambda K ε :=
  div_pos (mul_pos (by norm_num) (D_pos hK)) hε

lemma rho_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < rho K ε :=
  div_pos (pow_pos hε 2) (mul_pos (by norm_num) (D_pos hK))

/-- The proportion of deleted elements is far smaller than `ε`, which makes the cleanup steps
cheap. -/
lemma rho_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) : rho K ε ≤ ε / 1000 := by
  rw [rho, div_le_div_iff₀ (by nlinarith [hundred_le_D hK]) (by norm_num)]
  nlinarith [hundred_le_D hK]

lemma delta_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < delta K ε := by
  apply lt_min (lt_min (by norm_num) (div_pos (rho_pos hK hε) (by norm_num)))
  exact ArithmeticRemoval.removalBound_pos (by positivity [D_pos hK])
    (div_pos (rho_pos hK hε) (D_pos hK))

lemma delta_le_half : delta K ε ≤ 1 / 2 :=
  min_le_of_left_le (min_le_left _ _)

lemma eight_mul_delta_le_rho : 8 * delta K ε ≤ rho K ε := by
  rw [← le_div_iff₀' (by norm_num)]
  exact min_le_of_left_le (min_le_right _ _)

lemma delta_le_removalBound :
    delta K ε ≤ ArithmeticRemoval.removalBound (16 * D K ^ 7) (rho K ε / D K) :=
  min_le_right _ _

lemma alpha_pos (hK : 1 ≤ K) (hε : 0 < ε) : 0 < alpha K ε :=
  div_pos (delta_pos hK hε) (by linarith)

lemma mul_alpha_eq_delta (hK : 1 ≤ K) : 36 * (K * alpha K ε) = delta K ε := by
  unfold alpha
  field_simp [(by positivity : K ≠ 0)]

/-- The penalty of deleting a `rho K ε` proportion of elements is a small multiple of `ε`. -/
lemma Lambda_mul_rho (hK : 1 ≤ K) (hε : 0 < ε) : Lambda K ε * rho K ε = ε / 250 := by
  unfold Lambda rho
  field_simp [(D_pos hK).ne']
  ring

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
  refine lt_of_mul_lt_mul_right ?_ (sq_nonneg (min x y))
  linarith [pow_lt_pow_left₀ hpK hp three_ne_zero, mul_le_mul_of_nonneg_left
    (mul_le_mul (min_le_left x y) (min_le_right x y) (lt_min hx hy).le hx.le) hs]

/-- A set `X` with `(1 - ε / 4) * #A ≤ #X`, for `ε ≤ 1`, satisfies `3 * c ≤ 4 * #X` for every
`c ≤ #A`. -/
private lemma three_mul_le_four_mul {a x c : ℕ} (hε1 : ε ≤ 1) (hca : c ≤ a)
    (hx : (1 - ε / 4) * a ≤ x) : 3 * c ≤ 4 * x := by
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  linarith [mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) a),
    (by exact_mod_cast hca : (c : ℝ) ≤ a)]

/-! ### Popular sums -/

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The popular sums: the elements of `X + Y` with at least `alpha K ε * min #X #Y`
representations. -/
def popularSums (K ε : ℝ) (X Y : Finset G) : Finset G :=
  {s ∈ X + Y | alpha K ε * min (#X : ℝ) #Y ≤ X.addConvolution Y s}

lemma popularSums_subset (K ε : ℝ) (X Y : Finset G) : popularSums K ε X Y ⊆ X + Y :=
  filter_subset _ _

lemma mem_popularSums {X Y : Finset G} {s : G} :
    s ∈ popularSums K ε X Y ↔ s ∈ X + Y ∧ alpha K ε * min (#X : ℝ) #Y ≤ X.addConvolution Y s :=
  mem_filter

/-- The bad pairs are counted by the representations of the sums outside `P`. -/
private lemma card_badPairs_eq_sum_addConvolution (X Y P : Finset G) :
    #(Cleanup.badPairs X Y P) = ∑ s ∈ (X + Y) \ P, X.addConvolution Y s := by
  simp only [← card_add_eq]
  rw [sum_card_fiberwise_eq_card_filter, Cleanup.badPairs]
  congr 1
  ext ⟨u, v⟩
  simp only [mem_filter, mem_product, mem_sdiff]
  grind [add_mem_add]

/-- Every pair of `X ×ˢ Y` either has its sum in `P` or is bad. -/
private lemma sum_addConvolution_add_card_badPairs (X Y P : Finset G) :
    ∑ s ∈ P, (X.addConvolution Y s : ℝ) + #(Cleanup.badPairs X Y P) = #X * #Y := by
  rw [← Nat.cast_sum]
  simp only [← card_add_eq]
  rw [sum_card_fiberwise_eq_card_filter, Cleanup.badPairs, ← Nat.cast_mul, ← card_product]
  exact_mod_cast card_filter_add_card_filter_not _

/-- The sums of `P` carry at most `#P * min #X #Y` pairs. -/
private lemma sum_addConvolution_le_card_mul_min (X Y P : Finset G) :
    ∑ s ∈ P, (X.addConvolution Y s : ℝ) ≤ #P * min (#X : ℝ) #Y := by
  rw [← nsmul_eq_mul]
  apply sum_le_card_nsmul
  intro s _
  exact_mod_cast le_min addConvolution_le_card_left addConvolution_le_card_right

/-- If fewer than `2 * K * min #X #Y` sums carry all but a `δ ≤ 1 / 2` proportion of the pairs, then
the sizes of `X` and `Y` are within a factor `4 * K` of each other. -/
private lemma max_lt_four_mul_min {X Y P : Finset G} {δ : ℝ} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hδ : δ ≤ 1 / 2) (hP : #P < 2 * K * min (#X : ℝ) #Y)
    (hbad : #(Cleanup.badPairs X Y P) ≤ δ * (#X * #Y)) :
    max (#X : ℝ) #Y < 4 * K * min (#X : ℝ) #Y := by
  have hn : 0 < min (#X : ℝ) #Y := by positivity
  refine lt_of_mul_lt_mul_left ?_ hn.le
  linarith [sum_addConvolution_le_card_mul_min X Y P, sum_addConvolution_add_card_badPairs X Y P,
    min_mul_max (#X : ℝ) #Y, mul_lt_mul_of_pos_right hP hn,
    mul_le_mul_of_nonneg_right hδ (by positivity : (0 : ℝ) ≤ #X * #Y)]

/-! ### The sampling estimates -/

section Sampling

variable {X Y : Finset G} {c₁ c₂ : ℕ}

/-- A popular sum is seen by the two samples with probability at least `1 - ε / 4`. -/
private lemma one_sub_div_four_le_hitProb (hε : 0 < ε) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X) (hkY : 3 * c₂ ≤ 4 * #Y)
    (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂))) {s : G}
    (hs : s ∈ popularSums K ε X Y) : 1 - ε / 4 ≤ hitProb X Y c₁ c₂ s := by
  obtain ⟨hs, hr⟩ := mem_popularSums.1 hs
  grw [← div_le_hitProb hs hc₁ hc₂ hkX hkY]
  refine one_sub_div_four_le_div hε (by positivity) (by positivity) ?_
  rw [← min_mul_max (#X : ℝ) #Y]
  linarith [mul_le_mul_of_nonneg_left hκ (by positivity : (0 : ℝ) ≤ min (#X : ℝ) #Y),
    mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ ε * (c₁ * c₂))]

/-- The expected size of the sumset of the samples is at least `1 - ε / 4` times the number of
popular sums. -/
private lemma mul_card_popularSums_le_expectCardAdd (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂))) :
    (1 - ε / 4) * #(popularSums K ε X Y) ≤ expectCardAdd X Y c₁ c₂ := by
  rw [expectCardAdd_eq_sum_hitProb, mul_comm, ← nsmul_eq_mul, ← sum_const]
  grw [← sum_le_sum_of_subset_of_nonneg (popularSums_subset K ε X Y) fun s _ _ ↦
    hitProb_nonneg X Y c₁ c₂ s]
  apply sum_le_sum
  intro s hs
  exact one_sub_div_four_le_hitProb hε hX hY hc₁ hc₂ hkX hkY hκ hs

/-- An unpopular sum `s ∈ X + Y` is seen by the two samples with probability at least its number of
representations times `c₁ * c₂ / (9 * #X * #Y + alpha K ε * min #X #Y * c₁ * c₂)`. -/
private lemma addConvolution_mul_div_le_hitProb (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) {s : G} (hs : s ∈ X + Y) (hsP : s ∉ popularSums K ε X Y) :
    X.addConvolution Y s *
        (c₁ * c₂ / (9 * (#X * #Y) + alpha K ε * min (#X : ℝ) #Y * (c₁ * c₂))) ≤
      hitProb X Y c₁ c₂ s := by
  have hα := alpha_pos hK hε
  have hr : X.addConvolution Y s < alpha K ε * min (#X : ℝ) #Y := by
    simpa [mem_popularSums, hs] using hsP
  grw [← div_le_hitProb hs hc₁ hc₂ hkX hkY, ← mul_div_assoc]
  gcongr

/-- The expected size of the sumset of the samples is at least the number of bad pairs times
`c₁ * c₂ / (9 * #X * #Y + alpha K ε * min #X #Y * c₁ * c₂)`. -/
private lemma card_badPairs_mul_div_le_expectCardAdd (hK : 1 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) :
    #(Cleanup.badPairs X Y (popularSums K ε X Y)) *
        (c₁ * c₂ / (9 * (#X * #Y) + alpha K ε * min (#X : ℝ) #Y * (c₁ * c₂))) ≤
      expectCardAdd X Y c₁ c₂ := by
  rw [card_badPairs_eq_sum_addConvolution, Nat.cast_sum, sum_mul, expectCardAdd_eq_sum_hitProb]
  grw [← sum_le_sum_of_subset_of_nonneg (sdiff_subset (t := popularSums K ε X Y)) fun s _ _ ↦
    hitProb_nonneg X Y c₁ c₂ s]
  apply sum_le_sum
  intro s hs
  obtain ⟨hs, hsP⟩ := mem_sdiff.1 hs
  exact addConvolution_mul_div_le_hitProb hK hε hX hY hc₁ hc₂ hkX hkY hs hsP

/-- If the sampling estimate fails, there are fewer than `2 * K * min #X #Y` popular sums. -/
private lemma card_popularSums_lt (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂)))
    (hE : expectCardAdd X Y c₁ c₂ < K * min (#X : ℝ) #Y) :
    #(popularSums K ε X Y) < 2 * K * min (#X : ℝ) #Y := by
  have hKn : 0 ≤ K * min (#X : ℝ) #Y := mul_nonneg (by linarith) (by positivity)
  by_contra! h
  linarith [mul_card_popularSums_le_expectCardAdd hε hX hY hc₁ hc₂ hkX hkY hκ,
    mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε / 4),
    mul_le_mul_of_nonneg_right hε1 hKn]

/-- If the sampling estimate fails, the popular sums do not exhaust the sumset. -/
private lemma card_popularSums_lt_mul_card_add (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂)))
    (hE : expectCardAdd X Y c₁ c₂ < (1 - ε) * #(X + Y)) :
    #(popularSums K ε X Y) < (1 - ε / 2) * #(X + Y) := by
  have hS : (0 : ℝ) ≤ #(X + Y) := by positivity
  by_contra! h
  linarith [mul_card_popularSums_le_expectCardAdd hε hX hY hc₁ hc₂ hkX hkY hκ,
    mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε / 4), mul_nonneg hε.le hS,
    mul_nonneg (mul_nonneg hε.le hε.le) hS]

/-- If the sampling estimate fails, at most a `delta K ε` proportion of the pairs have an unpopular
sum. -/
private lemma card_badPairs_popularSums_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X)
    (hkY : 3 * c₂ ≤ 4 * #Y) (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂)))
    (hE : expectCardAdd X Y c₁ c₂ < K * min (#X : ℝ) #Y) :
    #(Cleanup.badPairs X Y (popularSums K ε X Y)) ≤ delta K ε * (#X * #Y) := by
  have hα := alpha_pos hK hε
  by_contra! h
  refine hE.not_ge ?_
  grw [← card_badPairs_mul_div_le_expectCardAdd hK hε hX hY hc₁ hc₂ hkX hkY, ← h.le,
    mul_div_assoc', le_div_iff₀ (by positivity), ← min_mul_max (#X : ℝ) #Y,
    ← mul_alpha_eq_delta hK]
  exact mul_add_le_mul (by linarith) (by positivity) min_le_max
    (hκ.trans (mul_le_of_le_one_left (by positivity) hε1))

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

variable {X Y P : Finset G}

/-- If `#(X + Y) ≤ D K * min #X #Y` and the sums outside a set `P` with
`#P < (1 - ε / 2) * #(X + Y)` carry at most a `delta K ε` proportion of the pairs, then the cleanup
theorem gives a pair of nonempty subsets of smaller potential. -/
private lemma exists_min_card_add_add_lt_of_card_add_le (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : #(X + Y) ≤ D K * min (#X : ℝ) #Y)
    (hP : #P < (1 - ε / 2) * #(X + Y)) (hbad : #(Cleanup.badPairs X Y P) ≤ delta K ε * (#X * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, X₀.Nonempty ∧ Y₀.Nonempty ∧
      min (#(X₀ + Y₀) : ℝ) (D K * min (#X₀ : ℝ) #Y₀) + Lambda K ε * (#(X \ X₀) + #(Y \ Y₀)) <
        min (#(X + Y) : ℝ) (D K * min (#X : ℝ) #Y) := by
  obtain ⟨X₀, hX₀, Y₀, hY₀, hdX, hdY, hsum⟩ :=
    Cleanup.exists_subset_card_sdiff_le_card_add_le hX hY (by linarith [hundred_le_D hK])
      (rho_pos hK hε) hS (delta_pos hK hε).le delta_le_removalBound hbad
  have hn : 0 < min (#X : ℝ) #Y := by positivity
  have hρn := mul_le_mul_of_nonneg_right (rho_le hK hε hε1) hn.le
  refine ⟨X₀, hX₀, Y₀, hY₀, nonempty_of_card_sdiff_lt (hdX.trans_lt ?_),
    nonempty_of_card_sdiff_lt (hdY.trans_lt ?_), ?_⟩
  · linarith [min_le_left (#X : ℝ) #Y, mul_le_mul_of_nonneg_right hε1 hn.le]
  · linarith [min_le_right (#X : ℝ) #Y, mul_le_mul_of_nonneg_right hε1 hn.le]
  have hΛρ : Lambda K ε * (rho K ε * min (#X : ℝ) #Y) = ε / 250 * min (#X : ℝ) #Y := by
    rw [← mul_assoc, Lambda_mul_rho hK hε]
  rw [min_eq_left hS]
  linarith [min_le_left (#(X₀ + Y₀) : ℝ) (D K * min (#X₀ : ℝ) #Y₀), mul_pos hε hn,
    mul_le_mul_of_nonneg_left (add_le_add hdX hdY) (Lambda_pos hK hε).le,
    mul_le_mul_of_nonneg_left (min_le_of_left_le (by exact_mod_cast card_le_card_add_right hY) :
      min (#X : ℝ) #Y ≤ #(X + Y)) hε.le]

/-- If `#(X + Y) > D K * min #X #Y`, the sizes of `X` and `Y` are within a factor `4 * K` of each
other, and fewer than `2 * K * min #X #Y` sums carry all but a `delta K ε` proportion of the pairs,
then the covering bound gives a pair of nonempty subsets of smaller potential. -/
private lemma exists_min_card_add_add_lt_of_lt_card_add (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : D K * min (#X : ℝ) #Y < #(X + Y))
    (hP : #P < 2 * K * min (#X : ℝ) #Y) (hXY : max (#X : ℝ) #Y < 4 * K * min (#X : ℝ) #Y)
    (hbad : #(Cleanup.badPairs X Y P) ≤ delta K ε * (#X * #Y)) :
    ∃ X₁ ⊆ X, ∃ Y₁ ⊆ Y, X₁.Nonempty ∧ Y₁.Nonempty ∧
      min (#(X₁ + Y₁) : ℝ) (D K * min (#X₁ : ℝ) #Y₁) + Lambda K ε * (#(X \ X₁) + #(Y \ Y₁)) <
        min (#(X + Y) : ℝ) (D K * min (#X : ℝ) #Y) := by
  have hρ : rho K ε < 1 := by linarith [rho_le hK hε hε1]
  obtain ⟨X₁, hX₁, Y₁, hY₁, hdX, hdY, hsum⟩ :=
    Cleanup.exists_subset_card_sdiff_le_card_add_mul_le hX hY (delta_pos hK hε) hρ.le
      eight_mul_delta_le_rho hbad
  refine ⟨X₁, hX₁, Y₁, hY₁,
    nonempty_of_card_sdiff_lt (hdX.trans_lt (mul_lt_of_lt_one_left (by positivity) hρ)),
    nonempty_of_card_sdiff_lt (hdY.trans_lt (mul_lt_of_lt_one_left (by positivity) hρ)), ?_⟩
  have hΛρ : Lambda K ε * (rho K ε * #X + rho K ε * #Y) = ε / 250 * (#X + #Y) := by
    rw [← mul_add, ← mul_assoc, Lambda_mul_rho hK hε]
  grw [min_le_left (#(X₁ + Y₁) : ℝ)]
  rw [min_eq_right hS.le, D]
  linarith [lt_of_mul_le_two_mul_pow_three (by positivity) (by positivity) (by positivity)
      (by positivity) hP hsum,
    mul_le_mul_of_nonneg_left (add_le_add hdX hdY) (Lambda_pos hK hε).le,
    le_max_left (#X : ℝ) #Y, le_max_right (#X : ℝ) #Y,
    mul_le_mul_of_nonneg_right hε1 (by positivity : (0 : ℝ) ≤ #X + #Y),
    mul_le_mul_of_nonneg_right (le_self_pow₀ hK three_ne_zero)
      (by positivity : (0 : ℝ) ≤ min (#X : ℝ) #Y)]

end Cleanup

/-! ### The minimizing pair -/

/-- If the sampling estimate fails for a pair `(X, Y)` with large enough samples, then some pair of
nonempty subsets of `X` and `Y` has smaller potential. -/
private lemma exists_min_card_add_add_lt (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {X Y : Finset G} (hX : X.Nonempty) (hY : Y.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₂ : 1 ≤ c₂) (hkX : 3 * c₁ ≤ 4 * #X) (hkY : 3 * c₂ ≤ 4 * #Y)
    (hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂)))
    (h : expectCardAdd X Y c₁ c₂ < min (min ((1 - ε) * #(X + Y)) (K * #X)) (K * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, X₀.Nonempty ∧ Y₀.Nonempty ∧
      min (#(X₀ + Y₀) : ℝ) (D K * min (#X₀ : ℝ) #Y₀) + Lambda K ε * (#(X \ X₀) + #(Y \ Y₀)) <
        min (#(X + Y) : ℝ) (D K * min (#X : ℝ) #Y) := by
  rw [lt_min_iff, lt_min_iff] at h
  obtain ⟨⟨hES, hEX⟩, hEY⟩ := h
  have hEK : expectCardAdd X Y c₁ c₂ < K * min (#X : ℝ) #Y := by
    rw [mul_min_of_nonneg _ _ (by linarith)]
    exact lt_min hEX hEY
  have hbad := card_badPairs_popularSums_le hK hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hEK
  obtain hS | hS := le_or_gt (#(X + Y) : ℝ) (D K * min (#X : ℝ) #Y)
  · exact exists_min_card_add_add_lt_of_card_add_le hK hε hε1 hX hY hS
      (card_popularSums_lt_mul_card_add hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hES) hbad
  · have hP := card_popularSums_lt hK hε hε1 hX hY hc₁ hc₂ hkX hkY hκ hEK
    exact exists_min_card_add_add_lt_of_lt_card_add hK hε hε1 hX hY hS hP
      (max_lt_four_mul_min hX hY delta_le_half hP hbad) hbad

omit [AddCommGroup G] in
/-- The penalty bound of the minimizing pair keeps all but an `ε / 4` proportion of each set. -/
private lemma one_sub_div_four_mul_le_card (hK : 1 ≤ K) (hε : 0 < ε) {A B X Y : Finset G}
    (hXA : X ⊆ A) (hYB : Y ⊆ B) (h : Lambda K ε * (#(A \ X) + #(B \ Y)) ≤ D K * min (#A : ℝ) #B) :
    (1 - ε / 4) * #A ≤ #X ∧ (1 - ε / 4) * #B ≤ #Y := by
  rw [Lambda, div_mul_eq_mul_div, div_le_iff₀ hε, cast_card_sdiff hXA, cast_card_sdiff hYB] at h
  have hΔ : (#A - #X : ℝ) + (#B - #Y) ≤ ε / 4 * min (#A : ℝ) #B := by
    nlinarith [D_pos hK]
  constructor <;> linarith [mul_le_mul_of_nonneg_left (min_le_left (#A : ℝ) #B) hε.le,
    mul_le_mul_of_nonneg_left (min_le_right (#A : ℝ) #B) hε.le,
    (by exact_mod_cast card_le_card hXA : (#X : ℝ) ≤ #A),
    (by exact_mod_cast card_le_card hYB : (#Y : ℝ) ≤ #B)]

/-- **The popular sums of a minimizing pair.** Let `K ≥ 1` and `0 < ε ≤ 1`, and let
`1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` satisfy `36 * max #A #B < ε * alpha K ε * c₁ * c₂`. There are
`X ⊆ A` and `Y ⊆ B` with at least `(1 - ε / 4) * #A` and `(1 - ε / 4) * #B` elements such that the
sumset of `c₁` random points of `X` and `c₂` random points of `Y` has expected size at least
`min ((1 - ε) * #(X + Y)) (K * #X) (K * #Y)`. -/
lemma exists_subset_min_le_expectCardAdd (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : 36 * max (#A : ℝ) #B < ε * (alpha K ε * (c₁ * c₂))) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧ (1 - ε / 4) * #A ≤ #X ∧ (1 - ε / 4) * #B ≤ #Y ∧
      min (min ((1 - ε) * #(X + Y)) (K * #X)) (K * #Y) ≤ expectCardAdd X Y c₁ c₂ := by
  obtain ⟨X, hXA, Y, hYB, hX, hY, hsize, hmin⟩ :=
    exists_subset_min_card_add_le_min_card_add_add hA hB (D_pos hK).le (Lambda K ε)
  obtain ⟨hXcard, hYcard⟩ := one_sub_div_four_mul_le_card hK hε hXA hYB hsize
  refine ⟨X, hXA, Y, hYB, hX, hY, hXcard, hYcard, ?_⟩
  by_contra! h
  have hκ : 36 * max (#X : ℝ) #Y ≤ ε * (alpha K ε * (c₁ * c₂)) := by
    grw [card_le_card hXA, card_le_card hYB]
    exact hc.le
  obtain ⟨X₀, hX₀, Y₀, hY₀, hX₀ne, hY₀ne, hlt⟩ := exists_min_card_add_add_lt hK hε hε1 hX hY
    hc₁ hc₂ (three_mul_le_four_mul hε1 hc₁A hXcard) (three_mul_le_four_mul hε1 hc₂B hYcard) hκ h
  linarith [hmin X₀ hX₀ Y₀ hY₀ hX₀ne hY₀ne]

end

end LargeSumsetsFromSubsets.MediumSizedSubsets
