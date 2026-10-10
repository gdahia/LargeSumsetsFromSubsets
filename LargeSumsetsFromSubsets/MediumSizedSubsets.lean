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
subsets*, in three forms:

* `exists_medium_sized_subsets_with_large_sumset_core`, the normalised form, for a doubling
  parameter `K ≥ 1` and an error `0 < ε ≤ 1`;
* `exists_medium_sized_subsets_with_large_sumset_sample`, the original finite
  uniform-expectation form, deduced from the normalised form by replacing `σ` with
  `2 * max σ 1 ≥ 1` and `ε` with `min ε 1 / 2 ∈ (0, 1]`; the two replacements are what turns
  the inequalities of the normalised form into the strict ones asked for here;
* `exists_medium_sized_subsets_with_large_sumset_subsets`, the symmetric square-root form,
  obtained from the finite uniform-expectation form by specialising to
  `c₁ = c₂ = bltSampleSize σ ε (max #A #B)`, of order `√(max #A #B)`, and
  replacing the expectation by a single good sample. Sampling requires this common size to be
  at most both `#A` and `#B`; when it is not, one of the two sets is already smaller than the
  bound asked for, and the whole of it, or a subset of the other set of exactly the required
  size, does the job.

The core form is proved by a penalised-minimality argument. Among all pairs of nonempty subsets
`X ⊆ A` and `Y ⊆ B` one minimises the potential of
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

/-- The elementary inequality behind the estimate for a popular sum. -/
private lemma popular_arith {ε xy t : ℝ} (hε : 0 < ε) (hxy : 0 < xy) (htnn : 0 ≤ t)
    (ht : 36 * xy ≤ ε * t) : 1 - ε / 4 ≤ t / (9 * xy + t) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The elementary inequality behind the estimate for the unpopular sums: if the sums outside `P`
carried more than a `δ` proportion of the pairs, the expectation would already be too large. -/
private lemma unpopular_arith {K ε δ α n m xy κ : ℝ} (hK : 1 ≤ K) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hn : 0 < n) (hnm : n ≤ m) (hxy : n * m = xy) (hκ : 0 ≤ κ)
    (hCκ : 1296 * K * m ≤ ε * (δ * κ)) (hα : 36 * (K * α) = δ) :
    K * n * (9 * xy + α * n * κ) ≤ δ * xy * κ := by
  have hmpos : 0 < m := lt_of_lt_of_le hn hnm
  have hδκ : 1296 * K * m ≤ δ * κ := by
    nlinarith only [hCκ, mul_nonneg (mul_nonneg hδ.le hκ) (sub_nonneg.2 hε1)]
  have hfac : K * (9 * m + α * κ) ≤ δ * κ := by
    have hKα : K * (α * κ) = δ * κ / 36 := by
      rw [← hα]
      ring
    nlinarith
  have hrw : K * n * (9 * xy + α * n * κ) = n * n * (K * (9 * m + α * κ)) := by
    rw [← hxy]
    ring
  rw [hrw, ← hxy]
  nlinarith [mul_le_mul_of_nonneg_left hfac (by positivity : (0 : ℝ) ≤ n * n),
    mul_nonneg (mul_nonneg hδ.le hκ) hn.le]

open scoped Classical in
/-- The popular sums: those with at least `bltAlpha K ε * min #X #Y` representations. -/
noncomputable def popularSums (K ε : ℝ) (X Y : Finset G) : Finset G :=
  (X + Y).filter fun s => bltAlpha K ε * min (#X : ℝ) (#Y : ℝ) ≤ (Sampling.reprCount X Y s : ℝ)

lemma popularSums_subset (K ε : ℝ) (X Y : Finset G) : popularSums K ε X Y ⊆ X + Y :=
  filter_subset _ _

lemma mem_popularSums {K ε : ℝ} {X Y : Finset G} {s : G} :
    s ∈ popularSums K ε X Y ↔
      s ∈ X + Y ∧ bltAlpha K ε * min (#X : ℝ) (#Y : ℝ) ≤ (Sampling.reprCount X Y s : ℝ) := by
  unfold popularSums
  exact mem_filter

/-- The consequences of the failure of the sampling estimate for a fixed pair: the popular sums are
few, they do not exhaust the sumset, they carry almost every pair, and the two sets are
comparable. -/
private lemma popular_facts {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) {X Y : Finset G}
    (hXne : X.Nonempty) (hYne : Y.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hkX : 3 * c₁ ≤ 4 * #X) (hkY : 3 * c₂ ≤ 4 * #Y)
    (hκ : bltSampleConst K ε * max (#X : ℝ) (#Y : ℝ) ≤ (c₁ : ℝ) * c₂)
    (hES : Sampling.expectSumset X Y c₁ c₂ < (1 - ε) * (#(X + Y) : ℝ))
    (hEK : Sampling.expectSumset X Y c₁ c₂ < K * min (#X : ℝ) (#Y : ℝ)) :
    (#(popularSums K ε X Y) : ℝ) < 2 * K * min (#X : ℝ) (#Y : ℝ)
      ∧ (#(popularSums K ε X Y) : ℝ) < (1 - ε / 2) * (#(X + Y) : ℝ)
      ∧ (#(Cleanup.badPairs X Y (popularSums K ε X Y)) : ℝ)
          ≤ bltDelta K ε * ((#X : ℝ) * #Y)
      ∧ max (#X : ℝ) (#Y : ℝ) < 4 * K * min (#X : ℝ) (#Y : ℝ) := by
  classical
  have hδpos : 0 < bltDelta K ε := bltDelta_pos hK hε
  have hαpos : 0 < bltAlpha K ε := bltAlpha_pos hK hε
  have hCpos : 0 < bltSampleConst K ε := bltSampleConst_pos hK hε
  have hCα : ε * (bltSampleConst K ε * bltAlpha K ε) = 36 := mul_bltSampleConst_mul_bltAlpha hK hε
  have hKα : 36 * (K * bltAlpha K ε) = bltDelta K ε := mul_bltAlpha_eq_bltDelta hK
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hXne
  have hypos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hYne
  set n : ℝ := min (#X : ℝ) (#Y : ℝ) with hn
  set m : ℝ := max (#X : ℝ) (#Y : ℝ) with hm
  have hnpos : 0 < n := lt_min hxpos hypos
  have hnm : n * m = (#X : ℝ) * #Y := min_mul_max _ _
  have hnlem : n ≤ m := min_le_max
  have hmpos : 0 < m := lt_of_lt_of_le hnpos hnlem
  have hxypos : (0 : ℝ) < (#X : ℝ) * #Y := by positivity
  have hc₁pos : (0 : ℝ) < c₁ := by exact_mod_cast hc₁
  have hc₂pos : (0 : ℝ) < c₂ := by exact_mod_cast hc₂
  have hκpos : (0 : ℝ) < (c₁ : ℝ) * c₂ := mul_pos hc₁pos hc₂pos
  have hKpos : (0 : ℝ) < K := by linarith
  set P : Finset G := popularSums K ε X Y with hPdef
  have hPsub : P ⊆ X + Y := popularSums_subset K ε X Y
  have hPnn : (0 : ℝ) ≤ #P := by positivity
  have hEsum : Sampling.expectSumset X Y c₁ c₂ = ∑ s ∈ X + Y, Sampling.hitProb X Y c₁ c₂ s :=
    Sampling.expectSumset_eq_sum_hitProb X Y c₁ c₂
  have hpop : ∀ s ∈ P, 1 - ε / 4 ≤ Sampling.hitProb X Y c₁ c₂ s := by
    intro s hs
    rw [hPdef, mem_popularSums] at hs
    refine le_trans (popular_arith hε hxypos (by positivity) ?_)
      (Sampling.hitProb_lower_bound hs.1 hc₁ hc₂ hkX hkY)
    have hmul : bltAlpha K ε * n * (bltSampleConst K ε * m)
        ≤ (Sampling.reprCount X Y s : ℝ) * ((c₁ : ℝ) * c₂) :=
      mul_le_mul hs.2 hκ (mul_nonneg hCpos.le hmpos.le) (by positivity)
    have hval : ε * (bltAlpha K ε * n * (bltSampleConst K ε * m)) = 36 * ((#X : ℝ) * #Y) := by
      rw [← hnm, ← hCα]
      ring
    linarith only [mul_le_mul_of_nonneg_left hmul hε.le, hval]
  have hEpop : (1 - ε / 4) * (#P : ℝ) ≤ Sampling.expectSumset X Y c₁ c₂ := by
    rw [hEsum]
    refine le_trans (le_of_eq ?_) (le_trans (sum_le_sum hpop)
      (sum_le_sum_of_subset_of_nonneg hPsub fun s _ _ => Sampling.hitProb_nonneg X Y c₁ c₂ s))
    rw [sum_const, nsmul_eq_mul]
    ring
  have hPsmall : (#P : ℝ) < 2 * K * n := by
    by_contra! hcon
    have hKn : (0 : ℝ) < K * n := mul_pos hKpos hnpos
    linarith only [mul_le_mul_of_nonneg_left hcon (by linarith : (0 : ℝ) ≤ 1 - ε / 4), hEpop, hEK,
      hKn, mul_le_mul_of_nonneg_right hε1 hKn.le]
  have hPgap : (#P : ℝ) < (1 - ε / 2) * (#(X + Y) : ℝ) := by
    have hSpos : (0 : ℝ) < #(X + Y) := by exact_mod_cast card_pos.2 (hXne.add hYne)
    by_contra! hcon
    have hquad : (1 - ε) * (#(X + Y) : ℝ) ≤ (1 - ε / 4) * ((1 - ε / 2) * (#(X + Y) : ℝ)) := by
      nlinarith only [mul_nonneg hε.le hSpos.le,
        mul_nonneg (mul_nonneg hε.le hε.le) hSpos.le]
    linarith only [hEpop, hES, hquad,
      mul_le_mul_of_nonneg_left hcon (by linarith : (0 : ℝ) ≤ 1 - ε / 4)]
  have hbadeq : (#(Cleanup.badPairs X Y P) : ℝ)
      = ∑ s ∈ (X + Y) \ P, (Sampling.reprCount X Y s : ℝ) := by
    have h := Sampling.sum_reprCount X Y ((X + Y) \ P)
    have hset : (X ×ˢ Y).filter (fun p => p.1 + p.2 ∈ (X + Y) \ P) = Cleanup.badPairs X Y P := by
      ext p
      simp only [mem_filter, mem_product, mem_sdiff, Cleanup.mem_badPairs, and_assoc]
      constructor
      · rintro ⟨hpX, hpY, -, hpP⟩
        exact ⟨hpX, hpY, hpP⟩
      · rintro ⟨hpX, hpY, hpP⟩
        exact ⟨hpX, hpY, add_mem_add hpX hpY, hpP⟩
    rw [hset] at h
    exact_mod_cast h.symm
  have hbadsmall : (#(Cleanup.badPairs X Y P) : ℝ) ≤ bltDelta K ε * ((#X : ℝ) * #Y) := by
    by_contra! hcon
    have hdenpos : (0 : ℝ) < 9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂) := by
      positivity
    have hunpop : ∀ s ∈ (X + Y) \ P, (Sampling.reprCount X Y s : ℝ)
        * ((c₁ : ℝ) * c₂ / (9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂)))
        ≤ Sampling.hitProb X Y c₁ c₂ s := by
      intro s hs
      rw [mem_sdiff, hPdef, mem_popularSums] at hs
      have hsmall : (Sampling.reprCount X Y s : ℝ) < bltAlpha K ε * n := by
        by_contra hc
        exact hs.2 ⟨hs.1, le_of_not_gt hc⟩
      have hrnn : (0 : ℝ) ≤ (Sampling.reprCount X Y s : ℝ) := by positivity
      refine le_trans (le_of_eq (mul_div_assoc' _ _ _)) (le_trans ?_
        (Sampling.hitProb_lower_bound hs.1 hc₁ hc₂ hkX hkY))
      rw [div_le_div_iff₀ hdenpos (by positivity)]
      have hkey : (Sampling.reprCount X Y s : ℝ) * ((c₁ : ℝ) * c₂)
          * ((Sampling.reprCount X Y s : ℝ) * ((c₁ : ℝ) * c₂))
          ≤ (Sampling.reprCount X Y s : ℝ) * ((c₁ : ℝ) * c₂)
            * (bltAlpha K ε * n * ((c₁ : ℝ) * c₂)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall.le hκpos.le)
          (mul_nonneg hrnn hκpos.le)
      nlinarith only [hkey]
    have hEbad : (c₁ : ℝ) * c₂ / (9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂))
        * (#(Cleanup.badPairs X Y P) : ℝ) ≤ Sampling.expectSumset X Y c₁ c₂ := by
      rw [hEsum, hbadeq, mul_sum]
      refine le_trans (sum_le_sum ?_)
        (sum_le_sum_of_subset_of_nonneg sdiff_subset
          fun s _ _ => Sampling.hitProb_nonneg X Y c₁ c₂ s)
      intro s hs
      rw [mul_comm]
      exact hunpop s hs
    have hCκ : 1296 * K * m ≤ ε * (bltDelta K ε * ((c₁ : ℝ) * c₂)) := by
      have hval : ε * bltDelta K ε * (bltSampleConst K ε * m) = 1296 * K * m := by
        rw [← mul_bltDelta_mul_bltSampleConst hK hε]
        ring
      linarith only [mul_le_mul_of_nonneg_left hκ (mul_pos hε hδpos).le, hval]
    have harith := unpopular_arith (K := K) (ε := ε) (δ := bltDelta K ε) (α := bltAlpha K ε)
      (n := n) (m := m) (xy := (#X : ℝ) * #Y) (κ := (c₁ : ℝ) * c₂) hK hε1 hδpos hnpos hnlem
      hnm hκpos.le hCκ hKα
    have hfinal : K * n ≤ (c₁ : ℝ) * c₂
        / (9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂))
        * (bltDelta K ε * ((#X : ℝ) * #Y)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hdenpos]
      linarith only [harith]
    have hmono : (c₁ : ℝ) * c₂ / (9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂))
        * (bltDelta K ε * ((#X : ℝ) * #Y))
        ≤ (c₁ : ℝ) * c₂ / (9 * ((#X : ℝ) * #Y) + bltAlpha K ε * n * ((c₁ : ℝ) * c₂))
        * (#(Cleanup.badPairs X Y P) : ℝ) :=
      mul_le_mul_of_nonneg_left hcon.le (by positivity)
    linarith only [hEbad, hfinal, hmono, hEK]
  refine ⟨hPsmall, hPgap, hbadsmall, ?_⟩
  have hsplit : ∑ s ∈ P, (Sampling.reprCount X Y s : ℝ)
      + (#(Cleanup.badPairs X Y P) : ℝ) = (#X : ℝ) * #Y := by
    have h1 := Sampling.sum_reprCount X Y P
    have h2 := card_filter_add_card_filter_not (s := X ×ˢ Y)
      (p := fun p : G × G => p.1 + p.2 ∈ P)
    rw [card_product] at h2
    have h3 : ∑ s ∈ P, Sampling.reprCount X Y s + #(Cleanup.badPairs X Y P) = #X * #Y := by
      rw [h1, Cleanup.badPairs]
      exact h2
    exact_mod_cast h3
  have hsum : ∑ s ∈ P, (Sampling.reprCount X Y s : ℝ) ≤ (#P : ℝ) * n := by
    have hbound : ∀ s ∈ P, (Sampling.reprCount X Y s : ℝ) ≤ n := by
      intro s _
      rw [hn]
      apply le_min
      · exact_mod_cast Sampling.reprCount_le_left X Y s
      · exact_mod_cast Sampling.reprCount_le_right X Y s
    refine le_trans (sum_le_sum hbound) (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]
  have hgood : (1 - bltDelta K ε) * (n * m) ≤ (#P : ℝ) * n := by
    rw [hnm]
    linarith only [hsplit, hsum, hbadsmall]
  by_contra! hcon
  have hhalf : (1 : ℝ) / 2 * (n * m) ≤ (1 - bltDelta K ε) * (n * m) :=
    mul_le_mul_of_nonneg_right (by linarith only [bltDelta_le_half (K := K) (ε := ε)])
      (by positivity)
  linarith only [hgood, hhalf, mul_le_mul_of_nonneg_left hcon hnpos.le,
    mul_lt_mul_of_pos_right hPsmall hnpos]

/-- **Large sumsets from medium-sized subsets**, normalised form. For `K ≥ 1`, `0 < ε ≤ 1` and
`c₁ * c₂ > bltSampleConst K ε * max #A #B` there are `X ⊆ A` and `Y ⊆ B` with at least
`(1 - ε / 4) * #A` and `(1 - ε / 4) * #B` elements such that the expected size of the sumset of
`c₁` random points of `X` and `c₂` random points of `Y` is at least
`min ((1 - ε) * #(X + Y)) (K * #X) (K * #Y)`. -/
theorem exists_medium_sized_subsets_with_large_sumset_core {K ε : ℝ} (hK : 1 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁) (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hprod : bltSampleConst K ε * max (#A : ℝ) (#B : ℝ) < (c₁ : ℝ) * c₂) :
    ∃ X ⊆ A, ∃ Y ⊆ B, X.Nonempty ∧ Y.Nonempty ∧
      (1 - ε / 4) * (#A : ℝ) ≤ #X ∧ (1 - ε / 4) * (#B : ℝ) ≤ #Y ∧
      min (min ((1 - ε) * (#(X + Y) : ℝ)) (K * #X)) (K * #Y)
        ≤ Sampling.expectSumset X Y c₁ c₂ := by
  classical
  have hD100 : (100 : ℝ) ≤ bltCap K := hundred_le_bltCap hK
  have hDpos : (0 : ℝ) < bltCap K := by linarith
  have hΛpos : 0 < bltPenalty K ε := by
    unfold bltPenalty
    positivity
  have hρpos : 0 < bltRho K ε := bltRho_pos hK hε
  have hρle : bltRho K ε ≤ ε / 1000 := bltRho_le hK hε hε1
  have hδpos : 0 < bltDelta K ε := bltDelta_pos hK hε
  have hCpos : 0 < bltSampleConst K ε := bltSampleConst_pos hK hε
  have hΛρ : bltPenalty K ε * bltRho K ε = ε / 250 := bltPenalty_mul_bltRho hK hε
  obtain ⟨X, hXA, Y, hYB, hXne, hYne, hsize, hminimal⟩ :=
    exists_potential_minimiser A B hA hB (D := bltCap K) (Λ := bltPenalty K ε) hDpos
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hXne
  have hypos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hYne
  have hApos : (0 : ℝ) < #A := by exact_mod_cast card_pos.2 hA
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast card_pos.2 hB
  have hXleA : (#X : ℝ) ≤ #A := by exact_mod_cast card_le_card hXA
  have hYleB : (#Y : ℝ) ≤ #B := by exact_mod_cast card_le_card hYB
  have hdelsmall : ((#A : ℝ) - #X) + ((#B : ℝ) - #Y) ≤ ε * min (#A : ℝ) (#B : ℝ) / 4 := by
    rw [← le_div_iff₀' hΛpos] at hsize
    refine hsize.trans (le_of_eq ?_)
    unfold bltPenalty
    field_simp
  have hXcard : (1 - ε / 4) * (#A : ℝ) ≤ #X := by
    linarith only [hdelsmall, hYleB,
      mul_le_mul_of_nonneg_left (min_le_left (#A : ℝ) (#B : ℝ)) hε.le]
  have hYcard : (1 - ε / 4) * (#B : ℝ) ≤ #Y := by
    linarith only [hdelsmall, hXleA,
      mul_le_mul_of_nonneg_left (min_le_right (#A : ℝ) (#B : ℝ)) hε.le]
  refine ⟨X, hXA, Y, hYB, hXne, hYne, hXcard, hYcard, ?_⟩
  by_contra! hfail
  set n : ℝ := min (#X : ℝ) (#Y : ℝ) with hn
  set m : ℝ := max (#X : ℝ) (#Y : ℝ) with hm
  have hnpos : 0 < n := lt_min hxpos hypos
  have hnm : n * m = (#X : ℝ) * #Y := min_mul_max _ _
  have hnlem : n ≤ m := min_le_max
  have hnx : n ≤ (#X : ℝ) := min_le_left _ _
  have hny : n ≤ (#Y : ℝ) := min_le_right _ _
  have hES : Sampling.expectSumset X Y c₁ c₂ < (1 - ε) * (#(X + Y) : ℝ) :=
    hfail.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hEK : Sampling.expectSumset X Y c₁ c₂ < K * n := by
    rw [hn, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ K)]
    exact hfail.trans_le (min_le_min (min_le_right _ _) le_rfl)
  have hkX : 3 * c₁ ≤ 4 * #X := by
    have hc : (c₁ : ℝ) ≤ #A := by exact_mod_cast hc₁A
    have h : (3 : ℝ) * c₁ ≤ 4 * #X := by
      linarith only [hXcard, hc, mul_le_mul_of_nonneg_right hε1 hApos.le]
    exact_mod_cast h
  have hkY : 3 * c₂ ≤ 4 * #Y := by
    have hc : (c₂ : ℝ) ≤ #B := by exact_mod_cast hc₂B
    have h : (3 : ℝ) * c₂ ≤ 4 * #Y := by
      linarith only [hYcard, hc, mul_le_mul_of_nonneg_right hε1 hBpos.le]
    exact_mod_cast h
  have hκ : bltSampleConst K ε * m ≤ (c₁ : ℝ) * c₂ := by
    refine le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hCpos.le) hprod)
    rw [hm]
    exact max_le (hXleA.trans (le_max_left _ _)) (hYleB.trans (le_max_right _ _))
  obtain ⟨hPsmall, hPgap, hbadsmall, hmn⟩ :=
    popular_facts hK hε hε1 hXne hYne hc₁ hc₂ hkX hkY hκ hES hEK
  set P : Finset G := popularSums K ε X Y with hPdef
  rcases le_or_gt (#(X + Y) : ℝ) (bltCap K * n) with hcase | hcase
  · -- Small sumset: the arithmetic-removal cleanup wins.
    obtain ⟨X₀, hX₀X, Y₀, hY₀Y, hdX, hdY, hsum⟩ :=
      Cleanup.exists_cleanup (P := P) hXne hYne (by linarith) hρpos hcase hδpos.le
        bltDelta_le_removal hbadsmall
    have hdX' : (#X : ℝ) - #X₀ ≤ bltRho K ε * n := by
      rwa [card_sdiff_of_subset hX₀X, Nat.cast_sub (card_le_card hX₀X)] at hdX
    have hdY' : (#Y : ℝ) - #Y₀ ≤ bltRho K ε * n := by
      rwa [card_sdiff_of_subset hY₀Y, Nat.cast_sub (card_le_card hY₀Y)] at hdY
    have hρn : bltRho K ε * n ≤ ε / 1000 * n := mul_le_mul_of_nonneg_right hρle hnpos.le
    have hεn : ε * n ≤ 1 * n := mul_le_mul_of_nonneg_right hε1 hnpos.le
    have hX₀ne : X₀.Nonempty := by
      rw [← card_pos]
      have h : (0 : ℝ) < #X₀ := by linarith only [hdX', hnx, hρn, hεn, hnpos]
      exact_mod_cast h
    have hY₀ne : Y₀.Nonempty := by
      rw [← card_pos]
      have h : (0 : ℝ) < #Y₀ := by linarith only [hdY', hny, hρn, hεn, hnpos]
      exact_mod_cast h
    have hcap : cappedSumset (bltCap K) X Y = (#(X + Y) : ℝ) := by
      have h₁ : (#(X + Y) : ℝ) ≤ bltCap K * #X := by
        linarith only [hcase, mul_le_mul_of_nonneg_left hnx hDpos.le]
      have h₂ : (#(X + Y) : ℝ) ≤ bltCap K * #Y := by
        linarith only [hcase, mul_le_mul_of_nonneg_left hny hDpos.le]
      unfold cappedSumset
      rw [min_eq_left h₁, min_eq_left h₂]
    have hpen : bltPenalty K ε * (((#X : ℝ) - #X₀) + ((#Y : ℝ) - #Y₀)) ≤ 2 * (ε / 250) * n := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hdX' hdY') hΛpos.le
      have hval : bltPenalty K ε * (bltRho K ε * n + bltRho K ε * n) = 2 * (ε / 250) * n := by
        rw [← hΛρ]
        ring
      linarith only [hval ▸ h]
    have hSge : n ≤ (#(X + Y) : ℝ) := by
      have h : (#X : ℝ) ≤ #(X + Y) := by exact_mod_cast card_le_card_add_right hYne
      linarith only [h, hnx]
    have hstep := hminimal X₀ hX₀X Y₀ hY₀Y hX₀ne hY₀ne
    rw [hcap] at hstep
    linarith only [hstep, cappedSumset_le_card (D := bltCap K) X₀ Y₀, hsum, hpen, hPgap, hρn,
      mul_le_mul_of_nonneg_left hSge hε.le, mul_pos hε hnpos]
  · -- Large sumset: the covering bound wins.
    obtain ⟨X₁, hX₁X, Y₁, hY₁Y, hdX, hdY, hsum⟩ :=
      Cleanup.exists_covering (P := P) hXne hYne hδpos (by linarith)
        eight_mul_bltDelta_le_bltRho hbadsmall
    have hdX' : (#X : ℝ) - #X₁ ≤ bltRho K ε * #X := by
      rwa [card_sdiff_of_subset hX₁X, Nat.cast_sub (card_le_card hX₁X)] at hdX
    have hdY' : (#Y : ℝ) - #Y₁ ≤ bltRho K ε * #Y := by
      rwa [card_sdiff_of_subset hY₁Y, Nat.cast_sub (card_le_card hY₁Y)] at hdY
    have hX₁ne : X₁.Nonempty := by
      rw [← card_pos]
      have h : (0 : ℝ) < #X₁ := by
        linarith only [hdX', hxpos, mul_le_mul_of_nonneg_right hρle hxpos.le,
          mul_le_mul_of_nonneg_right hε1 hxpos.le]
      exact_mod_cast h
    have hY₁ne : Y₁.Nonempty := by
      rw [← card_pos]
      have h : (0 : ℝ) < #Y₁ := by
        linarith only [hdY', hypos, mul_le_mul_of_nonneg_right hρle hypos.le,
          mul_le_mul_of_nonneg_right hε1 hypos.le]
      exact_mod_cast h
    have hsumsmall : (#(X₁ + Y₁) : ℝ) ≤ 16 * K ^ 3 * n := by
      have hQnn : (0 : ℝ) ≤ #(X₁ + Y₁) := by positivity
      have hPnn : (0 : ℝ) ≤ #P := by positivity
      have hcube : (#P : ℝ) ^ 3 ≤ (2 * K * n) ^ 3 := pow_le_pow_left₀ hPnn hPsmall.le 3
      have hxy : n * n ≤ (#X : ℝ) * #Y := by
        linarith only [hnm, mul_le_mul_of_nonneg_left hnlem hnpos.le]
      have hval : 2 * (2 * K * n) ^ 3 = 16 * K ^ 3 * n * (n * n) := by ring
      refine le_of_mul_le_mul_right ?_ (mul_pos hnpos hnpos)
      linarith only [hsum, hcube, hval, mul_le_mul_of_nonneg_left hxy hQnn]
    have hcap : cappedSumset (bltCap K) X Y = bltCap K * n := by
      unfold cappedSumset
      rw [hn, mul_min_of_nonneg _ _ hDpos.le, min_assoc]
      refine min_eq_right (le_of_lt ?_)
      rw [← mul_min_of_nonneg _ _ hDpos.le, ← hn]
      exact hcase
    have hpen : bltPenalty K ε * (((#X : ℝ) - #X₁) + ((#Y : ℝ) - #Y₁))
        ≤ ε / 250 * ((#X : ℝ) + #Y) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hdX' hdY') hΛpos.le
      have hval : bltPenalty K ε * (bltRho K ε * (#X : ℝ) + bltRho K ε * #Y)
          = ε / 250 * ((#X : ℝ) + #Y) := by
        rw [← hΛρ]
        ring
      linarith only [hval ▸ h]
    have hxym : (#X : ℝ) + #Y ≤ 2 * m := by
      rw [hm]
      linarith only [le_max_left (#X : ℝ) (#Y : ℝ), le_max_right (#X : ℝ) (#Y : ℝ)]
    have hmnn : (0 : ℝ) ≤ m := le_trans hnpos.le hnlem
    have hKle3 : K ≤ K ^ 3 := by
      nlinarith only [hK, mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ K)
        (by linarith : (0 : ℝ) ≤ K - 1)) (by linarith : (0 : ℝ) ≤ K + 1)]
    have hKcube : K * n ≤ K ^ 3 * n := mul_le_mul_of_nonneg_right hKle3 hnpos.le
    have hK3n : (0 : ℝ) < K ^ 3 * n := mul_pos (pow_pos (by linarith : (0 : ℝ) < K) 3) hnpos
    have hstep := hminimal X₁ hX₁X Y₁ hY₁Y hX₁ne hY₁ne
    rw [hcap] at hstep
    have hDval : bltCap K * n = 100 * (K ^ 3 * n) := by
      unfold bltCap
      ring
    linarith only [hstep, cappedSumset_le_card (D := bltCap K) X₁ Y₁, hsumsmall, hpen, hxym, hmn,
      hKcube, hK3n, hDval, mul_le_mul_of_nonneg_right hε1 hmnn,
      mul_le_mul_of_nonneg_left hxym (by positivity : (0 : ℝ) ≤ ε / 250)]

/-- The constant `c(σ, ε)` in Theorem 2 of Bollobás, Leader and Tiba. -/
def originalBltConstant (σ ε : ℝ) (_hσ : 0 < σ) (_hε : 0 < ε) : ℝ :=
  bltSampleConst (2 * max σ 1) (min ε 1 / 2)

/-- **Large sumsets from medium-sized subsets** (Bollobás, Leader and Tiba, Theorem 2). Let `A`
and `B` be finite nonempty subsets of an abelian group and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ > originalBltConstant σ ε * max #A #B`. There are `A₀ ⊆ A` and `B₀ ⊆ B` with
more than `(1 - ε) * #A` and `(1 - ε) * #B` elements such that, for `c₁` points of `A₀` and `c₂`
points of `B₀` chosen independently and uniformly at random, with repetitions allowed, the sets
`A'` and `B'` of chosen points satisfy
`𝔼 #(A' + B') > min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀) (σ * #B₀)`. -/
theorem exists_medium_sized_subsets_with_large_sumset_sample {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (c₁ c₂ : ℕ) (hc₁pos : 1 ≤ c₁) (hc₁A : c₁ ≤ A.card) (hc₂pos : 1 ≤ c₂)
    (hc₂B : c₂ ≤ B.card)
    (hcprod : originalBltConstant σ ε hσ hε * (max A.card B.card : ℝ) < c₁ * c₂) :
    ∃ A₀ B₀ : Finset G, A₀.Nonempty ∧ B₀.Nonempty ∧ A₀ ⊆ A ∧ B₀ ⊆ B ∧
      (1 - ε) * (A.card : ℝ) < (A₀.card : ℝ) ∧
      (1 - ε) * (B.card : ℝ) < (B₀.card : ℝ) ∧
      min (min ((1 - ε) * ((A₀ + B₀).card : ℝ)) (σ * (A₀.card : ℝ)))
          (σ * (B₀.card : ℝ)) <
        𝔼 ab : (Fin c₁ → ↑A₀) × (Fin c₂ → ↑B₀),
          ((bltSample A₀ ab.1 + bltSample B₀ ab.2).card : ℝ) := by
  have hK : (1 : ℝ) ≤ 2 * max σ 1 := by
    have := le_max_right σ 1
    linarith
  have hσK : σ < 2 * max σ 1 := by
    have h₁ := le_max_left σ 1
    have h₂ := le_max_right σ 1
    linarith
  have hε' : 0 < min ε 1 / 2 := by
    have := lt_min hε (zero_lt_one' ℝ)
    linarith
  have hε'1 : min ε 1 / 2 ≤ 1 := by
    have := min_le_right ε 1
    linarith
  have hε'ε : min ε 1 / 2 < ε := by
    have := min_le_left ε 1
    linarith
  obtain ⟨X, hXA, Y, hYB, hXne, hYne, hXcard, hYcard, hexp⟩ :=
    exists_medium_sized_subsets_with_large_sumset_core (K := 2 * max σ 1) (ε := min ε 1 / 2)
      hK hε' hε'1 hA hB hc₁pos hc₁A hc₂pos hc₂B hcprod
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 hA
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast card_pos.2 hB
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.2 hXne
  have hypos : (0 : ℝ) < Y.card := by exact_mod_cast card_pos.2 hYne
  have hSpos : (0 : ℝ) < (X + Y).card := by exact_mod_cast card_pos.2 (hXne.add hYne)
  refine ⟨X, Y, hXne, hYne, hXA, hYB, ?_, ?_, ?_⟩
  · nlinarith [hXcard, hε'ε, hε', hApos]
  · nlinarith [hYcard, hε'ε, hε', hBpos]
  · refine lt_of_lt_of_le ?_ hexp
    refine lt_min (lt_min ?_ ?_) ?_
    · refine lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) ?_
      nlinarith [hε'ε, hSpos]
    · refine lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) ?_
      nlinarith [hσK, hxpos]
    · refine lt_of_le_of_lt (min_le_right _ _) ?_
      nlinarith [hσK, hypos]

/-- An inflated BLT constant convenient for the symmetric square-root corollary. -/
def bltConstant (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) : ℝ :=
  8 * (max 1 (originalBltConstant σ ε hσ hε) + σ + 1) ^ 2

/-- The common size of the two samples, of order `√M` where `M` is the size of the larger set. -/
private def bltSampleSize (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) : ℕ :=
  ⌈Real.sqrt (max 1 (originalBltConstant σ ε hσ hε) * M)⌉₊ + 1

lemma one_le_bltConstant {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    1 ≤ bltConstant σ ε hσ hε := by
  unfold bltConstant
  nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε)]

/-- The deterministic form of `exists_medium_sized_subsets_with_large_sumset_sample`: some sample
attains the expectation. -/
private lemma exists_medium_sized_subsets_with_large_sumset_subsets_card_le {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty)
    (hB : B.Nonempty) (c₁ c₂ : ℕ) (hc₁pos : 1 ≤ c₁) (hc₁A : c₁ ≤ #A)
    (hc₂pos : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hcprod : originalBltConstant σ ε hσ hε * (max #A #B : ℝ) < c₁ * c₂) :
    ∃ A' A₀ B' B₀ : Finset G, A' ⊆ A₀ ∧ A₀ ⊆ A ∧ B' ⊆ B₀ ∧ B₀ ⊆ B ∧
      (1 - ε) * (#A : ℝ) ≤ (#A₀ : ℝ) ∧
      (1 - ε) * (#B : ℝ) ≤ (#B₀ : ℝ) ∧ #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
      min (min ((1 - ε) * (#(A₀ + B₀) : ℝ)) (σ * (#A₀ : ℝ)))
          (σ * (#B₀ : ℝ)) ≤ (#(A' + B') : ℝ) := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hA₀A, hB₀B, hA₀card, hB₀card, hexpect⟩ :=
    exists_medium_sized_subsets_with_large_sumset_sample hσ hε hA hB c₁ c₂ hc₁pos hc₁A hc₂pos
      hc₂B hcprod
  let : Nonempty ↥A₀ := hA₀.to_subtype
  let : Nonempty ↥B₀ := hB₀.to_subtype
  obtain ⟨⟨a, b⟩, _, hab⟩ := exists_lt_of_lt_expect univ_nonempty hexpect
  exact ⟨bltSample A₀ a, A₀, bltSample B₀ b, B₀,
    bltSample_subset A₀ a, hA₀A, bltSample_subset B₀ b, hB₀B,
    hA₀card.le, hB₀card.le, card_bltSample_le A₀ a, card_bltSample_le B₀ b, hab.le⟩

private lemma one_le_bltSampleSize {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) :
    1 ≤ bltSampleSize σ ε hσ hε M := by
  simp [bltSampleSize]

/-- The two samples are large enough for `exists_medium_sized_subsets_with_large_sumset_sample`.
-/
private lemma lt_bltSampleSize_sq {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) :
    originalBltConstant σ ε hσ hε * (M : ℝ) <
      (bltSampleSize σ ε hσ hε M : ℝ) ^ 2 := by
  unfold bltSampleSize
  push_cast
  refine (mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) (originalBltConstant σ ε hσ hε)) ?_).trans_lt ?_
  · positivity
  · nth_rewrite 1 [← Real.sq_sqrt (mul_nonneg
      ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))
      (by positivity))]
    nlinarith [Nat.le_ceil (Real.sqrt
      (max 1 (originalBltConstant σ ε hσ hε) * (M : ℝ))),
      Real.sqrt_nonneg (max 1 (originalBltConstant σ ε hσ hε) * (M : ℝ))]

private lemma bltSampleSize_le_mul_sqrt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {M : ℕ}
    (hM : 1 ≤ M) :
    (bltSampleSize σ ε hσ hε M : ℝ) ≤
      (max 1 (originalBltConstant σ ε hσ hε) + 2) * Real.sqrt (M : ℝ) := by
  unfold bltSampleSize
  push_cast
  rw [Real.sqrt_mul
    ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))]
  apply le_trans (b := Real.sqrt (max 1 (originalBltConstant σ ε hσ hε)) *
    Real.sqrt (M : ℝ) + 2)
  · nlinarith [Nat.ceil_lt_add_one (mul_nonneg
      (Real.sqrt_nonneg (max 1 (originalBltConstant σ ε hσ hε)))
      (Real.sqrt_nonneg (M : ℝ)))]
  · rw [add_mul]
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)) ?_
    · rw [Real.sqrt_le_left
        ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))]
      nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε)]
    · nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (M : ℝ)),
        Real.sqrt_nonneg (M : ℝ), (by exact_mod_cast hM : (1 : ℝ) ≤ M)]

private lemma bltSampleSize_le_bltConstant_mul_sqrt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {M : ℕ}
    (hM : 1 ≤ M) :
    (bltSampleSize σ ε hσ hε M : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (M : ℝ) := by
  refine (bltSampleSize_le_mul_sqrt hσ hε hM).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  unfold bltConstant
  nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε),
    sq_nonneg (max 1 (originalBltConstant σ ε hσ hε) + σ)]

private lemma cast_ceil_le_add_one {x K : ℝ} (hxK : x ≤ K) (hK : 0 ≤ K) :
    (⌈x⌉₊ : ℝ) ≤ K + 1 := by
  by_cases hx : 0 ≤ x
  · refine (Nat.ceil_lt_add_one hx).le.trans ?_
    linarith
  · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hx)]
    norm_num
    linarith

/-- A set too small to be sampled already fits, with room to spare, under the bound asked of the
medium-sized subsets. -/
private lemma mul_add_one_le_bltConstant_mul_sqrt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {N M : ℕ}
    (hM : 1 ≤ M) (hN : N < bltSampleSize σ ε hσ hε M) :
    σ * (N : ℝ) + 1 ≤ bltConstant σ ε hσ hε * Real.sqrt (M : ℝ) := by
  replace hN : (N : ℝ) < (bltSampleSize σ ε hσ hε M : ℝ) := by
    exact_mod_cast hN
  unfold bltConstant
  refine le_trans (b :=
    (σ * (max 1 (originalBltConstant σ ε hσ hε) + 2) + 1) * Real.sqrt (M : ℝ))
    ?_ (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  · refine le_trans (b := σ * (max 1 (originalBltConstant σ ε hσ hε) + 2) *
      Real.sqrt (M : ℝ) + 1) ?_ ?_
    · nlinarith [bltSampleSize_le_mul_sqrt hσ hε hM]
    · nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (M : ℝ)), Real.sqrt_nonneg (M : ℝ),
        (by exact_mod_cast hM : (1 : ℝ) ≤ M)]
  · nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε),
      sq_nonneg (max 1 (originalBltConstant σ ε hσ hε) + σ)]

/-- The unbalanced case of `exists_medium_sized_subsets_with_large_sumset_subsets`: when `A` is too
small to be sampled, `A` itself serves as its own medium-sized subset and a subset of `B` of the
size of the target sumset serves as the other one. -/
private lemma exists_subset_card_le_bltConstant_mul_sqrt {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {A B : Finset G} (hA : A.Nonempty)
    (hsmall : #A < bltSampleSize σ ε hσ hε (max #A #B)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (#B' : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max #A #B : ℝ) ∧
      min (min ((1 - ε) * (#(A + B) : ℝ)) (σ * (#A : ℝ)))
          (σ * (#B : ℝ)) ≤ (#(A + B') : ℝ) := by
  set T := min (min ((1 - ε) * (#(A + B) : ℝ)) (σ * (#A : ℝ))) (σ * (#B : ℝ))
  have hceil : (⌈T⌉₊ : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max #A #B : ℝ) := by
    apply (cast_ceil_le_add_one ((min_le_left _ _).trans (min_le_right _ _))
      (by positivity)).trans
    rw [← Nat.cast_max]
    exact mul_add_one_le_bltConstant_mul_sqrt hσ hε
      ((Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero).trans (le_max_left _ _)) hsmall
  by_cases hcard : ⌈T⌉₊ ≤ #B
  · obtain ⟨B', hB'B, hB'card⟩ := exists_subset_card_eq hcard
    refine ⟨B', hB'B, hB'card ▸ hceil, (Nat.le_ceil T).trans ?_⟩
    rw [← hB'card]
    exact_mod_cast card_le_card_add_left hA
  · refine ⟨B, Subset.refl B, le_trans ?_ hceil, ?_⟩
    · exact_mod_cast Nat.le_of_lt (lt_of_not_ge hcard)
    · refine (min_le_left _ _).trans ((min_le_left _ _).trans ?_)
      nlinarith

/-- **Large sumsets from medium-sized subsets**, in the symmetric square-root form. There are
`A' ⊆ A'' ⊆ A` and `B' ⊆ B'' ⊆ B` such that `A''` and `B''` contain all but an `ε` proportion of
`A` and `B`, the sets `A'` and `B'` have at most `bltConstant σ ε * √(max #A #B)` elements, and
`#(A' + B') ≥ min ((1 - ε) * #(A'' + B'')) (σ * #A'') (σ * #B'')`. -/
theorem exists_medium_sized_subsets_with_large_sumset_subsets {σ ε : ℝ} {A B : Finset G}
    (hσ : 0 < σ) (hε : 0 < ε) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ A' A'' B' B'' : Finset G, A' ⊆ A'' ∧ A'' ⊆ A ∧ B' ⊆ B'' ∧ B'' ⊆ B ∧
      (1 - ε) * (#A : ℝ) ≤ (#A'' : ℝ) ∧ (1 - ε) * (#B : ℝ) ≤ (#B'' : ℝ) ∧
      (#A' : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max #A #B : ℝ) ∧
      (#B' : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max #A #B : ℝ) ∧
      min (min ((1 - ε) * (#(A'' + B'') : ℝ)) (σ * (#A'' : ℝ)))
          (σ * (#B'' : ℝ)) ≤ (#(A' + B') : ℝ) := by
  set r := bltSampleSize σ ε hσ hε (max #A #B) with hr
  have hrbound : (r : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max #A #B : ℝ) := by
    rw [hr, ← Nat.cast_max]
    exact bltSampleSize_le_bltConstant_mul_sqrt hσ hε
      ((Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero).trans (le_max_left _ _))
  by_cases hrA : r ≤ #A
  · by_cases hrB : r ≤ #B
    · obtain ⟨A', A₀, B', B₀, hA'A₀, hA₀A, hB'B₀, hB₀B, hA₀card, hB₀card,
          hA'card, hB'card, hsum⟩ :=
        exists_medium_sized_subsets_with_large_sumset_subsets_card_le hσ hε hA hB r r
          (one_le_bltSampleSize hσ hε _) hrA (one_le_bltSampleSize hσ hε _) hrB
          (by simpa [hr, pow_two] using lt_bltSampleSize_sq hσ hε (max #A #B))
      refine ⟨A', A₀, B', B₀, hA'A₀, hA₀A, hB'B₀, hB₀B, hA₀card, hB₀card, ?_, ?_, hsum⟩
      · exact le_trans (by exact_mod_cast hA'card) hrbound
      · exact le_trans (by exact_mod_cast hB'card) hrbound
    · obtain ⟨A', hA'A, hA'bound, hsum⟩ :=
        exists_subset_card_le_bltConstant_mul_sqrt hσ hε hB
          (by rw [max_comm]; exact lt_of_not_ge hrB)
      refine ⟨A', A, B, B, hA'A, Subset.refl A, Subset.refl B, Subset.refl B, ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · simpa only [Nat.cast_max, max_comm] using hA'bound
      · exact le_trans (by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hrB)) hrbound
      · simpa [add_comm, min_comm, min_left_comm, min_assoc] using hsum
  · obtain ⟨B', hB'B, hB'bound, hsum⟩ :=
      exists_subset_card_le_bltConstant_mul_sqrt hσ hε hA (lt_of_not_ge hrA)
    refine ⟨A, A, B', B, Subset.refl A, Subset.refl A, hB'B, Subset.refl B, ?_, ?_, ?_,
      hB'bound, hsum⟩
    · nlinarith
    · nlinarith
    · exact le_trans (by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hrA)) hrbound

end

end LargeSumsetsFromSubsets
