/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Additive.Convolution
import LargeSumsetsFromSmallSubsets.Sampling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Sampling with replacement from two sets

Let `X` and `Y` be finite subsets of an abelian group, choose `k₁` points of `X` and `k₂` points of
`Y` independently and uniformly at random, with repetitions allowed, and let `X'` and `Y'` be the
sets of chosen points. This file writes the expectation of `#(X' + Y')` as the sum over `s ∈ X + Y`
of the probability `hitProb X Y k₁ k₂ s` that `s ∈ X' + Y'`, and bounds that probability from
below in terms of the number `X.addConvolution Y s` of representations `s = u + v` with `u ∈ X` and
`v ∈ Y`.

The bound is a second-moment estimate. The representations of a fixed `s` form a matching, so the
events "the two entries of a representation are both chosen" are pairwise nonpositively correlated,
and the second moment of their number `Z` is at most `𝔼 Z + (𝔼 Z) ^ 2`. The pointwise inequality
`1 ≥ 2 * c * Z - (c * Z) ^ 2`, valid when `Z` is positive, then bounds the probability that `Z` is
positive from below by `𝔼 Z / (1 + 𝔼 Z)`.

## Main definitions

* `LargeSumsetsFromSubsets.MediumSizedSubsets.hits X k a`: the samples `f : Fin k → X` that take
  the value `a`.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.hitCount X k`: the number `#X ^ k - (#X - 1) ^ k` of
  samples that take a given value of `X`.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.hitProb X Y k₁ k₂ s`: the probability that
  `s ∈ X' + Y'`.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.expectCardAdd X Y k₁ k₂`: the expectation of
  `#(X' + Y')`.

## Main statements

* `LargeSumsetsFromSubsets.MediumSizedSubsets.expectCardAdd_eq_sum_hitProb`: the expectation of
  `#(X' + Y')` is the sum over `s ∈ X + Y` of `hitProb X Y k₁ k₂ s`.
* `LargeSumsetsFromSubsets.MediumSizedSubsets.div_le_hitProb`: if `3 * k₁ ≤ 4 * #X` and
  `3 * k₂ ≤ 4 * #Y`, then `hitProb X Y k₁ k₂ s ≥ r * k₁ * k₂ / (9 * #X * #Y + r * k₁ * k₂)`, where
  `r = X.addConvolution Y s`.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets.MediumSizedSubsets

open Finset

open scoped BigOperators Pointwise

variable {G : Type*}

/-! ### Counting samples -/

/-- The number of samples `f : Fin k → X` that take a given value of `X`. -/
def hitCount (X : Finset G) (k : ℕ) : ℕ := #X ^ k - (#X - 1) ^ k

/-- The samples that take a given value of `X` and those that miss it make up all samples. -/
lemma hitCount_add (X : Finset G) (k : ℕ) : hitCount X k + (#X - 1) ^ k = #X ^ k :=
  Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.sub_le _ _) k)

/-- A sample of `k ≥ 1` points of a nonempty set takes each of its values with positive
probability. -/
lemma hitCount_pos {X : Finset G} (hX : X.Nonempty) {k : ℕ} (hk : 1 ≤ k) : 0 < hitCount X k :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by grind [hX.card_pos]) (by grind))

/-- The elementary inequality `(x - 2) * x ≤ (x - 1) ^ 2`, raised to the power `k`. -/
private lemma sub_two_pow_mul_le {x : ℕ} (hx : 2 ≤ x) (k : ℕ) :
    (x - 2) ^ k * x ^ k ≤ ((x - 1) ^ k) ^ 2 := by
  rw [← pow_mul, ← mul_pow, mul_comm k 2, pow_mul]
  refine Nat.pow_le_pow_left ?_ k
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 2 := ⟨x - 2, by grind⟩
  grind

/-- A Bernoulli-type inequality: `(1 + j / x) * x ^ (j + 1) ≤ (x + 1) ^ (j + 1)`. -/
private lemma add_mul_pow_le (x j : ℕ) : (x + j + 1) * x ^ j ≤ (x + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ x j, pow_succ (x + 1) (j + 1)]
    nlinarith [Nat.mul_le_mul_right (x + 1) ih, Nat.zero_le ((j + 1) * x ^ j)]

/-- A given point is missed by all `k` sampled points with probability at most `x / (x + k)`. -/
private lemma sub_one_pow_mul_le {x : ℕ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x - 1) ^ k * (x + k) ≤ x ^ (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by grind⟩
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 1 := ⟨x - 1, by grind⟩
  rw [Nat.add_sub_cancel]
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by grind : 0 < t + 1) j)
  have hsq : t ^ (j + 1) * (t + 1 + 1) ^ (j + 1) ≤ (t + 1) ^ (j + 1 + 1) * (t + 1) ^ j := by
    rw [← pow_add, (by ring : j + 1 + 1 + j = 2 * (j + 1)), pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) _
  linarith [Nat.mul_le_mul_left (t ^ (j + 1)) (add_mul_pow_le (t + 1) j)]

/-- A sample of `k` points of `X`, where `3 * k ≤ 4 * #X`, takes a given value of `X` with
probability at least `k / (3 * #X)`. -/
private lemma mul_pow_le_three_mul_hitCount {X : Finset G} (hX : X.Nonempty) {k : ℕ} (hk : 1 ≤ k)
    (hkX : 3 * k ≤ 4 * #X) : k * #X ^ k ≤ 3 * #X * hitCount X k := by
  nlinarith [sub_one_pow_mul_le hX.card_pos hk, pow_succ #X k, hitCount_add X k]

variable [DecidableEq G]

/-- The samples `f : Fin k → X` that take the value `a`. -/
def hits (X : Finset G) (k : ℕ) (a : G) : Finset (Fin k → X) :=
  {f | a ∈ univ.image fun i ↦ (f i : G)}

/-- The samples that miss a value `a ∈ X` are the samples from `X \ {a}`. -/
private lemma card_compl_hits {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a)ᶜ = (#X - 1) ^ k := by
  rw [← card_erase_of_mem ha, ← sdiff_singleton_eq_erase,
    ← LargeSumsetsFromSmallSubsets.card_filter_forall_not_mem]
  congr 1
  ext f
  simp [hits]

/-- The samples that miss two distinct values `a, b ∈ X` are the samples from `X \ {a, b}`. -/
private lemma card_compl_hits_union {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (hab : a ≠ b) (k : ℕ) : #(hits X k a ∪ hits X k b)ᶜ = (#X - 2) ^ k := by
  rw [← card_pair hab, ← card_sdiff_of_subset (insert_subset ha (singleton_subset_iff.2 hb)),
    ← LargeSumsetsFromSmallSubsets.card_filter_forall_not_mem]
  congr 1
  ext f
  simp [hits, forall_and]

/-- All the values of `X` are taken by the same number of samples. -/
lemma card_hits {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) : #(hits X k a) = hitCount X k := by
  rw [hitCount, ← card_compl_hits ha, (by simp : #X ^ k = Fintype.card (Fin k → X)),
    ← card_add_card_compl (hits X k a), Nat.add_sub_cancel]

/-- Inclusion–exclusion for the samples that take two distinct values `a, b ∈ X`. -/
private lemma card_hits_inter_add {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (k : ℕ) : #(hits X k a ∩ hits X k b) + #X ^ k = 2 * hitCount X k + (#X - 2) ^ k := by
  linarith [card_inter_add_card_union (hits X k a) (hits X k b), card_hits ha k, card_hits hb k,
    card_compl_add_card (hits X k a ∪ hits X k b), card_compl_hits_union ha hb hab k,
    (by simp : Fintype.card (Fin k → X) = #X ^ k)]

/-- Two distinct values are nonpositively correlated: the samples that take both are at most a
`hitCount X k / #X ^ k` proportion of those that take one. -/
lemma card_hits_inter_mul_le {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (k : ℕ) : #(hits X k a ∩ hits X k b) * #X ^ k ≤ hitCount X k ^ 2 := by
  have hX : 2 ≤ #X := card_pair hab ▸ card_le_card (insert_subset ha (singleton_subset_iff.2 hb))
  nlinarith [sub_two_pow_mul_le hX k, congrArg (· * #X ^ k) (card_hits_inter_add ha hb hab k),
    congrArg (· ^ 2) (hitCount_add X k), congrArg (· * hitCount X k) (hitCount_add X k)]

/-! ### The probability that a sum is seen -/

variable [AddCommGroup G]

/-- The probability that `s ∈ X' + Y'`, where `X'` and `Y'` are the sets of values of `k₁` and `k₂`
points of `X` and `Y` chosen independently and uniformly at random. -/
noncomputable def hitProb (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : ℝ :=
  𝔼 ω : (Fin k₁ → X) × (Fin k₂ → Y),
    if s ∈ univ.image (fun i ↦ (ω.1 i : G)) + univ.image (fun i ↦ (ω.2 i : G)) then 1 else 0

/-- A probability is nonnegative. -/
lemma hitProb_nonneg (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : 0 ≤ hitProb X Y k₁ k₂ s := by
  rw [hitProb, Fintype.expect_eq_sum_div_card]
  positivity

/-- The expected size of `X' + Y'`, where `X'` and `Y'` are the sets of values of `k₁` and `k₂`
points of `X` and `Y` chosen independently and uniformly at random. -/
noncomputable def expectCardAdd (X Y : Finset G) (k₁ k₂ : ℕ) : ℝ :=
  𝔼 ω : (Fin k₁ → X) × (Fin k₂ → Y),
    (#(univ.image (fun i ↦ (ω.1 i : G)) + univ.image (fun i ↦ (ω.2 i : G))) : ℝ)

omit [AddCommGroup G] in
/-- The values of a sample from `X` lie in `X`. -/
private lemma image_subset {X : Finset G} {k : ℕ} (f : Fin k → X) :
    univ.image (fun i ↦ (f i : G)) ⊆ X := by
  simp [image_subset_iff]

/-- The expected size of `X' + Y'` is the sum, over `s ∈ X + Y`, of the probability that
`s ∈ X' + Y'`. -/
lemma expectCardAdd_eq_sum_hitProb (X Y : Finset G) (k₁ k₂ : ℕ) :
    expectCardAdd X Y k₁ k₂ = ∑ s ∈ X + Y, hitProb X Y k₁ k₂ s := by
  simp only [expectCardAdd, hitProb, Fintype.expect_eq_sum_div_card, ← sum_div]
  rw [sum_comm]
  congr with ⟨f, g⟩
  rw [sum_boole, filter_mem_eq_inter, inter_eq_right.2 (add_subset_add (image_subset f)
    (image_subset g))]

/-! ### The second-moment estimate -/

variable {X Y : Finset G} {k₁ k₂ : ℕ} {s : G}

/-- The number of representations `s = u + v` with `u ∈ X` and `v ∈ Y` whose two entries are both
chosen. -/
private noncomputable def sampledReprCount (X Y : Finset G) (k₁ k₂ : ℕ) (s : G)
    (ω : (Fin k₁ → X) × (Fin k₂ → Y)) : ℝ :=
  ∑ p ∈ {p ∈ X ×ˢ Y | p.1 + p.2 = s}, (if p.1 ∈ univ.image fun i ↦ (ω.1 i : G) then 1 else 0) *
    (if p.2 ∈ univ.image fun i ↦ (ω.2 i : G) then 1 else 0)

omit [AddCommGroup G] in
/-- Summing the indicator of `a` over all samples counts the samples that take the value `a`. -/
private lemma sum_indicator (X : Finset G) (k : ℕ) (a : G) :
    ∑ f : Fin k → X, (if a ∈ univ.image fun i ↦ (f i : G) then 1 else 0) = (#(hits X k a) : ℝ) := by
  rw [sum_boole]
  rfl

omit [AddCommGroup G] in
/-- Summing the product of the indicators of `a` and `b` over all samples counts the samples that
take both values. -/
private lemma sum_indicator_mul (X : Finset G) (k : ℕ) (a b : G) :
    ∑ f : Fin k → X, (if a ∈ univ.image fun i ↦ (f i : G) then 1 else 0) *
      (if b ∈ univ.image fun i ↦ (f i : G) then 1 else 0) = (#(hits X k a ∩ hits X k b) : ℝ) := by
  simp only [ite_zero_mul_ite_zero, mul_one, sum_boole, hits, ← filter_and]

/-- The first moment of the number of chosen representations. -/
private lemma sum_sampledReprCount :
    ∑ ω, sampledReprCount X Y k₁ k₂ s ω =
      X.addConvolution Y s * (hitCount X k₁ * hitCount Y k₂) := by
  simp only [sampledReprCount]
  rw [sum_comm, ← card_add_eq, ← nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl
  rintro ⟨u, v⟩ hp
  rw [mem_filter, mem_product] at hp
  obtain ⟨⟨hu, hv⟩, -⟩ := hp
  rw [← card_hits hu, ← card_hits hv, ← sum_indicator, ← sum_indicator, sum_mul_sum,
    ← Fintype.sum_prod_type']

/-- The second moment of the number of chosen representations, as a double sum over pairs of
representations. -/
private lemma sum_sq_sampledReprCount :
    ∑ ω, sampledReprCount X Y k₁ k₂ s ω ^ 2 =
      ∑ p ∈ {p ∈ X ×ˢ Y | p.1 + p.2 = s}, ∑ q ∈ {p ∈ X ×ˢ Y | p.1 + p.2 = s},
        (#(hits X k₁ p.1 ∩ hits X k₁ q.1) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2) : ℝ) := by
  simp only [sampledReprCount, sq, sum_mul_sum]
  rw [sum_comm]
  congr with p
  rw [sum_comm]
  congr with q
  rw [← sum_indicator_mul, ← sum_indicator_mul, sum_mul_sum, ← Fintype.sum_prod_type']
  congr with ω
  ring

/-- Distinct representations of `s` are nonpositively correlated, and a representation is correlated
with itself by its own frequency. -/
private lemma card_hits_inter_mul_card_hits_inter_le {p q : G × G}
    (hp : p ∈ {p ∈ X ×ˢ Y | p.1 + p.2 = s}) (hq : q ∈ {p ∈ X ×ˢ Y | p.1 + p.2 = s}) :
    (#(hits X k₁ p.1 ∩ hits X k₁ q.1) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2) : ℝ) ≤
      (if p = q then (hitCount X k₁ * hitCount Y k₂ : ℝ) else 0) +
        (hitCount X k₁ * hitCount Y k₂) ^ 2 / (#X ^ k₁ * #Y ^ k₂) := by
  obtain ⟨u, v⟩ := p
  obtain ⟨u', v'⟩ := q
  rw [mem_filter, mem_product] at hp hq
  obtain ⟨⟨hu, hv⟩, h⟩ := hp
  obtain ⟨⟨hu', hv'⟩, rfl⟩ := hq
  obtain rfl | huu' := eq_or_ne u u'
  · obtain rfl := add_left_cancel h
    rw [ite_eq_left rfl, inter_self, inter_self, card_hits hu, card_hits hv]
    exact le_add_of_nonneg_right (by positivity)
  have hvv' : v ≠ v' := by
    rintro rfl
    exact huu' (add_right_cancel h)
  have hX : X.Nonempty := ⟨u, hu⟩
  have hY : Y.Nonempty := ⟨v, hv⟩
  rw [ite_eq_right (by simp [huu']), zero_add, le_div_iff₀ (by positivity), mul_mul_mul_comm,
    mul_pow]
  exact_mod_cast Nat.mul_le_mul (card_hits_inter_mul_le hu hu' huu' k₁)
    (card_hits_inter_mul_le hv hv' hvv' k₂)

/-- The second moment of the number of chosen representations is at most its first moment plus the
square of its first moment, normalized by the number of samples. -/
private lemma sum_sq_sampledReprCount_le :
    ∑ ω, sampledReprCount X Y k₁ k₂ s ω ^ 2 ≤
      X.addConvolution Y s * (hitCount X k₁ * hitCount Y k₂) +
        (X.addConvolution Y s * (hitCount X k₁ * hitCount Y k₂)) ^ 2 / (#X ^ k₁ * #Y ^ k₂) := by
  rw [sum_sq_sampledReprCount]
  grw [sum_le_sum fun p hp ↦ sum_le_sum fun q hq ↦ card_hits_inter_mul_card_hits_inter_le hp hq]
  simp only [sum_add_distrib, sum_ite_eq, sum_ite_mem, inter_self, sum_const, nsmul_eq_mul,
    card_add_eq]
  exact le_of_eq (by ring)

/-- The pointwise inequality of the second-moment method: `2 * c * Z - (c * Z) ^ 2` is at most the
indicator of `s ∈ X' + Y'`, where `Z` is the number of chosen representations of `s`. -/
private lemma two_mul_sub_sq_le (c : ℝ) (ω : (Fin k₁ → X) × (Fin k₂ → Y)) :
    2 * (c * sampledReprCount X Y k₁ k₂ s ω) - (c * sampledReprCount X Y k₁ k₂ s ω) ^ 2 ≤
      if s ∈ univ.image (fun i ↦ (ω.1 i : G)) + univ.image (fun i ↦ (ω.2 i : G)) then 1 else 0 := by
  obtain ⟨f, g⟩ := ω
  by_cases hs : s ∈ univ.image (fun i ↦ (f i : G)) + univ.image (fun i ↦ (g i : G))
  · rw [ite_eq_left hs]
    nlinarith [sq_nonneg (1 - c * sampledReprCount X Y k₁ k₂ s (f, g))]
  rw [ite_eq_right hs]
  suffices sampledReprCount X Y k₁ k₂ s (f, g) = 0 by simp [this]
  apply sum_eq_zero
  rintro ⟨u, v⟩ hp
  obtain ⟨-, rfl⟩ := mem_filter.1 hp
  simp only [mul_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false]
  by_contra! huv
  exact hs (add_mem_add huv.1 huv.2)

/-- The algebra of the second-moment method: if `T ≥ 2 * c * W - c ^ 2 * S` for every `c` and
`S ≤ W + W ^ 2 / N`, then the choice `c = N / (N + W)` gives `T / N ≥ W / (N + W)`. -/
private lemma div_add_le_div_of_second_moment {N W S T : ℝ} (hN : 0 < N) (hW : 0 < W)
    (hS : S ≤ W + W ^ 2 / N) (hT : ∀ c, 2 * (c * W) - c ^ 2 * S ≤ T) :
    W / (N + W) ≤ T / N := by
  have hc : (N / (N + W)) ^ 2 * (W + W ^ 2 / N) = N / (N + W) * W := by field_simp
  have hcW : N / (N + W) * W ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg (N / (N + W))), hT (N / (N + W))]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hcW
  rw [div_le_div_iff₀ (by positivity) hN]
  linarith

/-- The core second-moment bound: the probability that `s ∈ X' + Y'` is at least `W / (N + W)`,
where `N` is the number of samples and `W / N` is the expected number of representations of `s`
whose two entries are both chosen. -/
private lemma div_add_le_hitProb (hs : s ∈ X + Y) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    X.addConvolution Y s * (hitCount X k₁ * hitCount Y k₂) /
        (#X ^ k₁ * #Y ^ k₂ + X.addConvolution Y s * (hitCount X k₁ * hitCount Y k₂)) ≤
      hitProb X Y k₁ k₂ s := by
  obtain ⟨u, hu, v, hv, -⟩ := mem_add.1 hs
  have hX : X.Nonempty := ⟨u, hu⟩
  have hY : Y.Nonempty := ⟨v, hv⟩
  rw [hitProb, Fintype.expect_eq_sum_div_card,
    (by simp : (Fintype.card ((Fin k₁ → X) × (Fin k₂ → Y)) : ℝ) = #X ^ k₁ * #Y ^ k₂)]
  refine div_add_le_div_of_second_moment (by positivity) (mul_pos (by simpa using hs)
    (mul_pos (Nat.cast_pos.2 (hitCount_pos hX hk₁)) (Nat.cast_pos.2 (hitCount_pos hY hk₂))))
    sum_sq_sampledReprCount_le ?_
  intro c
  grw [← sum_le_sum fun ω _ ↦ two_mul_sub_sq_le c ω]
  simp only [mul_pow, sum_sub_distrib, ← mul_sum, sum_sampledReprCount, le_refl]

/-- Monotonicity of `t ↦ t / (1 + t)`, in the form used to weaken the second-moment bound. -/
private lemma div_add_le_div_add {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / (b + a) ≤ c / (d + c) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The one-sum sampling estimate.** If `s` has `r` representations as a sum of an element of `X`
and an element of `Y`, and `3 * k₁ ≤ 4 * #X` and `3 * k₂ ≤ 4 * #Y`, then `s ∈ X' + Y'` with
probability at least `r * k₁ * k₂ / (9 * #X * #Y + r * k₁ * k₂)`. -/
lemma div_le_hitProb (hs : s ∈ X + Y) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hkX : 3 * k₁ ≤ 4 * #X)
    (hkY : 3 * k₂ ≤ 4 * #Y) :
    X.addConvolution Y s * (k₁ * k₂) / (9 * (#X * #Y) + X.addConvolution Y s * (k₁ * k₂)) ≤
      hitProb X Y k₁ k₂ s := by
  obtain ⟨u, hu, v, hv, -⟩ := mem_add.1 hs
  have hX : X.Nonempty := ⟨u, hu⟩
  have hY : Y.Nonempty := ⟨v, hv⟩
  grw [← div_add_le_hitProb hs hk₁ hk₂]
  apply div_add_le_div_add (by positivity) (by positivity) (by positivity) (by positivity)
  have h : (k₁ * #X ^ k₁ * (k₂ * #Y ^ k₂) : ℝ) ≤
      3 * #X * hitCount X k₁ * (3 * #Y * hitCount Y k₂) := by
    exact_mod_cast Nat.mul_le_mul (mul_pow_le_three_mul_hitCount hX hk₁ hkX)
      (mul_pow_le_three_mul_hitCount hY hk₂ hkY)
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ X.addConvolution Y s)]

end LargeSumsetsFromSubsets.MediumSizedSubsets
