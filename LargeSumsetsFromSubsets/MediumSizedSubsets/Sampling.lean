/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
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

Let `X` and `Y` be finite subsets of an abelian group, sample `k₁` points of `X` and `k₂` points of
`Y` independently and uniformly with replacement, and let `X'` and `Y'` be the sets of sampled
values. This file computes the expectation of `#(X' + Y')` as the sum over `s ∈ X + Y` of the
probability `hitProb` that `s` is seen, and bounds that probability from below in terms of the
number `reprCount X Y s` of representations `s = u + v` with `u ∈ X` and `v ∈ Y`.

The bound, `LargeSumsetsFromSubsets.Sampling.div_le_hitProb`, is a second-moment estimate.
The representations of a fixed `s` form a matching, so the events "the two entries of a
representation are both sampled" are pairwise nonpositively correlated, whence the second moment of
their number `Z` is at most `𝔼 Z + (𝔼 Z) ^ 2`; the pointwise inequality
`1 ≥ 2 * c * Z - (c * Z) ^ 2`, valid when `Z` is positive, then bounds the probability that `Z` is
positive from below by `𝔼 Z / (1 + 𝔼 Z)`.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

open Finset

open scoped BigOperators Pointwise

variable {G : Type*} [DecidableEq G]

/-- The finset underlying a sample with replacement from `A`. -/
def bltSample (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : Finset G := univ.image fun i ↦ f i

/-- The sample contains exactly the values of the sampling function. -/
lemma mem_bltSample {A : Finset G} {k : ℕ} {f : Fin k → ↥A} {a : G} :
    a ∈ bltSample A f ↔ ∃ i, (f i : G) = a := by
  simp [bltSample, eq_comm]

/-- A sample from `A` is a subset of `A`. -/
lemma bltSample_subset (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : bltSample A f ⊆ A := by
  intro a ha
  obtain ⟨i, rfl⟩ := mem_bltSample.1 ha
  exact (f i).prop

/-- A sample of `k` points has at most `k` elements. -/
lemma card_bltSample_le (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : #(bltSample A f) ≤ k :=
  card_image_le.trans (by simp)

namespace Sampling

/-! ### Counting samples -/

/-- The samples from `X` avoiding a set `Z` are exactly the samples from `X \ Z`. -/
lemma card_filter_forall_not_mem (X Z : Finset G) (k : ℕ) :
    #(univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ Z) = #(X \ Z) ^ k := by
  rw [← (by rw [univ_eq_attach, filter_attach (· ∉ Z), card_map, card_attach, sdiff_eq_filter] :
    #(univ.filter fun b : ↥X => (b : G) ∉ Z) = #(X \ Z)), ← Fintype.card_piFinset_const]
  congr 1
  ext f
  simp [Fintype.mem_piFinset]

/-- The samples from `X` that contain the element `a`. -/
def hits (X : Finset G) (k : ℕ) (a : G) : Finset (Fin k → ↥X) :=
  univ.filter fun f => a ∈ bltSample X f

/-- The samples from `X` avoiding the set `Z`. -/
private def avoiders (X Z : Finset G) (k : ℕ) : Finset (Fin k → ↥X) :=
  univ.filter fun f ↦ ∀ i, (f i : G) ∉ Z

/-- The samples from `X` avoiding `Z` are the samples from `X \ Z`. -/
private lemma card_avoiders (X Z : Finset G) (k : ℕ) : #(avoiders X Z k) = #(X \ Z) ^ k :=
  card_filter_forall_not_mem X Z k

/-- The samples missing `a` are those avoiding `{a}`. -/
private lemma univ_sdiff_hits (X : Finset G) (k : ℕ) (a : G) :
    univ \ hits X k a = avoiders X {a} k := by
  ext f
  simp [hits, avoiders, mem_bltSample]

/-- The samples missing `a` or `b` are those avoiding `{a}` or avoiding `{b}`. -/
private lemma univ_sdiff_hits_inter (X : Finset G) (k : ℕ) (a b : G) :
    univ \ (hits X k a ∩ hits X k b) = avoiders X {a} k ∪ avoiders X {b} k := by
  ext f
  simp [hits, avoiders, mem_bltSample, imp_iff_not_or]

/-- The samples avoiding `{a}` and `{b}` are those avoiding `{a, b}`. -/
private lemma avoiders_inter (X : Finset G) (k : ℕ) (a b : G) :
    avoiders X {a} k ∩ avoiders X {b} k = avoiders X {a, b} k := by
  ext f
  simp [avoiders, forall_and]

/-- The samples containing `a` and the samples from `X \ {a}` together make up all samples. -/
lemma card_hits_add {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) + (#X - 1) ^ k = #X ^ k := by
  rw [(by simp : #X ^ k = #(univ : Finset (Fin k → ↥X))),
    ← card_sdiff_add_card_eq_card (subset_univ (hits X k a)), univ_sdiff_hits, card_avoiders,
    sdiff_singleton_eq_erase, card_erase_of_mem ha, add_comm]

/-- The number of samples containing a fixed element `a ∈ X`. -/
lemma card_hits {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) = #X ^ k - (#X - 1) ^ k :=
  Nat.eq_sub_of_add_eq (card_hits_add ha k)

/-- The elementary inequality `(x - 2) * x ≤ (x - 1) ^ 2`, raised to the power `k`. -/
private lemma sub_two_pow_mul_le {x : ℕ} (hx : 2 ≤ x) (k : ℕ) :
    (x - 2) ^ k * x ^ k ≤ ((x - 1) ^ k) ^ 2 := by
  rw [← pow_mul, ← mul_pow, mul_comm k 2, pow_mul]
  refine Nat.pow_le_pow_left ?_ k
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 2 := ⟨x - 2, by grind⟩
  grind

/-- Inclusion–exclusion for the samples missing `a` or missing `b`. -/
private lemma card_hits_inter_add {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (k : ℕ) : #(hits X k a ∩ hits X k b) + 2 * (#X - 1) ^ k = #X ^ k + (#X - 2) ^ k := by
  have hunion := card_union_add_card_inter (avoiders X {a} k) (avoiders X {b} k)
  rw [← univ_sdiff_hits_inter, avoiders_inter, card_avoiders, card_avoiders, card_avoiders,
    sdiff_singleton_eq_erase, sdiff_singleton_eq_erase, card_erase_of_mem ha,
    card_erase_of_mem hb,
    card_sdiff_of_subset (by simp [insert_subset_iff, ha, hb] : ({a, b} : Finset G) ⊆ X),
    card_pair hab] at hunion
  have hsplit := card_sdiff_add_card_eq_card (subset_univ (hits X k a ∩ hits X k b))
  simp only [card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] at hsplit
  grind

/-- Two distinct elements are nonpositively correlated: the samples meeting both are fewer than
the product of the two frequencies. -/
lemma card_hits_inter_mul_le {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (k : ℕ) : #(hits X k a ∩ hits X k b) * #X ^ k ≤ #(hits X k a) * #(hits X k b) := by
  have hxle : 2 ≤ #X :=
    card_pair hab ▸ card_le_card (by simp [insert_subset_iff, ha, hb] : ({a, b} : Finset G) ⊆ X)
  have ha' := card_hits_add ha k
  have hb' := card_hits_add hb k
  nlinarith [sub_two_pow_mul_le hxle k, congrArg (· * #X ^ k) (card_hits_inter_add ha hb hab k),
    congrArg (· * #(hits X k b)) ha', congrArg (· * #X ^ k) hb', congrArg (· * (#X - 1) ^ k) hb']

/-- Monotonicity of `t ↦ t / (1 + t)`, in the form used to weaken the second-moment bound. -/
private lemma div_add_le_div_add {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / (b + a) ≤ c / (d + c) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### How often a fixed element is sampled -/

/-- A Bernoulli-type inequality: `(1 + j / x) * x ^ (j + 1) ≤ (x + 1) ^ (j + 1)`. -/
private lemma add_mul_pow_le (x j : ℕ) : (x + j + 1) * x ^ j ≤ (x + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ x j, pow_succ (x + 1) (j + 1)]
    nlinarith [Nat.mul_le_mul_right (x + 1) ih, Nat.zero_le ((j + 1) * x ^ j)]

/-- The complement of the frequency with which a fixed point is sampled: an element is missed by
all `k` samples with probability at most `x / (x + k)`. -/
private lemma pred_pow_mul_le {x : ℕ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x - 1) ^ k * (x + k) ≤ x ^ (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by grind⟩
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 1 := ⟨x - 1, by grind⟩
  rw [Nat.add_sub_cancel]
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by grind : 0 < t + 1) j)
  have hsq : t ^ (j + 1) * (t + 1 + 1) ^ (j + 1) ≤ (t + 1) ^ (2 * (j + 1)) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) _
  exact (le_of_eq (by ring)).trans ((Nat.mul_le_mul_left (t ^ (j + 1))
    (add_mul_pow_le (t + 1) j)).trans (hsq.trans_eq (by ring)))

/-- The number of samples containing a fixed point is at least a `k / (3 * x)` fraction of all
samples, provided `3 * k ≤ 4 * x`. -/
private lemma card_hits_lower {x k H : ℕ} (hx : 1 ≤ x) (hk : 1 ≤ k) (hkx : 3 * k ≤ 4 * x)
    (hH : H + (x - 1) ^ k = x ^ k) : k * x ^ k ≤ 3 * x * H := by
  have hmain : k * x ^ k ≤ H * (x + k) := by
    nlinarith [pred_pow_mul_le hx hk, pow_succ x k]
  exact hmain.trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (by grind))

/-! ### Representations of a sum -/

variable [AddCommGroup G]

/-- The representations `s = u + v` with `u ∈ X` and `v ∈ Y`. -/
def reprs (X Y : Finset G) (s : G) : Finset (G × G) := (X ×ˢ Y).filter fun p => p.1 + p.2 = s

/-- The number of representations `s = u + v` with `u ∈ X` and `v ∈ Y`. -/
def reprCount (X Y : Finset G) (s : G) : ℕ := #(reprs X Y s)

/-- A representation of `s` is a pair of `X ×ˢ Y` with sum `s`. -/
lemma mem_reprs {X Y : Finset G} {s : G} {p : G × G} :
    p ∈ reprs X Y s ↔ p.1 ∈ X ∧ p.2 ∈ Y ∧ p.1 + p.2 = s := by
  simp [reprs, and_assoc]

/-- Two distinct representations of the same sum differ in both coordinates. -/
lemma fst_ne_and_snd_ne_of_mem_reprs {X Y : Finset G} {s : G} {p q : G × G} (hp : p ∈ reprs X Y s)
    (hq : q ∈ reprs X Y s) (hpq : p ≠ q) : p.1 ≠ q.1 ∧ p.2 ≠ q.2 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  obtain ⟨-, -, rfl⟩ := mem_reprs.1 hp
  obtain ⟨-, -, hq⟩ := mem_reprs.1 hq
  constructor <;> rintro rfl <;> simp_all

/-- The representations of `s` inject into `X`, hence there are at most `#X` of them. -/
lemma reprCount_le_left (X Y : Finset G) (s : G) : reprCount X Y s ≤ #X := by
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    grind [mem_reprs]
  · intro p hp q hq h
    by_contra hpq
    obtain ⟨hne, -⟩ := fst_ne_and_snd_ne_of_mem_reprs hp hq hpq
    exact hne h

/-- The representations of `s` inject into `Y`, hence there are at most `#Y` of them. -/
lemma reprCount_le_right (X Y : Finset G) (s : G) : reprCount X Y s ≤ #Y := by
  apply card_le_card_of_injOn Prod.snd
  · intro p hp
    grind [mem_reprs]
  · intro p hp q hq h
    by_contra hpq
    obtain ⟨-, hne⟩ := fst_ne_and_snd_ne_of_mem_reprs hp hq hpq
    exact hne h

/-- Summing the representation function over a set of sums counts the pairs with sum there. -/
lemma sum_reprCount (X Y T : Finset G) :
    ∑ s ∈ T, reprCount X Y s = #((X ×ˢ Y).filter fun p => p.1 + p.2 ∈ T) :=
  sum_card_fiberwise_eq_card_filter _ _ _

/-! ### The probability that a sum is seen -/

/-- The probability that `s` belongs to the sumset of the two samples. -/
noncomputable def hitProb (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : ℝ :=
  𝔼 ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
    if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0

/-- A probability is nonnegative. -/
lemma hitProb_nonneg (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : 0 ≤ hitProb X Y k₁ k₂ s := by
  rw [hitProb, Fintype.expect_eq_sum_div_card]
  positivity

/-- The expected size of the sumset of the two samples. -/
noncomputable def expectSumset (X Y : Finset G) (k₁ k₂ : ℕ) : ℝ :=
  𝔼 ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), (#(bltSample X ω.1 + bltSample Y ω.2) : ℝ)

/-- The expected size of the sumset of the samples is the sum, over the possible sums, of the
probability that the sum is seen. -/
lemma expectSumset_eq_sum_hitProb (X Y : Finset G) (k₁ k₂ : ℕ) :
    expectSumset X Y k₁ k₂ = ∑ s ∈ X + Y, hitProb X Y k₁ k₂ s := by
  simp only [expectSumset, hitProb, Fintype.expect_eq_sum_div_card, ← sum_div]
  rw [sum_comm]
  congr with ω
  rw [sum_boole, filter_mem_eq_inter,
    inter_eq_right.2 (add_subset_add (bltSample_subset X ω.1) (bltSample_subset Y ω.2))]

/-! ### The second-moment estimate -/

/-- The number of samples of `X` containing a fixed element of `X`. -/
def hitCount (X : Finset G) (k : ℕ) : ℕ := #X ^ k - (#X - 1) ^ k

omit [AddCommGroup G] in
/-- All elements of `X` are sampled equally often. -/
lemma card_hits_eq_hitCount {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) = hitCount X k := card_hits ha k

omit [DecidableEq G] [AddCommGroup G] in
/-- An element of a nonempty set is sampled at least once among all samples of `k ≥ 1` points. -/
lemma one_le_hitCount {X : Finset G} (hX : 0 < #X) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ hitCount X k :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by grind) (by grind))

omit [DecidableEq G] [AddCommGroup G] in
/-- The samples containing a fixed element and those missing it make up all samples. -/
private lemma hitCount_add (X : Finset G) (k : ℕ) : hitCount X k + (#X - 1) ^ k = #X ^ k :=
  Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.sub_le _ _) k)

variable {X Y : Finset G} {k₁ k₂ : ℕ} {s : G}

/-- The number of representations of `s` whose two entries are both sampled. -/
private noncomputable def sampledReprs (X Y : Finset G) (k₁ k₂ : ℕ) (s : G)
    (ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) : ℝ :=
  ∑ p ∈ reprs X Y s, (if p.1 ∈ bltSample X ω.1 then (1 : ℝ) else 0) *
    (if p.2 ∈ bltSample Y ω.2 then (1 : ℝ) else 0)

omit [AddCommGroup G] in
/-- Summing the indicator of `a` over all samples counts the samples containing `a`. -/
private lemma sum_indicator (X : Finset G) (k : ℕ) (a : G) :
    ∑ f : Fin k → ↥X, (if a ∈ bltSample X f then (1 : ℝ) else 0) = #(hits X k a) := by
  rw [sum_boole]
  rfl

omit [AddCommGroup G] in
/-- Summing the product of the indicators of `a` and `b` over all samples counts the samples
containing both. -/
private lemma sum_indicator_mul (X : Finset G) (k : ℕ) (a b : G) :
    ∑ f : Fin k → ↥X, (if a ∈ bltSample X f then (1 : ℝ) else 0) *
      (if b ∈ bltSample X f then (1 : ℝ) else 0) = #(hits X k a ∩ hits X k b) := by
  simp only [ite_zero_mul_ite_zero, mul_one, sum_boole, hits, ← filter_and]

/-- The first moment of the number of sampled representations. -/
private lemma sum_sampledReprs :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω
      = ∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2) := by
  simp only [sampledReprs]
  rw [sum_comm]
  congr with p
  rw [← sum_indicator, ← sum_indicator, sum_mul_sum, ← Fintype.sum_prod_type']

/-- The second moment of the number of sampled representations, as a double sum over pairs of
representations. -/
private lemma sum_sq_sampledReprs :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω ^ 2
      = ∑ p ∈ reprs X Y s, ∑ q ∈ reprs X Y s,
        (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2) := by
  simp only [sampledReprs, sq, sum_mul_sum]
  rw [sum_comm]
  congr with p
  rw [sum_comm]
  congr with q
  rw [← sum_indicator_mul, ← sum_indicator_mul, sum_mul_sum, ← Fintype.sum_prod_type']
  congr with ω
  ring

/-- The number of sampled representations is nonnegative. -/
private lemma sampledReprs_nonneg (ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) :
    0 ≤ sampledReprs X Y k₁ k₂ s ω :=
  sum_nonneg fun _ _ ↦ by positivity

/-- If some representation of `s` is sampled, then `s` lies in the sumset of the samples. -/
private lemma mem_add_of_sampledReprs_pos {ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)}
    (hω : 0 < sampledReprs X Y k₁ k₂ s ω) : s ∈ bltSample X ω.1 + bltSample Y ω.2 := by
  obtain ⟨⟨u, v⟩, hp, hpne⟩ := exists_ne_zero_of_sum_ne_zero hω.ne'
  obtain ⟨-, -, rfl⟩ := mem_reprs.1 hp
  simp only [ne_eq, mul_eq_zero, ite_eq_right_iff, not_or, not_forall] at hpne
  obtain ⟨⟨hu, -⟩, hv, -⟩ := hpne
  exact add_mem_add hu hv

/-- Distinct representations are nonpositively correlated, and a representation is correlated with
itself by its own frequency. -/
private lemma card_inter_mul_card_inter_le (hX : 0 < #X) (hY : 0 < #Y) {p q : G × G}
    (hp : p ∈ reprs X Y s) (hq : q ∈ reprs X Y s) :
    (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2)
      ≤ (if p = q then (#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2) else 0)
        + (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
            * ((#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2))
            / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by
  obtain rfl | hpq := eq_or_ne p q
  · rw [ite_eq_left rfl, inter_self, inter_self]
    exact le_add_of_nonneg_right (by positivity)
  obtain ⟨hne₁, hne₂⟩ := fst_ne_and_snd_ne_of_mem_reprs hp hq hpq
  obtain ⟨hp₁, hp₂, -⟩ := mem_reprs.1 hp
  obtain ⟨hq₁, hq₂, -⟩ := mem_reprs.1 hq
  have hx : (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * (#X : ℝ) ^ k₁
      ≤ (#(hits X k₁ p.1) : ℝ) * #(hits X k₁ q.1) := by
    exact_mod_cast card_hits_inter_mul_le hp₁ hq₁ hne₁ k₁
  have hy : (#(hits Y k₂ p.2 ∩ hits Y k₂ q.2) : ℝ) * (#Y : ℝ) ^ k₂
      ≤ (#(hits Y k₂ p.2) : ℝ) * #(hits Y k₂ q.2) := by
    exact_mod_cast card_hits_inter_mul_le hp₂ hq₂ hne₂ k₂
  rw [ite_eq_right hpq, zero_add, le_div_iff₀ (by positivity)]
  linarith [mul_le_mul hx hy (by positivity) (by positivity)]

/-- The second moment of the number of sampled representations is at most its first moment plus
the square of its first moment, normalised by the number of samples. -/
private lemma sum_sq_sampledReprs_le (hX : 0 < #X) (hY : 0 < #Y) :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω ^ 2
      ≤ (∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2))
        + (∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)) ^ 2
            / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by
  rw [sum_sq_sampledReprs]
  refine (sum_le_sum fun p hp ↦ sum_le_sum fun q hq ↦
    card_inter_mul_card_inter_le hX hY hp hq).trans_eq ?_
  simp only [sum_add_distrib, sum_ite_eq, sum_ite_mem, inter_self, ← sum_div, ← mul_sum,
    ← sum_mul, sq]

/-- The expected number of sampled representations, up to the number of samples. -/
private lemma sum_card_hits_mul :
    ∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
      = reprCount X Y s * (hitCount X k₁ * hitCount Y k₂) := by
  rw [reprCount, ← nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp₁, hp₂, -⟩ := mem_reprs.1 hp
  rw [card_hits_eq_hitCount hp₁, card_hits_eq_hitCount hp₂]

/-- The pointwise inequality of the second-moment method: `2 * c * Z - (c * Z) ^ 2` is at most the
indicator that `s` is seen, where `Z` is the number of sampled representations of `s`. -/
private lemma two_mul_sub_sq_le (c : ℝ) (ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) :
    2 * (c * sampledReprs X Y k₁ k₂ s ω) - (c * sampledReprs X Y k₁ k₂ s ω) ^ 2
      ≤ if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0 := by
  obtain h | h := (sampledReprs_nonneg (s := s) ω).eq_or_lt
  · simp only [← h, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rw [ite_eq_left (mem_add_of_sampledReprs_pos h)]
    nlinarith [sq_nonneg (1 - c * sampledReprs X Y k₁ k₂ s ω)]

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

/-- The core second-moment bound: the probability that `s` is seen is at least `W / (N + W)`,
where `N` is the number of samples and `W / N` is the expected number of representations of `s`
whose two entries are both sampled. -/
private lemma hitProb_ge (hs : s ∈ X + Y) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    ((reprCount X Y s : ℝ) * (hitCount X k₁ * hitCount Y k₂))
        / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂
            + (reprCount X Y s : ℝ) * (hitCount X k₁ * hitCount Y k₂))
      ≤ hitProb X Y k₁ k₂ s := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_add.1 hs
  have hX : 0 < #X := card_pos.2 ⟨u, hu⟩
  have hY : 0 < #Y := card_pos.2 ⟨v, hv⟩
  have hW : (0 : ℝ) < reprCount X Y s * (hitCount X k₁ * hitCount Y k₂) :=
    mul_pos (Nat.cast_pos.2 (card_pos.2 ⟨(u, v), mem_reprs.2 ⟨hu, hv, huv⟩⟩))
      (mul_pos (Nat.cast_pos.2 (one_le_hitCount hX hk₁)) (Nat.cast_pos.2 (one_le_hitCount hY hk₂)))
  rw [hitProb, Fintype.expect_eq_sum_div_card,
    (by simp : (Fintype.card ((Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) : ℝ) = (#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂)]
  refine div_add_le_div_of_second_moment (by positivity) hW
    (sum_card_hits_mul (s := s) ▸ sum_sq_sampledReprs_le hX hY) ?_
  intro c
  refine le_trans (le_of_eq ?_) (sum_le_sum fun ω _ ↦ two_mul_sub_sq_le c ω)
  simp only [mul_pow, sum_sub_distrib, ← mul_sum, sum_sampledReprs, sum_card_hits_mul]

/-- **The one-sum sampling estimate.** If `s` has `r` representations as a sum of an element of `X`
and an element of `Y`, then `s` is seen by the two samples with probability at least
`r * k₁ * k₂ / (9 * #X * #Y + r * k₁ * k₂)`. -/
lemma div_le_hitProb (hs : s ∈ X + Y) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (hkX : 3 * k₁ ≤ 4 * #X) (hkY : 3 * k₂ ≤ 4 * #Y) :
    ((reprCount X Y s : ℝ) * (k₁ * k₂))
        / (9 * ((#X : ℝ) * #Y) + (reprCount X Y s : ℝ) * (k₁ * k₂))
      ≤ hitProb X Y k₁ k₂ s := by
  obtain ⟨u, hu, v, hv, -⟩ := mem_add.1 hs
  have hX : 0 < #X := card_pos.2 ⟨u, hu⟩
  have hY : 0 < #Y := card_pos.2 ⟨v, hv⟩
  refine le_trans ?_ (hitProb_ge hs hk₁ hk₂)
  apply div_add_le_div_add (by positivity) (by positivity) (by positivity) (by positivity)
  have hcomb : ((k₁ * #X ^ k₁ * (k₂ * #Y ^ k₂) : ℕ) : ℝ)
      ≤ ((3 * #X * hitCount X k₁ * (3 * #Y * hitCount Y k₂) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul (card_hits_lower hX hk₁ hkX (hitCount_add X k₁))
      (card_hits_lower hY hk₂ hkY (hitCount_add Y k₂))
  push_cast at hcomb
  nlinarith [mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ reprCount X Y s)]

end Sampling

end LargeSumsetsFromSubsets
