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

The bound, `LargeSumsetsFromSubsets.Sampling.hitProb_lower_bound`, is a second-moment estimate.
The representations of a fixed `s` form a matching, so the events "the two entries of a
representation are both sampled" are pairwise nonpositively correlated, whence the second moment of
their number `Z` exceeds neither `𝔼 Z + (𝔼 Z) ^ 2`; the pointwise inequality
`1 ≤ 2 * Z / t - (Z / t) ^ 2`, valid when `Z` is positive, then bounds the probability that `Z` is
positive from below by `𝔼 Z / (1 + 𝔼 Z)`.
-/

@[expose] public section

namespace LargeSumsetsFromSubsets

open Finset

open scoped BigOperators Pointwise

variable {G : Type*} [DecidableEq G]

/-- The finset underlying a sample with replacement from `A`. -/
def bltSample (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : Finset G := univ.image fun i ↦ f i

lemma mem_bltSample {A : Finset G} {k : ℕ} {f : Fin k → ↥A} {a : G} :
    a ∈ bltSample A f ↔ ∃ i, (f i : G) = a := by
  simp [bltSample, eq_comm]

lemma bltSample_subset (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : bltSample A f ⊆ A := by
  intro a ha
  obtain ⟨i, rfl⟩ := mem_bltSample.1 ha
  exact (f i).2

lemma card_bltSample_le (A : Finset G) {k : ℕ} (f : Fin k → ↥A) : #(bltSample A f) ≤ k := by
  apply card_image_le.trans
  simp

namespace Sampling

/-! ### Counting samples -/

/-- The samples from `X` avoiding a set `Z` are exactly the samples from `X \ Z`. -/
lemma card_avoid (X Z : Finset G) (k : ℕ) :
    #(univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ Z) = #(X \ Z) ^ k := by
  have hfib : (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ Z)
      = Fintype.piFinset fun _ : Fin k => univ.filter fun b : ↥X => (b : G) ∉ Z := by
    ext f
    simp [Fintype.mem_piFinset]
  have hcard : #(univ.filter fun b : ↥X => (b : G) ∉ Z) = #(X \ Z) := by
    refine card_bij (fun b _ => (b : G)) ?_ ?_ ?_
    · intro b hb
      exact mem_sdiff.2 ⟨b.2, (mem_filter.1 hb).2⟩
    · intro b _ c _ h
      exact Subtype.ext h
    · intro a ha
      exact ⟨⟨a, (mem_sdiff.1 ha).1⟩, mem_filter.2 ⟨mem_univ _, (mem_sdiff.1 ha).2⟩, rfl⟩
  rw [hfib, Fintype.card_piFinset, hcard]
  simp

/-- The samples from `X` that contain the element `a`. -/
def hits (X : Finset G) (k : ℕ) (a : G) : Finset (Fin k → ↥X) :=
  univ.filter fun f => a ∈ bltSample X f

omit [DecidableEq G] in
lemma card_univ_fun (X : Finset G) (k : ℕ) : #(univ : Finset (Fin k → ↥X)) = #X ^ k := by simp

lemma card_sdiff_singleton {X : Finset G} {a : G} (ha : a ∈ X) : #(X \ {a}) = #X - 1 := by
  rw [card_sdiff_of_subset (singleton_subset_iff.2 ha), card_singleton]

lemma card_hits_add {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) + (#X - 1) ^ k = #X ^ k := by
  have hcompl : (univ : Finset (Fin k → ↥X)) \ hits X k a
      = univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({a} : Finset G) := by
    ext f
    simp only [mem_sdiff, mem_univ, true_and, hits, mem_filter, mem_bltSample, not_exists,
      mem_singleton]
  have hsplit := card_sdiff_add_card_eq_card (s := hits X k a)
    (t := (univ : Finset (Fin k → ↥X))) (subset_univ _)
  rw [hcompl, card_avoid, card_sdiff_singleton ha, card_univ_fun] at hsplit
  omega

lemma card_hits {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) = #X ^ k - (#X - 1) ^ k := by
  have := card_hits_add ha k
  omega

private lemma sub_two_pow_mul_le {x : ℕ} (hx : 2 ≤ x) (k : ℕ) :
    (x - 2) ^ k * x ^ k ≤ ((x - 1) ^ k) ^ 2 := by
  rw [← pow_mul, ← mul_pow, mul_comm k 2, pow_mul]
  refine Nat.pow_le_pow_left ?_ k
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 2 := ⟨x - 2, by omega⟩
  have h1 : t + 2 - 1 = t + 1 := by omega
  have h2 : t + 2 - 2 = t := by omega
  rw [h1, h2]
  nlinarith

/-- Two distinct elements are nonpositively correlated: the samples meeting both are fewer than
the product of the two frequencies. -/
lemma card_hits_inter_mul_le {X : Finset G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (k : ℕ) : #(hits X k a ∩ hits X k b) * #X ^ k ≤ #(hits X k a) * #(hits X k b) := by
  have hpairsub : ({a, b} : Finset G) ⊆ X := by simp [insert_subset_iff, ha, hb]
  have hpaircard : #({a, b} : Finset G) = 2 := by
    rw [card_insert_of_notMem (by simpa using hab), card_singleton]
  have hxle : 2 ≤ #X := hpaircard ▸ card_le_card hpairsub
  have hcompl : (univ : Finset (Fin k → ↥X)) \ (hits X k a ∩ hits X k b)
      = (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({a} : Finset G))
        ∪ univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({b} : Finset G) := by
    ext f
    simp only [mem_sdiff, mem_univ, true_and, mem_inter, hits, mem_filter, mem_union,
      mem_bltSample, not_and_or, not_exists, mem_singleton]
  have hinter : (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({a} : Finset G))
      ∩ (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({b} : Finset G))
      = univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({a, b} : Finset G) := by
    ext f
    simp only [mem_inter, mem_filter, mem_univ, true_and, mem_singleton, mem_insert, not_or]
    exact forall_and.symm
  have hunion := card_union_add_card_inter
    (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({a} : Finset G))
    (univ.filter fun f : Fin k → ↥X => ∀ i, (f i : G) ∉ ({b} : Finset G))
  rw [hinter, card_avoid, card_avoid, card_avoid, card_sdiff_singleton ha,
    card_sdiff_singleton hb, card_sdiff_of_subset hpairsub, hpaircard] at hunion
  have hsplit := card_sdiff_add_card_eq_card (s := hits X k a ∩ hits X k b)
    (t := (univ : Finset (Fin k → ↥X))) (subset_univ _)
  rw [hcompl, card_univ_fun] at hsplit
  have ha' := card_hits_add ha (X := X) k
  have hb' := card_hits_add hb (X := X) k
  have h1 : #(hits X k a ∩ hits X k b) + 2 * (#X - 1) ^ k = #X ^ k + (#X - 2) ^ k := by omega
  have hI : #(hits X k a ∩ hits X k b) * #X ^ k + 2 * ((#X - 1) ^ k * #X ^ k)
      = #X ^ k * #X ^ k + (#X - 2) ^ k * #X ^ k := by
    have hfac : #(hits X k a ∩ hits X k b) * #X ^ k + 2 * ((#X - 1) ^ k * #X ^ k)
        = (#(hits X k a ∩ hits X k b) + 2 * (#X - 1) ^ k) * #X ^ k := by ring
    rw [hfac, h1]
    ring
  have hprod : #(hits X k a) * #(hits X k b) + 2 * ((#X - 1) ^ k * #X ^ k)
      = #X ^ k * #X ^ k + (#X - 1) ^ k * (#X - 1) ^ k := by
    have hab' : #(hits X k b) = #(hits X k a) := by omega
    rw [hab', ← ha']
    ring
  linarith [sub_two_pow_mul_le hxle k, hI, hprod]

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
    have hstep : (x + (j + 1) + 1) * x ^ (j + 1) ≤ (x + 1) * ((x + j + 1) * x ^ j) := by
      have hfac : (x + (j + 1) + 1) * x ≤ (x + 1) * (x + j + 1) := by nlinarith
      have hrw₁ : (x + (j + 1) + 1) * x ^ (j + 1) = (x + (j + 1) + 1) * x * x ^ j := by ring
      have hrw₂ : (x + 1) * ((x + j + 1) * x ^ j) = (x + 1) * (x + j + 1) * x ^ j := by ring
      rw [hrw₁, hrw₂]
      exact Nat.mul_le_mul_right _ hfac
    apply hstep.trans
    rw [pow_succ (x + 1) (j + 1), mul_comm ((x + 1) ^ (j + 1)) (x + 1)]
    exact Nat.mul_le_mul_left _ ih

/-- The complement of the frequency with which a fixed point is sampled: an element is missed by
all `k` samples with probability at most `x / (x + k)`. -/
private lemma pred_pow_mul_le {x : ℕ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x - 1) ^ k * (x + k) ≤ x ^ (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsq : (x - 1) ^ (j + 1) * (x + 1) ^ (j + 1) ≤ (x ^ 2) ^ (j + 1) := by
    rw [← mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    obtain ⟨t, rfl⟩ : ∃ t, x = t + 1 := ⟨x - 1, by omega⟩
    have h1 : t + 1 - 1 = t := by omega
    rw [h1]
    nlinarith
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by omega : 0 < x) j)
  have hrw : (x - 1) ^ (j + 1) * (x + (j + 1)) * x ^ j
      = (x - 1) ^ (j + 1) * ((x + j + 1) * x ^ j) := by ring
  rw [hrw]
  refine (Nat.mul_le_mul_left _ (add_mul_pow_le x j)).trans (hsq.trans ?_)
  rw [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The number of samples containing a fixed point is at least a `k / (3 * x)` fraction of all
samples, provided `3 * k ≤ 4 * x`. -/
private lemma card_hits_lower {x k H : ℕ} (hx : 1 ≤ x) (hk : 1 ≤ k) (hkx : 3 * k ≤ 4 * x)
    (hH : H + (x - 1) ^ k = x ^ k) : k * x ^ k ≤ 3 * x * H := by
  have hmain : k * x ^ k ≤ H * (x + k) := by
    have hkey := pred_pow_mul_le hx hk
    have hxpow : x ^ (k + 1) = x ^ k * x := by ring
    nlinarith [hH, hkey, hxpow]
  apply hmain.trans
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### Representations of a sum -/

variable [AddCommGroup G]

/-- The representations `s = u + v` with `u ∈ X` and `v ∈ Y`. -/
def reprs (X Y : Finset G) (s : G) : Finset (G × G) := (X ×ˢ Y).filter fun p => p.1 + p.2 = s

/-- The number of representations `s = u + v` with `u ∈ X` and `v ∈ Y`. -/
def reprCount (X Y : Finset G) (s : G) : ℕ := #(reprs X Y s)

lemma mem_reprs {X Y : Finset G} {s : G} {p : G × G} :
    p ∈ reprs X Y s ↔ p.1 ∈ X ∧ p.2 ∈ Y ∧ p.1 + p.2 = s := by
  simp [reprs, and_assoc]

/-- Two distinct representations of the same sum differ in both coordinates. -/
lemma repr_ne_of_ne {X Y : Finset G} {s : G} {p q : G × G} (hp : p ∈ reprs X Y s)
    (hq : q ∈ reprs X Y s) (hpq : p ≠ q) : p.1 ≠ q.1 ∧ p.2 ≠ q.2 := by
  rw [mem_reprs] at hp hq
  constructor
  · intro h
    refine hpq (Prod.ext h ?_)
    rw [← hq.2.2, ← h] at hp
    exact add_left_cancel hp.2.2
  · intro h
    refine hpq (Prod.ext ?_ h)
    rw [← hq.2.2, ← h] at hp
    exact add_right_cancel hp.2.2

/-- The representations of `s` inject into `X`, hence there are at most `#X` of them. -/
lemma reprCount_le_left (X Y : Finset G) (s : G) : reprCount X Y s ≤ #X := by
  apply card_le_card_of_injOn Prod.fst
  · intro _ hp
    exact (mem_reprs.1 hp).1
  · intro p hp q hq h
    by_contra hpq
    exact (repr_ne_of_ne hp hq hpq).1 h

/-- The representations of `s` inject into `Y`, hence there are at most `#Y` of them. -/
lemma reprCount_le_right (X Y : Finset G) (s : G) : reprCount X Y s ≤ #Y := by
  apply card_le_card_of_injOn Prod.snd (fun p hp => (mem_reprs.1 hp).2.1)
  intro p hp q hq h
  by_contra hpq
  exact (repr_ne_of_ne hp hq hpq).2 h

/-- Summing the representation function over a set of sums counts the pairs with sum there. -/
lemma sum_reprCount (X Y T : Finset G) :
    ∑ s ∈ T, reprCount X Y s = #((X ×ˢ Y).filter fun p => p.1 + p.2 ∈ T) := by
  refine Eq.trans (sum_congr rfl ?_)
    (card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 + p.2)
      (s := (X ×ˢ Y).filter fun p => p.1 + p.2 ∈ T) (t := T)
      fun p hp => (mem_filter.1 hp).2).symm
  intro s hs
  unfold reprCount reprs
  congr 1
  ext p
  simp only [mem_filter, mem_product, and_assoc]
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    rw [h.2.2]
    exact hs
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.2⟩

/-! ### The probability that a sum is seen -/

/-- The probability that `s` belongs to the sumset of the two samples. -/
noncomputable def hitProb (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : ℝ :=
  𝔼 ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
    if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0

lemma hitProb_nonneg (X Y : Finset G) (k₁ k₂ : ℕ) (s : G) : 0 ≤ hitProb X Y k₁ k₂ s := by
  rw [hitProb, Fintype.expect_eq_sum_div_card]
  refine div_nonneg (sum_nonneg ?_) (Nat.cast_nonneg _)
  intros ω
  split_ifs <;> norm_num

/-- The expected size of the sumset of the two samples. -/
noncomputable def expectSumset (X Y : Finset G) (k₁ k₂ : ℕ) : ℝ :=
  𝔼 ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), (#(bltSample X ω.1 + bltSample Y ω.2) : ℝ)

/-- The expected size of the sumset of the samples is the sum, over the possible sums, of the
probability that the sum is seen. -/
theorem expectSumset_eq_sum_hitProb (X Y : Finset G) (k₁ k₂ : ℕ) :
    expectSumset X Y k₁ k₂ = ∑ s ∈ X + Y, hitProb X Y k₁ k₂ s := by
  unfold expectSumset
  have hpt : ∀ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
      (#(bltSample X ω.1 + bltSample Y ω.2) : ℝ)
        = ∑ s ∈ X + Y, if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0 := by
    intro ω
    rw [sum_boole, filter_mem_eq_inter,
      inter_eq_right.2 (add_subset_add (bltSample_subset X ω.1) (bltSample_subset Y ω.2))]
  simp only [hpt, hitProb, Fintype.expect_eq_sum_div_card]
  rw [← sum_div, sum_comm]

/-! ### The second-moment estimate -/

/-- The number of samples of `X` containing a fixed element of `X`. -/
def hitCount (X : Finset G) (k : ℕ) : ℕ := #X ^ k - (#X - 1) ^ k

omit [AddCommGroup G] in
lemma card_hits_eq {X : Finset G} {a : G} (ha : a ∈ X) (k : ℕ) :
    #(hits X k a) = hitCount X k := card_hits ha k

omit [DecidableEq G] [AddCommGroup G] in
lemma one_le_hitCount {X : Finset G} (hX : 0 < #X) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ hitCount X k := by
  have : (#X - 1) ^ k < #X ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
  unfold hitCount
  omega

variable {X Y : Finset G} {k₁ k₂ : ℕ} {s : G}

/-- The number of representations of `s` whose two entries are both sampled. -/
private noncomputable def sampledReprs (X Y : Finset G) (k₁ k₂ : ℕ) (s : G)
    (ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) : ℝ :=
  ∑ p ∈ reprs X Y s, (if p.1 ∈ bltSample X ω.1 then (1 : ℝ) else 0) *
    (if p.2 ∈ bltSample Y ω.2 then (1 : ℝ) else 0)

private lemma sum_prod_factor {α β : Type*} [Fintype α] [Fintype β] (F : α → ℝ) (H : β → ℝ) :
    ∑ ω : α × β, F ω.1 * H ω.2 = (∑ a, F a) * ∑ b, H b := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

omit [AddCommGroup G] in
private lemma sum_indicator (X : Finset G) (k : ℕ) (a : G) :
    ∑ f : Fin k → ↥X, (if a ∈ bltSample X f then (1 : ℝ) else 0) = #(hits X k a) := by
  rw [sum_boole]
  rfl

omit [AddCommGroup G] in
private lemma sum_indicator_mul (X : Finset G) (k : ℕ) (a b : G) :
    ∑ f : Fin k → ↥X, (if a ∈ bltSample X f then (1 : ℝ) else 0) *
      (if b ∈ bltSample X f then (1 : ℝ) else 0) = #(hits X k a ∩ hits X k b) := by
  have hmul : ∀ f : Fin k → ↥X, (if a ∈ bltSample X f then (1 : ℝ) else 0) *
      (if b ∈ bltSample X f then (1 : ℝ) else 0)
      = if a ∈ bltSample X f ∧ b ∈ bltSample X f then (1 : ℝ) else 0 := by
    intro f
    split_ifs <;> simp_all
  simp only [hmul, sum_boole, hits, ← filter_and]

/-- The first moment of the number of sampled representations. -/
private lemma sum_sampledReprs :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω
      = ∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2) := by
  unfold sampledReprs
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_prod_factor (fun f : Fin k₁ → ↥X => if p.1 ∈ bltSample X f then (1 : ℝ) else 0)
      (fun g : Fin k₂ → ↥Y => if p.2 ∈ bltSample Y g then (1 : ℝ) else 0),
    sum_indicator, sum_indicator]

/-- The second moment of the number of sampled representations is at most its first moment plus
the square of its first moment, normalised by the number of samples. -/
private lemma sum_sq_sampledReprs :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω ^ 2
      = ∑ p ∈ reprs X Y s, ∑ q ∈ reprs X Y s,
        (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2) := by
  have hexp : ∀ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω ^ 2
      = ∑ p ∈ reprs X Y s, ∑ q ∈ reprs X Y s,
        ((if p.1 ∈ bltSample X ω.1 then (1 : ℝ) else 0) *
          (if q.1 ∈ bltSample X ω.1 then (1 : ℝ) else 0)) *
        ((if p.2 ∈ bltSample Y ω.2 then (1 : ℝ) else 0) *
          (if q.2 ∈ bltSample Y ω.2 then (1 : ℝ) else 0)) := by
    intro ω
    rw [sq, sampledReprs, Finset.sum_mul_sum]
    apply sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  simp only [hexp]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro q _
  rw [sum_prod_factor (fun f : Fin k₁ → ↥X => (if p.1 ∈ bltSample X f then (1 : ℝ) else 0) *
      (if q.1 ∈ bltSample X f then (1 : ℝ) else 0))
      (fun g : Fin k₂ → ↥Y => (if p.2 ∈ bltSample Y g then (1 : ℝ) else 0) *
      (if q.2 ∈ bltSample Y g then (1 : ℝ) else 0)),
    sum_indicator_mul, sum_indicator_mul]

private lemma sampledReprs_nonneg (ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) :
    0 ≤ sampledReprs X Y k₁ k₂ s ω := by
  apply sum_nonneg
  intro p _
  apply mul_nonneg <;> split_ifs <;> norm_num

private lemma mem_add_of_sampledReprs_pos {ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y)}
    (hω : 0 < sampledReprs X Y k₁ k₂ s ω) : s ∈ bltSample X ω.1 + bltSample Y ω.2 := by
  obtain ⟨p, hp, hpne⟩ := exists_ne_zero_of_sum_ne_zero hω.ne'
  by_cases h₁ : p.1 ∈ bltSample X ω.1
  · by_cases h₂ : p.2 ∈ bltSample Y ω.2
    · exact (mem_reprs.1 hp).2.2 ▸ add_mem_add h₁ h₂
    · simp [h₂] at hpne
  · simp [h₁] at hpne

private lemma sum_sq_sampledReprs_le (hX : 0 < #X) (hY : 0 < #Y) :
    ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y), sampledReprs X Y k₁ k₂ s ω ^ 2
      ≤ (∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2))
        + (∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)) ^ 2
            / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by
  have hXpos : (0 : ℝ) < (#X : ℝ) ^ k₁ := by positivity
  have hYpos : (0 : ℝ) < (#Y : ℝ) ^ k₂ := by positivity
  have hbound : ∀ p ∈ reprs X Y s, ∀ q ∈ reprs X Y s,
      (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2)
        ≤ (if p = q then (#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2) else 0)
          + (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
              * ((#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2))
              / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by
    intro p hp q hq
    by_cases hpq : p = q
    · subst hpq
      rw [ite_eq_left rfl, inter_self, inter_self]
      have hnn : (0 : ℝ) ≤ (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
          * ((#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2))
          / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by positivity
      linarith
    · rw [ite_eq_right hpq]
      obtain ⟨hne₁, hne₂⟩ := repr_ne_of_ne hp hq hpq
      have hx : (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * (#X : ℝ) ^ k₁
          ≤ (#(hits X k₁ p.1) : ℝ) * #(hits X k₁ q.1) := by
        exact_mod_cast card_hits_inter_mul_le (mem_reprs.1 hp).1 (mem_reprs.1 hq).1 hne₁ k₁
      have hy : (#(hits Y k₂ p.2 ∩ hits Y k₂ q.2) : ℝ) * (#Y : ℝ) ^ k₂
          ≤ (#(hits Y k₂ p.2) : ℝ) * #(hits Y k₂ q.2) := by
        exact_mod_cast card_hits_inter_mul_le (mem_reprs.1 hp).2.1 (mem_reprs.1 hq).2.1 hne₂ k₂
      rw [zero_add, le_div_iff₀ (by positivity)]
      have hlhs : (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * #(hits Y k₂ p.2 ∩ hits Y k₂ q.2)
          * ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂)
          = (#(hits X k₁ p.1 ∩ hits X k₁ q.1) : ℝ) * (#X : ℝ) ^ k₁
            * ((#(hits Y k₂ p.2 ∩ hits Y k₂ q.2) : ℝ) * (#Y : ℝ) ^ k₂) := by ring
      have hrhs : (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
          * ((#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2))
          = (#(hits X k₁ p.1) : ℝ) * #(hits X k₁ q.1)
            * ((#(hits Y k₂ p.2) : ℝ) * #(hits Y k₂ q.2)) := by ring
      rw [hlhs, hrhs]
      exact mul_le_mul hx hy (by positivity) (by positivity)
  rw [sum_sq_sampledReprs]
  refine (sum_le_sum fun p hp => sum_le_sum fun q hq => hbound p hp q hq).trans (le_of_eq ?_)
  have hrow : ∀ p ∈ reprs X Y s, ∑ q ∈ reprs X Y s,
      ((if p = q then (#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2) else 0)
        + (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
            * ((#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2))
            / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂))
      = (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
        + (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2)
            * (∑ q ∈ reprs X Y s, (#(hits X k₁ q.1) : ℝ) * #(hits Y k₂ q.2))
            / ((#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂) := by
    intro p hp
    rw [sum_add_distrib, sum_ite_eq, ite_eq_left hp, ← sum_div, ← mul_sum]
  rw [sum_congr rfl hrow, sum_add_distrib, ← sum_div, ← sum_mul, sq]

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
  have hr : 1 ≤ reprCount X Y s :=
    card_pos.2 ⟨(u, v), mem_reprs.2 ⟨hu, hv, huv⟩⟩
  set N : ℝ := (#X : ℝ) ^ k₁ * (#Y : ℝ) ^ k₂ with hNdef
  set W : ℝ := (reprCount X Y s : ℝ) * (hitCount X k₁ * hitCount Y k₂) with hWdef
  have hNpos : 0 < N := by positivity
  have hWpos : 0 < W := by
    have h₁ : (0 : ℝ) < (reprCount X Y s : ℝ) := by exact_mod_cast hr
    have h₂ : (0 : ℝ) < (hitCount X k₁ : ℝ) := by exact_mod_cast one_le_hitCount hX hk₁
    have h₃ : (0 : ℝ) < (hitCount Y k₂ : ℝ) := by exact_mod_cast one_le_hitCount hY hk₂
    rw [hWdef]
    exact mul_pos h₁ (mul_pos h₂ h₃)
  have hNW : 0 < N + W := by linarith
  have hWsum : ∑ p ∈ reprs X Y s, (#(hits X k₁ p.1) : ℝ) * #(hits Y k₂ p.2) = W := by
    rw [sum_congr rfl fun p hp => by
      rw [card_hits_eq (mem_reprs.1 hp).1, card_hits_eq (mem_reprs.1 hp).2.1],
      sum_const, nsmul_eq_mul, hWdef, reprCount]
  set c : ℝ := N / (N + W) with hcdef
  have hcpos : 0 < c := by positivity
  have hpt : ∀ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
      2 * (c * sampledReprs X Y k₁ k₂ s ω) - (c * sampledReprs X Y k₁ k₂ s ω) ^ 2
        ≤ if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0 := by
    intro ω
    rcases (sampledReprs_nonneg (X := X) (Y := Y) (k₁ := k₁) (k₂ := k₂) (s := s) ω).eq_or_lt with
      h | h
    · rw [← h]
      have : (0 : ℝ) ≤ if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0 := by
        split_ifs <;> norm_num
      simpa using this
    · rw [ite_eq_left (mem_add_of_sampledReprs_pos h)]
      nlinarith [sq_nonneg (1 - c * sampledReprs X Y k₁ k₂ s ω)]
  have hsum : c * W
      ≤ ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
          if s ∈ bltSample X ω.1 + bltSample Y ω.2 then (1 : ℝ) else 0 := by
    refine le_trans ?_ (sum_le_sum fun ω _ => hpt ω)
    have hexpand : ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
        (2 * (c * sampledReprs X Y k₁ k₂ s ω) - (c * sampledReprs X Y k₁ k₂ s ω) ^ 2)
        = 2 * c * W - c ^ 2 * ∑ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
            sampledReprs X Y k₁ k₂ s ω ^ 2 := by
      have hterm : ∀ ω : (Fin k₁ → ↥X) × (Fin k₂ → ↥Y),
          2 * (c * sampledReprs X Y k₁ k₂ s ω) - (c * sampledReprs X Y k₁ k₂ s ω) ^ 2
            = 2 * c * sampledReprs X Y k₁ k₂ s ω - c ^ 2 * sampledReprs X Y k₁ k₂ s ω ^ 2 :=
        fun ω => by ring
      simp only [hterm]
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sampledReprs, hWsum]
    rw [hexpand]
    have hsq := sum_sq_sampledReprs_le (X := X) (Y := Y) (k₁ := k₁) (k₂ := k₂) (s := s) hX hY
    rw [hWsum] at hsq
    have hc : c ^ 2 * (W + W ^ 2 / N) = c * W := by
      rw [hcdef]
      field_simp
    nlinarith [sq_nonneg c, hsq, hcpos]
  have hcard : ((Fintype.card ((Fin k₁ → ↥X) × (Fin k₂ → ↥Y)) : ℕ) : ℝ) = N := by
    simp [hNdef]
  rw [hitProb, Fintype.expect_eq_sum_div_card, hcard, div_le_div_iff₀ hNW hNpos]
  have hmul := mul_le_mul_of_nonneg_right hsum hNW.le
  have hcw : c * W * (N + W) = W * N := by
    rw [hcdef]
    field_simp
  linarith

/-- **The one-sum sampling estimate.** If `s` has `r` representations as a sum of an element of `X`
and an element of `Y`, then `s` is seen by the two samples with probability at least
`r * k₁ * k₂ / (9 * #X * #Y + r * k₁ * k₂)`. -/
theorem hitProb_lower_bound (hs : s ∈ X + Y) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (hkX : 3 * k₁ ≤ 4 * #X) (hkY : 3 * k₂ ≤ 4 * #Y) :
    ((reprCount X Y s : ℝ) * (k₁ * k₂))
        / (9 * ((#X : ℝ) * #Y) + (reprCount X Y s : ℝ) * (k₁ * k₂))
      ≤ hitProb X Y k₁ k₂ s := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_add.1 hs
  have hX : 0 < #X := card_pos.2 ⟨u, hu⟩
  have hY : 0 < #Y := card_pos.2 ⟨v, hv⟩
  refine le_trans ?_ (hitProb_ge hs hk₁ hk₂)
  apply div_add_le_div_add (by positivity) (by positivity) (by positivity) (by positivity)
  have hXhit : hitCount X k₁ + (#X - 1) ^ k₁ = #X ^ k₁ := by
    have hle : (#X - 1) ^ k₁ ≤ #X ^ k₁ := Nat.pow_le_pow_left (by omega) k₁
    unfold hitCount
    omega
  have hYhit : hitCount Y k₂ + (#Y - 1) ^ k₂ = #Y ^ k₂ := by
    have hle : (#Y - 1) ^ k₂ ≤ #Y ^ k₂ := Nat.pow_le_pow_left (by omega) k₂
    unfold hitCount
    omega
  have hnat : reprCount X Y s * (k₁ * k₂) * (#X ^ k₁ * #Y ^ k₂)
      ≤ reprCount X Y s * (hitCount X k₁ * hitCount Y k₂) * (9 * (#X * #Y)) := by
    have hcomb := Nat.mul_le_mul (card_hits_lower hX hk₁ hkX hXhit)
      (card_hits_lower hY hk₂ hkY hYhit)
    have hrw₁ : reprCount X Y s * (k₁ * k₂) * (#X ^ k₁ * #Y ^ k₂)
        = reprCount X Y s * (k₁ * #X ^ k₁ * (k₂ * #Y ^ k₂)) := by ring
    have hrw₂ : reprCount X Y s * (hitCount X k₁ * hitCount Y k₂) * (9 * (#X * #Y))
        = reprCount X Y s * (3 * #X * hitCount X k₁ * (3 * #Y * hitCount Y k₂)) := by ring
    rw [hrw₁, hrw₂]
    exact Nat.mul_le_mul_left _ hcomb
  exact_mod_cast hnat

end Sampling

end LargeSumsetsFromSubsets
