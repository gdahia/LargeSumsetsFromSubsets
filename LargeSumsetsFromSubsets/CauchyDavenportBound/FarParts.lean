/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound.ConsecutiveIntervals
import LargeSumsetsFromSubsets.CauchyDavenportBound.IntervalCovering
import LargeSumsetsFromSubsets.CauchyDavenportBound.Stickout
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Rify

/-!
# The far parts

The far parts of the proof of Theorem 1 of Bollobás, Leader and Tiba: the points of `A` and `B`
outside the intervals `I = I₁ ∪ I₂ ∪ I₃` and `J = J₁ ∪ J₂ ∪ J₃` of Lemma 9, which lie at distance
at least `⌊β * p / 8⌋₊` from the middle intervals `I₂` and `J₂`. Cut `J₂` into blocks of length
`l`. By Lemma 12 each point `x` of `A \ I` has a block `J'` with `x + J'` disjoint from `I₂ + J₂`,
and Corollary 11, applied to each block and to the points of `A \ I` that it serves, gives small
subsets of `A \ I` and `B` with `#(A \ I)` sums outside `I₂ + J₂` and outside a given set `W`.

## Main definitions

* `block v l i`: the `i`-th block `arithProg (v + i * l) 1 l` of length `l` of an interval
  starting at `v`.
* `goodPoints X T v l i`: the points `x` of `X` such that `x + block v l i` avoids `T`.

## Main statements

* `exists_card_eq_disjoint_add_of_disjoint`: Lemma 12 and Corollary 11 for a set `X` far from an
  interval `I` and a set `Y` dense in an interval `J`.
* `exists_card_eq_card_sdiff_add_card_sdiff_disjoint`: the far parts in the setting of Lemma 9.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {p : ℕ}

/-- The `i`-th block `arithProg (v + i * l) 1 l` of length `l` of an interval starting at `v`. -/
def block (v : ZMod p) (l i : ℕ) : Finset (ZMod p) := arithProg (v + (i * l : ℕ)) 1 l

/-- The points `x` of `X` whose translate `x + block v l i` avoids `T`. -/
def goodPoints (X T : Finset (ZMod p)) (v : ZMod p) (l i : ℕ) : Finset (ZMod p) :=
  X.filter fun x ↦ Disjoint ((block v l i).image (x + ·)) T

/-- The good points of `X` lie in `X`. -/
lemma goodPoints_subset {X : Finset (ZMod p)} (T : Finset (ZMod p)) (v : ZMod p) (l i : ℕ) :
    goodPoints X T v l i ⊆ X :=
  filter_subset _ _

/-- There are at most `#X` good points of `X`. -/
lemma card_goodPoints_le {X : Finset (ZMod p)} (T : Finset (ZMod p)) (v : ZMod p) (l i : ℕ) :
    #(goodPoints X T v l i) ≤ #X :=
  card_le_card (goodPoints_subset T v l i)

/-- The sums of good points of `X` for the `i`-th block and points of this block avoid `T`. -/
lemma disjoint_add_of_subset_goodPoints {X X' Y' T : Finset (ZMod p)} {v : ZMod p} {l i : ℕ}
    (hX' : X' ⊆ goodPoints X T v l i) (hY' : Y' ⊆ block v l i) : Disjoint (X' + Y') T := by
  rw [disjoint_left]
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
  obtain ⟨-, hxT⟩ := mem_filter.1 (hX' hx)
  exact disjoint_left.1 hxT (mem_image_of_mem _ (hY' hy))

/-- A block of length `l ≤ p` has `l` elements. -/
lemma card_block (v : ZMod p) {l : ℕ} (i : ℕ) (hl : l ≤ p) : #(block v l i) = l :=
  card_arithProg_one _ hl

/-- The `i`-th block of length `l` of `arithProg v 1 n` lies in it when `i < n / l`. -/
lemma block_subset_arithProg (v : ZMod p) {l n i : ℕ} (hi : i < n / l) :
    block v l i ⊆ arithProg v 1 n :=
  arithProg_add_natCast_subset v (by nlinarith [Nat.div_mul_le_self n l])

/-- If `Y` misses at most `l - t` points of `arithProg v 1 n`, then it meets each block of length
`l` of this interval in at least `t` points. -/
lemma le_card_inter_block {v : ZMod p} {Y : Finset (ZMod p)} {n l t i : ℕ} (hlp : l ≤ p)
    (hi : i < n / l) (ht : t + #(arithProg v 1 n \ Y) ≤ l) : t ≤ #(Y ∩ block v l i) := by
  rw [inter_comm]
  linarith [card_inter_add_card_sdiff (block v l i) Y, card_block v i hlp (l := l),
    card_le_card (sdiff_subset_sdiff (block_subset_arithProg v hi) (subset_refl Y))]

/-- If `X` avoids the points within `L` of `arithProg u 1 m`, then each point of `X` is a good point
for some block of `arithProg v 1 n`, so `#X` is at most the total number of good points. -/
lemma card_le_sum_card_goodPoints [NeZero p] {u v : ZMod p} {m n L l : ℕ} (hmnL : m + n + L ≤ p)
    (hl : 1 ≤ l) (hln : 2 * l ≤ n) (hlL : 2 * l ≤ L) {X : Finset (ZMod p)}
    (hX : Disjoint X (arithProg (u - L) 1 (m + 2 * L))) :
    #X ≤ ∑ i ∈ range (n / l), #(goodPoints X (arithProg u 1 m + arithProg v 1 n) v l i) := by
  grw [← card_biUnion_le]
  apply card_le_card
  intro x hx
  obtain ⟨i, hi, hdisj⟩ :=
    exists_lt_disjoint_image_add_arithProg v hmnL hl hln hlL (disjoint_left.1 hX hx)
  exact mem_biUnion.2 ⟨i, mem_range.2 hi, mem_filter.2 ⟨hx, hdisj⟩⟩

/-- If `a ≤ M`, `16 ≤ b` and `16 * M ≤ c * b`, then `16 * a ≤ min c a * b`. -/
lemma sixteen_mul_le_min_mul {a b c M : ℕ} (ha : a ≤ M) (hb : 16 ≤ b) (h : 16 * M ≤ c * b) :
    16 * a ≤ min c a * b := by
  rw [min_def]
  split_ifs <;> nlinarith

/-- **Lemma 12** and **Corollary 11** of Bollobás, Leader and Tiba. Let `I = arithProg u 1 m` and
`J = arithProg v 1 n` with `m + n + L ≤ p`, let `X` avoid the points within `L` of `I`, and let
every block of length `l` of `J` meet `Y` in at least `t` points. If `t` is large compared with
`X` and `W`, then some `X' ⊆ X` and `Y' ⊆ Y` with at most `N * cX` and `N * cY` elements, where
`n / l ≤ N`, have `#X` sums outside `W` and outside `I + J`. -/
lemma exists_card_eq_disjoint_add_of_disjoint [NeZero p] {u v : ZMod p} {m n L l : ℕ}
    (hmnL : m + n + L ≤ p) (hl : 1 ≤ l) (hln : 2 * l ≤ n) (hlL : 2 * l ≤ L)
    {X Y W : Finset (ZMod p)} (hX : Disjoint X (arithProg (u - L) 1 (m + 2 * L))) {cX cY t N : ℕ}
    (ht : t + #(arithProg v 1 n \ Y) ≤ l) (h16 : 16 ≤ min cY t) (hc : 16 * #X ≤ cX * min cY t)
    (hW : 6 * (#W + #X) ≤ t) (hN : n / l ≤ N) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' ≤ N * cX ∧ #Y' ≤ N * cY ∧ ∃ S ⊆ X' + Y', #S = #X ∧
      Disjoint S W ∧ Disjoint S (arithProg u 1 m + arithProg v 1 n) := by
  obtain ⟨X', Y', hXY', hcard⟩ := exists_subsets_min_le_card_biUnion_add_sdiff (range (n / l))
    (fun i ↦ goodPoints X (arithProg u 1 m + arithProg v 1 n) v l i) (fun i ↦ Y ∩ block v l i)
    W (cX := cX) (cY := min cY t) (M := #X)
    (fun i hi ↦ (min_le_right _ _).trans (le_card_inter_block (by grind) (mem_range.1 hi) ht))
    (fun i _ ↦ sixteen_mul_le_min_mul (card_goodPoints_le _ _ _ _) h16 hc)
    (fun i hi ↦ by grind [card_goodPoints_le (arithProg u 1 m + arithProg v 1 n) v l i (X := X),
      le_card_inter_block (by grind) (mem_range.1 hi) ht])
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq ((le_min le_rfl
    (by grind [card_le_sum_card_goodPoints (v := v) hmnL hl hln hlL hX])).trans hcard)
  refine ⟨(range (n / l)).biUnion X', ?_, (range (n / l)).biUnion Y', ?_, ?_, ?_, S, ?_, hSc,
    disjoint_of_subset_left hS sdiff_disjoint, ?_⟩
  · apply biUnion_subset.2
    intro i hi
    obtain ⟨hX', -, -, -⟩ := hXY' i hi
    exact hX'.trans (goodPoints_subset _ _ _ _)
  · apply biUnion_subset.2
    intro i hi
    obtain ⟨-, -, hY', -⟩ := hXY' i hi
    exact hY'.trans inter_subset_left
  · grw [card_biUnion_le_card_mul _ _ cX, card_range, hN]
    intro i hi
    obtain ⟨-, hX'c, -, -⟩ := hXY' i hi
    exact hX'c
  · grw [card_biUnion_le_card_mul _ _ cY, card_range, hN]
    intro i hi
    obtain ⟨-, -, -, hY'c⟩ := hXY' i hi
    exact hY'c.trans (min_le_left _ _)
  · grw [hS, sdiff_subset]
    apply biUnion_subset.2
    intro i hi
    exact add_subset_add (subset_biUnion_of_mem _ hi) (subset_biUnion_of_mem _ hi)
  · grw [hS, sdiff_subset]
    apply (disjoint_biUnion_left _ _ _).2
    intro i hi
    obtain ⟨hXi, -, hYi, -⟩ := hXY' i hi
    exact disjoint_add_of_subset_goodPoints hXi (hYi.trans inter_subset_right)

/-- The far part of `A` in the setting of Lemma 9, made of the points of `A` outside
`I = arithProg s 1 (a₁ + a₂ + a₃)`. Let `μ ≤ #B` with `α * #B ≤ μ`, `K ≤ μ` and
`6400 ≤ α * β * K`, let `B` be within `δ` of `J₂` with `2 ^ 12 * δ ≤ β * μ`, and let `W` and `A \ I`
have at most `e ≤ 2 * δ` elements in total. Then the blocks of length `⌊β * μ / 48⌋₊` of `J₂` give
some `X ⊆ A \ I` and `Y ⊆ B` with at most `⌈192 / (α * β)⌉₊ * c₁` and `⌈192 / (α * β)⌉₊ * c₂`
elements and with `#(A \ I)` sums outside `W` and outside `I₂ + J₂`. -/
lemma exists_card_eq_card_sdiff_disjoint (hp : p.Prime) {α β δ μ K : ℝ} (hα : 0 < α)
    (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1) {A B W : Finset (ZMod p)} (hμB : μ ≤ #B)
    (hαB : α * #B ≤ μ) (hμp : μ ≤ p) (hKμ : K ≤ μ) (hK : 6400 ≤ α * β * K)
    (hδ : 2 ^ 12 * δ ≤ β * μ) {s r : ZMod p} {a₁ a₂ a₃ b₁ b₂ : ℕ} (hL₁ : ⌊β * p / 8⌋₊ ≤ a₁)
    (hL₃ : ⌊β * p / 8⌋₊ ≤ a₃) (hp₂ : a₂ + b₂ + ⌊β * p / 8⌋₊ ≤ p)
    (hB₂ : #(B ∆ arithProg (r + b₁) 1 b₂) ≤ δ) {e : ℕ}
    (hWe : #W + #(A \ arithProg s 1 (a₁ + a₂ + a₃)) ≤ e) (he : e ≤ 2 * δ) {c₁ c₂ : ℕ}
    (hc₂B : c₂ ≤ #B) (hKc₂ : K ≤ c₂) (hKc : K * #A ≤ c₁ * c₂) :
    ∃ X ⊆ A \ arithProg s 1 (a₁ + a₂ + a₃), ∃ Y ⊆ B, #X ≤ ⌈192 / (α * β)⌉₊ * c₁ ∧
      #Y ≤ ⌈192 / (α * β)⌉₊ * c₂ ∧ ∃ S ⊆ X + Y, #S = #(A \ arithProg s 1 (a₁ + a₂ + a₃)) ∧
        Disjoint S W ∧ Disjoint S (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hαβ := mul_pos hα hβ
  have hβμ : 6400 ≤ β * μ := by nlinarith
  obtain ⟨hb₂, hb₂'⟩ := abs_le.1 (abs_card_sub_le_of_card_symmDiff_le (by grind) hB₂)
  refine exists_card_eq_disjoint_add_of_disjoint (L := ⌊β * p / 8⌋₊) (l := ⌊β * μ / 48⌋₊)
    (t := ⌊β * μ / 200⌋₊) hp₂ ?_ ?_ ?_
    (disjoint_of_subset_right (arithProg_sub_subset s hL₁ hL₃) sdiff_disjoint) ?_ ?_ ?_ ?_ ?_
  · rw [Nat.one_le_floor_iff]
    linarith
  · rify
    nlinarith [Nat.floor_le (by positivity : 0 ≤ β * μ / 48)]
  · apply Nat.le_floor
    push_cast
    nlinarith [Nat.floor_le (by positivity : 0 ≤ β * μ / 48)]
  · rify
    linarith [Nat.floor_le (by positivity : 0 ≤ β * μ / 200), Nat.lt_floor_add_one (β * μ / 48),
      (Nat.cast_le (α := ℝ)).2 (card_le_card (symmDiff_subset_sdiff' (s := B)
        (t := arithProg (r + b₁) 1 b₂)))]
  · apply le_min
    · rify
      nlinarith
    · apply Nat.le_floor
      push_cast
      linarith
  · grw [card_le_card sdiff_subset]
    rify
    have hmin : α * β / 400 * c₂ ≤ min (c₂ : ℝ) ⌊β * μ / 200⌋₊ :=
      le_min (by nlinarith [mul_le_of_le_one_left hβ.le hα₁, Nat.cast_nonneg (α := ℝ) c₂])
        (by linarith [Nat.lt_floor_add_one (β * μ / 200), mul_le_mul_of_nonneg_left hαB hβ.le,
          mul_le_mul_of_nonneg_left ((Nat.cast_le (α := ℝ)).2 hc₂B) hαβ.le,
          mul_le_mul_of_nonneg_left hKc₂ hαβ.le])
    linarith [mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg (α := ℝ) c₁),
      mul_le_mul_of_nonneg_left hKc hαβ.le, mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg #A)]
  · grw [hWe]
    apply Nat.le_floor
    push_cast
    linarith
  · rw [← Nat.cast_le (α := ℝ)]
    grw [Nat.cast_div_le, ← Nat.le_ceil]
    rw [div_le_div_iff₀ (Nat.cast_pos.2 (Nat.floor_pos.2 (by linarith))) (by positivity)]
    nlinarith [Nat.lt_floor_add_one (β * μ / 48), mul_le_mul_of_nonneg_left hb₂ hαβ.le,
      mul_le_mul_of_nonneg_left hαB hβ.le, mul_le_of_le_one_left hβ.le hα₁,
      mul_le_of_le_one_left ((Nat.cast_nonneg _).trans hB₂)
        ((mul_le_of_le_one_left hβ.le hα₁).trans hβ₁)]

/-- The far parts of `A` and `B` in the setting of Lemma 9, made of the points of `A` outside
`I = arithProg s 1 (a₁ + a₂ + a₃)` and of `B` outside `J = arithProg r 1 (b₁ + b₂ + b₃)`. If `Z` has
as many elements as the end parts `A ∩ I₁`, `B ∩ J₁`, `A ∩ I₃` and `B ∩ J₃` together, then some
subsets of `A` and `B` with at most `2 * ⌈192 / (α * β)⌉₊ * c₁` and `2 * ⌈192 / (α * β)⌉₊ * c₂`
elements have a set `S` of sums outside `Z` and outside `I₂ + J₂` with `#Z + #S = #(A \ I₂) +
#(B \ J₂)`. -/
lemma exists_card_eq_card_sdiff_add_card_sdiff_disjoint (hp : p.Prime) {α β δ μ K : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1) {A B Z : Finset (ZMod p)}
    (hμA : μ ≤ #A) (hμB : μ ≤ #B) (hαA : α * #A ≤ μ) (hαB : α * #B ≤ μ) (hμp : μ ≤ p)
    (hKμ : K ≤ μ) (hK : 6400 ≤ α * β * K) (hδ : 2 ^ 12 * δ ≤ β * μ) {s r : ZMod p}
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (hL₁ : ⌊β * p / 8⌋₊ ≤ a₁) (hL₃ : ⌊β * p / 8⌋₊ ≤ a₃)
    (hL₁' : ⌊β * p / 8⌋₊ ≤ b₁) (hL₃' : ⌊β * p / 8⌋₊ ≤ b₃) (hsum : a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p)
    (hA₂ : #(A ∆ arithProg (s + a₁) 1 a₂) ≤ δ) (hB₂ : #(B ∆ arithProg (r + b₁) 1 b₂) ≤ δ)
    (hZ : #Z = #(A ∩ arithProg s 1 a₁) + #(B ∩ arithProg r 1 b₁) +
      #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) + #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃))
    {c₁ c₂ : ℕ} (hc₁A : c₁ ≤ #A) (hc₂B : c₂ ≤ #B) (hKc₁ : K ≤ c₁) (hKc₂ : K ≤ c₂)
    (hKc : K * max (#A : ℝ) #B ≤ c₁ * c₂) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ 2 * ⌈192 / (α * β)⌉₊ * c₁ ∧ #B' ≤ 2 * ⌈192 / (α * β)⌉₊ * c₂ ∧
      ∃ S ⊆ A' + B',
        #Z + #S = #(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂) ∧
        Disjoint S Z ∧ Disjoint S (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  have hcount := card_inter_ends_add_card_sdiff_eq A B s r (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
    (b₁ := b₁) (b₂ := b₂) (b₃ := b₃) (by grind) (by grind)
  have hK₀ : 0 ≤ K := by nlinarith [mul_pos hα hβ]
  have he : #(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂) ≤ 2 * δ := by
    grw [card_le_card (symmDiff_subset_sdiff (s := A)),
      card_le_card (symmDiff_subset_sdiff (s := B))]
    linarith
  obtain ⟨X₁, hX₁, Y₁, hY₁, hX₁c, hY₁c, S₁, hS₁, hS₁c, hS₁Z, hS₁IJ⟩ :=
    exists_card_eq_card_sdiff_disjoint hp hα hα₁ hβ hβ₁ (W := Z) (s := s) (r := r) (a₂ := a₂)
      (b₁ := b₁) (b₂ := b₂) hμB hαB hμp hKμ hK hδ hL₁ hL₃ (by grind) hB₂ (by grind) (mod_cast he)
      hc₂B hKc₂ ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hKc)
  obtain ⟨X₂, hX₂, Y₂, hY₂, hX₂c, hY₂c, S₂, hS₂, hS₂c, hS₂W, hS₂IJ⟩ :=
    exists_card_eq_card_sdiff_disjoint hp hα hα₁ hβ hβ₁ (W := Z ∪ S₁) (s := r) (r := s)
      (a₂ := b₂) (b₁ := a₁) (b₂ := a₂) hμA hαA hμp hKμ hK hδ hL₁' hL₃' (by grind) hA₂
      (by grind [card_union_le Z S₁]) (mod_cast he) hc₁A hKc₁
      ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)).trans
        (hKc.trans_eq (mul_comm _ _)))
  obtain ⟨hS₂Z, hS₂S₁⟩ := disjoint_union_right.1 hS₂W
  refine ⟨X₁ ∪ Y₂, union_subset (hX₁.trans sdiff_subset) hY₂, Y₁ ∪ X₂,
    union_subset hY₁ (hX₂.trans sdiff_subset), by grind [card_union_le],
    by grind [card_union_le], S₁ ∪ S₂, ?_, ?_, disjoint_union_left.2 ⟨hS₁Z, hS₂Z⟩,
    disjoint_union_left.2 ⟨hS₁IJ, hS₂IJ.mono_right (add_comm _ _).subset⟩⟩
  · grw [hS₁, hS₂]
    rw [add_comm X₂ Y₂]
    exact union_subset (add_subset_add subset_union_left subset_union_left)
      (add_subset_add subset_union_right subset_union_right)
  · rw [card_union_of_disjoint hS₂S₁.symm, hS₁c, hS₂c]
    grind

end LargeSumsetsFromSubsets
