/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LargeSumsetsFromSubsets.ArithmeticProgression.NearInterval
import Mathlib.Tactic.Positivity.Finset

/-!
# The ends of the intervals

Lemma 9 of Bollobás, Leader and Tiba. Let `A, B ⊆ ZMod p` be within `γ * min #A #B` of intervals,
with `#A + #B ≤ (1 - β) * p` and `γ` much smaller than `β`. Then `ZMod p` splits in two ways into
consecutive intervals `I₁, I₂, I₃` and the rest, and `J₁, J₂, J₃` and the rest, such that
`I₁, I₃, J₁, J₃` have at least `⌊β * p / 8⌋` points, `A ∩ I₁` and `B ∩ J₁` have the same size, as
do `A ∩ I₃` and `B ∩ J₃`, `A` and `B` are within `133 * γ * min #A #B` of `I₂` and `J₂`, and the
pairs `(A ∩ I₁, B ∩ J₁)` and `(A ∩ I₃, B ∩ J₃)` are empty or contain a set far from every
arithmetic progression.

The proof is that of the paper, with the constants `14` and `2⁵` replaced by `30` and `2⁶` so that
the progression near an interval in the last step has at least `20` terms. The intervals `I₂'` and
`J₂'` of maximal length within `γ * min #A #B` of `A` and `B` are enlarged on both sides by
`⌊β * p / 8⌋` points, where `A` and `B` have density less than `1 / 2`. On the side where `A` has
more points than `B`, the end of `I₂'` is moved inside to the shortest interval whose part of `A`
is thirty times as large and close to an interval, and the end of `J₂'` so as to balance the two
sizes. The resulting part of `A` contains a sparse set beside a near interval thirty times as
large, so it is far from every progression.

## Implementation notes

The one-sided construction is carried out in local coordinates: `coords s X` is the set of the
`(x - s).val` for `x ∈ X`, which turns the intervals `arithProg (s + i) 1 n` with `i + n ≤ p` into
the intervals `Ico i (i + n)` of `ℕ`. The right ends are the left ends of the reflected sets
`A.image Neg.neg` and `B.image Neg.neg`. With `c = ⌊γ * min #A #B⌋₊`, the inner ends have at most
`33 * c` points, so the constants `133` and `266` of the statement are not tight.
-/

@[expose] public section

open Finset
open scoped symmDiff

namespace LargeSumsetsFromSubsets

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- `S` is far from arithmetic progressions: every arithmetic progression `P` satisfies
`#S ≤ κ * #(S ∆ P)`. -/
def IsFarFromArithProg (κ : ℕ) (S : Finset G) : Prop :=
  ∀ (a d : G) (n : ℕ), #S ≤ κ * #(S ∆ arithProg a d n)

section Card

variable {α : Type*} [DecidableEq α]

/-- The size of a symmetric difference, through the size of the intersection. -/
lemma card_symmDiff_add_two_mul_card_inter (X Y : Finset α) :
    #(X ∆ Y) + 2 * #(X ∩ Y) = #X + #Y := by
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff]
  grind [card_sdiff_add_card_inter X Y, card_sdiff_add_card_inter Y X, inter_comm X Y]

/-- Adding to `Y` a disjoint set `X` changes `#(A ∆ Y)` by `#X - 2 * #(A ∩ X)`. -/
lemma card_symmDiff_union_add {A X Y : Finset α} (h : Disjoint X Y) :
    #(A ∆ (X ∪ Y)) + 2 * #(A ∩ X) = #(A ∆ Y) + #X := by
  have hXY := card_symmDiff_add_two_mul_card_inter A (X ∪ Y)
  rw [inter_union_distrib_left,
    card_union_of_disjoint (h.mono inter_subset_right inter_subset_right),
    card_union_of_disjoint h] at hXY
  linarith [card_symmDiff_add_two_mul_card_inter A Y]

/-- A set `Y` has at most `#X + #(X ∆ Y)` elements. -/
lemma card_le_card_add_card_symmDiff (X Y : Finset α) : #Y ≤ #X + #(X ∆ Y) := by
  refine (card_le_card ?_).trans (card_union_le X (X ∆ Y))
  intro y hy
  by_cases hx : y ∈ X <;> simp [mem_symmDiff, hx, hy]

/-- A set `X` has at most `#(Y ∩ X) + #(X ∆ Y)` elements. -/
private lemma card_le_card_inter_add_card_symmDiff (X Y : Finset α) :
    #X ≤ #(Y ∩ X) + #(X ∆ Y) := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro x hx
  by_cases hy : x ∈ Y <;> simp [mem_symmDiff, hx, hy]

/-- Two disjoint sets cut out of `D` at most `#D` points. -/
lemma card_inter_add_card_inter_le (D : Finset α) {S T : Finset α} (h : Disjoint S T) :
    #(D ∩ S) + #(D ∩ T) ≤ #D := by
  rw [← card_union_of_disjoint (h.mono inter_subset_right inter_subset_right)]
  exact card_le_card (union_subset inter_subset_left inter_subset_left)

end Card

section Neg

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- Negation maps arithmetic progressions to arithmetic progressions. -/
lemma image_neg_arithProg (a d : H) (n : ℕ) :
    (arithProg a d n).image Neg.neg = arithProg (-a) (-d) n := by
  simp [arithProg, image_image, Function.comp_def, add_comm]

/-- A set whose reflection is far from arithmetic progressions is far from them. -/
lemma IsFarFromArithProg.of_image_neg {κ : ℕ} {S : Finset H}
    (h : IsFarFromArithProg κ (S.image Neg.neg)) : IsFarFromArithProg κ S := by
  intro a d n
  have := h (-a) (-d) n
  rwa [← image_neg_arithProg, ← image_symmDiff _ _ neg_injective,
    card_image_of_injective _ neg_injective, card_image_of_injective _ neg_injective] at this

end Neg

section Intervals

variable {p : ℕ}

/-- An interval splits into two consecutive intervals. -/
lemma arithProg_one_add_eq_union (a : ZMod p) (m n : ℕ) :
    arithProg a 1 (m + n) = arithProg a 1 m ∪ arithProg (a + m) 1 n := by
  rw [arithProg_add, nsmul_one]

/-- Two consecutive intervals of total length at most `p` are disjoint. -/
lemma disjoint_arithProg_one (a : ZMod p) {m n : ℕ} (h : m + n ≤ p) :
    Disjoint (arithProg a 1 m) (arithProg (a + m) 1 n) := by
  rw [← card_union_eq_card_add_card, ← arithProg_one_add_eq_union, card_arithProg_one _ h,
    card_arithProg_one _ (by grind), card_arithProg_one _ (by grind)]

/-- The reflection of an interval is an interval of the same length. -/
lemma image_neg_arithProg_one (a : ZMod p) (n : ℕ) :
    (arithProg a 1 n).image Neg.neg = arithProg (-(a + n) + 1) 1 n := by
  ext x
  simp only [mem_image, mem_arithProg, nsmul_one]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨n - (1 + i), by grind, ?_⟩
    rw [Nat.cast_sub (by grind)]
    push_cast
    ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨_, ⟨n - (1 + j), by grind, rfl⟩, ?_⟩
    rw [Nat.cast_sub (by grind)]
    push_cast
    ring

/-- The reflection of the part of `X` in an interval. -/
lemma image_neg_inter_arithProg_one (X : Finset (ZMod p)) (t : ZMod p) (n : ℕ) :
    (X ∩ arithProg (-(t + n) + 1) 1 n).image Neg.neg = X.image Neg.neg ∩ arithProg t 1 n := by
  rw [image_inter _ _ neg_injective, image_neg_arithProg_one]
  congr 2
  ring

/-- The start of the right end of the enlarged interval, as the reflection of the start of the
left end of the reflected interval. -/
lemma sub_natCast_add_natCast_eq_neg (u : ZMod p) {L M ℓ₁ ℓ₃ : ℕ} (h : ℓ₁ + ℓ₃ ≤ M) :
    u - L + ((L + ℓ₁ + (M - (ℓ₁ + ℓ₃)) : ℕ) : ZMod p) =
      -(-(u + M) + 1 - L + ((L + ℓ₃ : ℕ) : ZMod p)) + 1 := by
  rw [(by grind : L + ℓ₁ + (M - (ℓ₁ + ℓ₃)) = L + (M - ℓ₃))]
  push_cast [Nat.cast_sub (by grind : ℓ₃ ≤ M)]
  ring

/-- The value in `ℕ` of a difference of two natural numbers in `ZMod p`. -/
lemma val_natCast_sub_natCast {k t : ℕ} (hk : k < p) (ht : t ≤ p) :
    ((k : ZMod p) - t).val = if t ≤ k then k - t else k + p - t := by
  split_ifs with h
  · rw [← Nat.cast_sub h, ZMod.val_natCast_of_lt (by grind)]
  · rw [(by simp [Nat.cast_sub (by grind : t ≤ k + p)] :
      (k : ZMod p) - t = ((k + p - t : ℕ) : ZMod p)), ZMod.val_natCast_of_lt (by grind)]

/-- `A` gains at most `M - n` points of symmetric difference when an interval `I` of length `M`
is replaced by a subinterval of length `n`. -/
lemma card_symmDiff_arithProg_le (A : Finset (ZMod p)) (u : ZMod p) {ℓ n M : ℕ} (h : ℓ + n ≤ M)
    (hM : M ≤ p) : #(A ∆ arithProg (u + ℓ) 1 n) ≤ #(A ∆ arithProg u 1 M) + (M - n) := by
  have hsub : arithProg (u + ℓ) 1 n ⊆ arithProg u 1 M :=
    (subset_union_right.trans (arithProg_one_add_eq_union u ℓ n).symm.subset).trans
      (arithProg_mono u 1 h)
  refine (card_le_card (symmDiff_triangle A (arithProg u 1 M) _)).trans
    ((card_union_le _ _).trans ?_)
  rw [symmDiff_of_ge hsub, card_sdiff_of_subset hsub, card_arithProg_one _ hM,
    card_arithProg_one _ (by grind)]

/-- The local coordinates of `X ⊆ ZMod p` from `s`: the values `(x - s).val` for `x ∈ X`. -/
def coords (s : ZMod p) (X : Finset (ZMod p)) : Finset ℕ := X.image fun x ↦ (x - s).val

variable [NeZero p]

/-- An interval of length more than `p` is the interval of length `p`. -/
lemma arithProg_one_eq_min (a : ZMod p) (n : ℕ) : arithProg a 1 n = arithProg a 1 (min n p) := by
  rcases le_total n p with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, arithProg_one_eq_univ]
    exact eq_univ_of_forall fun x ↦ arithProg_mono a 1 h (by simp [arithProg_one_eq_univ])

/-- Local coordinates are injective. -/
lemma coords_injective (s : ZMod p) : Function.Injective fun x : ZMod p ↦ (x - s).val :=
  fun _ _ h ↦ sub_left_injective (ZMod.val_injective p h)

/-- Local coordinates preserve sizes. -/
@[simp]
lemma card_coords (s : ZMod p) (X : Finset (ZMod p)) : #(coords s X) = #X :=
  card_image_of_injective _ (coords_injective s)

/-- Local coordinates commute with intersections. -/
lemma coords_inter (s : ZMod p) (X Y : Finset (ZMod p)) :
    coords s (X ∩ Y) = coords s X ∩ coords s Y :=
  image_inter _ _ (coords_injective s)

/-- Local coordinates commute with symmetric differences. -/
lemma coords_symmDiff (s : ZMod p) (X Y : Finset (ZMod p)) :
    coords s (X ∆ Y) = coords s X ∆ coords s Y :=
  image_symmDiff _ _ (coords_injective s)

/-- The coordinate `k` from `s` belongs to `X` when `k < p` and `s + k ∈ X`. -/
lemma mem_coords {s : ZMod p} {X : Finset (ZMod p)} {k : ℕ} :
    k ∈ coords s X ↔ k < p ∧ s + k ∈ X := by
  simp only [coords, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ZMod.val_lt _, by rwa [ZMod.natCast_zmod_val, add_sub_cancel]⟩
  · rintro ⟨hk, hX⟩
    exact ⟨_, hX, by simp [ZMod.val_natCast_of_lt hk]⟩

/-- Membership in the local coordinates of an interval. -/
lemma mem_coords_arithProg {s : ZMod p} {t n k : ℕ} (ht : t ≤ p) (hn : n ≤ p) :
    k ∈ coords s (arithProg (s + t) 1 n) ↔ k < p ∧ (t ≤ k ∧ k < t + n ∨ k + p < t + n) := by
  rw [mem_coords, mem_arithProg_one_iff hn]
  refine and_congr_right ?_
  intro hk
  rw [add_sub_add_left_eq_sub, val_natCast_sub_natCast hk ht]
  grind

/-- In local coordinates from `s`, the interval `arithProg (s + i) 1 n` is `Ico i (i + n)`. -/
lemma coords_arithProg (s : ZMod p) {i n : ℕ} (h : i + n ≤ p) :
    coords s (arithProg (s + i) 1 n) = Ico i (i + n) := by
  ext k
  rw [mem_coords_arithProg (by grind) (by grind), mem_Ico]
  grind

/-- In local coordinates from `s`, the interval `arithProg s 1 n` is `range n`. -/
lemma coords_arithProg_self (s : ZMod p) {n : ℕ} (h : n ≤ p) :
    coords s (arithProg s 1 n) = range n := by
  simpa [← range_eq_Ico] using coords_arithProg s (i := 0) (n := n) (by grind)

/-- The size of the part of `X` in an interval starting at `s`, in local coordinates. -/
lemma card_inter_arithProg_eq (s : ZMod p) (X : Finset (ZMod p)) {n : ℕ} (h : n ≤ p) :
    #(X ∩ arithProg s 1 n) = #(coords s X ∩ range n) := by
  rw [← card_coords s, coords_inter, coords_arithProg_self s h]

/-- An interval of length `n` meets the interval of length `ℓ` starting at `s` in an interval,
when `n + ℓ ≤ p`. -/
lemma exists_coords_arithProg_inter_range (s a : ZMod p) {n ℓ : ℕ} (h : n + ℓ ≤ p) :
    ∃ i j, coords s (arithProg a 1 n) ∩ range ℓ = Ico i j := by
  obtain ⟨t, ht, rfl⟩ : ∃ t < p, a = s + t :=
    ⟨(a - s).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val, add_sub_cancel]⟩
  refine ⟨if t + n ≤ p then t else 0, min ℓ (if t + n ≤ p then t + n else t + n - p), ?_⟩
  ext k
  rw [mem_inter, mem_coords_arithProg ht.le (by grind), mem_range, mem_Ico]
  grind

end Intervals

section GoodEnd

/-- `ℓ` is an admissible length for the inner end of a set `α ⊆ ℕ` whose outer end is
`range L`: the part of `α` in `Ico L (L + ℓ)` is at least thirty times its part in `range L`, and
it is within a thirtieth of its size from an interval inside `Ico L (L + ℓ)`. -/
def IsGoodEnd (α : Finset ℕ) (L ℓ : ℕ) : Prop :=
  30 * #(α ∩ range L) ≤ #(α ∩ Ico L (L + ℓ)) ∧
    ∃ i j, L ≤ i ∧ j ≤ L + ℓ ∧ 30 * #(Ico i j ∆ (α ∩ Ico L (L + ℓ))) ≤ #(α ∩ Ico L (L + ℓ))

variable {α β : Finset ℕ} {L M ℓ c : ℕ}

/-- The empty inner end is admissible when `α` misses `range L`. -/
lemma isGoodEnd_zero (h : #(α ∩ range L) = 0) : IsGoodEnd α L 0 :=
  ⟨by simp [h], L, L, le_rfl, by simp, by simp⟩

/-- The part of `α` in `Ico a b` has at most `b - a` points. -/
private lemma card_inter_Ico_le (α : Finset ℕ) (a b : ℕ) : #(α ∩ Ico a b) ≤ b - a :=
  (card_le_card inter_subset_right).trans_eq (Nat.card_Ico a b)

/-- An initial segment `range L` is disjoint from the intervals starting at `L`. -/
private lemma disjoint_range_Ico (L m : ℕ) : Disjoint (range L) (Ico L m) := by
  rw [range_eq_Ico]
  exact Ico_disjoint_Ico_consecutive 0 L m

/-- The part of `α` in `range (L + ℓ)` splits into its parts in `range L` and `Ico L (L + ℓ)`. -/
lemma card_inter_range_add (α : Finset ℕ) (L ℓ : ℕ) :
    #(α ∩ range (L + ℓ)) = #(α ∩ range L) + #(α ∩ Ico L (L + ℓ)) := by
  rw [← card_union_of_disjoint
      ((disjoint_range_Ico L (L + ℓ)).mono inter_subset_right inter_subset_right),
    ← inter_union_distrib_left, range_eq_Ico, range_eq_Ico,
    Ico_union_Ico_eq_Ico (Nat.zero_le L) (Nat.le_add_right L ℓ)]

/-- Extending an initial segment by one point adds at most one point of `α`. -/
lemma card_inter_range_add_one_le (α : Finset ℕ) (n : ℕ) :
    #(α ∩ range (n + 1)) ≤ #(α ∩ range n) + 1 := by
  refine (card_le_card (?_ : _ ⊆ insert n (α ∩ range n))).trans (card_insert_le _ _)
  intro x
  simp only [mem_inter, mem_range, mem_insert]
  grind

/-- A set within `c` of `Ico L (L + M)` has at most `c` points in `range L`. -/
lemma card_inter_range_le (hα : #(α ∆ Ico L (L + M)) ≤ c) : #(α ∩ range L) ≤ c := by
  refine (card_le_card ?_).trans hα
  intro x
  simp only [mem_inter, mem_range, mem_symmDiff, mem_Ico]
  grind

/-- A set within `c` of `Ico L (L + M)` misses at most `c` points of `Ico L (L + ℓ)`. -/
lemma card_Ico_symmDiff_inter_le (hα : #(α ∆ Ico L (L + M)) ≤ c) (hℓ : ℓ ≤ M) :
    #(Ico L (L + ℓ) ∆ (α ∩ Ico L (L + ℓ))) ≤ c := by
  refine (card_le_card ?_).trans hα
  intro x
  simp only [mem_inter, mem_symmDiff, mem_Ico]
  grind

/-- A set within `c` of `Ico L (L + M)` has at least `ℓ - c` points in `Ico L (L + ℓ)`. -/
lemma le_card_inter_Ico_add (hα : #(α ∆ Ico L (L + M)) ≤ c) (hℓ : ℓ ≤ M) :
    ℓ ≤ #(α ∩ Ico L (L + ℓ)) + c := by
  have h := card_le_card_add_card_symmDiff (α ∩ Ico L (L + ℓ)) (Ico L (L + ℓ))
  rw [Nat.card_Ico, symmDiff_comm] at h
  grind [card_Ico_symmDiff_inter_le hα hℓ]

/-- A set within `c` of `Ico L (L + M)` admits the inner end `31 * c`. -/
lemma isGoodEnd_of_card_symmDiff_le (hα : #(α ∆ Ico L (L + M)) ≤ c) (hc : 31 * c ≤ M) :
    IsGoodEnd α L (31 * c) :=
  ⟨by linarith [le_card_inter_Ico_add hα hc, card_inter_range_le hα], L, L + 31 * c, le_rfl,
    le_rfl, by linarith [card_Ico_symmDiff_inter_le hα hc, le_card_inter_Ico_add hα hc]⟩

/-- The shortest admissible inner end has length at most `31 * c`. -/
lemma exists_isGoodEnd_min (hα : #(α ∆ Ico L (L + M)) ≤ c) (hc : 31 * c ≤ M) :
    ∃ ℓ ≤ 31 * c, IsGoodEnd α L ℓ ∧ ∀ ℓ' < ℓ, ¬IsGoodEnd α L ℓ' := by
  classical
  have h : ∃ ℓ, IsGoodEnd α L ℓ := ⟨_, isGoodEnd_of_card_symmDiff_le hα hc⟩
  exact ⟨Nat.find h, Nat.find_min' h (isGoodEnd_of_card_symmDiff_le hα hc), Nat.find_spec h,
    fun _ ↦ Nat.find_min h⟩

/-- A discrete intermediate value property: the sizes of the parts of `β` in the initial
segments take every value between two of them. -/
lemma exists_card_inter_range_eq {t m : ℕ} (h₀ : #(β ∩ range L) ≤ t)
    (h₁ : t ≤ #(β ∩ range (L + m))) : ∃ ℓ ≤ m, #(β ∩ range (L + ℓ)) = t := by
  induction m with
  | zero => exact ⟨0, le_rfl, le_antisymm h₀ h₁⟩
  | succ m ih =>
    by_cases ht : t ≤ #(β ∩ range (L + m))
    · obtain ⟨ℓ, hℓ, hℓt⟩ := ih ht
      exact ⟨ℓ, by grind, hℓt⟩
    · exact ⟨m + 1, le_rfl, le_antisymm ((card_inter_range_add_one_le β (L + m)).trans
        (by grind)) h₁⟩

/-- The one-sided construction in local coordinates: when `α` has at least as many points as `β`
in `range L`, the inner end of `α` is the shortest admissible one, and the inner end of `β`
balances the two sizes. -/
lemma exists_left_end_coords {N : ℕ} (hα : #(α ∆ Ico L (L + M)) ≤ c)
    (hβ : #(β ∆ Ico L (L + N)) ≤ c) (hM : 31 * c ≤ M) (hN : 33 * c ≤ N)
    (hαβ : #(β ∩ range L) ≤ #(α ∩ range L)) :
    ∃ ℓA ≤ 31 * c, ∃ ℓB ≤ 33 * c, IsGoodEnd α L ℓA ∧ (∀ ℓ' < ℓA, ¬IsGoodEnd α L ℓ') ∧
      #(α ∩ range (L + ℓA)) = #(β ∩ range (L + ℓB)) := by
  obtain ⟨ℓA, hℓA, hgood, hmin⟩ := exists_isGoodEnd_min hα hM
  obtain ⟨ℓB, hℓB, heq⟩ := exists_card_inter_range_eq (β := β) (L := L)
    (t := #(α ∩ range (L + ℓA))) (m := 33 * c) (by grind [card_inter_range_add α L ℓA])
    (by grind [card_inter_range_add α L ℓA, card_inter_range_add β L (33 * c),
      card_inter_range_le hα, le_card_inter_Ico_add hβ hN, card_inter_Ico_le α L (L + ℓA)])
  exact ⟨ℓA, hℓA, ℓB, hℓB, hgood, hmin, heq.symm⟩

/-- A sparse set beside an interval has at least as many points outside a final segment as
it has in all. -/
lemma card_inter_range_le_card_symmDiff_Ico
    (hsparse : ∀ k, 0 < k → k ≤ L → 2 * #(α ∩ Ico (L - k) L) < k) {k : ℕ} (hk : k ≤ L) :
    #(α ∩ range L) ≤ #((α ∩ range L) ∆ Ico (L - k) L) := by
  have h := card_symmDiff_add_two_mul_card_inter (α ∩ range L) (Ico (L - k) L)
  rw [inter_assoc, inter_eq_right.2 (by simp [subset_iff] : Ico (L - k) L ⊆ range L),
    Nat.card_Ico] at h
  grind [card_inter_Ico_le α (L - k) L, hsparse k]

/-- The part in `range L` of the symmetric difference of the part of `α` in `range (L + ℓ)` with
an interval reaching beyond `L` has at least `#(α ∩ range L)` points, by sparseness. -/
lemma card_inter_range_le_card_symmDiff_inter_range
    (hsparse : ∀ k, 0 < k → k ≤ L → 2 * #(α ∩ Ico (L - k) L) < k) {i j : ℕ} (hj : L < j) :
    #(α ∩ range L) ≤ #(((α ∩ range (L + ℓ)) ∆ Ico i j) ∩ range L) := by
  rw [(by ext x; simp only [mem_inter, mem_symmDiff, mem_range, mem_Ico]; grind :
    ((α ∩ range (L + ℓ)) ∆ Ico i j) ∩ range L = (α ∩ range L) ∆ Ico (L - (L - min i L)) L)]
  exact card_inter_range_le_card_symmDiff_Ico hsparse (Nat.sub_le L (min i L))

/-- When `ℓ` is not admissible but the part of `α` in `Ico L (L + (ℓ + 1))` is more than thirty
times its part in `range L`, this part is far from every interval inside `Ico L (L + ℓ)`. -/
lemma card_inter_Ico_le_mul_card_symmDiff_inter_Ico (hℓ : ¬IsGoodEnd α L ℓ)
    (h : 30 * #(α ∩ range L) < #(α ∩ Ico L (L + (ℓ + 1)))) (i j : ℕ) :
    #(α ∩ Ico L (L + (ℓ + 1))) ≤ 30 * #(((α ∩ range (L + (ℓ + 1))) ∆ Ico i j) ∩ Ico L (L + ℓ)) := by
  have hb := card_inter_range_add_one_le α (L + ℓ)
  rw [add_assoc, card_inter_range_add, card_inter_range_add α L ℓ] at hb
  simp only [IsGoodEnd, not_and, not_exists, not_le] at hℓ
  have h30 := hℓ (by grind) (max i L) (min j (L + ℓ)) (le_max_right _ _) (min_le_right _ _)
  rw [(by ext x; simp only [mem_inter, mem_symmDiff, mem_range, mem_Ico]; grind :
    Ico (max i L) (min j (L + ℓ)) ∆ (α ∩ Ico L (L + ℓ)) =
      ((α ∩ range (L + (ℓ + 1))) ∆ Ico i j) ∩ Ico L (L + ℓ))] at h30
  grind

/-- The core of the far-from-progression argument, in local coordinates. Let `α` be sparse in
the final segments of `range L` and `ℓ` the shortest admissible inner end. Then the part of `α` in
`range (L + ℓ)` has at most `64` times as many points as its symmetric difference with any
interval. -/
lemma card_le_mul_card_symmDiff_Ico
    (hsparse : ∀ k, 0 < k → k ≤ L → 2 * #(α ∩ Ico (L - k) L) < k) (hgood : IsGoodEnd α L ℓ)
    (hmin : ∀ ℓ' < ℓ, ¬IsGoodEnd α L ℓ') (i j : ℕ) :
    #(α ∩ range (L + ℓ)) ≤ 64 * #((α ∩ range (L + ℓ)) ∆ Ico i j) := by
  obtain ⟨h30, -⟩ := hgood
  rw [card_inter_range_add]
  rcases le_or_gt j L with hj | hj
  · have : α ∩ Ico L (L + ℓ) ⊆ (α ∩ range (L + ℓ)) ∆ Ico i j := by
      intro x
      simp only [mem_inter, mem_symmDiff, mem_range, mem_Ico]
      grind
    grind [card_le_card this]
  have hleft := card_inter_range_le_card_symmDiff_inter_range (ℓ := ℓ) (i := i) hsparse hj
  rcases h30.eq_or_lt with h | h
  · linarith [card_le_card (inter_subset_left (s₁ := (α ∩ range (L + ℓ)) ∆ Ico i j)
      (s₂ := range L))]
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by grind [card_inter_Ico_le α L (L + ℓ)]⟩
  linarith [card_inter_Ico_le_mul_card_symmDiff_inter_Ico (hmin ℓ' (by grind)) h i j,
    card_inter_add_card_inter_le ((α ∩ range (L + (ℓ' + 1))) ∆ Ico i j)
      (disjoint_range_Ico L (L + ℓ'))]

/-- The part of `α` in `range L` is nonempty when the part in `range (L + ℓ)` is, for the
shortest admissible inner end `ℓ`. -/
lemma pos_card_inter_range_of_isGoodEnd (hmin : ∀ ℓ' < ℓ, ¬IsGoodEnd α L ℓ')
    (h : 0 < #(α ∩ range (L + ℓ))) : 0 < #(α ∩ range L) := by
  by_contra! ha
  obtain rfl : ℓ = 0 := by
    by_contra hℓ
    exact hmin 0 (by grind) (isGoodEnd_zero (by grind))
  grind

/-- The part of `α` in `range (L + ℓ)` differs from an interval `Ico i j` inside
`Ico L (L + ℓ)` at most in the part of `α` in `range L` and in the difference between `Ico i j`
and the part of `α` in `Ico L (L + ℓ)`. -/
private lemma card_inter_range_symmDiff_Ico_le {i j : ℕ} (hi : L ≤ i) (hj : j ≤ L + ℓ) :
    #(Ico i j ∆ (α ∩ range (L + ℓ))) ≤ #(α ∩ range L) + #(Ico i j ∆ (α ∩ Ico L (L + ℓ))) := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro x
  simp only [mem_union, mem_symmDiff, mem_inter, mem_range, mem_Ico]
  grind

/-- A set `π` close to the part of `α` in `range (L + ℓ)`, for the shortest admissible inner end
`ℓ`, is close to an interval `Ico i j` with `20 ≤ j - i`, in the sense of the near-interval
lemma `exists_eq_arithProg_one_of_card_inter_arithProg_one`. -/
lemma exists_Ico_near_of_isGoodEnd {π : Finset ℕ} (hgood : IsGoodEnd α L ℓ)
    (hmin : ∀ ℓ' < ℓ, ¬IsGoodEnd α L ℓ')
    (h : 64 * #((α ∩ range (L + ℓ)) ∆ π) < #(α ∩ range (L + ℓ))) :
    ∃ i j, L ≤ i ∧ j ≤ L + ℓ ∧ 20 ≤ j - i ∧ 9 * (j - i) ≤ 10 * #(π ∩ Ico i j) ∧
      10 * #π ≤ 11 * (j - i) := by
  have ha := pos_card_inter_range_of_isGoodEnd hmin (by grind)
  rw [card_inter_range_add] at h
  obtain ⟨h30, i, j, hi, hj, hE⟩ := hgood
  have hD := (card_le_card (symmDiff_triangle (Ico i j) (α ∩ range (L + ℓ)) π)).trans
    (card_union_le _ _)
  have hI := Nat.card_Ico i j
  refine ⟨i, j, hi, hj, ?_, ?_, ?_⟩ <;>
    linarith [card_inter_range_symmDiff_Ico_le (α := α) hi hj,
      card_le_card_inter_add_card_symmDiff (Ico i j) π,
      card_le_card_add_card_symmDiff (Ico i j) (α ∩ Ico L (L + ℓ)),
      card_le_card_add_card_symmDiff (Ico i j) π]

end GoodEnd

section FarFromProgression

variable {p : ℕ}

/-- A progression close to the part of `A` in `arithProg s 1 (L + ℓ)`, for the shortest
admissible inner end `ℓ`, is an interval short enough to meet `arithProg s 1 (L + ℓ)` in an
interval. -/
lemma exists_eq_arithProg_one_of_isGoodEnd (hp : p.Prime) {A : Finset (ZMod p)} {s : ZMod p}
    {L ℓ : ℕ} (hgood : IsGoodEnd (coords s A) L ℓ)
    (hmin : ∀ ℓ' < ℓ, ¬IsGoodEnd (coords s A) L ℓ') (hLp : 8 * (L + ℓ) ≤ p) {a d : ZMod p}
    {n : ℕ} (h : 64 * #((coords s A ∩ range (L + ℓ)) ∆ coords s (arithProg a d n)) <
      #(coords s A ∩ range (L + ℓ))) :
    ∃ a' n', n' + (L + ℓ) ≤ p ∧ arithProg a d n = arithProg a' 1 n' := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, j, hi, hj, h20, hPQ, hP⟩ := exists_Ico_near_of_isGoodEnd hgood hmin h
  rw [← Nat.add_sub_cancel' (by grind : i ≤ j), ← coords_arithProg s (by grind),
    ← coords_inter, card_coords, Nat.add_sub_cancel' (by grind : i ≤ j)] at hPQ
  rw [card_coords] at hP
  obtain ⟨a', n', hP'⟩ :=
    exists_eq_arithProg_one_of_card_inter_arithProg_one hp h20 (by grind) hPQ hP
  refine ⟨a', min n' p, ?_, hP'.trans (arithProg_one_eq_min a' n')⟩
  rw [hP', arithProg_one_eq_min, card_arithProg_one _ (min_le_right _ _)] at hP
  grind

/-- The part of `A` in `arithProg s 1 (L + ℓ)` is far from every arithmetic progression, when
`A` is sparse in the final segments of `arithProg s 1 L` and `ℓ` is the shortest admissible
inner end. -/
lemma isFarFromArithProg_inter_arithProg (hp : p.Prime) {A : Finset (ZMod p)} {s : ZMod p}
    {L ℓ : ℕ} (hsparse : ∀ k, 0 < k → k ≤ L → 2 * #(coords s A ∩ Ico (L - k) L) < k)
    (hgood : IsGoodEnd (coords s A) L ℓ) (hmin : ∀ ℓ' < ℓ, ¬IsGoodEnd (coords s A) L ℓ')
    (hLp : 8 * (L + ℓ) ≤ p) : IsFarFromArithProg 64 (A ∩ arithProg s 1 (L + ℓ)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro a d n
  rw [← card_coords s, ← card_coords s (_ ∆ _), coords_symmDiff, coords_inter,
    coords_arithProg_self s (by grind)]
  by_contra! h
  obtain ⟨a', n', hn', hP⟩ := exists_eq_arithProg_one_of_isGoodEnd hp hgood hmin hLp h
  obtain ⟨i, j, hij⟩ := exists_coords_arithProg_inter_range s a' hn'
  refine h.not_ge ((card_le_mul_card_symmDiff_Ico hsparse hgood hmin i j).trans ?_)
  rw [hP, ← hij]
  refine Nat.mul_le_mul_left 64 (card_le_card ?_)
  intro x
  simp only [mem_symmDiff, mem_inter, mem_range]
  tauto

end FarFromProgression

section MaximalIntervals

variable {p : ℕ}

/-- `arithProg u 1 M` is an interval of maximal length among those within `c` of `A`. -/
def IsMaxNearInterval (c : ℕ) (A : Finset (ZMod p)) (u : ZMod p) (M : ℕ) : Prop :=
  M ≤ p ∧ #(A ∆ arithProg u 1 M) ≤ c ∧ ∀ w ℓ, ℓ ≤ p → #(A ∆ arithProg w 1 ℓ) ≤ c → ℓ ≤ M

variable {c M : ℕ} {A : Finset (ZMod p)} {u : ZMod p}

/-- A longest interval within `c` of `A` has at most `#A + c` points. -/
lemma IsMaxNearInterval.le_card_add (h : IsMaxNearInterval c A u M) : M ≤ #A + c := by
  obtain ⟨hMp, hAM, -⟩ := h
  grind [card_le_card_add_card_symmDiff A (arithProg u 1 M), card_arithProg_one u hMp]

/-- A longest interval within `c` of `A` has at least `#A - c` points. -/
lemma IsMaxNearInterval.card_le_add (h : IsMaxNearInterval c A u M) : #A ≤ M + c := by
  obtain ⟨hMp, hAM, -⟩ := h
  grind [card_le_card_add_card_symmDiff (arithProg u 1 M) A, card_arithProg_one u hMp,
    symmDiff_comm A (arithProg u 1 M)]

/-- Beside a longest interval within `c` of `A`, the set `A` has density less than `1 / 2`. -/
lemma IsMaxNearInterval.two_mul_card_inter_lt (h : IsMaxNearInterval c A u M) {k : ℕ}
    (hk : 0 < k) (hkM : k + M ≤ p) : 2 * #(A ∩ arithProg (u - k) 1 k) < k := by
  obtain ⟨-, hAM, hmax⟩ := h
  have hdisj := disjoint_arithProg_one (u - (k : ZMod p)) hkM
  rw [sub_add_cancel] at hdisj
  have := hmax (u - (k : ZMod p)) (k + M) hkM
  rw [arithProg_one_add_eq_union, sub_add_cancel] at this
  grind [card_symmDiff_union_add (A := A) hdisj,
    card_arithProg_one (u - (k : ZMod p)) (by grind : k ≤ p)]

/-- Replacing a longest interval within `c` of `A` by its middle part, without `ℓ₁` points on
the left and `ℓ₃` points on the right, keeps it within `c + (ℓ₁ + ℓ₃)` of `A`. -/
lemma IsMaxNearInterval.card_symmDiff_middle_le (h : IsMaxNearInterval c A u M)
    {L ℓ₁ ℓ₃ : ℕ} (hℓ : ℓ₁ + ℓ₃ ≤ M) :
    #(A ∆ arithProg (u - L + ((L + ℓ₁ : ℕ) : ZMod p)) 1 (M - (ℓ₁ + ℓ₃))) ≤ c + (ℓ₁ + ℓ₃) := by
  obtain ⟨hMp, hAM, -⟩ := h
  rw [(by push_cast; ring : u - (L : ZMod p) + ((L + ℓ₁ : ℕ) : ZMod p) = u + ℓ₁)]
  grind [card_symmDiff_arithProg_le A u (by grind : ℓ₁ + (M - (ℓ₁ + ℓ₃)) ≤ M) hMp]

/-- The reflection of a longest interval within `c` of `A` is a longest interval within `c` of
the reflection of `A`. -/
lemma IsMaxNearInterval.image_neg (h : IsMaxNearInterval c A u M) :
    IsMaxNearInterval c (A.image Neg.neg) (-(u + M) + 1) M := by
  obtain ⟨hMp, hAM, hmax⟩ := h
  refine ⟨hMp, ?_, ?_⟩
  · rwa [← image_neg_arithProg_one, ← image_symmDiff _ _ neg_injective,
      card_image_of_injective _ neg_injective]
  · intro w ℓ hℓ hw
    apply hmax (-(w + ℓ) + 1) ℓ hℓ
    rwa [← card_image_of_injective _ neg_injective, image_symmDiff _ _ neg_injective,
      image_neg_arithProg_one, (by ring : -(-(w + ℓ) + 1 + ℓ) + 1 = w)]

variable [NeZero p]

/-- If some interval is within `c` of `A`, then a longest one exists. -/
lemma exists_isMaxNearInterval {m : ℕ} {x : ZMod p} (hm : m ≤ p)
    (hx : #(A ∆ arithProg x 1 m) ≤ c) : ∃ u M, IsMaxNearInterval c A u M := by
  obtain ⟨⟨u, M⟩, hmem, hmax⟩ := exists_max_image
    ((univ ×ˢ range (p + 1)).filter fun q : ZMod p × ℕ ↦ #(A ∆ arithProg q.1 1 q.2) ≤ c)
    Prod.snd ⟨(x, m), by simpa [hx] using Nat.lt_succ_of_le hm⟩
  simp only [mem_filter, mem_product, mem_univ, mem_range, true_and] at hmem
  obtain ⟨hMp, hM⟩ := hmem
  refine ⟨u, M, by grind, hM, ?_⟩
  intro w ℓ hℓ hw
  exact hmax (w, ℓ) (by simpa [hw] using Nat.lt_succ_of_le hℓ)

/-- Sparseness beside a longest interval, in local coordinates. -/
lemma IsMaxNearInterval.two_mul_card_coords_inter_lt {s : ZMod p} {L : ℕ}
    (h : IsMaxNearInterval c A (s + L) M) (hLM : L + M ≤ p) {k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    2 * #(coords s A ∩ Ico (L - k) L) < k := by
  have := h.two_mul_card_inter_lt hk (by grind)
  rwa [(by push_cast [Nat.cast_sub hkL]; ring :
      s + (L : ZMod p) - (k : ZMod p) = s + ((L - k : ℕ) : ZMod p)),
    ← card_coords s, coords_inter, coords_arithProg s (by grind), Nat.sub_add_cancel hkL] at this

/-- A longest interval within `c` of `A`, in local coordinates. -/
lemma IsMaxNearInterval.card_coords_symmDiff_le {s : ZMod p} {L : ℕ}
    (h : IsMaxNearInterval c A (s + L) M) (hLM : L + M ≤ p) :
    #(coords s A ∆ Ico L (L + M)) ≤ c := by
  obtain ⟨-, hAM, -⟩ := h
  rwa [← coords_arithProg s hLM, ← coords_symmDiff, card_coords]

end MaximalIntervals

section LeftEnd

variable {p : ℕ}

/-- The one-sided construction, on the side where `A` has at least as many points as `B` beside
the longest intervals. -/
lemma exists_left_end_of_card_le (hp : p.Prime) {A B : Finset (ZMod p)} {s r : ZMod p}
    {c L M N : ℕ} (hA : IsMaxNearInterval c A (s + L) M) (hB : IsMaxNearInterval c B (r + L) N)
    (hM : 33 * c ≤ M) (hN : 33 * c ≤ N) (hLM : L + M ≤ p) (hLN : L + N ≤ p)
    (hLp : 8 * (L + 33 * c) ≤ p) (hAB : #(B ∩ arithProg r 1 L) ≤ #(A ∩ arithProg s 1 L)) :
    ∃ ℓA ≤ 33 * c, ∃ ℓB ≤ 33 * c,
      #(A ∩ arithProg s 1 (L + ℓA)) = #(B ∩ arithProg r 1 (L + ℓB)) ∧
      IsFarFromArithProg 64 (A ∩ arithProg s 1 (L + ℓA)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [card_inter_arithProg_eq s A (by grind), card_inter_arithProg_eq r B (by grind)] at hAB
  obtain ⟨ℓA, hℓA, ℓB, hℓB, hgood, hmin, heq⟩ := exists_left_end_coords
    (hA.card_coords_symmDiff_le hLM) (hB.card_coords_symmDiff_le hLN) (by grind) hN hAB
  refine ⟨ℓA, by grind, ℓB, hℓB, ?_, isFarFromArithProg_inter_arithProg hp
    (fun k hk hkL ↦ hA.two_mul_card_coords_inter_lt hLM hk hkL) hgood hmin (by grind)⟩
  rwa [card_inter_arithProg_eq s A (by grind), card_inter_arithProg_eq r B (by grind)]

/-- The one-sided construction: the left ends of the longest intervals within `c` of `A` and
`B` can be moved inside by at most `33 * c` points so that the parts of `A` and `B` in the left
ends have the same size and one of them is far from every arithmetic progression. -/
lemma exists_left_end (hp : p.Prime) {A B : Finset (ZMod p)} {s r : ZMod p}
    {c L M N : ℕ} (hA : IsMaxNearInterval c A (s + L) M) (hB : IsMaxNearInterval c B (r + L) N)
    (hM : 33 * c ≤ M) (hN : 33 * c ≤ N) (hLM : L + M ≤ p) (hLN : L + N ≤ p)
    (hLp : 8 * (L + 33 * c) ≤ p) :
    ∃ ℓA ≤ 33 * c, ∃ ℓB ≤ 33 * c,
      #(A ∩ arithProg s 1 (L + ℓA)) = #(B ∩ arithProg r 1 (L + ℓB)) ∧
      (IsFarFromArithProg 64 (A ∩ arithProg s 1 (L + ℓA)) ∨
        IsFarFromArithProg 64 (B ∩ arithProg r 1 (L + ℓB))) := by
  rcases le_total #(B ∩ arithProg r 1 L) #(A ∩ arithProg s 1 L) with h | h
  · obtain ⟨ℓA, hℓA, ℓB, hℓB, heq, hfar⟩ :=
      exists_left_end_of_card_le hp hA hB hM hN hLM hLN hLp h
    exact ⟨ℓA, hℓA, ℓB, hℓB, heq, Or.inl hfar⟩
  · obtain ⟨ℓB, hℓB, ℓA, hℓA, heq, hfar⟩ :=
      exists_left_end_of_card_le hp hB hA hN hM hLN hLM hLp h
    exact ⟨ℓA, hℓA, ℓB, hℓB, heq.symm, Or.inr hfar⟩

/-- The right ends: the left ends of the reflections, read back through the reflection. -/
lemma exists_right_end (hp : p.Prime) {A B : Finset (ZMod p)} {u v : ZMod p}
    {c L M N : ℕ} (hA : IsMaxNearInterval c A u M) (hB : IsMaxNearInterval c B v N)
    (hM : 66 * c ≤ M) (hN : 66 * c ≤ N) (hLM : L + M ≤ p) (hLN : L + N ≤ p)
    (hLp : 8 * (L + 33 * c) ≤ p) :
    ∃ ℓA ≤ 33 * c, ∃ ℓB ≤ 33 * c, ∀ ℓA' ≤ 33 * c, ∀ ℓB' ≤ 33 * c,
      #(A ∩ arithProg (u - L + ((L + ℓA' + (M - (ℓA' + ℓA)) : ℕ) : ZMod p)) 1 (L + ℓA)) =
        #(B ∩ arithProg (v - L + ((L + ℓB' + (N - (ℓB' + ℓB)) : ℕ) : ZMod p)) 1 (L + ℓB)) ∧
      (IsFarFromArithProg 64
          (A ∩ arithProg (u - L + ((L + ℓA' + (M - (ℓA' + ℓA)) : ℕ) : ZMod p)) 1 (L + ℓA)) ∨
        IsFarFromArithProg 64
          (B ∩ arithProg (v - L + ((L + ℓB' + (N - (ℓB' + ℓB)) : ℕ) : ZMod p)) 1 (L + ℓB))) := by
  obtain ⟨ℓA, hℓA, ℓB, hℓB, heq, hfar⟩ := exists_left_end hp
    (s := -(u + M) + 1 - L) (r := -(v + N) + 1 - L) (by rw [sub_add_cancel]; exact hA.image_neg)
    (by rw [sub_add_cancel]; exact hB.image_neg) (by grind) (by grind) hLM hLN hLp
  refine ⟨ℓA, hℓA, ℓB, hℓB, ?_⟩
  intro ℓA' hℓA' ℓB' hℓB'
  rw [sub_natCast_add_natCast_eq_neg u (by grind : ℓA' + ℓA ≤ M),
    sub_natCast_add_natCast_eq_neg v (by grind : ℓB' + ℓB ≤ N)]
  refine ⟨?_, hfar.imp ?_ ?_⟩
  · rw [← card_image_of_injective _ neg_injective, image_neg_inter_arithProg_one, heq,
      ← image_neg_inter_arithProg_one, card_image_of_injective _ neg_injective]
  all_goals
    intro h
    refine IsFarFromArithProg.of_image_neg ?_
    rwa [image_neg_inter_arithProg_one]

end LeftEnd

/-- The numerical facts behind Lemma 9: with `c ≤ γ * min a b`, the longest intervals have room
for the inner ends, and the enlarged intervals fit in `ZMod p`. -/
lemma interval_ends_numerics {p : ℕ} {β γ : ℝ} (hβ : β ≤ 1 / 1024) (hγ : 0 < γ)
    (hγβ : 2 ^ 20 * γ ≤ β) {a b c M N : ℕ} (hab : (a + b : ℝ) ≤ (1 - β) * p)
    (hc : (c : ℝ) ≤ γ * min (a : ℝ) b) (hM : M ≤ a + c) (hN : N ≤ b + c) (haM : a ≤ M + c)
    (hbN : b ≤ N + c) :
    66 * c ≤ M ∧ 66 * c ≤ N ∧ 4 * ⌊β * p / 8⌋₊ + M + N ≤ p ∧
      8 * (⌊β * p / 8⌋₊ + 33 * c) ≤ p := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hβ0 : 0 ≤ β := by linarith
  have hγp : γ * min (a : ℝ) b ≤ γ * p := mul_le_mul_of_nonneg_left
    ((min_le_left _ _).trans (by linarith [mul_nonneg hβ0 hp, Nat.cast_nonneg (α := ℝ) b]))
    hγ.le
  have hca : 67 * c ≤ min a b := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 67 * γ)
      (by positivity : (0 : ℝ) ≤ min (a : ℝ) b)]
  have hL : (⌊β * p / 8⌋₊ : ℝ) ≤ β * p / 8 := Nat.floor_le (by positivity)
  refine ⟨by grind, by grind, ?_, ?_⟩ <;> rw [← Nat.cast_le (α := ℝ)] <;> push_cast
  · linarith [(by exact_mod_cast hM : (M : ℝ) ≤ a + c), (by exact_mod_cast hN : (N : ℝ) ≤ b + c),
      mul_le_mul_of_nonneg_right hγβ hp, mul_nonneg hγ.le hp]
  · linarith [mul_le_mul_of_nonneg_right hβ hp, mul_le_mul_of_nonneg_right hγβ hp,
      mul_nonneg hγ.le hp]

/-- **Lemma 9** of Bollobás, Leader and Tiba, with the constants of this formalization. Here
`I₁ = arithProg s 1 a₁`, `I₂ = arithProg (s + a₁) 1 a₂`, `I₃ = arithProg (s + (a₁ + a₂)) 1 a₃`,
and `J₁`, `J₂`, `J₃` are defined likewise from `r` and `b₁`, `b₂`, `b₃`. -/
lemma exists_interval_ends {p : ℕ} (hp : p.Prime) {β γ : ℝ} (hβ : β ≤ 1 / 1024) (hγ : 0 < γ)
    (hγβ : 2 ^ 20 * γ ≤ β) {A B : Finset (ZMod p)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : (#A + #B : ℝ) ≤ (1 - β) * p) {x y : ZMod p} {m n : ℕ} (hm : m ≤ p) (hn : n ≤ p)
    (hAI : (#(A ∆ arithProg x 1 m) : ℝ) ≤ γ * min (#A : ℝ) #B)
    (hBJ : (#(B ∆ arithProg y 1 n) : ℝ) ≤ γ * min (#A : ℝ) #B) :
    ∃ (s r : ZMod p) (a₁ a₂ a₃ b₁ b₂ b₃ : ℕ),
      ⌊β * p / 8⌋₊ ≤ a₁ ∧ ⌊β * p / 8⌋₊ ≤ a₃ ∧ ⌊β * p / 8⌋₊ ≤ b₁ ∧ ⌊β * p / 8⌋₊ ≤ b₃ ∧
      a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p ∧
      (a₂ + b₂ : ℝ) ≤ #A + #B + 266 * γ * min (#A : ℝ) #B ∧
      #(A ∩ arithProg s 1 a₁) = #(B ∩ arithProg r 1 b₁) ∧
      #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) = #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) ∧
      (#(A ∆ arithProg (s + a₁) 1 a₂) : ℝ) ≤ 133 * γ * min (#A : ℝ) #B ∧
      (#(B ∆ arithProg (r + b₁) 1 b₂) : ℝ) ≤ 133 * γ * min (#A : ℝ) #B ∧
      (A ∩ arithProg s 1 a₁ = ∅ ∧ B ∩ arithProg r 1 b₁ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg s 1 a₁) ∨
        IsFarFromArithProg 64 (B ∩ arithProg r 1 b₁)) ∧
      (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ = ∅ ∧
          B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) ∨
        IsFarFromArithProg 64 (B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hcA, hcB, hc⟩ : ∃ c : ℕ, #(A ∆ arithProg x 1 m) ≤ c ∧ #(B ∆ arithProg y 1 n) ≤ c ∧
      (c : ℝ) ≤ γ * min (#A : ℝ) #B :=
    ⟨_, Nat.le_floor hAI, Nat.le_floor hBJ, Nat.floor_le (by positivity)⟩
  obtain ⟨u, M, hu⟩ := exists_isMaxNearInterval hm hcA
  obtain ⟨v, N, hv⟩ := exists_isMaxNearInterval hn hcB
  obtain ⟨hcM, hcN, hsum, hLp⟩ := interval_ends_numerics hβ hγ hγβ hAB hc hu.le_card_add
    hv.le_card_add hu.card_le_add hv.card_le_add
  set L := ⌊β * p / 8⌋₊
  obtain ⟨ℓ₁, hℓ₁, ℓ₁', hℓ₁', heq₁, hfar₁⟩ := exists_left_end hp (s := u - L) (r := v - L)
    (by rwa [sub_add_cancel]) (by rwa [sub_add_cancel]) (by grind) (by grind) (by grind)
    (by grind) hLp
  obtain ⟨ℓ₃, hℓ₃, ℓ₃', hℓ₃', hright⟩ :=
    exists_right_end hp hu hv hcM hcN (by grind) (by grind) hLp
  obtain ⟨heq₃, hfar₃⟩ := hright ℓ₁ (by grind) ℓ₁' (by grind)
  refine ⟨u - L, v - L, L + ℓ₁, M - (ℓ₁ + ℓ₃), L + ℓ₃, L + ℓ₁', N - (ℓ₁' + ℓ₃'), L + ℓ₃',
    Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    by grind, ?_, heq₁, heq₃, ?_, ?_, Or.inr hfar₁, Or.inr hfar₃⟩
  · linarith [(by exact_mod_cast (Nat.sub_le _ _).trans hu.le_card_add :
      ((M - (ℓ₁ + ℓ₃) : ℕ) : ℝ) ≤ #A + c),
      (by exact_mod_cast (Nat.sub_le _ _).trans hv.le_card_add :
        ((N - (ℓ₁' + ℓ₃') : ℕ) : ℝ) ≤ #B + c)]
  · exact (Nat.cast_le.2 ((hu.card_symmDiff_middle_le (by grind)).trans
      (by grind : c + (ℓ₁ + ℓ₃) ≤ 67 * c))).trans (by push_cast; linarith)
  · exact (Nat.cast_le.2 ((hv.card_symmDiff_middle_le (by grind)).trans
      (by grind : c + (ℓ₁' + ℓ₃') ≤ 67 * c))).trans (by push_cast; linarith)

end LargeSumsetsFromSubsets
