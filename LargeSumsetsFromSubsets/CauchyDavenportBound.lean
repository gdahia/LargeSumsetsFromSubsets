/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.IntervalSumsets.FewTranslates
public import LargeSumsetsFromSubsets.ZModStability
public import LargeSumsetsFromSubsets.IntervalEnds
import LargeSumsetsFromSubsets.IntervalCovering
import LargeSumsetsFromSubsets.IntervalSumsets
import LargeSumsetsFromSubsets.Stickout
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The Cauchy–Davenport bound from medium-sized subsets

Theorem 1 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*: for
`α, β > 0` there is `c > 0` such that if `A, B ⊆ ZMod p` are nonempty with
`α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, then for all `1 ≤ c₁ ≤ #A` and
`1 ≤ c₂ ≤ #B` with `c₁ * c₂ ≥ c * max #A #B` there are `A' ⊆ A` and `B' ⊆ B` with `c₁` and `c₂`
elements and `#(A' + B') ≥ #A + #B - 1`. The theorem assumes Theorems 4 and 5 of the paper,
`CauchyDavenportStability` and `FewTranslatesNearIntervals`.

The proof is that of the paper. If no small subsets reach `#A + #B - 1`, Theorem 6 places `A`
and `B` near intervals, after a dilation. Lemma 9 cuts `ZMod p` into the middle intervals `I₂` and
`J₂`, the end intervals `I₁, I₃, J₁, J₃` and the rest `I₀`, `J₀`. The middle parts are handled
by Theorem 8, the end parts by Theorem 6, and the parts of `A` and `B` in `I₀` and `J₀` by Lemma 12
and Corollary 11. The resulting sumsets lie in disjoint regions and add up to `#A + #B - 1`.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

section ArithProg

variable {p : ℕ}

/-- The interval `arithProg (a + k) 1 n` lies in `arithProg a 1 N` when `k + n ≤ N`. -/
lemma arithProg_add_natCast_subset (a : ZMod p) {k n N : ℕ} (h : k + n ≤ N) :
    arithProg (a + k) 1 n ⊆ arithProg a 1 N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_arithProg.1 hx
  exact mem_arithProg.2 ⟨k + i, by grind, by simp [add_assoc]⟩

/-- The interval `arithProg a 1 m` is disjoint from `arithProg (a + k) 1 n` when `m ≤ k` and
`k + n ≤ p`. -/
lemma disjoint_arithProg_one_of_le (a : ZMod p) {k m n : ℕ} (hmk : m ≤ k) (h : k + n ≤ p) :
    Disjoint (arithProg a 1 m) (arithProg (a + k) 1 n) :=
  (disjoint_arithProg_one a h).mono_left (arithProg_mono _ _ hmk)

/-- The interval `arithProg x 1 m` is disjoint from `arithProg y 1 n` when `y = x + k` with
`m ≤ k` and `k + n ≤ p`. -/
lemma disjoint_arithProg_one_of_eq_add {x y : ZMod p} {k m n : ℕ} (hmk : m ≤ k) (h : k + n ≤ p)
    (hy : y = x + k) : Disjoint (arithProg x 1 m) (arithProg y 1 n) :=
  hy ▸ disjoint_arithProg_one_of_le x hmk h

/-- The sumset of two intervals of lengths `m` and `n` lies in an interval of length `m + n`. -/
lemma arithProg_add_arithProg_subset (x y : ZMod p) (m n : ℕ) :
    arithProg x 1 m + arithProg y 1 n ⊆ arithProg (x + y) 1 (m + n) :=
  (add_arithProg_subset x y 1 m n).trans (arithProg_mono _ _ (Nat.sub_le _ 1))

/-- The interval of the points within `L` of `arithProg (s + a₁) 1 a₂` lies in
`arithProg s 1 (a₁ + a₂ + a₃)` when `L ≤ a₁` and `L ≤ a₃`. -/
lemma arithProg_sub_subset (s : ZMod p) {a₁ a₂ a₃ L : ℕ} (h₁ : L ≤ a₁) (h₃ : L ≤ a₃) :
    arithProg (s + a₁ - L) 1 (a₂ + 2 * L) ⊆ arithProg s 1 (a₁ + a₂ + a₃) := by
  rw [add_sub_assoc, ← Nat.cast_sub h₁]
  exact arithProg_add_natCast_subset s (by grind)

/-- The sizes of the parts of `A` in three consecutive intervals of `ZMod p` and outside them. -/
lemma card_eq_card_sdiff_add_card_inter (A : Finset (ZMod p)) (s : ZMod p) {a₁ a₂ a₃ : ℕ}
    (h : a₁ + a₂ + a₃ ≤ p) :
    #A = #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(A ∩ arithProg s 1 a₁) +
      #(A ∩ arithProg (s + a₁) 1 a₂) + #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) := by
  have h₁₂ := disjoint_arithProg_one s (m := a₁) (n := a₂) (by grind)
  have h₁₂₃ := disjoint_arithProg_one s (m := a₁ + a₂) (n := a₃) h
  rw [arithProg_add, nsmul_one] at h₁₂₃
  rw [← card_sdiff_add_card_inter A (arithProg s 1 (a₁ + a₂ + a₃)), arithProg_add,
    arithProg_add, nsmul_one, nsmul_one, inter_union_distrib_left, inter_union_distrib_left,
    card_union_of_disjoint, card_union_of_disjoint]
  · grind
  · exact h₁₂.mono inter_subset_right inter_subset_right
  · exact h₁₂₃.mono (union_subset_union inter_subset_right inter_subset_right)
      inter_subset_right

end ArithProg

section Reductions

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Padding: subsets with at most `c₁` and `c₂` elements whose sumset is large can be enlarged
to subsets with exactly `c₁` and `c₂` elements. -/
lemma exists_subset_card_eq_of_card_le {A B : Finset G} {c₁ c₂ k : ℕ} (hc₁ : c₁ ≤ #A)
    (hc₂ : c₂ ≤ #B) (h : ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧ k ≤ #(A' + B')) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ k ≤ #(A' + B') := by
  obtain ⟨A', hA', B', hB', hA'c, hB'c, hk⟩ := h
  obtain ⟨A'', hA'A'', hA'', rfl⟩ := exists_subsuperset_card_eq hA' hA'c hc₁
  obtain ⟨B'', hB'B'', hB'', rfl⟩ := exists_subsuperset_card_eq hB' hB'c hc₂
  exact ⟨A'', hA'', B'', hB'', rfl, rfl, hk.trans (card_le_card (add_subset_add hA'A'' hB'B''))⟩

/-- If every pair of subsets of `A` and `B` with at most `c₁` and `c₂` elements has at most `k`
sums, so does the sumset of uniform `c₁`- and `c₂`-subsets in expectation. -/
lemma expect_card_add_le_of_forall {A B : Finset G} {c₁ c₂ k : ℕ} (hc₁ : c₁ ≤ #A)
    (hc₂ : c₂ ≤ #B)
    (h : ∀ A' ⊆ A, ∀ B' ⊆ B, #A' ≤ c₁ → #B' ≤ c₂ → #(A' + B') ≤ k) :
    𝔼 A' ∈ powersetCard c₁ A, 𝔼 B' ∈ powersetCard c₂ B, (#(A' + B') : ℝ) ≤ k := by
  refine expect_le (powersetCard_nonempty.2 hc₁) ?_
  intro A' hA'
  refine expect_le (powersetCard_nonempty.2 hc₂) ?_
  intro B' hB'
  obtain ⟨hA'A, hA'c⟩ := mem_powersetCard.1 hA'
  obtain ⟨hB'B, hB'c⟩ := mem_powersetCard.1 hB'
  exact_mod_cast h A' hA'A B' hB'B hA'c.le hB'c.le

end Reductions

section Dilation

variable {p : ℕ}

/-- Large sumsets of small subsets can be pulled back along the multiplication by a unit. -/
lemma exists_card_add_of_image_mul (hp : p.Prime) {u : ZMod p} (hu : u ≠ 0)
    {A B : Finset (ZMod p)} {k₁ k₂ : ℕ}
    (h : ∃ A' ⊆ A.image (u * ·), ∃ B' ⊆ B.image (u * ·), #A' ≤ k₁ ∧ #B' ≤ k₂ ∧
      #(A.image (u * ·)) + #(B.image (u * ·)) - 1 ≤ #(A' + B')) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ k₁ ∧ #B' ≤ k₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  have := Fact.mk hp
  have hinj : Function.Injective (u * ·) := mul_right_injective₀ hu
  obtain ⟨A', hA', B', hB', hA'k, hB'k, hAB⟩ := h
  obtain ⟨A'', hA'', rfl⟩ := subset_image_iff.1 hA'
  obtain ⟨B'', hB'', rfl⟩ := subset_image_iff.1 hB'
  have hadd : (A'' + B'').image (u * ·) = A''.image (u * ·) + B''.image (u * ·) :=
    image_add (AddMonoidHom.mulLeft u)
  simp only [← hadd, card_image_of_injective _ hinj] at hA'k hB'k hAB
  exact ⟨A'', hA'', B'', hB'', hA'k, hB'k, hAB⟩

/-- Multiplication by the inverse of `d ≠ 0` maps a set close to an arithmetic progression of
common difference `d` to a set equally close to an interval. -/
lemma card_image_mul_symmDiff_arithProg (hp : p.Prime) {d : ZMod p} (hd : d ≠ 0)
    (A : Finset (ZMod p)) (a : ZMod p) (m : ℕ) :
    #(A.image (d⁻¹ * ·) ∆ arithProg (d⁻¹ * a) 1 m) = #(A ∆ arithProg a d m) := by
  have := Fact.mk hp
  have hinj : Function.Injective (d⁻¹ * ·) := mul_right_injective₀ (inv_ne_zero hd)
  rw [← inv_mul_cancel₀ hd, ← image_mul_arithProg, ← image_symmDiff _ _ hinj,
    card_image_of_injective _ hinj]

/-- Multiplication by the inverse of `d ≠ 0` preserves the size of a set. -/
lemma card_image_inv_mul (hp : p.Prime) {d : ZMod p} (hd : d ≠ 0) (A : Finset (ZMod p)) :
    #(A.image (d⁻¹ * ·)) = #A :=
  have := Fact.mk hp
  card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hd))

end Dilation

section Estimates

/-- A set `B` within `δ` of a set `J`: the two differences have at most `δ` elements in total,
and `B` and `J` exceed their intersection by these differences. -/
lemma card_sdiff_add_card_sdiff_le {G : Type*} [DecidableEq G] {B J : Finset G} {δ : ℝ}
    (h : (#(B ∆ J) : ℝ) ≤ δ) :
    (#(B \ J) : ℝ) + #(J \ B) ≤ δ ∧ (#B : ℝ) = #(B ∩ J) + #(B \ J) ∧
      (#J : ℝ) = #(B ∩ J) + #(J \ B) := by
  refine ⟨?_, by exact_mod_cast (card_inter_add_card_sdiff B J).symm, ?_⟩
  · rwa [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff,
      Nat.cast_add] at h
  · rw [inter_comm]
    exact_mod_cast (card_inter_add_card_sdiff J B).symm

/-- If `c ≤ M` and `θ * M ≤ x` with `0 ≤ θ ≤ 1`, then `θ * c ≤ min c x`. -/
lemma mul_le_min_of_le {θ c x M : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 ≤ c) (hcM : c ≤ M)
    (hx : θ * M ≤ x) : θ * c ≤ min c x :=
  le_min (by nlinarith) (by nlinarith)

/-- The condition of Theorem 6 for the subsets of sizes `min c₁ k` and `min c₂ k` of two sets of
size `k`, when one of `c₁` and `c₂` is less than `k`. -/
lemma mul_le_min_mul_min {c C c₁ c₂ k M : ℝ} (hc : c ≤ C) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hkM : k ≤ M) (h₁ : C ≤ c₁) (h₂ : C ≤ c₂) (hM : C * M ≤ c₁ * c₂) (hlt : c₁ < k ∨ c₂ < k) :
    c * k ≤ min c₁ k * min c₂ k := by
  have hck : c * k ≤ C * k := mul_le_mul_of_nonneg_right hc hk
  rcases le_total c₁ k with h₁k | h₁k <;> rcases le_total c₂ k with h₂k | h₂k
  · rw [min_eq_left h₁k, min_eq_left h₂k]
    nlinarith
  · rw [min_eq_left h₁k, min_eq_right h₂k]
    nlinarith
  · rw [min_eq_right h₁k, min_eq_left h₂k]
    nlinarith
  · rcases hlt with h | h <;> linarith

/-- The condition of Theorem 6 for the subsets of sizes `min c₁ k` and `min c₂ l` of two sets of
sizes `k = l ≤ M`, when one of `c₁` and `c₂` is less than `k`. -/
lemma mul_max_le_min_mul_min {c C : ℝ} {c₁ c₂ k l M : ℕ} (hkl : k = l) (hc : c ≤ C) (hC : 0 ≤ C)
    (hkM : k ≤ M) (h₁ : C ≤ c₁) (h₂ : C ≤ c₂) (hM : C * M ≤ c₁ * c₂) (hlt : c₁ < k ∨ c₂ < k) :
    c * max (k : ℝ) l ≤ (min c₁ k : ℕ) * (min c₂ l : ℕ) := by
  subst hkl
  push_cast
  rw [max_self]
  exact mul_le_min_mul_min hc hC (Nat.cast_nonneg _) (by exact_mod_cast hkM) h₁ h₂ hM
    (by exact_mod_cast hlt)

end Estimates

section EndParts

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- A set far from arithmetic progressions is empty if it is within `#S / 128` of one. -/
lemma eq_empty_of_isFarFromArithProg {S : Finset G} (hS : IsFarFromArithProg 64 S) {a d : G}
    {n : ℕ} (h : (#(S ∆ arithProg a d n) : ℝ) ≤ #S / 128) : S = ∅ := by
  have : (#S : ℝ) ≤ 64 * #(S ∆ arithProg a d n) := by exact_mod_cast hS a d n
  rw [← card_eq_zero, ← Nat.le_zero, ← Nat.cast_le (α := ℝ)]
  push_cast
  linarith

/-- A singleton is an arithmetic progression, so it is not far from arithmetic progressions. -/
lemma not_isFarFromArithProg_singleton (z : G) : ¬ IsFarFromArithProg 64 ({z} : Finset G) := by
  intro h
  simpa [arithProg_one_right] using h z 0 1

variable {p : ℕ}

/-- If `#S = #T ≥ 2` and `#(S + T) < #S + #T`, then `CauchyDavenportStability` places `S` and
`T` within `#S / 128` of arithmetic progressions with the same common difference. -/
lemma exists_arithProg_of_card_add_lt (h : CauchyDavenportStability) {β : ℝ} (hβ : 0 < β)
    (hp : p.Prime) {S T : Finset (ZMod p)} (hST : #S = #T) (hS : 2 ≤ #S)
    (hβp : (#S + #T : ℝ) ≤ (1 - β) * p) (hlt : #(S + T) < #S + #T) :
    ∃ a b d : ZMod p, ∃ m n : ℕ, (#(S ∆ arithProg a d m) : ℝ) ≤ #S / 128 ∧
      (#(T ∆ arithProg b d n) : ℝ) ≤ #S / 128 := by
  obtain ⟨ε, hε, h₃⟩ := h β hβ (1 / 128) (by norm_num)
  obtain ⟨a, b, d, m, n, hSP, hTQ, hPS, hQT⟩ := h₃ p hp S T hS (hST ▸ hS) hβp
    (by linarith [(by exact_mod_cast hlt : (#(S + T) : ℝ) + 1 ≤ #S + #T),
      (by positivity : 0 ≤ ε * min (#S : ℝ) #T)])
  rw [← hST, min_self] at hPS hQT
  refine ⟨a, b, d, m, n, ?_, ?_⟩
  · rw [arithProg, symmDiff_of_le hSP]
    linarith
  · rw [arithProg, symmDiff_of_le hTQ]
    linarith

/-- If `#S = #T ≥ 2`, one of `c₁` and `c₂` is less than `#S`, and no subsets of `S` and `T` with
at most `c₁` and `c₂` elements have `#S + #T` sums, then Theorem 6 for the subsets of sizes
`min c₁ #S` and `min c₂ #T` places `S` and `T` within `#S / 128` of arithmetic progressions. -/
lemma exists_arithProg_of_forall_card_add_lt_of_lt (h : CauchyDavenportStability) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (S T : Finset (ZMod p)) (c₁ c₂ M : ℕ), #S = #T → 2 ≤ #S →
      #S ≤ M → (#S + #T : ℝ) ≤ (1 - β) * p → 1 ≤ c₁ → 1 ≤ c₂ → c ≤ c₁ → c ≤ c₂ →
      c * M ≤ c₁ * c₂ → (c₁ < #S ∨ c₂ < #S) →
      (∀ S' ⊆ S, ∀ T' ⊆ T, #S' ≤ c₁ → #T' ≤ c₂ → #(S' + T') < #S + #T) →
      ∃ a b d : ZMod p, ∃ m n : ℕ, (#(S ∆ arithProg a d m) : ℝ) ≤ #S / 128 ∧
        (#(T ∆ arithProg b d n) : ℝ) ≤ #S / 128 := by
  obtain ⟨ε, hε, h₂⟩ := exists_arithProg_card_symmDiff_le_of_expect_card_add_le h hβ
    (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨c₆, h₆⟩ := h₂ 1 one_pos
  refine ⟨max c₆ 0, ?_⟩
  intro p hp S T c₁ c₂ M hST hS hSM hβp hc₁ hc₂ hcc₁ hcc₂ hcM hlt₁₂ hlt
  have hE := expect_card_add_le_of_forall (k := #S + #T - 1) (min_le_right c₁ #S)
    (min_le_right c₂ #T) fun S' hS' T' hT' h₁ h₂ ↦ Nat.le_sub_one_of_lt
      (hlt S' hS' T' hT' (h₁.trans (min_le_left _ _)) (h₂.trans (min_le_left _ _)))
  rw [Nat.cast_sub (by grind)] at hE
  push_cast at hE
  obtain ⟨a, b, d, -, m, n, hSP, hTQ⟩ := h₆ p hp S T (min c₁ #S) (min c₂ #T)
    (le_min hc₁ (by grind)) (min_le_right _ _) (le_min hc₂ (by grind)) (min_le_right _ _)
    (mul_max_le_min_mul_min hST (le_max_left _ _) (le_max_right _ _) hSM hcc₁ hcc₂ hcM hlt₁₂)
    hS (hST ▸ hS) (by simp [hST]) (by simp [hST]) hβp
    (hE.trans (le_add_of_nonneg_right (by positivity)))
  rw [← hST, min_self] at hSP hTQ
  exact ⟨a, b, d, m, n, by linarith, by linarith⟩

/-- If `#S = #T ≥ 2` and no subsets of `S` and `T` with at most `c₁` and `c₂` elements have
`#S + #T` sums, then `S` and `T` are within `#S / 128` of arithmetic progressions. For
`#S ≤ min c₁ c₂` this is `CauchyDavenportStability` for `S` and `T`, and otherwise Theorem 6 for
their subsets of sizes `min c₁ #S` and `min c₂ #T`. -/
lemma exists_arithProg_of_forall_card_add_lt (h : CauchyDavenportStability) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (S T : Finset (ZMod p)) (c₁ c₂ M : ℕ), #S = #T → 2 ≤ #S →
      #S ≤ M → (#S + #T : ℝ) ≤ (1 - β) * p → 1 ≤ c₁ → 1 ≤ c₂ → c ≤ c₁ → c ≤ c₂ →
      c * M ≤ c₁ * c₂ →
      (∀ S' ⊆ S, ∀ T' ⊆ T, #S' ≤ c₁ → #T' ≤ c₂ → #(S' + T') < #S + #T) →
      ∃ a b d : ZMod p, ∃ m n : ℕ, (#(S ∆ arithProg a d m) : ℝ) ≤ #S / 128 ∧
        (#(T ∆ arithProg b d n) : ℝ) ≤ #S / 128 := by
  obtain ⟨c, hc⟩ := exists_arithProg_of_forall_card_add_lt_of_lt h hβ
  refine ⟨c, ?_⟩
  intro p hp S T c₁ c₂ M hST hS hSM hβp hc₁ hc₂ hcc₁ hcc₂ hcM hlt
  by_cases hsmall : #S ≤ c₁ ∧ #S ≤ c₂
  · obtain ⟨hSc₁, hSc₂⟩ := hsmall
    exact exists_arithProg_of_card_add_lt h hβ hp hST hS hβp
      (hlt S subset_rfl T subset_rfl hSc₁ (hST ▸ hSc₂))
  · exact hc p hp S T c₁ c₂ M hST hS hSM hβp hc₁ hc₂ hcc₁ hcc₂ hcM (by grind) hlt

/-- **The end parts.** If `#S = #T` and the pair `(S, T)` is empty or contains a set far from
arithmetic progressions, then some subsets of `S` and `T` with at most `c₁` and `c₂` elements
have `#S + #T` sums. -/
lemma exists_card_add_le_card_add_of_isFar (h : CauchyDavenportStability) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (S T : Finset (ZMod p)) (c₁ c₂ M : ℕ), #S = #T →
      (S = ∅ ∧ T = ∅ ∨ IsFarFromArithProg 64 S ∨ IsFarFromArithProg 64 T) → #S ≤ M →
      (#S + #T : ℝ) ≤ (1 - β) * p → 1 ≤ c₁ → 1 ≤ c₂ → c ≤ c₁ → c ≤ c₂ → c * M ≤ c₁ * c₂ →
      ∃ S' ⊆ S, ∃ T' ⊆ T, #S' ≤ c₁ ∧ #T' ≤ c₂ ∧ #S + #T ≤ #(S' + T') := by
  obtain ⟨c, hc⟩ := exists_arithProg_of_forall_card_add_lt h hβ
  refine ⟨c, ?_⟩
  intro p hp S T c₁ c₂ M hST hfar hSM hβp hc₁ hc₂ hcc₁ hcc₂ hcM
  by_contra hne
  push Not at hne
  obtain h0 | h1 | h2 : #S = 0 ∨ #S = 1 ∨ 2 ≤ #S := by grind
  · simpa [h0, ← hST] using hne ∅ (empty_subset _) ∅ (empty_subset _) (by simp) (by simp)
  · obtain ⟨z, rfl⟩ := card_eq_one.1 h1
    obtain ⟨w, rfl⟩ := card_eq_one.1 (hST ▸ h1)
    simp [not_isFarFromArithProg_singleton] at hfar
  · obtain ⟨a, b, d, m, n, hSP, hTQ⟩ :=
      hc p hp S T c₁ c₂ M hST h2 hSM hβp hc₁ hc₂ hcc₁ hcc₂ hcM hne
    rcases hfar with ⟨rfl, -⟩ | hfar | hfar
    · simp at h2
    · simp [eq_empty_of_isFarFromArithProg hfar hSP] at h2
    · rw [hST] at hTQ h2
      simp [eq_empty_of_isFarFromArithProg hfar hTQ] at h2

/-- **The three windows.** For consecutive intervals `I₁, I₂, I₃` and `J₁, J₂, J₃` of `ZMod p`
of total length at most `p`, the sumsets `I₁ + J₁`, `I₂ + J₂` and `I₃ + J₃` lie in consecutive
intervals, so they are pairwise disjoint. -/
lemma disjoint_add_arithProg_of_add_le (s r : ZMod p) {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (h : a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p) :
    Disjoint (arithProg s 1 a₁ + arithProg r 1 b₁)
      (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) ∧
    Disjoint (arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ + arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃)
      (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) ∧
    Disjoint (arithProg s 1 a₁ + arithProg r 1 b₁)
      (arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ + arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) := by
  have h₁ := arithProg_add_arithProg_subset s r a₁ b₁
  have h₂ := arithProg_add_arithProg_subset (s + (a₁ : ZMod p)) (r + (b₁ : ZMod p)) a₂ b₂
  have h₃ := arithProg_add_arithProg_subset (s + ((a₁ + a₂ : ℕ) : ZMod p))
    (r + ((b₁ + b₂ : ℕ) : ZMod p)) a₃ b₃
  refine ⟨(disjoint_arithProg_one_of_eq_add (k := a₁ + b₁) le_rfl (by grind)
      (by push_cast; ring)).mono h₁ h₂,
    (disjoint_arithProg_one_of_eq_add (k := a₂ + b₂) le_rfl (by grind)
      (by push_cast; ring)).symm.mono h₃ h₂,
    (disjoint_arithProg_one_of_eq_add (k := a₁ + b₁ + (a₂ + b₂)) (by grind) (by grind)
      (by push_cast; ring)).mono h₁ h₃⟩

/-- **One end part.** If `#(A ∩ I) = #(B ∩ J)` and the pair `(A ∩ I, B ∩ J)` is empty or
contains a set far from arithmetic progressions, then some subsets of `A ∩ I` and `B ∩ J` with at
most `c₁` and `c₂` elements have `#(A ∩ I) + #(B ∩ J)` sums. -/
lemma exists_card_inter_add_le_of_isFar (h : CauchyDavenportStability) {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B I J : Finset (ZMod p)) (c₁ c₂ : ℕ),
      (#A + #B : ℝ) ≤ (1 - β) * p → #(A ∩ I) = #(B ∩ J) →
      (A ∩ I = ∅ ∧ B ∩ J = ∅ ∨ IsFarFromArithProg 64 (A ∩ I) ∨
        IsFarFromArithProg 64 (B ∩ J)) →
      1 ≤ c₁ → 1 ≤ c₂ → c ≤ c₁ → c ≤ c₂ → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A ∩ I, ∃ B' ⊆ B ∩ J, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
        #(A ∩ I) + #(B ∩ J) ≤ #(A' + B') := by
  obtain ⟨c, hc⟩ := exists_card_add_le_card_add_of_isFar h hβ
  refine ⟨c, ?_⟩
  intro p hp A B I J c₁ c₂ hβp hAB hfar hc₁ hc₂ hcc₁ hcc₂ hcM
  exact hc p hp _ _ c₁ c₂ (max #A #B) hAB hfar
    ((card_le_card inter_subset_left).trans (le_max_left _ _))
    (hβp.trans' (by gcongr <;> exact inter_subset_left)) hc₁ hc₂ hcc₁ hcc₂ (by simpa using hcM)

/-- Two sumsets `A₁ + B₁ ⊆ U₁` and `A₃ + B₃ ⊆ U₃`, with `U₁`, `U₂` and `U₃` pairwise disjoint,
give `k₁ + k₃` sums of `A₁ ∪ A₃` and `B₁ ∪ B₃` outside `U₂` when `k₁ ≤ #(A₁ + B₁)` and
`k₃ ≤ #(A₃ + B₃)`. -/
lemma exists_subset_add_union_card_eq_disjoint {A₁ A₃ B₁ B₃ U₁ U₂ U₃ : Finset G} {k₁ k₃ : ℕ}
    (h₁ : A₁ + B₁ ⊆ U₁) (h₃ : A₃ + B₃ ⊆ U₃) (hk₁ : k₁ ≤ #(A₁ + B₁)) (hk₃ : k₃ ≤ #(A₃ + B₃))
    (h₁₂ : Disjoint U₁ U₂) (h₃₂ : Disjoint U₃ U₂) (h₁₃ : Disjoint U₁ U₃) :
    ∃ Z ⊆ (A₁ ∪ A₃) + (B₁ ∪ B₃), #Z = k₁ + k₃ ∧ Disjoint Z U₂ := by
  obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq (s := (A₁ + B₁) ∪ (A₃ + B₃))
    (n := k₁ + k₃)
    (by rw [card_union_of_disjoint (h₁₃.mono h₁ h₃)]; exact add_le_add hk₁ hk₃)
  refine ⟨Z, hZ.trans (union_subset (add_subset_add subset_union_left subset_union_left)
    (add_subset_add subset_union_right subset_union_right)), hZc, ?_⟩
  exact (disjoint_union_left.2 ⟨h₁₂.mono_left h₁, h₃₂.mono_left h₃⟩).mono_left hZ

/-- **The end parts** in the setting of Lemma 9. Subsets of `A` and `B` with at most `2 * c₁`
and `2 * c₂` elements have a set `Z` of `#A₁ + #B₁ + #A₃ + #B₃` sums outside `I₂ + J₂`, where
`A₁ = A ∩ I₁`, `B₁ = B ∩ J₁`, `A₃ = A ∩ I₃` and `B₃ = B ∩ J₃`. -/
lemma exists_card_eq_disjoint_of_interval_ends (h : CauchyDavenportStability) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (s r : ZMod p)
      (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ : ℕ),
      a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p → (#A + #B : ℝ) ≤ (1 - β) * p →
      #(A ∩ arithProg s 1 a₁) = #(B ∩ arithProg r 1 b₁) →
      #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) = #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) →
      (A ∩ arithProg s 1 a₁ = ∅ ∧ B ∩ arithProg r 1 b₁ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg s 1 a₁) ∨
        IsFarFromArithProg 64 (B ∩ arithProg r 1 b₁)) →
      (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ = ∅ ∧
          B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) ∨
        IsFarFromArithProg 64 (B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃)) →
      1 ≤ c₁ → 1 ≤ c₂ → c ≤ c₁ → c ≤ c₂ → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ 2 * c₁ ∧ #B' ≤ 2 * c₂ ∧ ∃ Z ⊆ A' + B',
        #Z = #(A ∩ arithProg s 1 a₁) + #(B ∩ arithProg r 1 b₁) +
          #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) +
          #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) ∧
        Disjoint Z (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  obtain ⟨c, hc⟩ := exists_card_inter_add_le_of_isFar h hβ
  refine ⟨c, ?_⟩
  intro p hp A B s r a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ hsum hβp h₁ h₃ hf₁ hf₃ hc₁ hc₂ hcc₁ hcc₂ hcM
  obtain ⟨A₁, hA₁, B₁, hB₁, hA₁c, hB₁c, hAB₁⟩ :=
    hc p hp A B _ _ c₁ c₂ hβp h₁ hf₁ hc₁ hc₂ hcc₁ hcc₂ hcM
  obtain ⟨A₃, hA₃, B₃, hB₃, hA₃c, hB₃c, hAB₃⟩ :=
    hc p hp A B _ _ c₁ c₂ hβp h₃ hf₃ hc₁ hc₂ hcc₁ hcc₂ hcM
  obtain ⟨hW₁₂, hW₃₂, hW₁₃⟩ := disjoint_add_arithProg_of_add_le s r hsum
  obtain ⟨Z, hZ, hZc, hZW⟩ := exists_subset_add_union_card_eq_disjoint
    (add_subset_add (hA₁.trans inter_subset_right) (hB₁.trans inter_subset_right))
    (add_subset_add (hA₃.trans inter_subset_right) (hB₃.trans inter_subset_right))
    hAB₁ hAB₃ hW₁₂ hW₃₂ hW₁₃
  refine ⟨A₁ ∪ A₃, union_subset (hA₁.trans inter_subset_left) (hA₃.trans inter_subset_left),
    B₁ ∪ B₃, union_subset (hB₁.trans inter_subset_left) (hB₃.trans inter_subset_left),
    (card_union_le _ _).trans (by grind), (card_union_le _ _).trans (by grind), Z, hZ,
    by grind, hZW⟩

end EndParts

section FarParts

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

/-- A block of length `l ≤ p` has `l` elements. -/
lemma card_block (v : ZMod p) {l : ℕ} (i : ℕ) (hl : l ≤ p) : #(block v l i) = l :=
  card_arithProg_one _ hl

/-- The `i`-th block of length `l` of `arithProg v 1 n` lies in it when `i < n / l`. -/
lemma block_subset_arithProg (v : ZMod p) {l n i : ℕ} (hl : 1 ≤ l) (hi : i < n / l) :
    block v l i ⊆ arithProg v 1 n :=
  arithProg_add_natCast_subset v (by rw [← Nat.succ_mul, ← Nat.le_div_iff_mul_le hl]; exact hi)

/-- If `Y` misses at most `l - t` points of `arithProg v 1 n`, then it meets each block of
length `l` of this interval in at least `t` points. -/
lemma le_card_inter_block {v : ZMod p} {Y : Finset (ZMod p)} {n l t i : ℕ} (hlp : l ≤ p)
    (hl : 1 ≤ l) (hi : i < n / l) (ht : t + #(arithProg v 1 n \ Y) ≤ l) :
    t ≤ #(Y ∩ block v l i) := by
  rw [inter_comm]
  linarith [card_inter_add_card_sdiff (block v l i) Y, card_block v i hlp (l := l),
    card_le_card (sdiff_subset_sdiff (block_subset_arithProg v hl hi) (subset_refl Y))]

/-- If `X` avoids the points within `L` of `arithProg u 1 m`, then each point of `X` is a good
point for some block of `arithProg v 1 n`, so `#X` is at most the total number of good points. -/
lemma card_le_sum_card_goodPoints [NeZero p] {u v : ZMod p} {m n L l : ℕ}
    (hmnL : m + n + L ≤ p) (hl : 1 ≤ l) (hln : 2 * l ≤ n) (hlL : 2 * l ≤ L)
    {X : Finset (ZMod p)} (hX : Disjoint X (arithProg (u - L) 1 (m + 2 * L))) :
    #X ≤ ∑ i ∈ range (n / l), #(goodPoints X (arithProg u 1 m + arithProg v 1 n) v l i) := by
  refine (card_le_card ?_).trans card_biUnion_le
  intro x hx
  obtain ⟨i, hi, hdisj⟩ :=
    exists_lt_disjoint_image_add_arithProg hmnL hl hln hlL (disjoint_left.1 hX hx)
  exact mem_biUnion.2 ⟨i, mem_range.2 hi, mem_filter.2 ⟨hx, hdisj⟩⟩

/-- If `a ≤ M`, `16 ≤ b` and `16 * M ≤ c * b`, then `16 * a ≤ min c a * b`. -/
lemma sixteen_mul_le_min_mul {a b c M : ℕ} (ha : a ≤ M) (hb : 16 ≤ b) (h : 16 * M ≤ c * b) :
    16 * a ≤ min c a * b := by
  rcases le_total c a with hca | hac
  · rw [min_eq_left hca]
    nlinarith
  · rw [min_eq_right hac]
    nlinarith

/-- **The far parts**, from Lemma 12 and Corollary 11. Let `I = arithProg u 1 m` and
`J = arithProg v 1 n` with `m + n + L ≤ p`, let `X` avoid the points within `L` of `I`, and
let every block of length `l` of `J` meet `Y` in at least `t` points. If `t` is large compared
with `X` and `W`, then some `X' ⊆ X` and `Y' ⊆ Y` with at most `n / l * cX` and `n / l * cY`
elements have `#X` sums outside `W` and outside `I + J`. -/
lemma exists_card_eq_disjoint_add_of_disjoint [NeZero p] {u v : ZMod p} {m n L l : ℕ}
    (hmnL : m + n + L ≤ p) (hl : 1 ≤ l) (hln : 2 * l ≤ n) (hlL : 2 * l ≤ L)
    {X Y W : Finset (ZMod p)} (hX : Disjoint X (arithProg (u - L) 1 (m + 2 * L)))
    {cX cY t : ℕ} (ht : t + #(arithProg v 1 n \ Y) ≤ l) (h16 : 16 ≤ min cY t)
    (hc : 16 * #X ≤ cX * min cY t) (hW : 2 * (#W + #X) + 4 * #X ≤ t) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' ≤ n / l * cX ∧ #Y' ≤ n / l * cY ∧
      ∃ S ⊆ X' + Y', #S = #X ∧ Disjoint S W ∧
        Disjoint S (arithProg u 1 m + arithProg v 1 n) := by
  obtain ⟨X', Y', hXY', hcard⟩ := exists_subsets_min_le_card_biUnion_add_sdiff (range (n / l))
    (fun i ↦ goodPoints X (arithProg u 1 m + arithProg v 1 n) v l i)
    (fun i ↦ Y ∩ block v l i) W (cX := cX) (cY := min cY t) (M := #X)
    (fun i hi ↦ (min_le_right _ _).trans
      (le_card_inter_block (by grind) hl (mem_range.1 hi) ht))
    (fun i _ ↦ sixteen_mul_le_min_mul (card_goodPoints_le _ _ _ _) h16 hc)
    (fun i hi ↦ by
      linarith [card_goodPoints_le (arithProg u 1 m + arithProg v 1 n) v l i (X := X),
        le_card_inter_block (by grind) hl (mem_range.1 hi) ht])
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq ((le_min le_rfl
    (by linarith [card_le_sum_card_goodPoints (v := v) hmnL hl hln hlL hX])).trans hcard)
  refine ⟨(range (n / l)).biUnion X', ?_, (range (n / l)).biUnion Y', ?_, ?_, ?_, S, ?_, hSc,
    disjoint_of_subset_left hS sdiff_disjoint, ?_⟩
  · refine biUnion_subset.2 ?_
    intro i hi
    obtain ⟨hX', -, -, -⟩ := hXY' i hi
    exact hX'.trans (goodPoints_subset _ _ _ _)
  · refine biUnion_subset.2 ?_
    intro i hi
    obtain ⟨-, -, hY', -⟩ := hXY' i hi
    exact hY'.trans inter_subset_left
  · refine (card_biUnion_le_card_mul _ _ _ ?_).trans_eq (by rw [card_range])
    intro i hi
    obtain ⟨-, hX'c, -, -⟩ := hXY' i hi
    exact hX'c
  · refine (card_biUnion_le_card_mul _ _ _ ?_).trans_eq (by rw [card_range])
    intro i hi
    obtain ⟨-, -, -, hY'c⟩ := hXY' i hi
    exact hY'c.trans (min_le_left _ _)
  · refine hS.trans (sdiff_subset.trans (biUnion_subset.2 ?_))
    intro i hi
    exact add_subset_add (subset_biUnion_of_mem _ hi) (subset_biUnion_of_mem _ hi)
  · refine disjoint_of_subset_left (hS.trans sdiff_subset) ((disjoint_biUnion_left _ _ _).2 ?_)
    intro i hi
    rw [disjoint_left]
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    obtain ⟨hXi, -, hYi, -⟩ := hXY' i hi
    exact disjoint_left.1 (mem_filter.1 (hXi hx)).2
      (mem_image_of_mem _ (mem_inter.1 (hYi hy)).2)

/-- If `K / (α * β) ≤ μ` with `K ≥ 0` and `0 < α ≤ 1`, then `K ≤ β * μ`. -/
lemma le_mul_of_div_mul_le {K α β μ : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (h : K / (α * β) ≤ μ) : K ≤ β * μ := by
  have hμ : 0 ≤ μ := (by positivity : 0 ≤ K / (α * β)).trans h
  rw [div_le_iff₀ (by positivity)] at h
  nlinarith [mul_nonneg hβ.le hμ]

/-- Twice the floor of `x / 48` is at most `y` when `x / 24 ≤ y`. -/
lemma two_mul_floor_div_le {x y : ℝ} (hx : 0 ≤ x) (h : x / 24 ≤ y) :
    ((2 * ⌊x / 48⌋₊ : ℕ) : ℝ) ≤ y := by
  push_cast
  linarith [Nat.floor_le (by positivity : 0 ≤ x / 48)]

/-- The floor of `x / 200` plus `k ≤ x / 400` is at most the floor of `x / 48`. -/
lemma floor_div_add_le_floor_div {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hk : (k : ℝ) ≤ x / 400) :
    ⌊x / 200⌋₊ + k ≤ ⌊x / 48⌋₊ :=
  Nat.le_floor (by push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ x / 200)])

/-- The number `b / ⌊β * μ / 48⌋₊` of blocks is at most `192 / (α * β)` when `96 ≤ β * μ`,
`b ≤ 2 * B` and `α * B ≤ μ`. -/
lemma natCast_div_floor_le {α β μ B : ℝ} {b : ℕ} (hα : 0 < α) (hβ : 0 < β) (hβμ : 96 ≤ β * μ)
    (hB : α * B ≤ μ) (hb : b ≤ 2 * B) : ((b / ⌊β * μ / 48⌋₊ : ℕ) : ℝ) ≤ 192 / (α * β) := by
  refine Nat.cast_div_le.trans ?_
  rw [div_le_div_iff₀ (by exact_mod_cast Nat.floor_pos.2 (by linarith)) (by positivity)]
  linarith [Nat.lt_floor_add_one (β * μ / 48), mul_le_mul_of_nonneg_left hB hβ.le,
    mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ α * β)]

/-- If `6400 / (α * β) ≤ c` with `0 < α ≤ 1` and `0 < β ≤ 1`, then `6400 ≤ c`. -/
lemma six_thousand_four_hundred_le {α β : ℝ} {c : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) (hc : 6400 / (α * β) ≤ c) : 6400 ≤ c := by
  exact_mod_cast (le_div_self (by norm_num : (0 : ℝ) ≤ 6400) (by positivity)
    (by nlinarith : α * β ≤ 1)).trans hc

/-- If `6400 / (α * β) ≤ c` with `0 < α ≤ 1` and `0 < β ≤ 1`, then `1 ≤ c`. -/
lemma one_le_of_div_mul_le {α β : ℝ} {c : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) (hc : 6400 / (α * β) ≤ c) : 1 ≤ c :=
  (six_thousand_four_hundred_le hα hα₁ hβ hβ₁ hc).trans' (by norm_num)

/-- If `6400 / (α * β) ≤ c` and `3200 ≤ β * μ`, then `c` and `⌊β * μ / 200⌋₊` are at least
`16`. -/
lemma sixteen_le_min_floor {α β μ : ℝ} {c : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) (hβμ : 3200 ≤ β * μ) (hc : 6400 / (α * β) ≤ c) :
    16 ≤ min c ⌊β * μ / 200⌋₊ :=
  le_min ((six_thousand_four_hundred_le hα hα₁ hβ hβ₁ hc).trans' (by norm_num))
    (Nat.le_floor (by push_cast; linarith))

/-- If `6400 / (α * β) * a ≤ c₁ * c₂` with `c₂ ≤ b`, `α * b ≤ μ` and `400 ≤ β * μ`, then
`16 * a ≤ c₁ * min c₂ ⌊β * μ / 200⌋₊`. -/
lemma sixteen_mul_le_mul_min_floor {α β μ : ℝ} {a b c₁ c₂ : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hβμ : 400 ≤ β * μ) (hb : α * b ≤ μ) (hc₂ : c₂ ≤ b)
    (hc : 6400 / (α * β) * a ≤ c₁ * c₂) : 16 * a ≤ c₁ * min c₂ ⌊β * μ / 200⌋₊ := by
  have hθ := mul_le_min_of_le (θ := α * β / 400) (c := c₂) (x := ⌊β * μ / 200⌋₊) (M := b)
    (by positivity) (by linarith [(by nlinarith : α * β ≤ 1)]) (Nat.cast_nonneg _)
    (by exact_mod_cast hc₂)
    (by linarith [Nat.lt_floor_add_one (β * μ / 200), mul_le_mul_of_nonneg_left hb hβ.le])
  have he : α * β / 400 * (6400 / (α * β) * a) = 16 * a := by
    field_simp
    ring
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ α * β / 400),
    mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α := ℝ) c₁)]

/-- **The far part of `A`** in the setting of Lemma 9, made of the points of `A` outside
`I = arithProg s 1 (a₁ + a₂ + a₃)`. Let `μ ≤ #B` be large with `α * #B ≤ μ`, `6400 ≤ β * μ` and
`2 ^ 20 * γ * μ ≤ β * μ`, let `B` be within `133 * γ * μ` of `J₂`, and let `W` and `A \ I` have
at most `e ≤ 266 * γ * μ` elements in total. Then some `X ⊆ A \ I` and `Y ⊆ B` with at most
`192 / (α * β) * c₁` and `192 / (α * β) * c₂` elements have `#(A \ I)` sums outside `W` and
outside `I₂ + J₂`. -/
lemma exists_far_part (hp : p.Prime) {α β γ μ : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) {A B W : Finset (ZMod p)} (hμB : μ ≤ #B) (hαB : α * #B ≤ μ) (hμp : μ ≤ p)
    (hβμ : 6400 ≤ β * μ) (hγμ : 2 ^ 20 * γ * μ ≤ β * μ)
    {s r : ZMod p} {a₁ a₂ a₃ b₁ b₂ : ℕ} (hL₁ : ⌊β * p / 8⌋₊ ≤ a₁) (hL₃ : ⌊β * p / 8⌋₊ ≤ a₃)
    (hp₂ : a₂ + b₂ + ⌊β * p / 8⌋₊ ≤ p)
    (hB₂ : (#(B ∆ arithProg (r + b₁) 1 b₂) : ℝ) ≤ 133 * γ * μ)
    {e : ℕ} (hWe : #W + #(A \ arithProg s 1 (a₁ + a₂ + a₃)) ≤ e) (he : (e : ℝ) ≤ 266 * γ * μ)
    {c₁ c₂ : ℕ} (hc₂B : c₂ ≤ #B) (hKc₂ : 6400 / (α * β) ≤ c₂)
    (hKc : 6400 / (α * β) * #A ≤ c₁ * c₂) :
    ∃ X ⊆ A \ arithProg s 1 (a₁ + a₂ + a₃), ∃ Y ⊆ B, (#X : ℝ) ≤ 192 / (α * β) * c₁ ∧
      (#Y : ℝ) ≤ 192 / (α * β) * c₂ ∧ ∃ S ⊆ X + Y, #S = #(A \ arithProg s 1 (a₁ + a₂ + a₃)) ∧
        Disjoint S W ∧ Disjoint S (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hμ₀ : 0 ≤ μ := (mul_nonneg hα.le (Nat.cast_nonneg _)).trans hαB
  obtain ⟨hBJ, hB, hJ⟩ := card_sdiff_add_card_sdiff_le hB₂
  rw [card_arithProg_one _ (by grind)] at hJ
  obtain ⟨X, hX, Y, hY, hXc, hYc, S, hS, hSc, hSW, hSIJ⟩ :=
    exists_card_eq_disjoint_add_of_disjoint (u := s + (a₁ : ZMod p)) (v := r + (b₁ : ZMod p))
      (L := ⌊β * p / 8⌋₊) (l := ⌊β * μ / 48⌋₊) (t := ⌊β * μ / 200⌋₊)
      (Y := B) (W := W) (cX := c₁) (cY := c₂) hp₂ (Nat.le_floor (by push_cast; linarith))
      (Nat.cast_le.1 (two_mul_floor_div_le (by positivity)
        (by linarith [mul_le_mul_of_nonneg_right hβ₁ hμ₀,
          Nat.cast_nonneg (α := ℝ) #(B \ arithProg (r + (b₁ : ZMod p)) 1 b₂)])))
      (Nat.le_floor (two_mul_floor_div_le (by positivity)
        (by linarith [mul_le_mul_of_nonneg_left hμp hβ.le])))
      (disjoint_of_subset_right (arithProg_sub_subset s hL₁ hL₃) sdiff_disjoint)
      (floor_div_add_le_floor_div (by positivity)
        (by linarith [Nat.cast_nonneg (α := ℝ) #(B \ arithProg (r + (b₁ : ZMod p)) 1 b₂)]))
      (sixteen_le_min_floor hα hα₁ hβ hβ₁ (by linarith) hKc₂)
      ((Nat.mul_le_mul_left 16 (card_le_card sdiff_subset)).trans
        (sixteen_mul_le_mul_min_floor hα hα₁ hβ hβ₁ (by linarith) hαB hc₂B hKc))
      (Nat.le_floor (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) #W,
        (by exact_mod_cast hWe : (#W + #(A \ arithProg s 1 (a₁ + a₂ + a₃)) : ℝ) ≤ e)]))
  have hbl := natCast_div_floor_le (μ := μ) (b := b₂) hα hβ (by linarith) hαB
    (by linarith [mul_le_mul_of_nonneg_right hβ₁ hμ₀,
      Nat.cast_nonneg (α := ℝ) #(B \ arithProg (r + (b₁ : ZMod p)) 1 b₂)])
  refine ⟨X, hX, Y, hY, ?_, ?_, S, hS, hSc, hSW, hSIJ⟩
  · exact ((Nat.cast_le (α := ℝ)).2 hXc).trans (by push_cast; gcongr)
  · exact ((Nat.cast_le (α := ℝ)).2 hYc).trans (by push_cast; gcongr)

end FarParts

section MiddlePart

variable {p : ℕ}

/-- **A set near an interval.** Let `A` be within `133 * γ * μ` of `I = arithProg x 1 m` with
`m ≤ p`, `400 * γ ≤ 1` and `α * #A ≤ μ ≤ #A`. Then `2 * μ / 3 ≤ m`, `α * m ≤ 4 * μ / 3`, the
part `A ∩ I` has at least `α / 2 * #A` elements and is nonempty, and `I \ A` has at most
`133 * γ * μ` elements. -/
lemma near_interval_bounds {A : Finset (ZMod p)} {x : ZMod p} {m : ℕ} {α γ μ : ℝ} (hm : m ≤ p)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hγ₁ : 400 * γ ≤ 1) (hμA : μ ≤ #A)
    (hαA : α * #A ≤ μ) (hA₀ : 0 < #A) (hA : (#(A ∆ arithProg x 1 m) : ℝ) ≤ 133 * γ * μ) :
    2 * μ / 3 ≤ m ∧ α * m ≤ 4 * μ / 3 ∧ α / 2 * #A ≤ #(A ∩ arithProg x 1 m) ∧
      0 < #(A ∩ arithProg x 1 m) ∧ (#(arithProg x 1 m \ A) : ℝ) ≤ 133 * γ * μ := by
  obtain ⟨hd, hA', hI⟩ := card_sdiff_add_card_sdiff_le hA
  rw [card_arithProg_one _ hm] at hI
  have hμ₀ : 0 ≤ μ := (mul_nonneg hα.le (Nat.cast_nonneg _)).trans hαA
  have hAI : α / 2 * #A ≤ #(A ∩ arithProg x 1 m) := by
    nlinarith [mul_le_mul_of_nonneg_right hγ₁ hμ₀, Nat.cast_nonneg (α := ℝ) #(arithProg x 1 m \ A),
      mul_le_mul_of_nonneg_right hα₁ (Nat.cast_nonneg (α := ℝ) #A)]
  refine ⟨by nlinarith [mul_le_mul_of_nonneg_right hγ₁ hμ₀,
      Nat.cast_nonneg (α := ℝ) #(arithProg x 1 m \ A)], ?_, hAI,
    Nat.cast_pos.1 (hAI.trans_lt' (by positivity)),
    by linarith [Nat.cast_nonneg (α := ℝ) #(A \ arithProg x 1 m)]⟩
  rw [hI]
  nlinarith [mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card inter_subset_left :
      (#(A ∩ arithProg x 1 m) : ℝ) ≤ #A) hα.le, mul_le_mul_of_nonneg_right hγ₁ hμ₀,
    mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) #(arithProg x 1 m \ A)) hα₁,
    Nat.cast_nonneg (α := ℝ) #(A \ arithProg x 1 m)]

/-- If `400 * γ ≤ γ₈` and `2 * μ / 3 ≤ x` with `γ, μ ≥ 0`, then `133 * γ * μ ≤ γ₈ * x`. -/
lemma mul_le_mul_min_of_le {γ γ₈ μ x : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hγ₈ : 400 * γ ≤ γ₈)
    (hx : 2 * μ / 3 ≤ x) : 133 * γ * μ ≤ γ₈ * x := by
  nlinarith [mul_nonneg hγ hμ]

/-- The condition of Theorem 8 for the subsets of sizes `min c₁ x` and `min c₂ y` of sets of
sizes `x` and `y` with `α / 2 * a ≤ x ≤ a` and `α / 2 * b ≤ y ≤ b`. -/
lemma mul_max_le_min_mul_min_of_le {α c : ℝ} {a b x y c₁ c₂ : ℕ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hxa : x ≤ a) (hyb : y ≤ b) (hx : α / 2 * a ≤ x) (hy : α / 2 * b ≤ y) (hc₁ : c₁ ≤ a)
    (hc₂ : c₂ ≤ b) (hc : 4 * max c 0 / α ^ 2 * max (a : ℝ) b ≤ c₁ * c₂) :
    c * max (x : ℝ) y ≤ (min c₁ x : ℕ) * (min c₂ y : ℕ) := by
  have h₁ := mul_le_min_of_le (θ := α / 2) (by positivity) (by linarith) (Nat.cast_nonneg _)
    (by exact_mod_cast hc₁) hx
  have h₂ := mul_le_min_of_le (θ := α / 2) (by positivity) (by linarith) (Nat.cast_nonneg _)
    (by exact_mod_cast hc₂) hy
  have he : (α / 2) ^ 2 * (4 * max c 0 / α ^ 2 * max (a : ℝ) b) = max c 0 * max (a : ℝ) b := by
    field_simp
    ring
  push_cast
  linarith [mul_le_mul (le_max_left c 0) (max_le_max (by exact_mod_cast hxa : (x : ℝ) ≤ a)
      (by exact_mod_cast hyb : (y : ℝ) ≤ b)) (by positivity) (le_max_right c 0),
    mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (α / 2) ^ 2),
    mul_le_mul h₁ h₂ (by positivity) (by positivity)]

/-- **The middle part**, from Theorem 8. There is `γ₈ > 0` such that for `0 < α ≤ 1` there is
`c` with the following property. Let `A` and `B` be within `133 * γ * μ` of intervals `I` and `J`
of total length at most `p`, where `400 * γ ≤ min γ₈ 1` and `α * #A, α * #B ≤ μ ≤ #A, #B`. If
`1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` satisfy `c * max #A #B ≤ c₁ * c₂`, then some subsets of `A ∩ I`
and `B ∩ J` with at most `c₁` and `c₂` elements have `#(A ∩ I) + #(B ∩ J) - 1` sums. -/
lemma exists_middle_part (h : FewTranslatesNearIntervals) :
    ∃ γ₈ > (0 : ℝ), ∀ α > (0 : ℝ), α ≤ 1 → ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (A B : Finset (ZMod p)) (x y : ZMod p) (m n c₁ c₂ : ℕ) (γ μ : ℝ), m + n ≤ p →
      0 ≤ γ → 400 * γ ≤ γ₈ → 400 * γ ≤ 1 → μ ≤ #A → μ ≤ #B → α * #A ≤ μ → α * #B ≤ μ →
      (#(A ∆ arithProg x 1 m) : ℝ) ≤ 133 * γ * μ →
      (#(B ∆ arithProg y 1 n) : ℝ) ≤ 133 * γ * μ →
      1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ #A → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A ∩ arithProg x 1 m, ∃ B' ⊆ B ∩ arithProg y 1 n, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧
        #(A ∩ arithProg x 1 m) + #(B ∩ arithProg y 1 n) - 1 ≤ #(A' + B') := by
  obtain ⟨γ₈, hγ₈, h₈⟩ :=
    exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg h
  refine ⟨γ₈, hγ₈, ?_⟩
  intro α hα hα₁
  obtain ⟨c₈, hc₈⟩ := h₈ (α / 2) (by positivity)
  refine ⟨4 * max c₈ 0 / α ^ 2, ?_⟩
  intro p hp A B x y m n c₁ c₂ γ μ hmn hγ hγ₈' hγ₁ hμA hμB hαA hαB hA hB hc₁ hc₂ hc₁A hc₂B hc
  obtain ⟨hmμ, hαm, hAI, hAI₀, hIA⟩ :=
    near_interval_bounds (by grind) hα hα₁ hγ₁ hμA hαA (by grind) hA
  obtain ⟨hnμ, hαn, hBJ, hBJ₀, hJB⟩ :=
    near_interval_bounds (by grind) hα hα₁ hγ₁ hμB hαB (by grind) hB
  have hγ₈μ := mul_le_mul_min_of_le hγ ((mul_nonneg hα.le (Nat.cast_nonneg _)).trans hαA) hγ₈'
    (le_min hmμ hnμ)
  obtain ⟨A', hA', B', hB', hA'c, hB'c, hAB'⟩ := hc₈ p hp x y m n (A ∩ arithProg x 1 m)
    (B ∩ arithProg y 1 n) (min c₁ #(A ∩ arithProg x 1 m)) (min c₂ #(B ∩ arithProg y 1 n))
    inter_subset_right inter_subset_right hmn (by linarith)
    (by rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith)
    (by rw [sdiff_inter_self_right]; linarith) (by rw [sdiff_inter_self_right]; linarith)
    (le_min hc₁ hAI₀) (min_le_right _ _) (le_min hc₂ hBJ₀) (min_le_right _ _)
    (mul_max_le_min_mul_min_of_le hα hα₁ (card_le_card inter_subset_left)
      (card_le_card inter_subset_left) hAI hBJ hc₁A hc₂B hc)
  exact ⟨A', hA', B', hB', hA'c ▸ min_le_left _ _, hB'c ▸ min_le_left _ _, hAB'⟩

end MiddlePart

section IntervalCase

variable {G : Type*} [DecidableEq G]

/-- **The final count.** If `Z ⊆ A₁ + B₁`, `A₂ + B₂` and `S ⊆ A₃ + B₃` are pairwise disjoint,
then the unions `A₁ ∪ A₂ ∪ A₃` and `B₁ ∪ B₂ ∪ B₃` have at least `#Z + #(A₂ + B₂) + #S` sums. -/
lemma card_add_card_add_card_le_card_add [Add G] {A₁ A₂ A₃ B₁ B₂ B₃ Z S : Finset G}
    (hZ : Z ⊆ A₁ + B₁) (hS : S ⊆ A₃ + B₃) (hZT : Disjoint Z (A₂ + B₂)) (hSZ : Disjoint S Z)
    (hST : Disjoint S (A₂ + B₂)) :
    #Z + #(A₂ + B₂) + #S ≤ #((A₁ ∪ A₂ ∪ A₃) + (B₁ ∪ B₂ ∪ B₃)) := by
  rw [← card_union_of_disjoint hZT,
    ← card_union_of_disjoint (disjoint_union_right.2 ⟨hSZ, hST⟩).symm]
  refine card_le_card (union_subset (union_subset (hZ.trans ?_) ?_) (hS.trans ?_))
  · exact add_subset_add (subset_union_left.trans subset_union_left)
      (subset_union_left.trans subset_union_left)
  · exact add_subset_add (subset_union_right.trans subset_union_left)
      (subset_union_right.trans subset_union_left)
  · exact add_subset_add subset_union_right subset_union_right

/-- The union of two sets has at most as many elements as the two sets together, in `ℝ`. -/
lemma natCast_card_union_le (s t : Finset G) : (#(s ∪ t) : ℝ) ≤ #s + #t := by
  exact_mod_cast card_union_le s t

/-- The union of three sets has at most as many elements as the three sets together. -/
lemma card_union_union_le (s₁ s₂ s₃ : Finset G) : #(s₁ ∪ s₂ ∪ s₃) ≤ #s₁ + #s₂ + #s₃ := by
  grind [card_union_le]

/-- **The size of the subsets.** Three sets with at most `2 * c`, `c` and `D * c` elements have
at most `N * c` elements together when `3 + D ≤ N`. -/
lemma card_union_union_le_mul {s₁ s₂ s₃ : Finset G} {c N : ℕ} {D : ℝ} (hN : 3 + D ≤ N)
    (h₁ : #s₁ ≤ 2 * c) (h₂ : #s₂ ≤ c) (h₃ : (#s₃ : ℝ) ≤ D * c) : #(s₁ ∪ s₂ ∪ s₃) ≤ N * c := by
  have h := card_union_union_le s₁ s₂ s₃
  rw [← Nat.cast_le (α := ℝ)] at h h₁ h₂ ⊢
  push_cast at h h₁ h₂ ⊢
  linarith [mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg (α := ℝ) c)]

/-- The difference `B \ J` has at most as many elements as the symmetric difference. -/
lemma card_sdiff_le_card_symmDiff (B J : Finset G) : #(B \ J) ≤ #(B ∆ J) :=
  card_le_card (by rw [symmDiff_def]; exact le_sup_left)

/-- A bound on `max (max a b) d` bounds `a`, `b` and `d`. -/
lemma le_of_max_max_le {a b d x : ℝ} (h : max (max a b) d ≤ x) : a ≤ x ∧ b ≤ x ∧ d ≤ x := by
  simpa [and_assoc] using h

/-- A bound on `max (max a b) d * M` with `M ≥ 0` bounds `a * M`, `b * M` and `d * M`. -/
lemma mul_le_of_max_max_mul_le {a b d M x : ℝ} (hM : 0 ≤ M) (h : max (max a b) d * M ≤ x) :
    a * M ≤ x ∧ b * M ≤ x ∧ d * M ≤ x := by
  rw [max_mul_of_nonneg _ _ hM, max_mul_of_nonneg _ _ hM] at h
  exact le_of_max_max_le h

/-- For `0 < α ≤ 1` and `0 < β ≤ 1`, the ceiling of `400 / (α * β)` is at least
`3 + 2 * (192 / (α * β))`. -/
lemma three_add_le_ceil {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1) :
    3 + 2 * (192 / (α * β)) ≤ (⌈400 / (α * β)⌉₊ : ℝ) := by
  have h16 := le_div_self (by norm_num : (0 : ℝ) ≤ 16) (by positivity) (by nlinarith : α * β ≤ 1)
  have he : 400 / (α * β) = 2 * (192 / (α * β)) + 16 / (α * β) := by ring
  linarith [Nat.le_ceil (400 / (α * β))]

/-- The closeness `γ = min (β / 2 ^ 20) (γ₈ / 400)` to intervals used for Theorem 1. -/
noncomputable def nearIntervalConst (β γ₈ : ℝ) : ℝ := min (β / 2 ^ 20) (γ₈ / 400)

/-- The constant `nearIntervalConst β γ₈` is positive. -/
lemma nearIntervalConst_pos {β γ₈ : ℝ} (hβ : 0 < β) (hγ₈ : 0 < γ₈) :
    0 < nearIntervalConst β γ₈ := by
  unfold nearIntervalConst
  positivity

/-- The constant `nearIntervalConst β γ₈` is at most `β / 2 ^ 20`. -/
lemma two_pow_mul_nearIntervalConst_le (β γ₈ : ℝ) : 2 ^ 20 * nearIntervalConst β γ₈ ≤ β := by
  unfold nearIntervalConst
  linarith [min_le_left (β / 2 ^ 20) (γ₈ / 400)]

/-- The constant `nearIntervalConst β γ₈` is at most `γ₈ / 400`. -/
lemma four_hundred_mul_nearIntervalConst_le (β γ₈ : ℝ) : 400 * nearIntervalConst β γ₈ ≤ γ₈ := by
  unfold nearIntervalConst
  linarith [min_le_right (β / 2 ^ 20) (γ₈ / 400)]

variable {p : ℕ}

/-- The parts of `A` and `B` in the end intervals and outside `I` and `J` have together as many
elements as the parts outside the middle intervals `I₂` and `J₂`. -/
lemma card_ends_add_card_sdiff_eq (A B : Finset (ZMod p)) (s r : ZMod p)
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (hA : a₁ + a₂ + a₃ ≤ p) (hB : b₁ + b₂ + b₃ ≤ p) :
    #(A ∩ arithProg s 1 a₁) + #(B ∩ arithProg r 1 b₁) +
        #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) + #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) +
        #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(B \ arithProg r 1 (b₁ + b₂ + b₃)) =
      #(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂) := by
  linarith [card_eq_card_sdiff_add_card_inter A s hA, card_eq_card_sdiff_add_card_inter B r hB,
    card_inter_add_card_sdiff A (arithProg (s + (a₁ : ZMod p)) 1 a₂),
    card_inter_add_card_sdiff B (arithProg (r + (b₁ : ZMod p)) 1 b₂)]

/-- **The far parts** of `A` and `B` in the setting of Lemma 9, made of the points of `A` outside
`I = arithProg s 1 (a₁ + a₂ + a₃)` and of `B` outside `J = arithProg r 1 (b₁ + b₂ + b₃)`. If `Z`,
`A \ I` and `B \ J` have together at most as many elements as `A \ I₂` and `B \ J₂`, then some
subsets of `A` and `B` with at most `384 / (α * β) * c₁` and `384 / (α * β) * c₂` elements have
`#(A \ I) + #(B \ J)` sums outside `Z` and outside `I₂ + J₂`. -/
lemma exists_far_parts (hp : p.Prime) {α β γ μ : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) (hγβ : 2 ^ 20 * γ ≤ β) {A B Z : Finset (ZMod p)} (hμA : μ ≤ #A)
    (hμB : μ ≤ #B) (hαA : α * #A ≤ μ) (hαB : α * #B ≤ μ) (hμp : μ ≤ p)
    (hμ : 6400 / (α * β) ≤ μ) {s r : ZMod p} {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (hL₁ : ⌊β * p / 8⌋₊ ≤ a₁) (hL₃ : ⌊β * p / 8⌋₊ ≤ a₃) (hL₁' : ⌊β * p / 8⌋₊ ≤ b₁)
    (hL₃' : ⌊β * p / 8⌋₊ ≤ b₃) (hsum : a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p)
    (hA₂ : (#(A ∆ arithProg (s + a₁) 1 a₂) : ℝ) ≤ 133 * γ * μ)
    (hB₂ : (#(B ∆ arithProg (r + b₁) 1 b₂) : ℝ) ≤ 133 * γ * μ)
    (hZ : #Z + #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(B \ arithProg r 1 (b₁ + b₂ + b₃)) ≤
      #(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂))
    {c₁ c₂ : ℕ} (hc₁A : c₁ ≤ #A) (hc₂B : c₂ ≤ #B) (hKc₁ : 6400 / (α * β) ≤ c₁)
    (hKc₂ : 6400 / (α * β) ≤ c₂) (hKc : 6400 / (α * β) * max (#A : ℝ) #B ≤ c₁ * c₂) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (#A' : ℝ) ≤ 2 * (192 / (α * β)) * c₁ ∧
      (#B' : ℝ) ≤ 2 * (192 / (α * β)) * c₂ ∧
      ∃ S ⊆ A' + B',
        #S = #(A \ arithProg s 1 (a₁ + a₂ + a₃)) + #(B \ arithProg r 1 (b₁ + b₂ + b₃)) ∧
        Disjoint S Z ∧ Disjoint S (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  have hβμ := le_mul_of_div_mul_le (by norm_num) hα hα₁ hβ hμ
  have hγμ := mul_le_mul_of_nonneg_right hγβ ((mul_nonneg hα.le (Nat.cast_nonneg _)).trans hαA)
  have he : ((#(A \ arithProg (s + a₁) 1 a₂) + #(B \ arithProg (r + b₁) 1 b₂) : ℕ) : ℝ) ≤
      266 * γ * μ := by
    push_cast
    linarith [(Nat.cast_le (α := ℝ)).2 (card_sdiff_le_card_symmDiff A (arithProg (s + a₁) 1 a₂)),
      (Nat.cast_le (α := ℝ)).2 (card_sdiff_le_card_symmDiff B (arithProg (r + b₁) 1 b₂))]
  obtain ⟨X₁, hX₁, Y₁, hY₁, hX₁c, hY₁c, S₁, hS₁, hS₁c, hS₁Z, hS₁IJ⟩ :=
    exists_far_part hp hα hα₁ hβ hβ₁ (W := Z) (s := s) (r := r) (a₂ := a₂) (b₁ := b₁)
      (b₂ := b₂) hμB hαB hμp hβμ hγμ hL₁ hL₃ (by grind) hB₂ (by grind) he hc₂B hKc₂
      ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hKc)
  obtain ⟨X₂, hX₂, Y₂, hY₂, hX₂c, hY₂c, S₂, hS₂, hS₂c, hS₂W, hS₂IJ⟩ :=
    exists_far_part hp hα hα₁ hβ hβ₁ (W := Z ∪ S₁) (s := r) (r := s) (a₂ := b₂) (b₁ := a₁)
      (b₂ := a₂) hμA hαA hμp hβμ hγμ hL₁' hL₃' (by grind) hA₂ (by grind [card_union_le Z S₁]) he
      hc₁A hKc₁
      ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)).trans
        (hKc.trans_eq (mul_comm _ _)))
  obtain ⟨hS₂Z, hS₂S₁⟩ := disjoint_union_right.1 hS₂W
  refine ⟨X₁ ∪ Y₂, union_subset (hX₁.trans sdiff_subset) hY₂, Y₁ ∪ X₂,
    union_subset hY₁ (hX₂.trans sdiff_subset),
    by linarith [natCast_card_union_le X₁ Y₂], by linarith [natCast_card_union_le Y₁ X₂],
    S₁ ∪ S₂, union_subset (hS₁.trans (add_subset_add subset_union_left subset_union_left))
      (hS₂.trans ((add_comm X₂ Y₂).subset.trans
        (add_subset_add subset_union_right subset_union_right))),
    by rw [card_union_of_disjoint hS₂S₁.symm, hS₁c, hS₂c],
    disjoint_union_left.2 ⟨hS₁Z, hS₂Z⟩,
    disjoint_union_left.2 ⟨hS₁IJ, hS₂IJ.mono_right (add_comm _ _).subset⟩⟩

/-- Under the hypotheses of Theorem 1 with `α ≤ 1`, the size `μ = min #A #B` satisfies
`α * #A ≤ μ`, `α * #B ≤ μ` and `μ ≤ p`. -/
lemma min_card_bounds {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    {A B : Finset (ZMod p)} (hAB : α * #B ≤ #A) (hBA : (#A : ℝ) ≤ α⁻¹ * #B)
    (hABp : (#A + #B : ℝ) ≤ (1 - β) * p) :
    min (#A : ℝ) #B ≤ #A ∧ min (#A : ℝ) #B ≤ #B ∧ α * #A ≤ min (#A : ℝ) #B ∧
      α * #B ≤ min (#A : ℝ) #B ∧ min (#A : ℝ) #B ≤ p := by
  refine ⟨min_le_left _ _, min_le_right _ _,
    le_min (mul_le_of_le_one_left (Nat.cast_nonneg _) hα₁) (by rwa [← le_inv_mul_iff₀ hα]),
    le_min hAB (mul_le_of_le_one_left (Nat.cast_nonneg _) hα₁), ?_⟩
  have := mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) p) (by linarith : 1 - β ≤ 1)
  linarith [min_le_left (#A : ℝ) #B, Nat.cast_nonneg (α := ℝ) #B]

/-- **Theorem 1 for sets near intervals.** For `0 < α ≤ 1` and `0 < β ≤ 2⁻¹⁰` there are `γ > 0`
and `K` with the following property. Let `A` and `B` be within `γ * min #A #B` of intervals of
`ZMod p`, with `α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, and let `c₁ ≤ #A` and
`c₂ ≤ #B` satisfy `K ≤ c₁`, `K ≤ c₂` and `K * max #A #B ≤ c₁ * c₂`. Then some subsets of `A`
and `B` with at most `⌈400 / (α * β)⌉₊ * c₁` and `⌈400 / (α * β)⌉₊ * c₂` elements have
`#A + #B - 1` sums. -/
lemma exists_card_add_of_near_intervals (h₄ : CauchyDavenportStability)
    (h₅ : FewTranslatesNearIntervals) {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1 / 1024) :
    ∃ γ > (0 : ℝ), ∃ K : ℝ, ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty →
      B.Nonempty → α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      ∀ (x y : ZMod p) (m n : ℕ), (#(A ∆ arithProg x 1 m) : ℝ) ≤ γ * min (#A : ℝ) #B →
      (#(B ∆ arithProg y 1 n) : ℝ) ≤ γ * min (#A : ℝ) #B →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → K ≤ c₁ → K ≤ c₂ → K * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ ⌈400 / (α * β)⌉₊ * c₁ ∧ #B' ≤ ⌈400 / (α * β)⌉₊ * c₂ ∧
        #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ₈, hγ₈, h₈⟩ := exists_middle_part h₅
  obtain ⟨c₈, hc₈⟩ := h₈ α hα hα₁
  obtain ⟨cₑ, hcₑ⟩ := exists_card_eq_disjoint_of_interval_ends h₄ hβ
  refine ⟨nearIntervalConst β γ₈, nearIntervalConst_pos hβ hγ₈,
    max (max cₑ c₈) (6400 / (α * β)), ?_⟩
  intro p hp A B hA hB hAB hBA hABp x y m n hAx hBy c₁ c₂ hc₁A hc₂B hKc₁ hKc₂ hKc
  obtain ⟨hₑ₁, h₈₁, hK₁⟩ := le_of_max_max_le hKc₁
  obtain ⟨hₑ₂, h₈₂, hK₂⟩ := le_of_max_max_le hKc₂
  obtain ⟨hₑ, h₈, hK⟩ := mul_le_of_max_max_mul_le (by positivity) hKc
  obtain ⟨hμA, hμB, hαA, hαB, hμp⟩ := min_card_bounds hα hα₁ hβ hAB hBA hABp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, r, a₁, a₂, a₃, b₁, b₂, b₃, hL₁, hL₃, hL₁', hL₃', hsum, -, h₁, h₃, hA₂, hB₂, hf₁,
    hf₃⟩ := exists_interval_ends (x := x) (y := y) hp hβ₁ (nearIntervalConst_pos hβ hγ₈)
      (two_pow_mul_nearIntervalConst_le β γ₈) hA hB hABp (min_le_right m p) (min_le_right n p)
      (by rwa [← arithProg_one_eq_min]) (by rwa [← arithProg_one_eq_min])
  obtain ⟨A₁, hA₁, B₁, hB₁, hA₁c, hB₁c, Z, hZ, hZc, hZ₂⟩ := hcₑ p hp A B s r a₁ a₂ a₃ b₁
    b₂ b₃ c₁ c₂ hsum hABp h₁ h₃ hf₁ hf₃ (one_le_of_div_mul_le hα hα₁ hβ (by linarith) hK₁)
    (one_le_of_div_mul_le hα hα₁ hβ (by linarith) hK₂) hₑ₁ hₑ₂ hₑ
  obtain ⟨A₂, hA₂', B₂, hB₂', hA₂c, hB₂c, hAB₂⟩ := hc₈ p hp A B (s + a₁) (r + b₁) a₂ b₂ c₁ c₂
    _ _ (by grind) (nearIntervalConst_pos hβ hγ₈).le (four_hundred_mul_nearIntervalConst_le β γ₈)
    (by linarith [two_pow_mul_nearIntervalConst_le β γ₈, nearIntervalConst_pos hβ hγ₈])
    hμA hμB hαA hαB hA₂ hB₂ (one_le_of_div_mul_le hα hα₁ hβ (by linarith) hK₁)
    (one_le_of_div_mul_le hα hα₁ hβ (by linarith) hK₂) hc₁A hc₂B h₈
  have hcount := card_ends_add_card_sdiff_eq A B s r (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
    (b₁ := b₁) (b₂ := b₂) (b₃ := b₃) (by grind) (by grind)
  obtain ⟨A₃, hA₃, B₃, hB₃, hA₃c, hB₃c, S, hS, hSc, hSZ, hS₂⟩ := exists_far_parts hp hα hα₁ hβ
    (by linarith) (two_pow_mul_nearIntervalConst_le β γ₈) hμA hμB hαA hαB hμp
    (le_min (hK₁.trans (by exact_mod_cast hc₁A)) (hK₂.trans (by exact_mod_cast hc₂B)))
    hL₁ hL₃ hL₁' hL₃' hsum hA₂ hB₂ (by rw [hZc]; exact hcount.le) hc₁A hc₂B hK₁ hK₂ hK
  have hT : A₂ + B₂ ⊆ arithProg (s + (a₁ : ZMod p)) 1 a₂ + arithProg (r + (b₁ : ZMod p)) 1 b₂ :=
    add_subset_add (hA₂'.trans inter_subset_right) (hB₂'.trans inter_subset_right)
  refine ⟨A₁ ∪ A₂ ∪ A₃, union_subset (union_subset hA₁ (hA₂'.trans inter_subset_left)) hA₃,
    B₁ ∪ B₂ ∪ B₃, union_subset (union_subset hB₁ (hB₂'.trans inter_subset_left)) hB₃,
    card_union_union_le_mul (three_add_le_ceil hα hα₁ hβ (by linarith)) hA₁c hA₂c hA₃c,
    card_union_union_le_mul (three_add_le_ceil hα hα₁ hβ (by linarith)) hB₁c hB₂c hB₃c, ?_⟩
  refine le_trans ?_
    (card_add_card_add_card_le_card_add hZ hS (hZ₂.mono_right hT) hSZ (hS₂.mono_right hT))
  grind [card_inter_add_card_sdiff A (arithProg (s + (a₁ : ZMod p)) 1 a₂),
    card_inter_add_card_sdiff B (arithProg (r + (b₁ : ZMod p)) 1 b₂)]

end IntervalCase

section Theorem1

/-- Dividing `c ≥ 2 * N` by `N` loses at most half of `c / N`: `c ≤ 2 * N * (c / N)`. -/
lemma le_two_mul_mul_div {c N : ℕ} (hN : 0 < N) (hc : 2 * N ≤ c) :
    (c : ℝ) ≤ 2 * N * (c / N : ℕ) := by
  have h : (c : ℝ) < (c / N : ℕ) * N + N := by exact_mod_cast Nat.lt_div_mul_add (a := c) hN
  have hc' : (2 * N : ℝ) ≤ c := by exact_mod_cast hc
  linarith

/-- If `4 * N ^ 2 * K ≤ c` with `1 ≤ K` and `0 < N`, then `2 * N ≤ c`. -/
lemma two_mul_le_of_four_mul_sq_mul_le {c N : ℕ} {K : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (hc : 4 * N ^ 2 * K ≤ c) : 2 * N ≤ c := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact_mod_cast (by nlinarith [mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ N ^ 2)] :
    (2 * N : ℝ) ≤ c)

/-- If `4 * N ^ 2 * K ≤ c₁` with `1 ≤ K`, then `c₁ / N` is at least `2 * N * K`. -/
lemma two_mul_mul_le_div {c₁ N : ℕ} {K : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (hc₁ : 4 * N ^ 2 * K ≤ c₁) : 2 * N * K ≤ (c₁ / N : ℕ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [le_two_mul_mul_div hN (two_mul_le_of_four_mul_sq_mul_le hN hK hc₁)]

/-- If `C * M ≤ c₁ * c₂` with `c₂ ≤ M` and `0 < M`, then `C ≤ c₁`. -/
lemma le_of_mul_le_mul_of_le {c₁ c₂ : ℕ} {C M : ℝ} (hM : 0 < M) (hc₂M : c₂ ≤ M)
    (hc : C * M ≤ c₁ * c₂) : C ≤ c₁ :=
  le_of_mul_le_mul_right (hc.trans (mul_le_mul_of_nonneg_left hc₂M (Nat.cast_nonneg _))) hM

/-- **The reduced parameters.** If `4 * N ^ 2 * K * M ≤ c₁ * c₂` with `c₁, c₂ ≤ M`, `1 ≤ K` and
`0 < M`, then `c₁ / N` and `c₂ / N` are at least `K`, their product is at least `K * M`, and `c₁`
and `c₂` are at least `2`. -/
lemma le_div_of_mul_le_mul {c₁ c₂ N : ℕ} {K M : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hM : 0 < M)
    (hc₁M : c₁ ≤ M) (hc₂M : c₂ ≤ M) (hc : 4 * N ^ 2 * K * M ≤ c₁ * c₂) :
    K ≤ (c₁ / N : ℕ) ∧ K ≤ (c₂ / N : ℕ) ∧ K * M ≤ (c₁ / N : ℕ) * (c₂ / N : ℕ) ∧ 2 ≤ c₁ ∧
      2 ≤ c₂ := by
  have hc₁ := le_of_mul_le_mul_of_le hM hc₂M hc
  have hc₂ := le_of_mul_le_mul_of_le hM hc₁M (hc.trans_eq (mul_comm _ _))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨by nlinarith [two_mul_mul_le_div hN hK hc₁], by nlinarith [two_mul_mul_le_div hN hK hc₂],
    le_of_mul_le_mul_left (a := 4 * (N : ℝ) ^ 2) ?_ (by positivity),
    le_trans (by grind) (two_mul_le_of_four_mul_sq_mul_le hN hK hc₁),
    le_trans (by grind) (two_mul_le_of_four_mul_sq_mul_le hN hK hc₂)⟩
  nlinarith [mul_le_mul (le_two_mul_mul_div hN (two_mul_le_of_four_mul_sq_mul_le hN hK hc₁))
    (le_two_mul_mul_div hN (two_mul_le_of_four_mul_sq_mul_le hN hK hc₂)) (Nat.cast_nonneg _)
    (by positivity)]

/-- **Theorem 6 at the threshold.** There is `c` such that if no subsets of `A` and `B` with at
most `c₁` and `c₂` elements have `#A + #B - 1` sums, then `A` and `B` are within
`γ * min #A #B` of arithmetic progressions with the same nonzero common difference. -/
lemma exists_arithProg_of_forall_card_add_lt_card_add_sub_one (h : CauchyDavenportStability)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (c₁ c₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      2 ≤ #A → 2 ≤ #B → α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      (∀ A' ⊆ A, ∀ B' ⊆ B, #A' ≤ c₁ → #B' ≤ c₂ → #(A' + B') < #A + #B - 1) →
      ∃ a b d : ZMod p, d ≠ 0 ∧ ∃ m n : ℕ,
        (#(A ∆ arithProg a d m) : ℝ) ≤ γ * min (#A : ℝ) #B ∧
        (#(B ∆ arithProg b d n) : ℝ) ≤ γ * min (#A : ℝ) #B := by
  obtain ⟨ε, hε, h₆⟩ := exists_arithProg_card_symmDiff_le_of_expect_card_add_le h hβ hγ
  obtain ⟨c, hc⟩ := h₆ α hα
  refine ⟨c, ?_⟩
  intro p hp A B c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc hA hB hAB hBA hABp hlt
  have hE := expect_card_add_le_of_forall (k := #A + #B - 2) hc₁A hc₂B
    fun A' hA' B' hB' h₁ h₂ ↦
      Nat.le_sub_of_add_le (Nat.lt_sub_iff_add_lt.1 (hlt A' hA' B' hB' h₁ h₂))
  rw [Nat.cast_sub (by grind)] at hE
  push_cast at hE
  exact hc p hp A B c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc hA hB hAB hBA hABp
    (hE.trans (by linarith [(by positivity : 0 ≤ ε * min (#A : ℝ) #B)]))

/-- **Theorem 1 for sets near arithmetic progressions.** The statement of
`exists_card_add_of_near_intervals` for sets near arithmetic progressions with the same common
difference `d ≠ 0`, obtained by multiplying by `d⁻¹`. -/
lemma exists_card_add_of_near_arithProg (h₄ : CauchyDavenportStability)
    (h₅ : FewTranslatesNearIntervals) {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1 / 1024) :
    ∃ γ > (0 : ℝ), ∃ K : ℝ, ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty →
      B.Nonempty → α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      ∀ (a b d : ZMod p) (m n : ℕ), d ≠ 0 →
      (#(A ∆ arithProg a d m) : ℝ) ≤ γ * min (#A : ℝ) #B →
      (#(B ∆ arithProg b d n) : ℝ) ≤ γ * min (#A : ℝ) #B →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → K ≤ c₁ → K ≤ c₂ → K * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ ⌈400 / (α * β)⌉₊ * c₁ ∧ #B' ≤ ⌈400 / (α * β)⌉₊ * c₂ ∧
        #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ, hγ, K, hK⟩ := exists_card_add_of_near_intervals h₄ h₅ hα hα₁ hβ hβ₁
  refine ⟨γ, hγ, K, ?_⟩
  intro p hp A B hA hB hAB hBA hABp a b d m n hd hAP hBQ c₁ c₂ hc₁A hc₂B hKc₁ hKc₂ hKc
  have := Fact.mk hp
  apply exists_card_add_of_image_mul hp (inv_ne_zero hd)
  exact hK p hp _ _ (hA.image _) (hB.image _)
    (by rwa [card_image_inv_mul hp hd, card_image_inv_mul hp hd])
    (by rwa [card_image_inv_mul hp hd, card_image_inv_mul hp hd])
    (by rwa [card_image_inv_mul hp hd, card_image_inv_mul hp hd]) (d⁻¹ * a) (d⁻¹ * b) m n
    (by rwa [card_image_mul_symmDiff_arithProg hp hd, card_image_inv_mul hp hd,
      card_image_inv_mul hp hd])
    (by rwa [card_image_mul_symmDiff_arithProg hp hd, card_image_inv_mul hp hd,
      card_image_inv_mul hp hd])
    c₁ c₂ (by rwa [card_image_inv_mul hp hd]) (by rwa [card_image_inv_mul hp hd]) hKc₁ hKc₂
    (by rwa [card_image_inv_mul hp hd, card_image_inv_mul hp hd])

/-- Theorem 1 for `α ≤ 1` and `β ≤ 2⁻¹⁰`, with subsets of at most `c₁` and `c₂` elements. -/
lemma exists_card_add_of_le_one (h₄ : CauchyDavenportStability)
    (h₅ : FewTranslatesNearIntervals) {α β : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β)
    (hβ₁ : β ≤ 1 / 1024) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, c₁ ≤ #A → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ ∧ #B' ≤ c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨γ, hγ, K₁, hK₁⟩ := exists_card_add_of_near_arithProg h₄ h₅ hα hα₁ hβ hβ₁
  obtain ⟨c₆, hc₆⟩ := exists_arithProg_of_forall_card_add_lt_card_add_sub_one h₄ hα hβ hγ
  refine ⟨4 * ⌈400 / (α * β)⌉₊ ^ 2 * max (max K₁ c₆) 1, by positivity, ?_⟩
  intro p hp A B hA hB hAB hBA hABp c₁ c₂ hc₁A hc₂B hc
  have hmax : 0 < max (#A : ℝ) #B := lt_max_of_lt_left (by exact_mod_cast hA.card_pos)
  obtain ⟨hKq₁, hKq₂, hKq, h2₁, h2₂⟩ := le_div_of_mul_le_mul (Nat.ceil_pos.2 (by positivity))
    (le_max_right _ _) hmax ((Nat.cast_le.2 hc₁A).trans (le_max_left _ _))
    ((Nat.cast_le.2 hc₂B).trans (le_max_right _ _)) hc
  obtain ⟨hK₁q₁, -, hq₁⟩ := le_of_max_max_le hKq₁
  obtain ⟨hK₁q₂, -, hq₂⟩ := le_of_max_max_le hKq₂
  obtain ⟨hK₁q, hc₆q, -⟩ := mul_le_of_max_max_mul_le hmax.le hKq
  by_cases hsmall : ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ c₁ / ⌈400 / (α * β)⌉₊ ∧
      #B' ≤ c₂ / ⌈400 / (α * β)⌉₊ ∧ #A + #B - 1 ≤ #(A' + B')
  · obtain ⟨A', hA', B', hB', h₁, h₂, h₃⟩ := hsmall
    exact ⟨A', hA', B', hB', h₁.trans (Nat.div_le_self _ _), h₂.trans (Nat.div_le_self _ _), h₃⟩
  push Not at hsmall
  obtain ⟨a, b, d, hd, m, n, hAP, hBQ⟩ := hc₆ p hp A B _ _ (by exact_mod_cast hq₁)
    ((Nat.div_le_self _ _).trans hc₁A) (by exact_mod_cast hq₂)
    ((Nat.div_le_self _ _).trans hc₂B) hc₆q (h2₁.trans hc₁A) (h2₂.trans hc₂B) hAB hBA hABp hsmall
  obtain ⟨A', hA', B', hB', h₁, h₂, h₃⟩ := hK₁ p hp A B hA hB hAB hBA hABp a b d m n hd hAP hBQ
    _ _ ((Nat.div_le_self _ _).trans hc₁A) ((Nat.div_le_self _ _).trans hc₂B) hK₁q₁ hK₁q₂ hK₁q
  exact ⟨A', hA', B', hB', h₁.trans (Nat.mul_div_le _ _), h₂.trans (Nat.mul_div_le _ _), h₃⟩

end Theorem1

/-- **Theorem 1** of Bollobás, Leader and Tiba, assuming their Theorems 4 and 5. For `α, β > 0`
there is `c > 0` such that if `A, B ⊆ ZMod p` are nonempty with `α * #B ≤ #A ≤ α⁻¹ * #B` and
`#A + #B ≤ (1 - β) * p`, then for all `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B` with
`c₁ * c₂ ≥ c * max #A #B` there are `A' ⊆ A` and `B' ⊆ B` with `c₁` and `c₂` elements and
`#(A' + B') ≥ #A + #B - 1`. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add
    (h₄ : CauchyDavenportStability) (h₅ : FewTranslatesNearIntervals) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ #A + #B - 1 ≤ #(A' + B') := by
  obtain ⟨c, hc, h⟩ := exists_card_add_of_le_one h₄ h₅ (lt_min hα one_pos) (min_le_right α 1)
    (lt_min hβ (by norm_num)) (min_le_right β (1 / 1024))
  refine ⟨c, hc, ?_⟩
  intro p hp A B hA hB hAB hBA hABp c₁ c₂ hc₁ hc₁A hc₂ hc₂B hcc
  refine exists_subset_card_eq_of_card_le hc₁A hc₂B (h p hp A B hA hB ?_ ?_ ?_ c₁ c₂ hc₁A hc₂B hcc)
  · exact (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hAB
  · exact hBA.trans (mul_le_mul_of_nonneg_right (inv_anti₀ (lt_min hα one_pos)
      (min_le_left α 1)) (Nat.cast_nonneg _))
  · exact hABp.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left β (1 / 1024)])
      (Nat.cast_nonneg _))

end LargeSumsetsFromSubsets
