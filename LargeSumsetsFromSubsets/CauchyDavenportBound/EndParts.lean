/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.CauchyDavenportBound.IntervalEnds
public import Mathlib.Algebra.BigOperators.Expect
import LargeSumsetsFromSubsets.CauchyDavenportBound.ConsecutiveIntervals
import LargeSumsetsFromSubsets.CauchyDavenportStability
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Rify

/-!
# The end parts

The end parts of the proof of Theorem 1 of Bollobás, Leader and Tiba. Lemma 9 provides end
intervals `I₁, I₃` and `J₁, J₃` such that `#(A ∩ I₁) = #(B ∩ J₁)` and one of `A ∩ I₁` and `B ∩ J₁`
is far from arithmetic progressions or both are empty, and likewise for `I₃` and `J₃`. Then small
subsets of `A ∩ I₁` and `B ∩ J₁` already have `#(A ∩ I₁) + #(B ∩ J₁)` sums: otherwise Theorem 4,
or Theorem 6 for their subsets of the sizes allowed, places both sets close to arithmetic
progressions.

## Main statements

* `exists_card_add_le_card_add_of_isFar`: small subsets of end parts `S` and `T` of equal size, one
  of them far from arithmetic progressions, have `#S + #T` sums.
* `exists_card_eq_disjoint_of_interval_ends`: small subsets of `A` and `B` have
  `#A₁ + #B₁ + #A₃ + #B₃` sums outside `I₂ + J₂`.
-/

@[expose] public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- If no subsets of `A` and `B` with at most `c₁` and `c₂` elements have `k` sums, then uniformly
random subsets of `A` and `B` with `min c₁ #A` and `min c₂ #B` elements have at most `k - 1` sums
in expectation. -/
lemma expect_card_add_le_of_forall_card_add_lt {A B : Finset G} {c₁ c₂ k : ℕ}
    (h : ∀ A' ⊆ A, ∀ B' ⊆ B, #A' ≤ c₁ → #B' ≤ c₂ → #(A' + B') < k) :
    𝔼 A' ∈ powersetCard (min c₁ #A) A, 𝔼 B' ∈ powersetCard (min c₂ #B) B, (#(A' + B') : ℝ) ≤
      k - 1 := by
  refine expect_le (powersetCard_nonempty.2 (min_le_right _ _)) ?_
  intro A' hA'
  refine expect_le (powersetCard_nonempty.2 (min_le_right _ _)) ?_
  intro B' hB'
  obtain ⟨hA'A, hA'c⟩ := mem_powersetCard.1 hA'
  obtain ⟨hB'B, hB'c⟩ := mem_powersetCard.1 hB'
  rw [le_sub_iff_add_le]
  exact_mod_cast h A' hA'A B' hB'B (by grind) (by grind)

end AddCommGroup

section AddCommMonoid

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- A nonempty set within `#S / 128` of an arithmetic progression is not far from arithmetic
progressions. -/
lemma not_isFarFromArithProg_of_mul_card_symmDiff_le {S : Finset G} (hS : S.Nonempty) {a d : G}
    {n : ℕ} (h : 128 * #(S ∆ arithProg a d n) ≤ #S) : ¬ IsFarFromArithProg 64 S := by
  intro hfar
  grind [hfar a d n, hS.card_pos]

/-- A singleton is an arithmetic progression, so it is not far from arithmetic progressions. -/
lemma not_isFarFromArithProg_singleton (z : G) : ¬ IsFarFromArithProg 64 ({z} : Finset G) :=
  not_isFarFromArithProg_of_mul_card_symmDiff_le (singleton_nonempty z) (a := z) (d := 0) (n := 1)
    (by simp [arithProg_one_right])

/-- Let `A₁ + B₁ ⊆ U₁` and `A₃ + B₃ ⊆ U₃` with `U₁`, `U₂` and `U₃` pairwise disjoint. If
`k₁ ≤ #(A₁ + B₁)` and `k₃ ≤ #(A₃ + B₃)`, then `A₁ ∪ A₃` and `B₁ ∪ B₃` have `k₁ + k₃` sums outside
`U₂`. -/
lemma exists_subset_add_union_card_eq_disjoint {A₁ A₃ B₁ B₃ U₁ U₂ U₃ : Finset G} {k₁ k₃ : ℕ}
    (h₁ : A₁ + B₁ ⊆ U₁) (h₃ : A₃ + B₃ ⊆ U₃) (hk₁ : k₁ ≤ #(A₁ + B₁)) (hk₃ : k₃ ≤ #(A₃ + B₃))
    (h₁₂ : Disjoint U₁ U₂) (h₃₂ : Disjoint U₃ U₂) (h₁₃ : Disjoint U₁ U₃) :
    ∃ Z ⊆ (A₁ ∪ A₃) + (B₁ ∪ B₃), #Z = k₁ + k₃ ∧ Disjoint Z U₂ := by
  obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq
    ((add_le_add hk₁ hk₃).trans_eq (card_union_of_disjoint (h₁₃.mono h₁ h₃)).symm)
  refine ⟨Z, hZ.trans ?_, hZc,
    (disjoint_union_left.2 ⟨h₁₂.mono_left h₁, h₃₂.mono_left h₃⟩).mono_left hZ⟩
  exact union_subset (add_subset_add subset_union_left subset_union_left)
    (add_subset_add subset_union_right subset_union_right)

end AddCommMonoid

/-- The condition of Theorem 6 for the subsets with `min c₁ k` and `min c₂ k` elements of two sets
of size `k ≤ M`, when `C ≤ c₁`, `C ≤ c₂`, `C * M ≤ c₁ * c₂` and one of `c₁` and `c₂` is less than
`k`. -/
lemma mul_le_min_mul_min {c C M : ℝ} {c₁ c₂ k : ℕ} (hc : c ≤ C) (hC : 0 ≤ C) (hkM : k ≤ M)
    (h₁ : C ≤ c₁) (h₂ : C ≤ c₂) (hM : C * M ≤ c₁ * c₂) (hlt : c₁ < k ∨ c₂ < k) :
    c * k ≤ (min c₁ k : ℕ) * (min c₂ k : ℕ) := by
  grw [hc]
  push_cast
  rw [min_def, min_def]
  split_ifs <;> rcases hlt with hlt | hlt <;> rify at hlt <;> nlinarith

variable {p : ℕ}

/-- If `#S = #T ≥ 2` and `#(S + T) < #S + #T`, then Theorem 4 places `S` and `T` within `#S / 128`
of arithmetic progressions with the same common difference. -/
lemma exists_arithProg_of_card_add_lt {β : ℝ} (hβ : 0 < β) (hp : p.Prime) {S T : Finset (ZMod p)}
    (hST : #S = #T) (hS : 2 ≤ #S) (hβp : #S + #T ≤ (1 - β) * p) (hlt : #(S + T) < #S + #T) :
    ∃ a b d : ZMod p, ∃ m n : ℕ, 128 * #(S ∆ arithProg a d m) ≤ #S ∧
      128 * #(T ∆ arithProg b d n) ≤ #T := by
  obtain ⟨ε, hε, h₄⟩ :=
    exists_subset_arithProg_card_sdiff_le_of_card_add_le hβ (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨a, b, d, m, n, hSP, hTQ, hPS, hQT⟩ := h₄ p hp S T hS (hST ▸ hS) hβp
    (le_add_of_le_of_nonneg (le_sub_iff_add_le.2 (mod_cast hlt)) (by positivity))
  refine ⟨a, b, d, m, n, ?_, ?_⟩
  · rw [symmDiff_of_le hSP]
    rify
    linarith [min_le_left (#S : ℝ) #T]
  · rw [symmDiff_of_le hTQ]
    rify
    linarith [min_le_right (#S : ℝ) #T]

/-- If `#S = #T ≥ 2`, one of `c₁` and `c₂` is less than `#S`, and no subsets of `S` and `T` with at
most `c₁` and `c₂` elements have `#S + #T` sums, then Theorem 6 for the subsets with `min c₁ #S` and
`min c₂ #T` elements places `S` and `T` within `#S / 128` of arithmetic progressions. -/
lemma exists_arithProg_of_forall_card_add_lt_of_lt {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (S T : Finset (ZMod p)) (c₁ c₂ : ℕ) (M : ℝ), #S = #T → 2 ≤ #S →
      #S ≤ M → #S + #T ≤ (1 - β) * p → c ≤ c₁ → c ≤ c₂ → c * M ≤ c₁ * c₂ →
      (c₁ < #S ∨ c₂ < #S) → (∀ S' ⊆ S, ∀ T' ⊆ T, #S' ≤ c₁ → #T' ≤ c₂ → #(S' + T') < #S + #T) →
      ∃ a b d : ZMod p, ∃ m n : ℕ, 128 * #(S ∆ arithProg a d m) ≤ #S ∧
        128 * #(T ∆ arithProg b d n) ≤ #T := by
  obtain ⟨ε, hε, h₆⟩ := exists_arithProg_card_symmDiff_le_of_expect_card_add_le hβ
    (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨c₆, hc₆⟩ := h₆ 1 one_pos
  refine ⟨max c₆ 1, ?_⟩
  intro p hp S T c₁ c₂ M hST hS hSM hβp hcc₁ hcc₂ hcM hlt₁₂ hlt
  have hE := expect_card_add_le_of_forall_card_add_lt hlt
  push_cast at hE
  obtain ⟨a, b, d, -, m, n, hSP, hTQ⟩ := hc₆ p hp S T (min c₁ #S) (min c₂ #T)
    (le_min (Nat.one_le_cast.1 ((le_max_right c₆ 1).trans hcc₁)) (by grind)) (min_le_right _ _)
    (le_min (Nat.one_le_cast.1 ((le_max_right c₆ 1).trans hcc₂)) (by grind)) (min_le_right _ _)
    (by simpa [← hST] using mul_le_min_mul_min (le_max_left c₆ 1)
          (zero_le_one.trans (le_max_right c₆ 1)) hSM hcc₁ hcc₂ hcM hlt₁₂)
    hS (hST ▸ hS) (by simp [hST]) (by simp [hST]) hβp
    (le_add_of_le_of_nonneg hE (by positivity))
  rw [← hST, min_self] at hSP
  rw [hST, min_self] at hTQ
  refine ⟨a, b, d, m, n, ?_, ?_⟩
  · rify
    linarith
  · rify
    linarith

/-- If `#S = #T ≥ 2` and no subsets of `S` and `T` with at most `c₁` and `c₂` elements have
`#S + #T` sums, then `S` and `T` are within `#S / 128` of arithmetic progressions. For
`#S ≤ min c₁ c₂` this is Theorem 4 for `S` and `T`, and otherwise Theorem 6 for their subsets with
`min c₁ #S` and `min c₂ #T` elements. -/
lemma exists_arithProg_of_forall_card_add_lt {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (S T : Finset (ZMod p)) (c₁ c₂ : ℕ) (M : ℝ), #S = #T → 2 ≤ #S →
      #S ≤ M → #S + #T ≤ (1 - β) * p → c ≤ c₁ → c ≤ c₂ → c * M ≤ c₁ * c₂ →
      (∀ S' ⊆ S, ∀ T' ⊆ T, #S' ≤ c₁ → #T' ≤ c₂ → #(S' + T') < #S + #T) →
      ∃ a b d : ZMod p, ∃ m n : ℕ, 128 * #(S ∆ arithProg a d m) ≤ #S ∧
        128 * #(T ∆ arithProg b d n) ≤ #T := by
  obtain ⟨c, hc⟩ := exists_arithProg_of_forall_card_add_lt_of_lt hβ
  refine ⟨c, ?_⟩
  intro p hp S T c₁ c₂ M hST hS hSM hβp hcc₁ hcc₂ hcM hlt
  by_cases hsmall : #S ≤ c₁ ∧ #S ≤ c₂
  · obtain ⟨hSc₁, hSc₂⟩ := hsmall
    exact exists_arithProg_of_card_add_lt hβ hp hST hS hβp
      (hlt S subset_rfl T subset_rfl hSc₁ (hST ▸ hSc₂))
  · exact hc p hp S T c₁ c₂ M hST hS hSM hβp hcc₁ hcc₂ hcM (by grind) hlt

/-- An end part. Let `S ⊆ A` and `T ⊆ B` with `#S = #T`, where one of `S` and `T` is far from
arithmetic progressions or both are empty. Then some subsets of `S` and `T` with at most `c₁` and
`c₂` elements have `#S + #T` sums. -/
lemma exists_card_add_le_card_add_of_isFar {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B S T : Finset (ZMod p)) (c₁ c₂ : ℕ), S ⊆ A → T ⊆ B →
      #A + #B ≤ (1 - β) * p → #S = #T →
      (S = ∅ ∧ T = ∅ ∨ IsFarFromArithProg 64 S ∨ IsFarFromArithProg 64 T) →
      c ≤ c₁ → c ≤ c₂ → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ S' ⊆ S, ∃ T' ⊆ T, #S' ≤ c₁ ∧ #T' ≤ c₂ ∧ #S + #T ≤ #(S' + T') := by
  obtain ⟨c, hc⟩ := exists_arithProg_of_forall_card_add_lt hβ
  refine ⟨c, ?_⟩
  intro p hp A B S T c₁ c₂ hSA hTB hβp hST hfar hcc₁ hcc₂ hcM
  by_contra hne
  push Not at hne
  obtain h0 | h1 | h2 : #S = 0 ∨ #S = 1 ∨ 2 ≤ #S := by grind
  · simpa [h0, ← hST] using hne ∅ (empty_subset _) ∅ (empty_subset _) (by simp) (by simp)
  · obtain ⟨z, rfl⟩ := card_eq_one.1 h1
    obtain ⟨w, rfl⟩ := card_eq_one.1 (hST ▸ h1)
    simp [not_isFarFromArithProg_singleton] at hfar
  obtain ⟨a, b, d, m, n, hSP, hTQ⟩ := hc p hp S T c₁ c₂ _ hST h2
    (le_max_of_le_left (by exact_mod_cast card_le_card hSA)) (by grw [hSA, hTB]; exact hβp) hcc₁
    hcc₂ hcM hne
  rcases hfar with ⟨rfl, -⟩ | hfar | hfar
  · simp at h2
  · exact not_isFarFromArithProg_of_mul_card_symmDiff_le (card_pos.1 (by grind)) hSP hfar
  · exact not_isFarFromArithProg_of_mul_card_symmDiff_le (card_pos.1 (by grind)) hTQ hfar

variable {p : ℕ}

/-- The end parts in the setting of Lemma 9. Subsets of `A` and `B` with at most `2 * c₁` and
`2 * c₂` elements have a set `Z` of `#A₁ + #B₁ + #A₃ + #B₃` sums outside `I₂ + J₂`, where
`A₁ = A ∩ I₁`, `B₁ = B ∩ J₁`, `A₃ = A ∩ I₃` and `B₃ = B ∩ J₃`. -/
lemma exists_card_eq_disjoint_of_interval_ends {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (s r : ZMod p)
      (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ : ℕ),
      a₁ + a₂ + a₃ + (b₁ + b₂ + b₃) ≤ p → #A + #B ≤ (1 - β) * p →
      #(A ∩ arithProg s 1 a₁) = #(B ∩ arithProg r 1 b₁) →
      #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) = #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) →
      (A ∩ arithProg s 1 a₁ = ∅ ∧ B ∩ arithProg r 1 b₁ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg s 1 a₁) ∨
        IsFarFromArithProg 64 (B ∩ arithProg r 1 b₁)) →
      (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃ = ∅ ∧
          B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃ = ∅ ∨
        IsFarFromArithProg 64 (A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) ∨
        IsFarFromArithProg 64 (B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃)) →
      c ≤ c₁ → c ≤ c₂ → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      ∃ A' ⊆ A, ∃ B' ⊆ B, #A' ≤ 2 * c₁ ∧ #B' ≤ 2 * c₂ ∧ ∃ Z ⊆ A' + B',
        #Z = #(A ∩ arithProg s 1 a₁) + #(B ∩ arithProg r 1 b₁) +
          #(A ∩ arithProg (s + (a₁ + a₂ : ℕ)) 1 a₃) +
          #(B ∩ arithProg (r + (b₁ + b₂ : ℕ)) 1 b₃) ∧
        Disjoint Z (arithProg (s + a₁) 1 a₂ + arithProg (r + b₁) 1 b₂) := by
  obtain ⟨c, hc⟩ := exists_card_add_le_card_add_of_isFar hβ
  refine ⟨c, ?_⟩
  intro p hp A B s r a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ hsum hβp h₁ h₃ hf₁ hf₃ hcc₁ hcc₂ hcM
  obtain ⟨A₁, hA₁, B₁, hB₁, hA₁c, hB₁c, hAB₁⟩ := hc p hp A B _ _ c₁ c₂ inter_subset_left
    inter_subset_left hβp h₁ hf₁ hcc₁ hcc₂ hcM
  obtain ⟨A₃, hA₃, B₃, hB₃, hA₃c, hB₃c, hAB₃⟩ := hc p hp A B _ _ c₁ c₂ inter_subset_left
    inter_subset_left hβp h₃ hf₃ hcc₁ hcc₂ hcM
  obtain ⟨hW₁₂, hW₃₂, hW₁₃⟩ := disjoint_add_arithProg_of_add_le s r hsum
  obtain ⟨Z, hZ, hZc, hZW⟩ := exists_subset_add_union_card_eq_disjoint
    (add_subset_add (hA₁.trans inter_subset_right) (hB₁.trans inter_subset_right))
    (add_subset_add (hA₃.trans inter_subset_right) (hB₃.trans inter_subset_right))
    hAB₁ hAB₃ hW₁₂ hW₃₂ hW₁₃
  refine ⟨A₁ ∪ A₃, union_subset (hA₁.trans inter_subset_left) (hA₃.trans inter_subset_left),
    B₁ ∪ B₃, union_subset (hB₁.trans inter_subset_left) (hB₃.trans inter_subset_left),
    by grind [card_union_le], by grind [card_union_le], Z, hZ, by grind, hZW⟩

end LargeSumsetsFromSubsets
