/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.PowersetCard
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Tactic.Linarith.Frontend

/-!
# Random subsets and random samples

Bollobás, Leader and Tiba sample `c` points of a set either independently or as a uniformly random
`c`-subset. This file compares the two for a monotone function `g` of the sampled set:

* `expect_powersetCard_mono`: the expectation of `g` over the `k`-subsets of `A` is nondecreasing
  in `k`;
* `expect_image_le_expect_powersetCard`: the set of values of `m` independent uniform samples is
  dominated by a uniform `m`-subset;
* `mul_expect_powersetCard_le_expect_powersetCard_inter`: a uniform `c`-subset of `A` meets a
  subset `A'` containing all but a `μ` proportion of `A` in a set dominating a uniform
  `m`-subset of `A'`, for `2 * m ≤ c`, up to the factor `1 - 2 * μ`;
* `mul_expect_card_add_le_expect_powersetCard`: the resulting comparison for sumsets of two
  samples.

The proofs rest on a symmetrization argument. The permutations of `A`, extended by the identity
outside `A`, act on the subsets of `A`. For a family of random sets whose distribution is
invariant under these permutations, the expectation of `g` is the expectation, over the size `j`
of the random set, of the expectation of `g` over the `j`-subsets of `A`
(`expect_eq_expect_expect_powersetCard`).
-/

@[expose] public section

open Finset Equiv Equiv.Perm
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

variable {α : Type*} [DecidableEq α] {A : Finset α} {g : Finset α → ℝ}

/-! ### Permutations of a finite set -/

/-- A permutation of `A'`, extended by the identity outside `A'`, maps subsets of a superset `A`
of `A'` to subsets of `A`. -/
lemma image_ofSubtype_subset {A' U : Finset α} (σ : Perm A') (hA' : A' ⊆ A) (hU : U ⊆ A) :
    U.image (ofSubtype σ) ⊆ A := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
  by_cases h : y ∈ A'
  · exact hA' ((ofSubtype_apply_mem_iff_mem σ y).2 h)
  · rw [ofSubtype_apply_of_not_mem σ h]
    exact hU hy

/-- A permutation of `A'`, extended by the identity outside `A'`, maps `k`-subsets of a superset
`A` of `A'` to `k`-subsets of `A`. -/
lemma image_ofSubtype_mem_powersetCard {A' U : Finset α} {k : ℕ} (σ : Perm A') (hA' : A' ⊆ A)
    (hU : U ∈ powersetCard k A) : U.image (ofSubtype σ) ∈ powersetCard k A := by
  obtain ⟨hUA, rfl⟩ := mem_powersetCard.1 hU
  exact mem_powersetCard.2 ⟨image_ofSubtype_subset σ hA' hUA,
    card_image_of_injective _ (ofSubtype σ).injective⟩

/-- A permutation of `A`, extended by the identity outside `A`, maps `A` onto itself. -/
lemma image_ofSubtype_self (σ : Perm A) : A.image (ofSubtype σ) = A :=
  eq_of_subset_of_card_le (image_ofSubtype_subset σ subset_rfl subset_rfl)
    (card_image_of_injective _ (ofSubtype σ).injective).ge

/-- Extending permutations of `A` by the identity outside `A` is compatible with composition. -/
lemma image_image_ofSubtype (σ τ : Perm A) (U : Finset α) :
    (U.image (ofSubtype τ)).image (ofSubtype σ) = U.image (ofSubtype (σ * τ)) := by
  rw [image_image, map_mul, coe_mul]

/-- The inverse of a permutation of `A` undoes its action on the subsets of `α`. -/
lemma image_ofSubtype_inv_image_ofSubtype (σ : Perm A) (U : Finset α) :
    (U.image (ofSubtype σ)).image (ofSubtype σ⁻¹) = U := by
  rw [image_image_ofSubtype, inv_mul_cancel, map_one, coe_one, image_id]

/-- Two subsets of `A` of the same size are mapped to each other by a permutation of `A`. -/
lemma exists_image_ofSubtype_eq {U V : Finset α} (hU : U ⊆ A) (hV : V ⊆ A) (h : #U = #V) :
    ∃ τ : Perm A, U.image (ofSubtype τ) = V := by
  have := Set.powersetCard.isPretransitive (α := A) (n := #U)
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Perm A)
    (Set.powersetCard.ofCard (n := #U) (s := U.subtype (· ∈ A))
      (by simp [card_subtype, filter_true_of_mem hU]))
    (Set.powersetCard.ofCard (s := V.subtype (· ∈ A))
      (by simp [card_subtype, filter_true_of_mem hV, h]))
  refine ⟨τ, ?_⟩
  have := congrArg (fun s ↦ (Subtype.val s : Finset A).map (Function.Embedding.subtype _)) hτ
  simp only [Set.powersetCard.coe_smul, Set.powersetCard.val_ofCard, subtype_map_of_mem hV]
    at this
  rw [← this]
  conv_lhs => rw [← subtype_map_of_mem hU]
  simp [smul_finset_def, map_eq_image, image_image, Function.comp_def, Perm.smul_def]

/-! ### Symmetrization -/

/-- The average of `g` over the images of `U` under the permutations of `A`, extended by the
identity outside `A`. -/
noncomputable def permExpect (A : Finset α) (g : Finset α → ℝ) (U : Finset α) : ℝ :=
  𝔼 σ : Perm A, g (U.image (ofSubtype σ))

/-- `permExpect A g` is invariant under the permutations of `A`. -/
lemma permExpect_image_ofSubtype (τ : Perm A) (U : Finset α) :
    permExpect A g (U.image (ofSubtype τ)) = permExpect A g U := by
  unfold permExpect
  exact Fintype.expect_equiv (Equiv.mulRight τ) _ _ fun σ ↦ by rw [image_image_ofSubtype]; rfl

/-- `permExpect A g` takes the same value on subsets of `A` of the same size. -/
lemma permExpect_eq_of_card_eq {U V : Finset α} (hU : U ⊆ A) (hV : V ⊆ A) (h : #U = #V) :
    permExpect A g U = permExpect A g V := by
  obtain ⟨τ, rfl⟩ := exists_image_ofSubtype_eq hU hV h
  rw [permExpect_image_ofSubtype]

/-- If the permutations of `A` act on a finite family `X` compatibly with a map `φ`, then the
expectation of `g ∘ φ` over `X` equals that of `permExpect A g ∘ φ`. -/
lemma expect_eq_expect_permExpect {ι : Type*} {X : Finset ι} (φ : ι → Finset α)
    (act : Perm A → ι → ι) (hX : ∀ σ, ∀ x ∈ X, act σ x ∈ X)
    (hinv : ∀ σ x, act σ⁻¹ (act σ x) = x)
    (hφ : ∀ σ, ∀ x ∈ X, φ (act σ x) = (φ x).image (ofSubtype σ)) :
    𝔼 x ∈ X, g (φ x) = 𝔼 x ∈ X, permExpect A g (φ x) := by
  unfold permExpect
  rw [expect_comm]
  have (σ : Perm A) : 𝔼 x ∈ X, g ((φ x).image (ofSubtype σ)) = 𝔼 x ∈ X, g (φ x) := by
    refine expect_nbij' (act σ) (act σ⁻¹) (hX σ) (hX σ⁻¹) (fun x _ ↦ hinv σ x)
      (fun x _ ↦ by simpa using hinv σ⁻¹ x) ?_
    intro x hx
    rw [hφ σ x hx]
  simp [this]

/-- The expectation of `g` over the `#U`-subsets of `A` equals `permExpect A g U`. -/
lemma expect_powersetCard_eq_permExpect {U : Finset α} (hU : U ⊆ A) :
    𝔼 T ∈ powersetCard #U A, g T = permExpect A g U := by
  refine (expect_eq_expect_permExpect (φ := fun T ↦ T) (fun σ T ↦ T.image (ofSubtype σ))
    (fun σ _ ↦ image_ofSubtype_mem_powersetCard σ subset_rfl)
    image_ofSubtype_inv_image_ofSubtype (fun _ _ _ ↦ rfl)).trans ?_
  rw [expect_congr rfl (g := fun _ ↦ permExpect A g U) ?_,
    expect_const ⟨U, mem_powersetCard.2 ⟨hU, rfl⟩⟩]
  intro T hT
  obtain ⟨hTA, hTU⟩ := mem_powersetCard.1 hT
  exact permExpect_eq_of_card_eq hTA hU hTU

/-- Symmetrization: if the permutations of `A` act on a finite family `X` compatibly with a map
`φ` into the subsets of `A`, then the expectation of `g ∘ φ` over `X` equals the expectation over
`x ∈ X` of the expectation of `g` over the subsets of `A` of the size of `φ x`. -/
lemma expect_eq_expect_expect_powersetCard {ι : Type*} {X : Finset ι} (φ : ι → Finset α)
    (hφA : ∀ x ∈ X, φ x ⊆ A) (act : Perm A → ι → ι) (hX : ∀ σ, ∀ x ∈ X, act σ x ∈ X)
    (hinv : ∀ σ x, act σ⁻¹ (act σ x) = x)
    (hφ : ∀ σ, ∀ x ∈ X, φ (act σ x) = (φ x).image (ofSubtype σ)) :
    𝔼 x ∈ X, g (φ x) = 𝔼 x ∈ X, 𝔼 T ∈ powersetCard #(φ x) A, g T := by
  rw [expect_eq_expect_permExpect φ act hX hinv hφ]
  exact expect_congr rfl fun x hx ↦ (expect_powersetCard_eq_permExpect (hφA x hx)).symm

/-! ### Uniform subsets and independent samples -/

omit [DecidableEq α] in
/-- The expectation of a monotone function over the `k`-subsets of `A` is nondecreasing in `k`,
as long as `k ≤ #A`. -/
lemma expect_powersetCard_mono (hg : Monotone g) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ #A) :
    𝔼 S ∈ powersetCard k A, g S ≤ 𝔼 T ∈ powersetCard l A, g T := by
  classical
  obtain ⟨V, hVA, rfl⟩ := exists_subset_card_eq hl
  obtain ⟨U, hUV, rfl⟩ := exists_subset_card_eq hkl
  rw [expect_powersetCard_eq_permExpect (hUV.trans hVA), expect_powersetCard_eq_permExpect hVA]
  exact expect_le_expect fun σ _ ↦ hg (image_subset_image hUV)

/-- The set of values of `m` independent uniform samples from `A` is dominated by a uniform
`m`-subset of `A`. -/
lemma expect_image_le_expect_powersetCard (hg : Monotone g) {m : ℕ} (hm : m ≤ #A) :
    𝔼 f : Fin m → A, g (univ.image fun i ↦ (f i : α)) ≤ 𝔼 S ∈ powersetCard m A, g S := by
  rw [expect_eq_expect_expect_powersetCard (fun f : Fin m → A ↦ univ.image fun i ↦ (f i : α))
    (fun f _ ↦ by simp [subset_iff]) (fun σ f i ↦ σ (f i)) (fun _ _ _ ↦ mem_univ _)
    (fun σ f ↦ by simp) (fun σ f _ ↦ by simp [image_image, Function.comp_def])]
  have : Nonempty (Fin m → A) := by
    rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · obtain rfl : m = 0 := by simpa using hm
      exact ⟨fun i ↦ i.elim0⟩
    · exact ⟨fun _ ↦ ⟨a, ha⟩⟩
  refine (expect_le_expect fun f _ ↦ expect_powersetCard_mono hg
    (card_image_le.trans (by simp)) hm).trans ?_
  simp

/-! ### Restriction to a large subset -/

/-- The expected number of points of `D ⊆ A` in a uniform `c`-subset of `A` is
`c * #D / #A`. -/
lemma expect_card_inter_powersetCard {D : Finset α} (hD : D ⊆ A) {c : ℕ} (hc : c ≤ #A) :
    𝔼 S ∈ powersetCard c A, (#(S ∩ D) : ℝ) = c * #D / #A := by
  rcases Nat.eq_zero_or_pos c with rfl | hc₀
  · simp
  have hcount (x) (hx : x ∈ D) : #{S ∈ powersetCard c A | x ∈ S} = (#A - 1).choose (c - 1) := by
    simpa using card_filter_powersetCard_subset {x} A c (singleton_subset_iff.2 (hD hx)) hc₀
  rw [expect_eq_sum_div_card, card_powersetCard]
  simp_rw [inter_comm _ D]
  rw [← Nat.cast_sum, sum_card_inter hcount,
    div_eq_div_iff (by simpa using (Nat.choose_pos hc).ne') (by simpa using (hc₀.trans_le hc).ne')]
  exact_mod_cast (by grind [Nat.add_one_mul_choose_eq (#A - 1) (c - 1)] :
    #D * (#A - 1).choose (c - 1) * #A = c * #D * (#A).choose c)

/-- If a `c`-subset `S` of `A` meets `A'` in fewer than `m` points, where `2 * m ≤ c`, then at
least `c / 2` points of `S` lie in `A \ A'`. -/
lemma mul_one_sub_ite_le_two_mul_card_inter_sdiff {A' S : Finset α} {c m : ℕ}
    (hmc : 2 * m ≤ c) (hS : S ∈ powersetCard c A) :
    (c : ℝ) * (1 - if m ≤ #(S ∩ A') then 1 else 0) ≤ 2 * #(S ∩ (A \ A')) := by
  obtain ⟨hSA, rfl⟩ := mem_powersetCard.1 hS
  rw [← inter_sdiff_assoc, inter_eq_left.2 hSA, mul_sub, mul_one, mul_ite, mul_one, mul_zero]
  have : m ≤ #(S ∩ A') ∨ (#S : ℝ) ≤ 2 * #(S \ A') := by
    exact_mod_cast (by grind [card_inter_add_card_sdiff S A'] :
      m ≤ #(S ∩ A') ∨ #S ≤ 2 * #(S \ A'))
  grind

/-- Markov's inequality: if `A'` contains all but a `μ` proportion of `A`, with `0 ≤ μ`, and
`2 * m ≤ c ≤ #A`, then a uniform `c`-subset of `A` meets `A'` in at least `m` points with
probability at least `1 - 2 * μ`. -/
lemma one_sub_two_mul_le_expect_ite {A' : Finset α} {μ : ℝ} (hμ₀ : 0 ≤ μ)
    (hμ : (#(A \ A') : ℝ) ≤ μ * #A) {c m : ℕ} (hmc : 2 * m ≤ c) (hc : c ≤ #A) :
    1 - 2 * μ ≤ 𝔼 S ∈ powersetCard c A, if m ≤ #(S ∩ A') then (1 : ℝ) else 0 := by
  have hne : (powersetCard c A).Nonempty := powersetCard_nonempty.2 hc
  rcases Nat.eq_zero_or_pos c with rfl | hc₀
  · obtain rfl : m = 0 := by grind
    simp only [zero_le, ite_true, expect_const hne]
    linarith
  have := expect_le_expect fun S hS ↦
    mul_one_sub_ite_le_two_mul_card_inter_sdiff (A := A) (A' := A') hmc hS
  rw [← mul_expect, expect_sub_distrib, expect_const hne, ← mul_expect,
    expect_card_inter_powersetCard sdiff_subset hc] at this
  have : (c : ℝ) * #(A \ A') / #A ≤ c * μ := by
    rw [div_le_iff₀ (by exact_mod_cast hc₀.trans_le hc)]
    nlinarith
  nlinarith [(by exact_mod_cast hc₀ : (0 : ℝ) < c)]

/-- If `A'` contains all but a `μ` proportion of `A`, with `0 ≤ μ`, and `2 * m ≤ c ≤ #A`, then a
uniform `c`-subset of `A` meets `A'` in a set dominating a uniform `m`-subset of `A'`, up to the
factor `1 - 2 * μ`. -/
lemma mul_expect_powersetCard_le_expect_powersetCard_inter (hg : Monotone g)
    (hg₀ : ∀ S, 0 ≤ g S) {A' : Finset α} (hA' : A' ⊆ A) {μ : ℝ} (hμ₀ : 0 ≤ μ)
    (hμ : (#(A \ A') : ℝ) ≤ μ * #A) {c m : ℕ} (hmc : 2 * m ≤ c) (hc : c ≤ #A) :
    (1 - 2 * μ) * 𝔼 T ∈ powersetCard m A', g T ≤ 𝔼 S ∈ powersetCard c A, g (S ∩ A') := by
  rw [expect_eq_expect_expect_powersetCard (A := A') (fun S ↦ S ∩ A')
    (fun _ _ ↦ inter_subset_right) (fun σ S ↦ S.image (ofSubtype σ))
    (fun σ _ ↦ image_ofSubtype_mem_powersetCard σ hA') image_ofSubtype_inv_image_ofSubtype
    (fun σ S _ ↦ by rw [image_inter _ _ (ofSubtype σ).injective, image_ofSubtype_self])]
  refine (mul_le_mul_of_nonneg_right (one_sub_two_mul_le_expect_ite hμ₀ hμ hmc hc)
    (expect_nonneg fun T _ ↦ hg₀ T)).trans ?_
  rw [expect_mul]
  refine expect_le_expect ?_
  intro S _
  rw [ite_mul, one_mul, zero_mul]
  grind [expect_powersetCard_mono hg (k := m) (l := #(S ∩ A')) (A := A'),
    card_le_card (inter_subset_right (s₁ := S) (s₂ := A')),
    expect_nonneg (s := powersetCard #(S ∩ A') A') fun T _ ↦ hg₀ T]

/-- If `A'` contains all but a `μ` proportion of `A`, with `0 ≤ μ ≤ 1 / 2`, `2 * m ≤ c ≤ #A` and
`m ≤ #A'`, then a uniform `c`-subset of `A` dominates the set of values of `m` independent
uniform samples from `A'`, up to the factor `1 - 2 * μ`. -/
lemma mul_expect_image_le_expect_powersetCard (hg : Monotone g) (hg₀ : ∀ S, 0 ≤ g S)
    {A' : Finset α} (hA' : A' ⊆ A) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ : μ ≤ 1 / 2)
    (hAA' : (#(A \ A') : ℝ) ≤ μ * #A) {c m : ℕ} (hmc : 2 * m ≤ c) (hc : c ≤ #A)
    (hm : m ≤ #A') :
    (1 - 2 * μ) * 𝔼 f : Fin m → A', g (univ.image fun i ↦ (f i : α)) ≤
      𝔼 S ∈ powersetCard c A, g S := by
  refine (mul_le_mul_of_nonneg_left (expect_image_le_expect_powersetCard hg hm)
    (by linarith)).trans <|
    (mul_expect_powersetCard_le_expect_powersetCard_inter hg hg₀ hA' hμ₀ hAA' hmc
      hc).trans ?_
  exact expect_le_expect fun S _ ↦ hg inter_subset_left

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The expected size of the sumset of uniform `c₁`- and `c₂`-subsets of `A` and `B` is at least
`(1 - 2 * μ) ^ 2` times that of the sets of values of `m₁` and `m₂` independent samples from
subsets `A'` and `B'` containing all but a `μ` proportion of `A` and `B`, for `2 * m₁ ≤ c₁` and
`2 * m₂ ≤ c₂`. -/
lemma mul_expect_card_add_le_expect_powersetCard {A A' B B' : Finset G} (hA' : A' ⊆ A)
    (hB' : B' ⊆ B) {μ : ℝ} (hμ : μ ≤ 1 / 2) (hAA' : (#(A \ A') : ℝ) ≤ μ * #A)
    (hBB' : (#(B \ B') : ℝ) ≤ μ * #B) {c₁ c₂ m₁ m₂ : ℕ} (hmc₁ : 2 * m₁ ≤ c₁) (hc₁ : c₁ ≤ #A)
    (hmc₂ : 2 * m₂ ≤ c₂) (hc₂ : c₂ ≤ #B) (hm₁ : m₁ ≤ #A') (hm₂ : m₂ ≤ #B') :
    (1 - 2 * μ) ^ 2 * 𝔼 fg : (Fin m₁ → A') × (Fin m₂ → B'),
        (#(univ.image (fun i ↦ (fg.1 i : G)) + univ.image (fun i ↦ (fg.2 i : G))) : ℝ) ≤
      𝔼 S ∈ powersetCard c₁ A, 𝔼 T ∈ powersetCard c₂ B, (#(S + T) : ℝ) := by
  obtain hμ₀ | hμ₀ := lt_or_ge μ 0
  · obtain rfl : A = ∅ := by
      rw [← card_eq_zero, ← Nat.cast_eq_zero (R := ℝ)]
      nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ #(A \ A')), (Nat.cast_nonneg _ : (0 : ℝ) ≤ #A)]
    obtain rfl : A' = ∅ := subset_empty.1 hA'
    obtain rfl : m₁ = 0 := by simpa using hm₁
    obtain rfl : c₁ = 0 := by simpa using hc₁
    simp
  rw [← univ_product_univ, expect_product, pow_two, mul_assoc, mul_expect]
  refine (mul_le_mul_of_nonneg_left (expect_le_expect (g := fun f ↦ 𝔼 T ∈ powersetCard c₂ B,
    (#((univ.image fun i ↦ (f i : G)) + T) : ℝ)) ?_) (by linarith)).trans ?_
  · intro f _
    exact mul_expect_image_le_expect_powersetCard
      (g := fun T ↦ (#((univ.image fun i ↦ (f i : G)) + T) : ℝ))
      (fun _ _ h ↦ Nat.cast_le.2 (card_le_card (add_subset_add_left h))) (fun _ ↦ by positivity)
      hB' hμ₀ hμ hBB' hmc₂ hc₂ hm₂
  rw [expect_comm, mul_expect, expect_comm (powersetCard c₁ A) (powersetCard c₂ B)]
  exact expect_le_expect fun T _ ↦ mul_expect_image_le_expect_powersetCard
    (g := fun S ↦ (#(S + T) : ℝ))
    (fun _ _ h ↦ Nat.cast_le.2 (card_le_card (add_subset_add_right h))) (fun _ ↦ by positivity)
    hA' hμ₀ hμ hAA' hmc₁ hc₁ hm₁

end LargeSumsetsFromSubsets
