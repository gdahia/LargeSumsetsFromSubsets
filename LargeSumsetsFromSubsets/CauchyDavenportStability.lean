/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import LargeSumsetsFromSmallSubsets.NearCauchyDavenport
import LargeSumsetsFromSubsets.AddCommGroup
import LargeSumsetsFromSubsets.SubsetSampling
import Mathlib.Tactic.NormNum.GCD

/-!
# Sets in `ZMod p` whose sampled sumsets are small

Theorem 6 of Bollobás, Leader and Tiba: if the sumset of uniform `c₁`- and `c₂`-subsets of
`A, B ⊆ ZMod p` has expected size at most `#A + #B - 1 + ε * min #A #B`, then `A` and `B` are close
to arithmetic progressions with the same common difference. The proof combines their Theorem 2,
`exists_subset_min_lt_expect_card_add`, with Theorem 4 of the paper, a stability form of the
Cauchy–Davenport theorem that the paper deduces from a theorem of Grynkiewicz. Theorem 4 is
Corollary 24 of Bollobás, Leader and Tiba, *Large sumsets from small subsets*, which is proved in
`LargeSumsetsFromSmallSubsets`.

## Main statements

* `exists_subset_arithProg_card_sdiff_le_of_card_add_le`: Theorem 4 of the paper.
* `exists_arithProg_card_symmDiff_le_of_expect_card_add_le`: Theorem 6 of the paper.
-/

public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-- **Theorem 4** of Bollobás, Leader and Tiba, a stability form of the Cauchy–Davenport theorem.
For `β, γ > 0` there is `ε > 0` such that if `A, B ⊆ ZMod p` have at least two elements,
`#A + #B ≤ (1 - β) * p` and `#(A + B) ≤ #A + #B - 1 + ε * min #A #B`, then `A` and `B` are contained
in arithmetic progressions `P` and `Q` with the same common difference such that `P \ A` and `Q \ B`
have at most `γ * min #A #B` elements. This is Corollary 24 of *Large sumsets from small subsets*,
`LargeSumsetsFromSmallSubsets.NearCauchyDavenport.exists_subset_arithProg_of_card_add_le`. -/
lemma exists_subset_arithProg_card_sdiff_le_of_card_add_le {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    ∃ ε > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), 2 ≤ #A → 2 ≤ #B →
      #A + #B ≤ (1 - β) * p → #(A + B) ≤ #A + #B - 1 + ε * min (#A : ℝ) #B →
      ∃ a b d : ZMod p, ∃ m n : ℕ, A ⊆ arithProg a d m ∧ B ⊆ arithProg b d n ∧
        #(arithProg a d m \ A) ≤ γ * min (#A : ℝ) #B ∧
        #(arithProg b d n \ B) ≤ γ * min (#A : ℝ) #B := by
  refine ⟨_, LargeSumsetsFromSmallSubsets.NearCauchyDavenport.epsilon_pos hβ hγ, ?_⟩
  intro p hp A B hA hB hAB h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, d, m, n, -, hA', hB', hPA, hQB⟩ :=
    LargeSumsetsFromSmallSubsets.NearCauchyDavenport.exists_subset_arithProg_of_card_add_le hβ hγ
      hA hB hAB (by rwa [Nat.cast_min])
  simp only [nearCauchyDavenport_arithProg_eq, Nat.cast_min] at hA' hB' hPA hQB
  exact ⟨a, b, d, m, n, hA', hB', hPA, hQB⟩

section Bookkeeping

/-! ### Real-number bookkeeping -/

variable {α δ μ ε ε₁ κ a b a' b' s E : ℝ}

/-- The hypotheses `α * y ≤ x ≤ α⁻¹ * y` with `y > 0` force `α ≤ 1`. -/
private lemma le_one_of_mul_le_of_le_inv_mul {x y : ℝ} (hα : 0 < α) (hy : 0 < y) (h₁ : α * y ≤ x)
    (h₂ : x ≤ α⁻¹ * y) : α ≤ 1 := by
  by_contra! h
  nlinarith [(le_inv_mul_iff₀ hα).1 (h₁.trans h₂),
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h hy) hα]

/-- If `c₁ * c₂ ≥ 16 * (max K 0 + 1) * M` with `M > 0` and `c₁, c₂ ≥ 2`, then the halves `c₁ / 2`
and `c₂ / 2` have product larger than `K * M`. -/
private lemma mul_lt_half_mul_half {K M : ℝ} {c₁ c₂ : ℕ} (hM : 0 < M) (h₁ : 2 ≤ c₁) (h₂ : 2 ≤ c₂)
    (h : 16 * (max K 0 + 1) * M ≤ c₁ * c₂) : K * M < (c₁ / 2 : ℕ) * (c₂ / 2 : ℕ) := by
  have hc : (c₁ * c₂ : ℝ) ≤ 4 * (c₁ / 2 : ℕ) * (4 * (c₂ / 2 : ℕ)) := by
    exact_mod_cast Nat.mul_le_mul (by grind) (by grind)
  nlinarith [mul_le_mul_of_nonneg_right (le_max_left K 0) hM.le]

/-- If `c₁ * c₂ ≥ 16 * (max K 0 + 1) * M` with `1 ≤ c₂ ≤ M`, then `c₁ ≥ 2`. -/
private lemma two_le_of_mul_le {K M : ℝ} {c₁ c₂ : ℕ} (hc₂ : 1 ≤ c₂) (hc₂M : c₂ ≤ M)
    (h : 16 * (max K 0 + 1) * M ≤ c₁ * c₂) : 2 ≤ c₁ := by
  exact_mod_cast (by nlinarith [le_max_right K 0, (Nat.one_le_cast (α := ℝ)).2 hc₂] : (2 : ℝ) ≤ c₁)

/-- If `k > (1 - μ) * n` with `μ ≤ 1 / 2`, then `k` is at least `m` for every `m ≤ n / 2`. -/
private lemma le_card_of_lt {n k m : ℕ} (hμ : μ ≤ 1 / 2) (hm : 2 * m ≤ n)
    (h : (1 - μ) * n < k) : m ≤ k := by
  have hm' : (2 * m : ℝ) ≤ n := by exact_mod_cast hm
  exact_mod_cast (by nlinarith : (m : ℝ) ≤ k)

/-- If `k > (1 - μ) * n` with `μ ≤ 1 / 2` and `n ≥ 2`, then `k ≥ 2`. -/
private lemma two_le_of_lt {n k : ℕ} (hμ : μ ≤ 1 / 2) (hn : 2 ≤ n) (h : (1 - μ) * n < k) :
    2 ≤ k :=
  Nat.one_lt_cast.1 (by nlinarith [(Nat.ofNat_le_cast (α := ℝ)).2 hn] : (1 : ℝ) < k)

/-- For `μ ≤ 1 / 100`, the number `(1 - 2 * μ) ^ 2 * (1 - μ)` is at least `1 - 5 * μ`. -/
private lemma one_sub_five_mul_le_sq_mul (hμ1 : μ ≤ 1 / 100) :
    1 - 5 * μ ≤ (1 - 2 * μ) ^ 2 * (1 - μ) := by
  nlinarith [mul_nonneg (sq_nonneg μ) (by linarith : 0 ≤ 2 - μ)]

/-- For `0 ≤ μ ≤ 1 / 100`, the number `(1 - 2 * μ) ^ 2 * (1 - μ)` is at most `1`. -/
private lemma sq_mul_le_one (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 100) : (1 - 2 * μ) ^ 2 * (1 - μ) ≤ 1 := by
  nlinarith [mul_nonneg hμ0 (by nlinarith : 0 ≤ 5 - 8 * μ + 4 * μ ^ 2)]

/-- If `α * a ≤ b` and `α * b ≤ a` with `α ≤ 1`, then `α * a + α * b ≤ 2 * min a b`. -/
private lemma mul_add_mul_le_two_mul_min (hα1 : α ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : α * b ≤ a)
    (hba : α * a ≤ b) : α * a + α * b ≤ 2 * min a b := by
  nlinarith [le_min (by nlinarith : α * a ≤ a) hba, le_min hab (by nlinarith : α * b ≤ b)]

/-- In the proof of Theorem 6, the terms `σ * #A*` and `σ * #B*` of Theorem 2 are too large to be
the minimum. -/
private lemma add_sub_one_add_lt_mul (hα : 0 < α) (hα1 : α ≤ 1) (hμ1 : μ ≤ 1 / 100)
    (hε1 : ε ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : α * b ≤ a) (ha' : (1 - μ) * a < a') :
    a + b - 1 + ε * min a b < (1 - 2 * μ) ^ 2 * (4 / α * a') := by
  have ht : 2 * (1 - μ) * (a + b) ≤ 4 / α * a' := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    nlinarith [mul_le_of_le_one_right ha hα1]
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (1 - 2 * μ)),
    mul_le_mul_of_nonneg_right (one_sub_five_mul_le_sq_mul hμ1) (add_nonneg ha hb),
    mul_le_mul_of_nonneg_right hμ1 (add_nonneg ha hb), min_le_left a b, min_le_right a b,
    mul_le_of_le_one_left (le_min ha hb) hε1]

/-- In the proof of Theorem 6, the minimum in the conclusion of Theorem 2 is its sumset term. -/
private lemma mul_lt_of_min_lt (hα : 0 < α) (hα1 : α ≤ 1) (hμ1 : μ ≤ 1 / 100)
    (hε1 : ε ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : α * b ≤ a) (hba : α * a ≤ b)
    (ha' : (1 - μ) * a < a') (hb' : (1 - μ) * b < b')
    (hmin : min (min ((1 - μ) * s) (4 / α * a')) (4 / α * b') < E)
    (hE : (1 - 2 * μ) ^ 2 * E ≤ a + b - 1 + ε * min a b) :
    (1 - 2 * μ) ^ 2 * (1 - μ) * s < a + b - 1 + ε * min a b := by
  have hκ : 0 < (1 - 2 * μ) ^ 2 := by nlinarith
  have hb'a' := add_sub_one_add_lt_mul hα hα1 hμ1 hε1 hb ha hba hb'
  rw [add_comm b, min_comm] at hb'a'
  rcases min_lt_iff.1 hmin with h | h
  · rcases min_lt_iff.1 h with h | h <;>
      nlinarith [mul_lt_mul_of_pos_left h hκ, add_sub_one_add_lt_mul hα hα1 hμ1 hε1 ha hb hab ha']
  · nlinarith [mul_lt_mul_of_pos_left h hκ]

/-- In the proof of Theorem 6, the bound `a + b - 1 + ε * min a b` for `A` and `B` is at most `κ`
times the bound `a' + b' - 1 + ε₁ * min a' b'` for the large subsets `A*` and `B*`, where
`1 - 5 * α * δ ≤ κ ≤ 1`. -/
private lemma add_sub_one_add_le_mul (hα1 : α ≤ 1) (hδ : 0 < δ) (hδε₁ : δ ≤ ε₁ / 100)
    (hεε₁ : ε ≤ ε₁ / 8) (hμ1 : α * δ ≤ 1 / 100) (hκ5 : 1 - 5 * (α * δ) ≤ κ) (hκ1 : κ ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : α * b ≤ a) (hba : α * a ≤ b) (ha' : (1 - α * δ) * a < a')
    (hb' : (1 - α * δ) * b < b') (ha'a : a' ≤ a) (hb'b : b' ≤ b) :
    a + b - 1 + ε * min a b ≤ κ * (a' + b' - 1 + ε₁ * min a' b') := by
  have hM : (1 - α * δ) * min a b ≤ min a' b' :=
    le_min (by nlinarith [min_le_left a b]) (by nlinarith [min_le_right a b])
  have hM0 : 0 ≤ min a b := le_min ha hb
  nlinarith [mul_le_mul_of_nonneg_right hκ5 (by nlinarith : 0 ≤ a' + b'),
    mul_le_mul_of_nonneg_right (by linarith : 1 / 2 ≤ κ)
      (mul_nonneg (by linarith) ((mul_nonneg (by linarith) hM0).trans hM) : 0 ≤ ε₁ * min a' b'),
    mul_le_mul_of_nonneg_left (add_le_add ha'a hb'b) (by nlinarith : 0 ≤ α * δ),
    mul_le_mul_of_nonneg_left (mul_add_mul_le_two_mul_min hα1 ha hb hab hba) hδ.le,
    mul_le_mul_of_nonneg_right hδε₁ hM0, mul_le_mul_of_nonneg_right hεε₁ hM0,
    mul_le_mul_of_nonneg_right hμ1 hM0]

/-- Bookkeeping in the proof of Theorem 6: the bound on the expected sumset of `A` and `B`, with the
conclusion of Theorem 2, bounds the sumset of the large subsets `A*` and `B*`. -/
private lemma le_add_sub_one_add_of_min_lt (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ)
    (hδε₁ : δ ≤ ε₁ / 100) (hδ1 : δ ≤ 1 / 100) (hεε₁ : ε ≤ ε₁ / 8) (hε1 : ε ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : α * b ≤ a) (hba : α * a ≤ b) (ha' : (1 - α * δ) * a < a')
    (hb' : (1 - α * δ) * b < b') (ha'a : a' ≤ a) (hb'b : b' ≤ b)
    (hmin : min (min ((1 - α * δ) * s) (4 / α * a')) (4 / α * b') < E)
    (hE : (1 - 2 * (α * δ)) ^ 2 * E ≤ a + b - 1 + ε * min a b) :
    s ≤ a' + b' - 1 + ε₁ * min a' b' := by
  have hμ1 : α * δ ≤ 1 / 100 := by nlinarith
  have hκ5 := one_sub_five_mul_le_sq_mul hμ1
  apply le_of_lt
  refine lt_of_mul_lt_mul_left ?_ (hκ5.trans' (by linarith))
  grw [mul_lt_of_min_lt hα hα1 hμ1 hε1 ha hb hab hba ha' hb' hmin hE]
  exact add_sub_one_add_le_mul hα1 hδ hδε₁ hεε₁ hμ1 hκ5 (sq_mul_le_one (mul_pos hα hδ).le hμ1) ha
    hb hab hba ha' hb' ha'a hb'b

end Bookkeeping

section Finset

variable {ι : Type*} [DecidableEq ι] {s t u : Finset ι}

/-- If `u ⊆ s` and `u ⊆ t`, then `s ∆ t` has at most `#(s \ u) + #(t \ u)` elements. -/
lemma card_symmDiff_le_card_sdiff_add_card_sdiff (hs : u ⊆ s) (ht : u ⊆ t) :
    #(s ∆ t) ≤ #(s \ u) + #(t \ u) := by
  grw [symmDiff_triangle s u t, sup_eq_union, card_union_le, symmDiff_of_ge hs, symmDiff_of_le ht]

/-- If `t ⊆ s` keeps more than a `1 - μ` proportion of `s`, then `s \ t` has at most `μ * #s`
elements. -/
private lemma card_sdiff_le_of_lt {μ : ℝ} (h : t ⊆ s) (h' : (1 - μ) * #s < #t) :
    #(s \ t) ≤ μ * #s := by
  rw [card_sdiff_of_subset h, Nat.cast_sub (card_le_card h)]
  linarith

/-- In the proof of Theorem 6, `s` is close to a progression `P` containing a large subset `t` of
`s`. -/
private lemma card_symmDiff_le_mul_min {α δ γ M M' : ℝ} {P : Finset ι} (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hδγ : δ ≤ γ / 2) (hts : t ⊆ s) (htP : t ⊆ P) (ht : (1 - α * δ) * #s < #t)
    (hP : #(P \ t) ≤ γ / 2 * M') (hM' : M' ≤ M) (hαM : α * #s ≤ M) : #(s ∆ P) ≤ γ * M := by
  nlinarith [(by exact_mod_cast card_symmDiff_le_card_sdiff_add_card_sdiff hts htP :
      (#(s ∆ P) : ℝ) ≤ #(s \ t) + #(P \ t)),
    card_sdiff_le_of_lt hts ht, mul_le_mul_of_nonneg_left hαM hδ,
    mul_le_mul_of_nonneg_right hδγ (hαM.trans' (by positivity) : 0 ≤ M)]

end Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Theorem 2 applied to the halves `c₁ / 2` and `c₂ / 2` of the sample sizes. -/
private lemma exists_subset_min_lt_expect_card_add_half {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁) (hc₁A : c₁ ≤ #A)
    (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : 16 * (max (MediumSizedSubsets.c σ μ) 0 + 1) * max (#A : ℝ) #B ≤ c₁ * c₂) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (1 - μ) * #A < #A' ∧ (1 - μ) * #B < #B' ∧
      min (min ((1 - μ) * #(A' + B')) (σ * #A')) (σ * #B') <
        𝔼 f : Fin (c₁ / 2) → A', 𝔼 g : Fin (c₂ / 2) → B',
          (#(univ.image (fun i ↦ (f i : G)) + univ.image (fun i ↦ (g i : G))) : ℝ) := by
  have h₁ := two_le_of_mul_le hc₂ (le_max_of_le_right (by exact_mod_cast hc₂B)) hc
  have h₂ := two_le_of_mul_le hc₁ (le_max_of_le_left (by exact_mod_cast hc₁A))
    (hc.trans_eq (mul_comm _ _))
  obtain ⟨A', hA'A, B', hB'B, -, -, hA', hB', hmin⟩ :=
    exists_subset_min_lt_expect_card_add hσ hμ hA hB (c₁ := c₁ / 2) (c₂ := c₂ / 2) (by grind)
      ((Nat.div_le_self _ _).trans hc₁A) (by grind) ((Nat.div_le_self _ _).trans hc₂B)
      (mul_lt_half_mul_half (lt_max_of_lt_left (by exact_mod_cast hA.card_pos)) h₁ h₂ hc)
  rw [← univ_product_univ, expect_product] at hmin
  exact ⟨A', hA'A, B', hB'B, hA', hB', hmin⟩

/-- If `A' ⊆ A` and `B' ⊆ B` keep more than a `1 - μ` proportion of `A` and `B`, with
`0 ≤ μ ≤ 1 / 2`, then the expected sumset of uniform `c₁`- and `c₂`-subsets of `A` and `B` is at
least `(1 - 2 * μ) ^ 2` times that of independent `c₁ / 2`- and `c₂ / 2`-samples of `A'` and
`B'`. -/
private lemma mul_expect_card_add_half_le_expect_powersetCard {A A' B B' : Finset G} (hA'A : A' ⊆ A)
    (hB'B : B' ⊆ B) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ : μ ≤ 1 / 2) (hA' : (1 - μ) * #A < #A')
    (hB' : (1 - μ) * #B < #B') {c₁ c₂ : ℕ} (hc₁A : c₁ ≤ #A) (hc₂B : c₂ ≤ #B) :
    (1 - 2 * μ) ^ 2 * 𝔼 f : Fin (c₁ / 2) → A', 𝔼 g : Fin (c₂ / 2) → B',
        (#(univ.image (fun i ↦ (f i : G)) + univ.image (fun i ↦ (g i : G))) : ℝ) ≤
      𝔼 S ∈ powersetCard c₁ A, 𝔼 T ∈ powersetCard c₂ B, (#(S + T) : ℝ) :=
  mul_expect_card_add_le_expect_powersetCard hA'A hB'B hμ₀ hμ (card_sdiff_le_of_lt hA'A hA')
    (card_sdiff_le_of_lt hB'B hB') (Nat.mul_div_le c₁ 2) hc₁A (Nat.mul_div_le c₂ 2) hc₂B
    (le_card_of_lt hμ ((Nat.mul_div_le c₁ 2).trans hc₁A) hA')
    (le_card_of_lt hμ ((Nat.mul_div_le c₂ 2).trans hc₂B) hB')

/-- The analytic core of Theorem 6. Theorem 2 and the comparison of independent samples with uniform
subsets produce large subsets `A* ⊆ A` and `B* ⊆ B` whose sumset has at most
`#A* + #B* - 1 + ε₁ * min #A* #B*` elements. -/
private lemma exists_subset_card_add_le_of_expect_card_add_le {α δ ε ε₁ : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hδ : 0 < δ) (hδε₁ : δ ≤ ε₁ / 100) (hδ1 : δ ≤ 1 / 100) (hεε₁ : ε ≤ ε₁ / 8)
    (hε1 : ε ≤ 1) {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {c₁ c₂ : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₁A : c₁ ≤ #A) (hc₂ : 1 ≤ c₂) (hc₂B : c₂ ≤ #B)
    (hc : 16 * (max (MediumSizedSubsets.c (4 / α) (α * δ)) 0 + 1) * max (#A : ℝ) #B ≤ c₁ * c₂)
    (hαA : α * #B ≤ #A) (hαB : α * #A ≤ #B)
    (hE : 𝔼 A' ∈ powersetCard c₁ A, 𝔼 B' ∈ powersetCard c₂ B, (#(A' + B') : ℝ) ≤
      #A + #B - 1 + ε * min (#A : ℝ) #B) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (1 - α * δ) * #A < #A' ∧ (1 - α * δ) * #B < #B' ∧
      #(A' + B') ≤ #A' + #B' - 1 + ε₁ * min (#A' : ℝ) #B' := by
  obtain ⟨A', hA'A, B', hB'B, hA', hB', hmin⟩ := exists_subset_min_lt_expect_card_add_half
    (div_pos four_pos hα) (mul_pos hα hδ) hA hB hc₁ hc₁A hc₂ hc₂B hc
  refine ⟨A', hA'A, B', hB'B, hA', hB', le_add_sub_one_add_of_min_lt hα hα1 hδ hδε₁ hδ1 hεε₁ hε1
    (by positivity) (by positivity) hαA hαB hA' hB' (by exact_mod_cast card_le_card hA'A)
    (by exact_mod_cast card_le_card hB'B) hmin ?_⟩
  grw [mul_expect_card_add_half_le_expect_powersetCard hA'A hB'B (mul_pos hα hδ).le (by nlinarith)
    hA' hB' hc₁A hc₂B]
  exact hE

/-- The last step of Theorem 6. If large subsets `A' ⊆ A` and `B' ⊆ B` lie in progressions with
common difference `d` that they nearly fill, then `d ≠ 0` and `A` and `B` are within `γ * min #A #B`
of these progressions. -/
private lemma exists_arithProg_card_symmDiff_le_of_subset {α δ γ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 0 < δ) (hδγ : δ ≤ γ / 2) {A B A' B' : Finset G} (hA'A : A' ⊆ A) (hB'B : B' ⊆ B)
    (hA' : (1 - α * δ) * #A < #A') (hB' : (1 - α * δ) * #B < #B') (hαA : α * #B ≤ #A)
    (hαB : α * #A ≤ #B) (hA'₂ : 2 ≤ #A')
    (h : ∃ a b d : G, ∃ m n : ℕ, A' ⊆ arithProg a d m ∧ B' ⊆ arithProg b d n ∧
      #(arithProg a d m \ A') ≤ γ / 2 * min (#A' : ℝ) #B' ∧
      #(arithProg b d n \ B') ≤ γ / 2 * min (#A' : ℝ) #B') :
    ∃ a b d : G, d ≠ 0 ∧ ∃ m n : ℕ,
      #(A ∆ arithProg a d m) ≤ γ * min (#A : ℝ) #B ∧
      #(B ∆ arithProg b d n) ≤ γ * min (#A : ℝ) #B := by
  obtain ⟨a, b, d, m, n, hAP, hBQ, hPA, hQB⟩ := h
  have hM : min (#A' : ℝ) #B' ≤ min (#A : ℝ) #B :=
    min_le_min (by exact_mod_cast card_le_card hA'A) (by exact_mod_cast card_le_card hB'B)
  exact ⟨a, b, d, ne_zero_of_two_le_card_of_subset_arithProg hA'₂ hAP, m, n,
    card_symmDiff_le_mul_min hα.le hδ.le hδγ hA'A hAP hA' hPA hM (le_min (by nlinarith) hαB),
    card_symmDiff_le_mul_min hα.le hδ.le hδγ hB'B hBQ hB' hQB hM (le_min hαA (by nlinarith))⟩

/-- **Theorem 6** of Bollobás, Leader and Tiba. For `β, γ > 0` there is `ε > 0` such that for
`α > 0` there is `c` with the following property. Let `A, B ⊆ ZMod p` have at least two elements,
`α * #B ≤ #A ≤ α⁻¹ * #B` and `#A + #B ≤ (1 - β) * p`, and let `1 ≤ c₁ ≤ #A` and `1 ≤ c₂ ≤ #B`
satisfy `c₁ * c₂ ≥ c * max #A #B`. If the sumset of uniform `c₁`- and `c₂`-subsets of `A` and `B`
has expected size at most `#A + #B - 1 + ε * min #A #B`, then `A` and `B` are within `γ * min #A #B`
of arithmetic progressions with the same nonzero common difference. -/
lemma exists_arithProg_card_symmDiff_le_of_expect_card_add_le {β γ : ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) :
    ∃ ε > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime → ∀ (A B : Finset (ZMod p)) (c₁ c₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ → 2 ≤ #A → 2 ≤ #B →
      α * #B ≤ #A → #A ≤ α⁻¹ * #B → #A + #B ≤ (1 - β) * p →
      𝔼 A' ∈ powersetCard c₁ A, 𝔼 B' ∈ powersetCard c₂ B, (#(A' + B') : ℝ) ≤
        #A + #B - 1 + ε * min (#A : ℝ) #B →
      ∃ a b d : ZMod p, d ≠ 0 ∧ ∃ m n : ℕ,
        #(A ∆ arithProg a d m) ≤ γ * min (#A : ℝ) #B ∧
        #(B ∆ arithProg b d n) ≤ γ * min (#A : ℝ) #B := by
  obtain ⟨ε₁, hε₁, hCD⟩ := exists_subset_arithProg_card_sdiff_le_of_card_add_le hβ (half_pos hγ)
  obtain ⟨δ, hδ, hδε₁, hδγ, hδ1⟩ : ∃ δ > 0, δ ≤ ε₁ / 100 ∧ δ ≤ γ / 2 ∧ δ ≤ 1 / 100 :=
    ⟨min (min ε₁ γ) 1 / 100, by positivity, by grind, by grind, by grind⟩
  refine ⟨min ε₁ 1 / 8, by positivity, ?_⟩
  intro α hα
  refine ⟨16 * (max (MediumSizedSubsets.c (4 / α) (α * δ)) 0 + 1), ?_⟩
  intro p hp A B c₁ c₂ hc₁ hc₁A hc₂ hc₂B hc hA hB hαA hAα hβp hE
  have hα1 := le_one_of_mul_le_of_le_inv_mul hα (Nat.cast_pos.2 (by grind)) hαA hAα
  have hαB := (le_inv_mul_iff₀ hα).1 hAα
  obtain ⟨A', hA'A, B', hB'B, hA', hB', hsum⟩ :=
    exists_subset_card_add_le_of_expect_card_add_le hα hα1 hδ hδε₁ hδ1
      (by linarith [min_le_left ε₁ 1]) (by linarith [min_le_right ε₁ 1]) (card_pos.1 (by grind))
      (card_pos.1 (by grind)) hc₁ hc₁A hc₂ hc₂B hc hαA hαB hE
  obtain ⟨hA'₂, hB'₂⟩ : 2 ≤ #A' ∧ 2 ≤ #B' :=
    ⟨two_le_of_lt (by nlinarith) hA hA', two_le_of_lt (by nlinarith) hB hB'⟩
  exact exists_arithProg_card_symmDiff_le_of_subset hα hα1 hδ hδγ hA'A hB'B hA' hB' hαA hαB hA'₂
    (hCD p hp A' B' hA'₂ hB'₂ (hβp.trans' (by gcongr)) hsum)

end LargeSumsetsFromSubsets
