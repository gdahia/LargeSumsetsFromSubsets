/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression
public import LargeSumsetsFromSubsets.IntervalSumsets.FewTranslates
public import LargeSumsetsFromSubsets.IntervalSumsets.Sampling
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Rify
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Small subsets of sets close to intervals

Theorem 8 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*. There is
`γ > 0` such that for `α > 0` there is `c` with the following property. Let `X ⊆ I` and `Y ⊆ J`
miss at most `γ * min #I #J` points of the intervals `I` and `J`, with
`α * #J ≤ #I ≤ α⁻¹ * #J`. Then for `1 ≤ c₁ ≤ #X` and `1 ≤ c₂ ≤ #Y` with
`c₁ * c₂ ≥ c * max #X #Y` there are `X' ⊆ X` and `Y' ⊆ Y` with `c₁` and `c₂` elements and
`#(X' + Y') ≥ #X + #Y - 1`. The theorem assumes Theorem 5 of the paper,
`FewTranslatesNearIntervals`.

The proof is that of the paper. With `d` of order `c₂`, the sets are split into their residue
classes modulo `d`. In each class `y` where `Y` is dense, Theorem 5 gives a family of bounded
subsets of the class of `Y`. The sample of `Y` is a union of members of these families, one for
each class, and the sample of `X` is the largest class of `X` together with `t` random dense
classes. Every class of the sumset is then large in expectation, and `d - 1` more elements of `X`
and of `Y` complete the sumset.

* `exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico`: the theorem in `ℤ`;
* `exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range`: the theorem
  for intervals of `ZMod p` with `#I + #J ≤ p`, as stated in the paper.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-- The conclusion of `exists_fewTranslates_int` for given constants `γ`, `α` and `c`. -/
def FewTranslatesInt (γ α : ℝ) (c : ℕ) : Prop :=
  ∀ (x y : ℤ) (m n R : ℕ) (B : Finset ℤ),
    α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n →
    B ⊆ Ico y (y + n) → y ∈ B → y + n - 1 ∈ B →
    (#(Ico y (y + n) \ B) : ℝ) ≤ γ * min (m : ℝ) n →
    ∃ (k : ℕ) (F : Fin (k + 1) → Finset ℤ), (∀ i, F i ⊆ B ∧ #(F i) ≤ c) ∧
      ∀ A ⊆ Ico (x - R) (x + m + R), (#(A ∆ Ico x (x + m)) : ℝ) ≤ γ * min (m : ℝ) n →
        (#A + #B - 1 : ℝ) ≤ 𝔼 i, (#(A + F i) : ℝ)

/-- `FewTranslatesInt` still holds for a smaller `γ`. -/
lemma FewTranslatesInt.mono {γ γ' α : ℝ} {c : ℕ} (h : FewTranslatesInt γ α c) (hγ : γ' ≤ γ) :
    FewTranslatesInt γ' α c := by
  intro x y m n R B h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨k, F, hF, hA⟩ := h x y m n R B h₁ h₂ h₃ h₄ h₅ (h₆.trans (by gcongr))
  exact ⟨k, F, hF, fun A hA₁ hA₂ ↦ hA A hA₁ (hA₂.trans (by gcongr))⟩

/-! ### Elementary bounds -/

/-- If `128 ≤ γ₀ * l` with `0 < γ₀ ≤ 1`, then `γ₀ * l ≤ l`. -/
lemma mul_le_self_of_le_mul {γ₀ l : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hl : 128 ≤ γ₀ * l) :
    γ₀ * l ≤ l :=
  mul_le_of_le_one_left (pos_of_mul_pos_right (by linarith) hγ₀.le).le hγ₀₁

/-- If `128 / γ₀ ≤ K` with `0 < γ₀ ≤ 1`, then `1 ≤ K`. -/
lemma one_le_of_div_le {γ₀ : ℝ} {K : ℕ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hK : 128 / γ₀ ≤ K) :
    1 ≤ K := by
  exact_mod_cast ((one_le_div hγ₀).2 (by linarith)).trans hK

/-- If `128 / γ₀ ≤ K` and `(K + 1) * d` is at most `m` and `n`, then
`128 ≤ γ₀ * (min m n / d)`. -/
lemma le_mul_min_div_of_mul_le {γ₀ : ℝ} {K d m n : ℕ} (hγ₀ : 0 < γ₀) (hd : 0 < d)
    (hK : 128 / γ₀ ≤ K) (hm : (K + 1) * d ≤ m) (hn : (K + 1) * d ≤ n) :
    128 ≤ γ₀ * (min (m : ℝ) n / d) := by
  have h : ((K : ℝ) + 1) * d ≤ min (m : ℝ) n := le_min (by exact_mod_cast hm) (by exact_mod_cast hn)
  rw [← le_div_iff₀ (by exact_mod_cast hd)] at h
  rw [div_le_iff₀ hγ₀] at hK
  nlinarith [mul_le_mul_of_nonneg_left h hγ₀.le]

/-- The arithmetic of the hypotheses of Theorem 5 in a dense class. Let `0 < γ₀ ≤ 1`,
`0 < α ≤ 1`, `α * v ≤ u`, `α * u ≤ v` and `128 ≤ γ₀ * min u v`. If `u - 1 ≤ μ ≤ u` and
`v - 2 - γ₀ * min u v / 4 ≤ ν ≤ v + 2`, then `γ₀ * min u v / 4 ≤ γ₀ * min μ ν`,
`α / 2 * ν ≤ μ` and `μ ≤ (α / 2)⁻¹ * ν`. -/
lemma le_mul_min_and_mul_le {α γ₀ u v μ ν : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α)
    (hα₁ : α ≤ 1) (hαv : α * v ≤ u) (hαu : α * u ≤ v) (hl : 128 ≤ γ₀ * min u v)
    (hμ₁ : u - 1 ≤ μ) (hμ₂ : μ ≤ u) (hν₁ : v - 2 - γ₀ * min u v / 4 ≤ ν) (hν₂ : ν ≤ v + 2) :
    γ₀ * min u v / 4 ≤ γ₀ * min μ ν ∧ α / 2 * ν ≤ μ ∧ μ ≤ (α / 2)⁻¹ * ν := by
  have hγl := mul_le_self_of_le_mul hγ₀ hγ₀₁ hl
  have hu := min_le_left u v
  have hv := min_le_right u v
  refine ⟨?_, by nlinarith [mul_le_mul_of_nonneg_left hν₂ hα.le], ?_⟩
  · linarith [mul_le_mul_of_nonneg_left
      (le_min (by linarith) (by linarith) : min u v / 4 ≤ min μ ν) hγ₀.le]
  · rw [inv_div, div_mul_eq_mul_div, le_div_iff₀ hα]
    linarith [mul_le_mul_of_nonneg_left hμ₂ hα.le]

/-! ### Sizes of the classes -/

variable {d : ℕ} [NeZero d] {a b : ℤ} {m n : ℕ} {X Y : Finset ℤ} {r : ZMod d} {θ : ℝ}

/-- The quotient `m / d` in `ℕ` is within `1` of the quotient in `ℝ`. -/
lemma div_sub_one_le_natCast_div (m : ℕ) : (m : ℝ) / d - 1 ≤ ((m / d : ℕ) : ℝ) := by
  rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast Nat.pos_of_neZero d), add_one_mul]
  exact_mod_cast (Nat.lt_div_mul_add (Nat.pos_of_neZero d)).le

omit [NeZero d] in
/-- The condition `α * n ≤ m ≤ α⁻¹ * n` passes to the quotients by `d`. -/
lemma mul_div_le_div_of_mul_le {α : ℝ} (hα : 0 < α) (hαn : α * n ≤ m)
    (hαm : (m : ℝ) ≤ α⁻¹ * n) : α * (n / d) ≤ m / d ∧ α * (m / d) ≤ n / d := by
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact ⟨by gcongr, by gcongr; exact (le_inv_mul_iff₀ hα).1 hαm⟩

omit [NeZero d] in
/-- A set `X ⊆ Ico a (a + m)` has at most `m` elements. -/
lemma card_le_of_subset_Ico (hX : X ⊆ Ico a (a + m)) : #X ≤ m := by
  simpa using card_le_card hX

omit [NeZero d] in
/-- A set `X ⊆ Ico a (a + m)` and the points of the interval it misses add up to `m`. -/
lemma card_Ico_sdiff_add_card (hX : X ⊆ Ico a (a + m)) :
    (#(Ico a (a + m) \ X) : ℝ) + #X = m := by
  exact_mod_cast (card_sdiff_add_card_eq_card hX).trans (by simp)

omit [NeZero d] in
/-- A set `X ⊆ Ico a (a + m)` missing at most `γ₀ / 256 * min m n` points of the interval, with
`γ₀ ≤ 1`, has at least `m / 2` elements. -/
lemma le_two_mul_card {γ₀ : ℝ} (hX : X ⊆ Ico a (a + m)) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1)
    (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n) : m ≤ 2 * #X := by
  exact_mod_cast (by nlinarith [card_Ico_sdiff_add_card hX, min_le_left (m : ℝ) n,
    (by positivity : (0 : ℝ) ≤ min (m : ℝ) n)] : (m : ℝ) ≤ 2 * #X)

/-- A class of `Ico a (a + m)` modulo `d` has at least `m / d - 2` elements. -/
lemma sub_two_le_card_modFibre_Ico : (m : ℝ) / d - 2 ≤ #(modFibre d r (Ico a (a + m))) := by
  linarith [div_sub_one_le_natCast_div (d := d) m, (by exact_mod_cast le_card_modFibre_Ico_add_one :
    ((m / d : ℕ) : ℝ) ≤ #(modFibre d r (Ico a (a + m))) + 1)]

/-- A class of `Ico a (a + m)` modulo `d` has at most `m / d + 2` elements. -/
lemma card_modFibre_Ico_le_add_two : (#(modFibre d r (Ico a (a + m))) : ℝ) ≤ m / d + 2 := by
  linarith [(Nat.cast_div_le : ((m / d : ℕ) : ℝ) ≤ m / d), (by exact_mod_cast card_modFibre_Ico_le :
    (#(modFibre d r (Ico a (a + m))) : ℝ) ≤ (m / d : ℕ) + 2)]

/-- A class of `X ⊆ Ico a (a + m)` has at most `m / d + 2` elements. -/
lemma card_modFibre_le_of_subset_Ico (hX : X ⊆ Ico a (a + m)) :
    (#(modFibre d r X) : ℝ) ≤ m / d + 2 :=
  le_trans (by exact_mod_cast card_le_card (modFibre_mono hX)) card_modFibre_Ico_le_add_two

/-- The class `r` of `Ico a (a + m)` is the disjoint union of the class `r` of `X` and the
points of the class missed by `X`. -/
lemma card_modFibre_sdiff_add (hX : X ⊆ Ico a (a + m)) :
    (#(modFibre d r (Ico a (a + m)) \ modFibre d r X) : ℝ) + #(modFibre d r X) =
      #(modFibre d r (Ico a (a + m))) := by
  exact_mod_cast card_sdiff_add_card_eq_card (modFibre_mono hX)

/-! ### Dense classes -/

/-- The residues `r` modulo `d` such that `X` misses at most `θ` points of the class `r` of
`Ico a (a + m)`. -/
noncomputable def denseRes (d : ℕ) [NeZero d] (a : ℤ) (m : ℕ) (X : Finset ℤ) (θ : ℝ) :
    Finset (ZMod d) :=
  {r | (#(modFibre d r (Ico a (a + m)) \ modFibre d r X) : ℝ) ≤ θ}

/-- A residue `r` is in `denseRes d a m X θ` when `X` misses at most `θ` points of the class
`r` of `Ico a (a + m)`. -/
lemma mem_denseRes :
    r ∈ denseRes d a m X θ ↔ (#(modFibre d r (Ico a (a + m)) \ modFibre d r X) : ℝ) ≤ θ := by
  simp [denseRes]

/-- More classes are dense for a larger threshold. -/
lemma denseRes_mono {θ' : ℝ} (h : θ ≤ θ') : denseRes d a m X θ ⊆ denseRes d a m X θ' :=
  fun _ hr ↦ mem_denseRes.2 ((mem_denseRes.1 hr).trans h)

/-- A dense class of `X` has at least `m / d - 2 - θ` elements. -/
lemma le_card_modFibre_of_mem_denseRes (hX : X ⊆ Ico a (a + m)) (hr : r ∈ denseRes d a m X θ) :
    (m : ℝ) / d - 2 - θ ≤ #(modFibre d r X) := by
  linarith [mem_denseRes.1 hr, card_modFibre_sdiff_add (r := r) hX,
    sub_two_le_card_modFibre_Ico (r := r) (a := a) (m := m)]

/-- A class of `X` which is not dense has at most `m / d + 2 - θ` elements. -/
lemma card_modFibre_le_of_notMem_denseRes (hX : X ⊆ Ico a (a + m))
    (hr : r ∉ denseRes d a m X θ) : (#(modFibre d r X) : ℝ) ≤ m / d + 2 - θ := by
  rw [mem_denseRes, not_le] at hr
  linarith [card_modFibre_sdiff_add (r := r) hX,
    card_modFibre_Ico_le_add_two (r := r) (a := a) (m := m)]

/-- Markov's inequality: few classes are not dense. -/
lemma card_univ_sdiff_denseRes_le (hθ : 0 < θ)
    (h : (#(Ico a (a + m) \ X) : ℝ) ≤ d * θ / 16) :
    (#(univ \ denseRes d a m X θ) : ℝ) ≤ d / 16 := by
  refine le_of_mul_le_mul_right ?_ hθ
  refine le_trans ?_ (h.trans_eq (by ring))
  rw [← sum_card_modFibre (d := d) (Ico a (a + m) \ X), Nat.cast_sum, ← nsmul_eq_mul]
  refine (card_nsmul_le_sum _ _ _ ?_).trans
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity)
  intro r hr
  simp only [mem_sdiff, mem_univ, mem_denseRes, not_le, true_and] at hr
  rw [modFibre_sdiff]
  exact hr.le

/-- If `X` misses at most `γ₀ / 256 * L` points of `Ico a (a + m)`, at most `d / 16` classes
miss more than `γ₀ * (L / d) / 16` points. -/
lemma card_univ_sdiff_denseRes_le_of_le {γ₀ L : ℝ} (hL : 0 < γ₀ * (L / d))
    (h : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * L) :
    (#(univ \ denseRes d a m X (γ₀ * (L / d) / 16)) : ℝ) ≤ d / 16 := by
  refine card_univ_sdiff_denseRes_le (by positivity) (h.trans_eq ?_)
  field_simp [(Nat.pos_of_neZero d).ne']
  ring

/-- If `X ⊆ Ico a (a + m)` misses at most `γ₀ / 256 * L` points of the interval and the class
`r₀` of `X` is the largest, then the class `r₀` has at least `m / d - γ₀ * (L / d) / 256`
elements. -/
lemma sub_le_card_modFibre_of_forall_le {γ₀ L : ℝ} {r₀ : ZMod d} (hX : X ⊆ Ico a (a + m))
    (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * L)
    (hmax : ∀ r, #(modFibre d r X) ≤ #(modFibre d r₀ X)) :
    (m : ℝ) / d - γ₀ * (L / d) / 256 ≤ #(modFibre d r₀ X) := by
  rw [(by ring : γ₀ * (L / d) / 256 = γ₀ / 256 * L / d), ← sub_div,
    div_le_iff₀ (by exact_mod_cast Nat.pos_of_neZero d)]
  linarith [card_Ico_sdiff_add_card hX, card_le_mul_card_modFibre hmax]

/-- The largest class of `X` is dense. -/
lemma mem_denseRes_of_forall_le {γ₀ : ℝ} {r₀ : ZMod d} (hX : X ⊆ Ico a (a + m))
    (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hl : 128 ≤ γ₀ * (min (m : ℝ) n / d)) (hmax : ∀ r, #(modFibre d r X) ≤ #(modFibre d r₀ X)) :
    r₀ ∈ denseRes d a m X (γ₀ * (min (m : ℝ) n / d) / 16) := by
  rw [mem_denseRes]
  linarith [card_modFibre_sdiff_add (r := r₀) hX,
    card_modFibre_Ico_le_add_two (r := r₀) (a := a) (m := m),
    sub_le_card_modFibre_of_forall_le hX hXI hmax]

/-- The classes in `EX` and `EY'` are larger than the classes outside `EY` by `θ / 16`. -/
lemma add_le_card_modFibre_add (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n))
    (hθ : 128 ≤ θ) {r₀ x y y' : ZMod d} (hx : x ∈ denseRes d a m X (θ / 16))
    (hy : y ∈ denseRes d b n Y (θ / 16)) (hy' : y' ∉ denseRes d b n Y (θ / 4)) :
    (#(modFibre d r₀ X) + #(modFibre d y' Y) : ℝ) + θ / 16 ≤
      #(modFibre d x X) + #(modFibre d y Y) := by
  linarith [card_modFibre_le_of_subset_Ico (r := r₀) hX,
    card_modFibre_le_of_notMem_denseRes hY hy', le_card_modFibre_of_mem_denseRes hX hx,
    le_card_modFibre_of_mem_denseRes hY hy]

/-- A set of residues and its complement have `d` elements together. -/
lemma card_univ_sdiff_add_card (E : Finset (ZMod d)) : (#(univ \ E) : ℝ) + #E = d := by
  exact_mod_cast (card_sdiff_add_card_eq_card (subset_univ E)).trans (by simp)

/-- For `ξ` uniform in `EX ^ t`, the probability that every `z - ξ i` is outside `EY'` is at most
`2 ^ (-t)`. -/
lemma card_filter_sub_notMem_pow_le {EX EY' : Finset (ZMod d)} (hX : (#(univ \ EX) : ℝ) ≤ d / 16)
    (hY : (#(univ \ EY') : ℝ) ≤ d / 16) (z : ZMod d) (t : ℕ) :
    (#{x ∈ EX | z - x ∉ EY'} : ℝ) ^ t ≤ (1 / 2) ^ t * #EX ^ t := by
  have h : (#{x ∈ EX | z - x ∉ EY'} : ℝ) ≤ #(univ \ EY') := by
    refine Nat.cast_le.2 (card_le_card_of_injOn (fun x ↦ z - x) ?_
      fun x _ y _ h ↦ sub_right_injective h)
    intro x hx
    simp only [coe_filter] at hx
    obtain ⟨-, hx⟩ := hx
    simpa using hx
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith [card_univ_sdiff_add_card EX]) t

/-- If `α * n ≤ m ≤ α⁻¹ * n` with `α ≤ 1` and `2 ≤ min m n / d`, then `α` times the sum of the
sizes of a class of `X ⊆ Ico a (a + m)` and a class of `Y ⊆ Ico b (b + n)` is at most
`4 * (min m n / d)`. -/
lemma mul_card_modFibre_add_le {α : ℝ} (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n))
    (hα : 0 < α) (hα₁ : α ≤ 1) (hαn : α * n ≤ m) (hαm : (m : ℝ) ≤ α⁻¹ * n)
    (hl : 2 ≤ min (m : ℝ) n / d) (r y : ZMod d) :
    α * (#(modFibre d r X) + #(modFibre d y Y) : ℝ) ≤ 4 * (min (m : ℝ) n / d) := by
  rw [← min_div_div_right (Nat.cast_nonneg d)] at hl ⊢
  obtain ⟨hαv, hαu⟩ := mul_div_le_div_of_mul_le (d := d) hα hαn hαm
  linarith [mul_le_mul_of_nonneg_left (add_le_add (card_modFibre_le_of_subset_Ico (r := r) hX)
    (card_modFibre_le_of_subset_Ico (r := y) hY)) hα.le,
    le_min (mul_le_of_le_one_left (by positivity) hα₁) hαu,
    le_min hαv (mul_le_of_le_one_left (by positivity) hα₁)]

/-- The loss `2 ^ (-t)` on the sizes of two classes is smaller than the gain. -/
lemma half_pow_mul_card_add_le {α γ₀ : ℝ} {t : ℕ} (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hα : 0 < α) (hα₁ : α ≤ 1) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1)
    (hαn : α * n ≤ m) (hαm : (m : ℝ) ≤ α⁻¹ * n) (ht : (1 / 2 : ℝ) ^ t ≤ α * γ₀ / 128)
    (hl : 2 ≤ min (m : ℝ) n / d) (r y : ZMod d) :
    (1 / 2) ^ t * (#(modFibre d r X) + #(modFibre d y Y) : ℝ) ≤
      (1 - (1 / 2) ^ t) * (γ₀ * (min (m : ℝ) n / d) / 16) := by
  nlinarith [mul_le_mul_of_nonneg_right ht
      (by positivity : (0 : ℝ) ≤ #(modFibre d r X) + #(modFibre d y Y)),
    mul_le_mul_of_nonneg_left (mul_card_modFibre_add_le hX hY hα hα₁ hαn hαm hl r y) hγ₀.le,
    mul_le_mul_of_nonneg_right (ht.trans (by nlinarith) : (1 / 2 : ℝ) ^ t ≤ 1 / 128)
      (by positivity : 0 ≤ γ₀ * (min (m : ℝ) n / d))]

/-! ### The families of Theorem 5 -/

/-- A dense class `y` of `Y ⊆ Ico b (b + n)` lies in an interval of length `n'` with
`n / d - 2 - θ ≤ n' ≤ n / d + 2` whose endpoints belong to the class and of which the class
misses at most `θ` points. -/
lemma exists_Ico_of_mem_denseRes {y : ZMod d} (hY : Y ⊆ Ico b (b + n))
    (hy : y ∈ denseRes d b n Y θ) (hθ : θ < n / d - 2) :
    ∃ (y₀ : ℤ) (n' : ℕ), modFibre d y Y ⊆ Ico y₀ (y₀ + n') ∧ y₀ ∈ modFibre d y Y ∧
      y₀ + n' - 1 ∈ modFibre d y Y ∧ (n : ℝ) / d - 2 - θ ≤ n' ∧ (n' : ℝ) ≤ n / d + 2 ∧
      (#(Ico y₀ (y₀ + n') \ modFibre d y Y) : ℝ) ≤ θ := by
  have hYy := le_card_modFibre_of_mem_denseRes hY hy
  obtain ⟨y₀, n', hB, hy₀, hy₁, hn₂, hn₁, hmiss⟩ := exists_Ico_subset_modFibre_Ico
    (card_pos.1 (Nat.cast_pos.1 ((sub_pos.2 hθ).trans_le hYy))) (modFibre_mono hY)
  exact ⟨y₀, n', hB, hy₀, hy₁, hYy.trans (by exact_mod_cast hn₂),
    (Nat.cast_le.2 hn₁).trans card_modFibre_Ico_le_add_two,
    (Nat.cast_le.2 hmiss).trans (mem_denseRes.1 hy)⟩

/-- In a dense class `y` of `Y`, Theorem 5 gives a family of subsets of the class of `Y` of size
at most `c₀` which is good for every dense class `x` of `X`. -/
lemma exists_family_of_mem_denseRes {γ₀ α : ℝ} {c₀ : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : (m : ℝ) ≤ α⁻¹ * n)
    (hl₀ : 128 ≤ γ₀ * (min (m : ℝ) n / d)) {y : ZMod d}
    (hy : y ∈ denseRes d b n Y (γ₀ * (min (m : ℝ) n / d) / 4)) :
    ∃ (k : ℕ) (F : Fin (k + 1) → Finset ℤ), (∀ i, F i ⊆ modFibre d y Y ∧ #(F i) ≤ c₀) ∧
      ∀ x ∈ denseRes d a m X (γ₀ * (min (m : ℝ) n / d) / 16),
        (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
          𝔼 i, (#(modFibre d x X + F i) : ℝ) := by
  rw [← min_div_div_right (Nat.cast_nonneg d)] at hl₀ hy ⊢
  obtain ⟨hαv, hαu⟩ := mul_div_le_div_of_mul_le (d := d) hα hαn hαm
  obtain ⟨y₀, n', hB, hy₀, hy₁, hn'₁, hn'₂, hmiss⟩ := exists_Ico_of_mem_denseRes hY hy
    (by linarith [mul_le_self_of_le_mul hγ₀ hγ₀₁ hl₀, min_le_right ((m : ℝ) / d) (n / d)])
  obtain ⟨hmin, hμν, hνμ⟩ := le_mul_min_and_mul_le hγ₀ hγ₀₁ hα hα₁ hαv hαu hl₀
    (div_sub_one_le_natCast_div m) Nat.cast_div_le hn'₁ hn'₂
  obtain ⟨k, F, hF, hA⟩ :=
    hT (a / d) y₀ (m / d) n' 2 _ hμν hνμ hB hy₀ hy₁ (hmiss.trans hmin)
  refine ⟨k, F, hF, ?_⟩
  intro x hx
  refine hA _ ((modFibre_mono hX).trans (modFibre_Ico_subset.trans
    (Ico_subset_Ico (by grind) (by grind)))) ?_
  refine (Nat.cast_le.2 (card_symmDiff_Ico_le (modFibre_mono (r := x) hX))).trans
    (le_trans ?_ hmin)
  push_cast
  linarith [mem_denseRes.1 hx]

/-- For every residue `y` there is a family of subsets of the class `y` of `Y` of size at most
`c₀`, which is good for every dense class of `X` when `y` is a dense class of `Y`. -/
lemma exists_family {γ₀ α : ℝ} {c₀ : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : (m : ℝ) ≤ α⁻¹ * n)
    (hl₀ : 128 ≤ γ₀ * (min (m : ℝ) n / d)) (y : ZMod d) :
    ∃ (k : ℕ) (F : Fin (k + 1) → Finset ℤ), (∀ i, F i ⊆ modFibre d y Y ∧ #(F i) ≤ c₀) ∧
      (y ∈ denseRes d b n Y (γ₀ * (min (m : ℝ) n / d) / 4) →
        ∀ x ∈ denseRes d a m X (γ₀ * (min (m : ℝ) n / d) / 16),
          (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
            𝔼 i, (#(modFibre d x X + F i) : ℝ)) := by
  by_cases hy : y ∈ denseRes d b n Y (γ₀ * (min (m : ℝ) n / d) / 4)
  · obtain ⟨k, F, hF, hA⟩ :=
      exists_family_of_mem_denseRes hT hγ₀ hγ₀₁ hα hα₁ hX hY hαn hαm hl₀ hy
    exact ⟨k, F, hF, fun _ ↦ hA⟩
  · exact ⟨0, fun _ ↦ ∅, fun _ ↦ ⟨empty_subset _, by simp⟩, fun h ↦ absurd h hy⟩

/-! ### The samples -/

/-- If `min m n / d` is large, there are `X' ⊆ X` with at most `(t + 1) * (m / d + 2)` elements
and `Y' ⊆ Y` with at most `d * c₀` elements whose sumset has at least `#X + #Y - d` elements. -/
lemma exists_subset_card_add_le_card_add {γ₀ α : ℝ} {c₀ t : ℕ}
    (hT : FewTranslatesInt γ₀ (α / 2) c₀) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α)
    (hα₁ : α ≤ 1) (ht : (1 / 2 : ℝ) ^ t ≤ α * γ₀ / 128) (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : (m : ℝ) ≤ α⁻¹ * n)
    (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : (#(Ico b (b + n) \ Y) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hl : 128 ≤ γ₀ * (min (m : ℝ) n / d)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' ≤ (t + 1) * (m / d + 2) ∧ #Y' ≤ d * c₀ ∧
      #X + #Y ≤ #(X' + Y') + d := by
  obtain ⟨r₀, hmax⟩ := Finite.exists_max fun r ↦ #(modFibre d r X)
  have hr₀ := mem_denseRes_of_forall_le hX hXI hl hmax
  choose k F hF hFA using exists_family hT hγ₀ hγ₀₁ hα hα₁ hX hY hαn hαm hl
  choose hFY hFc using hF
  obtain ⟨ξ, -, hξ⟩ := exists_le_of_le_expect (piFinset_nonempty.2 fun _ ↦ ⟨r₀, hr₀⟩)
    (le_expect_card_sampleX_add_sampleY (t := t) (F := F) hr₀ hmax (denseRes_mono (by linarith))
      hFA (fun x hx y hy y' hy' ↦ add_le_card_modFibre_add hX hY hl hx hy hy')
      (fun z ↦ card_filter_sub_notMem_pow_le (card_univ_sdiff_denseRes_le_of_le (by linarith) hXI)
        (card_univ_sdiff_denseRes_le_of_le (by linarith) hYJ) z t)
      (half_pow_mul_card_add_le hX hY hα hα₁ hγ₀ hγ₀₁ hαn hαm ht
        (by linarith [mul_le_self_of_le_mul hγ₀ hγ₀₁ hl]) r₀) (by positivity) (by linarith))
  obtain ⟨ω, -, hω⟩ := exists_le_of_le_expect univ_nonempty hξ
  refine ⟨sampleX d X r₀ ξ, sampleX_subset,
    sampleY d (denseRes d b n Y (γ₀ * (min (m : ℝ) n / d) / 4)) F ω, sampleY_subset hFY,
    card_sampleX_le ?_, (card_sampleY_le hFc).trans ?_, ?_⟩
  · intro r
    rw [← card_modFibre]
    exact (card_le_card (modFibre_mono hX)).trans card_modFibre_Ico_le
  · gcongr
    exact (card_le_univ _).trans (ZMod.card d).le
  · rify
    linarith

/-- If `16 * (t + 1) * (K + 1) * x ≤ c₁ * c₂`, `x` is large and `d` is about `c₂ / (K + 1)`,
then `(t + 1) * (m / d + 2) + (d - 1) ≤ c₁`: the arithmetic of the sizes of the samples
of `X`. -/
lemma add_le_of_mul_le_mul {t K d m c₁ c₂ x : ℕ} (hd : 0 < d) (hK : 1 ≤ K)
    (h₁ : 16 * (t + 1) * (K + 1) * x ≤ c₁ * c₂) (h₂ : m ≤ 2 * x)
    (h₃ : c₂ < (K + 1) * d + (K + 1)) (h₄ : 16 * (t + 1) * (K + 1) ≤ c₂) (h₅ : c₂ ≤ c₁)
    (h₆ : d * (K + 1) ≤ c₂) : (t + 1) * (m / d + 2) + (d - 1) ≤ c₁ := by
  have hA : 4 * (t + 1) * m ≤ d * c₁ := by
    refine Nat.le_of_mul_le_mul_left (c := 2 * (K + 1)) ?_ (by positivity)
    nlinarith [Nat.mul_le_mul_left c₁ (by nlinarith : c₂ ≤ 2 * (K + 1) * d),
      Nat.mul_le_mul_left (8 * (t + 1) * (K + 1)) h₂]
  have hB : 4 * (t + 1) * (m / d) ≤ c₁ := by
    refine Nat.le_of_mul_le_mul_left (c := d) ?_ hd
    nlinarith [Nat.div_mul_le_self m d]
  nlinarith [Nat.sub_le d 1]

/-- Theorem 8 for `c₂ ≤ c₁`, with explicit constants and a given `d` of order `c₂ / (K + 1)`. -/
lemma exists_subset_card_eq_of_le_of_mul_le {γ₀ α : ℝ} {c₀ t K : ℕ}
    (hT : FewTranslatesInt γ₀ (α / 2) c₀) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α)
    (hα₁ : α ≤ 1) (ht : (1 / 2 : ℝ) ^ t ≤ α * γ₀ / 128) (hc₀ : c₀ ≤ K) (hK : 128 / γ₀ ≤ K)
    {c₁ c₂ : ℕ} (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m)
    (hαm : (m : ℝ) ≤ α⁻¹ * n) (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : (#(Ico b (b + n) \ Y) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁X : c₁ ≤ #X)
    (hc₂Y : c₂ ≤ #Y) (hc₂₁ : c₂ ≤ c₁) (h₁ : 16 * (t + 1) * (K + 1) * #X ≤ c₁ * c₂)
    (h₄ : 16 * (t + 1) * (K + 1) ≤ c₂) (hd₁ : d * (K + 1) ≤ c₂)
    (hd₂ : c₂ < (K + 1) * d + (K + 1)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  have hd := Nat.pos_of_neZero d
  obtain ⟨X', hX', Y', hY', hX'c, hY'c, hsum⟩ :=
    exists_subset_card_add_le_card_add hT hγ₀ hγ₀₁ hα hα₁ ht hX hY hαn hαm hXI hYJ
      (le_mul_min_div_of_mul_le hγ₀ hd hK (by grind [card_le_of_subset_Ico hX])
        (by grind [card_le_of_subset_Ico hY]))
  refine exists_subset_card_eq_of_le_card_add (j := d - 1) (card_pos.1 (by grind))
    (card_pos.1 (by grind)) hX' hY' ((Nat.add_le_add_right hX'c _).trans
      (add_le_of_mul_le_mul hd (one_le_of_div_le hγ₀ hγ₀₁ hK) h₁
        (le_two_mul_card hX hγ₀ hγ₀₁ hXI) hd₂ h₄ hc₂₁ hd₁)) hc₁X ?_ hc₂Y (by grind)
  nlinarith [Nat.mul_le_mul_left d hc₀, Nat.sub_le d 1]

/-- Theorem 8 for `c₂ ≤ c₁`, with explicit constants. -/
lemma exists_subset_card_eq_of_le {γ₀ α : ℝ} {c₀ t K : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1)
    (ht : (1 / 2 : ℝ) ^ t ≤ α * γ₀ / 128) (hc₀ : c₀ ≤ K) (hK : 128 / γ₀ ≤ K) {c₁ c₂ : ℕ}
    (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m)
    (hαm : (m : ℝ) ≤ α⁻¹ * n) (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : (#(Ico b (b + n) \ Y) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁X : c₁ ≤ #X)
    (hc₂ : 1 ≤ c₂) (hc₂Y : c₂ ≤ #Y) (hc₂₁ : c₂ ≤ c₁)
    (hc : 16 * ((t : ℝ) + 1) * (K + 1) * #X ≤ c₁ * c₂) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  have h₁ : 16 * (t + 1) * (K + 1) * #X ≤ c₁ * c₂ := by exact_mod_cast hc
  have h₄ : 16 * (t + 1) * (K + 1) ≤ c₂ :=
    Nat.le_of_mul_le_mul_right (h₁.trans (Nat.mul_le_mul_right c₂ hc₁X) |>.trans_eq
      (mul_comm _ _)) (by grind)
  have : NeZero (c₂ / (K + 1)) := ⟨(Nat.div_pos (by nlinarith) (by grind)).ne'⟩
  exact exists_subset_card_eq_of_le_of_mul_le hT hγ₀ hγ₀₁ hα hα₁ ht hc₀ hK hX hY hαn hαm hXI hYJ
    hc₁X hc₂Y hc₂₁ h₁ h₄ (Nat.div_mul_le_self c₂ (K + 1)) (Nat.lt_mul_div_self_add (by grind))

/-- Theorem 8 with explicit constants. -/
lemma exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_fewTranslatesInt {γ₀ α : ℝ}
    {c₀ t K : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1)
    (ht : (1 / 2 : ℝ) ^ t ≤ α * γ₀ / 128) (hc₀ : c₀ ≤ K) (hK : 128 / γ₀ ≤ K) {c₁ c₂ : ℕ}
    (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m)
    (hαm : (m : ℝ) ≤ α⁻¹ * n) (hXI : (#(Ico a (a + m) \ X) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : (#(Ico b (b + n) \ Y) : ℝ) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁ : 1 ≤ c₁)
    (hc₁X : c₁ ≤ #X) (hc₂ : 1 ≤ c₂) (hc₂Y : c₂ ≤ #Y)
    (hc : 16 * ((t : ℝ) + 1) * (K + 1) * max (#X : ℝ) #Y ≤ c₁ * c₂) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  rcases le_total c₂ c₁ with hc₂₁ | hc₁₂
  · exact exists_subset_card_eq_of_le hT hγ₀ hγ₀₁ hα hα₁ ht hc₀ hK hX hY hαn hαm hXI hYJ hc₁X
      hc₂ hc₂Y hc₂₁ ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hc)
  · obtain ⟨Y', hY', X', hX', hY'c, hX'c, hYX⟩ := exists_subset_card_eq_of_le hT hγ₀ hγ₀₁ hα
      hα₁ ht hc₀ hK hY hX ((le_inv_mul_iff₀ hα).1 hαm) ((le_inv_mul_iff₀ hα).2 hαn)
      (by rwa [min_comm (n : ℝ)]) (by rwa [min_comm (n : ℝ)]) hc₂Y hc₁ hc₁X hc₁₂
      ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)).trans
        (hc.trans_eq (mul_comm _ _)))
    exact ⟨X', hX', Y', hY', hX'c, hY'c, by rwa [add_comm #X, add_comm X']⟩

/-- **Theorem 8** of Bollobás, Leader and Tiba for intervals of integers, assuming their
Theorem 5. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico
    (h : FewTranslatesNearIntervals) :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ (a b : ℤ) (m n : ℕ) (X Y : Finset ℤ) (c₁ c₂ : ℕ),
      X ⊆ Ico a (a + m) → Y ⊆ Ico b (b + n) → α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n →
      (#(Ico a (a + m) \ X) : ℝ) ≤ γ * min (m : ℝ) n →
      (#(Ico b (b + n) \ Y) : ℝ) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  obtain ⟨γ₀, hγ₀, hT⟩ := exists_fewTranslates_int h
  refine ⟨min γ₀ 1 / 256, by positivity, ?_⟩
  intro α hα
  obtain ⟨c₀, hc₀⟩ := hT (min α 1 / 2) (by positivity)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < min α 1 * min γ₀ 1 / 128)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨16 * ((t : ℝ) + 1) * (max c₀ ⌈128 / min γ₀ 1⌉₊ + 1), ?_⟩
  intro a b m n X Y c₁ c₂ hX hY hαn hαm hXI hYJ hc₁ hc₁X hc₂ hc₂Y hc
  exact exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_fewTranslatesInt
    (FewTranslatesInt.mono hc₀ (min_le_left _ _)) (by positivity)
    (min_le_right _ _) (by positivity) (min_le_right _ _) ht.le (le_max_left _ _)
    ((Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))) hX hY
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans hαn)
    (hαm.trans (mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (min_le_left _ _))
      (Nat.cast_nonneg _))) hXI hYJ hc₁ hc₁X hc₂ hc₂Y hc

/-! ### Intervals of `ZMod p` -/

section ZMod

variable {p : ℕ} [NeZero p]

/-- The lift `u ↦ (u - x).val` of `ZMod p` to `ℤ`, which maps the interval of length `m` starting
at `x` onto `Ico 0 m`. -/
def liftSub (x u : ZMod p) : ℤ := ((u - x).val : ℤ)

/-- The lift `u ↦ (u - x).val` is injective. -/
lemma liftSub_injective (x : ZMod p) : (liftSub x).Injective :=
  fun _ _ h ↦ sub_left_injective (ZMod.val_injective p (Nat.cast_injective h))

/-- The lift `u ↦ (u - x).val` maps the interval of length `m ≤ p` starting at `x` onto
`Ico 0 m`. -/
lemma image_liftSub_arithProg (x : ZMod p) {m : ℕ} (hm : m ≤ p) :
    (arithProg x 1 m).image (liftSub x) = Ico (0 : ℤ) (0 + m) := by
  ext q
  simp only [mem_image, mem_Ico, liftSub, mem_arithProg_one_iff hm, zero_add]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by positivity, by exact_mod_cast hu⟩
  · rintro ⟨h₀, hq⟩
    refine ⟨x + (q.toNat : ZMod p), ?_, ?_⟩ <;>
      rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by grind)] <;> grind

/-- The lift of a sumset of subsets of intervals `I` and `J` with `#I + #J ≤ p` contains the
sumset of the lifts. -/
lemma card_image_liftSub_add_le {x y : ZMod p} {m n : ℕ} (hmn : m + n ≤ p)
    {X Y : Finset (ZMod p)} (hX : X ⊆ arithProg x 1 m) (hY : Y ⊆ arithProg y 1 n) :
    #(X.image (liftSub x) + Y.image (liftSub y)) ≤ #(X + Y) := by
  refine (card_le_card ?_).trans (card_image_le (f := liftSub (x + y)))
  intro q hq
  obtain ⟨_, hu', _, hv', rfl⟩ := mem_add.1 hq
  obtain ⟨u, hu, rfl⟩ := mem_image.1 hu'
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hv'
  refine mem_image.2 ⟨u + v, add_mem_add hu hv, ?_⟩
  have h₁ := (mem_arithProg_one_iff (by grind)).1 (hX hu)
  have h₂ := (mem_arithProg_one_iff (by grind)).1 (hY hv)
  rw [liftSub, liftSub, liftSub, add_sub_add_comm, ZMod.val_add_of_lt (by grind)]
  push_cast
  rfl

end ZMod

/-- **Theorem 8** of Bollobás, Leader and Tiba, assuming their Theorem 5, for intervals written
as arithmetic progressions. There is `γ > 0` such that for `α > 0` there is `c` with the
following property. Let `X` and `Y` be subsets of intervals `I` and `J` of `ZMod p` with `m` and
`n` elements, `m + n ≤ p`, `α * n ≤ m ≤ α⁻¹ * n`, missing at most `γ * min m n` points of `I`
and of `J`. For `1 ≤ c₁ ≤ #X` and `1 ≤ c₂ ≤ #Y` with `c₁ * c₂ ≥ c * max #X #Y` there are
`X' ⊆ X` and `Y' ⊆ Y` with `c₁` and `c₂` elements and `#(X' + Y') ≥ #X + #Y - 1`. -/
lemma exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg
    (h : FewTranslatesNearIntervals) :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (x y : ZMod p) (m n : ℕ) (X Y : Finset (ZMod p)) (c₁ c₂ : ℕ),
      X ⊆ arithProg x 1 m → Y ⊆ arithProg y 1 n → m + n ≤ p → α * n ≤ m →
      (m : ℝ) ≤ α⁻¹ * n → (#(arithProg x 1 m \ X) : ℝ) ≤ γ * min (m : ℝ) n →
      (#(arithProg y 1 n \ Y) : ℝ) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  obtain ⟨γ, hγ, hZ⟩ := exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico h
  refine ⟨γ, hγ, ?_⟩
  intro α hα
  obtain ⟨c, hc⟩ := hZ α hα
  refine ⟨c, ?_⟩
  intro p hp x y m n X Y c₁ c₂ hX hY hmn hαn hαm hXI hYJ hc₁ hc₁X hc₂ hc₂Y hcc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hXc := card_image_of_injective X (liftSub_injective x)
  have hYc := card_image_of_injective Y (liftSub_injective y)
  obtain ⟨X₁, hX₁, Y₁, hY₁, hX₁c, hY₁c, hsum⟩ := hc 0 0 m n (X.image (liftSub x))
    (Y.image (liftSub y)) c₁ c₂
    ((image_subset_image hX).trans (image_liftSub_arithProg x (by grind)).le)
    ((image_subset_image hY).trans (image_liftSub_arithProg y (by grind)).le) hαn hαm
    (by rwa [← image_liftSub_arithProg x (by grind), ← image_sdiff _ _ (liftSub_injective x),
      card_image_of_injective _ (liftSub_injective x)])
    (by rwa [← image_liftSub_arithProg y (by grind), ← image_sdiff _ _ (liftSub_injective y),
      card_image_of_injective _ (liftSub_injective y)])
    hc₁ (hXc ▸ hc₁X) hc₂ (hYc ▸ hc₂Y) (by rwa [hXc, hYc])
  obtain ⟨X', hX', rfl⟩ := subset_image_iff.1 hX₁
  obtain ⟨Y', hY', rfl⟩ := subset_image_iff.1 hY₁
  rw [card_image_of_injective _ (liftSub_injective x)] at hX₁c
  rw [card_image_of_injective _ (liftSub_injective y)] at hY₁c
  rw [hXc, hYc] at hsum
  exact ⟨X', hX', Y', hY', hX₁c, hY₁c,
    hsum.trans (card_image_liftSub_add_le hmn (hX'.trans hX) (hY'.trans hY))⟩

/-- **Theorem 8** of Bollobás, Leader and Tiba, assuming their Theorem 5. There is $\gamma > 0$
such that for $\alpha > 0$ there is $c$ with the following property. Let $X$ and $Y$ be subsets of
intervals $I$ and $J$ of $\mathbb{Z}_p$ with $m$ and $n$ elements, where $m + n \le p$ and
$\alpha n \le m \le \alpha^{-1} n$, each missing at most $\gamma \min(m, n)$ points of its
interval. If $1 \le c_1 \le |X|$ and $1 \le c_2 \le |Y|$ satisfy $c_1 c_2 \ge c \max(|X|, |Y|)$,
there are $X' \subseteq X$ and $Y' \subseteq Y$ with $c_1$ and $c_2$ elements and
$|X' + Y'| \ge |X| + |Y| - 1$. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range
    (h : FewTranslatesNearIntervals) :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (x y : ZMod p) (m n : ℕ) (X Y : Finset (ZMod p)) (c₁ c₂ : ℕ),
      X ⊆ (range m).image (fun i : ℕ ↦ x + i) → Y ⊆ (range n).image (fun i : ℕ ↦ y + i) →
      m + n ≤ p → α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n →
      (#((range m).image (fun i : ℕ ↦ x + i) \ X) : ℝ) ≤ γ * min (m : ℝ) n →
      (#((range n).image (fun i : ℕ ↦ y + i) \ Y) : ℝ) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  simpa [arithProg_one_eq_image_range] using
    exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg h

end LargeSumsetsFromSubsets
