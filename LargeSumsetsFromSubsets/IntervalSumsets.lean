/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticProgression.Basic
public import LargeSumsetsFromSubsets.IntervalSumsets.FewTranslates
public import LargeSumsetsFromSubsets.IntervalSumsets.ResidueClasses
import LargeSumsetsFromSubsets.IntervalSumsets.Sampling
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

Theorem 8 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized subsets*. There is `γ > 0`
such that for `α > 0` there is `c` with the following property. Let `X ⊆ I` and `Y ⊆ J` miss at most
`γ * min #I #J` points of the intervals `I` and `J`, with `α * #J ≤ #I ≤ α⁻¹ * #J`. Then for
`1 ≤ c₁ ≤ #X` and `1 ≤ c₂ ≤ #Y` with `c₁ * c₂ ≥ c * max #X #Y` there are `X' ⊆ X` and `Y' ⊆ Y` with
`c₁` and `c₂` elements and `#(X' + Y') ≥ #X + #Y - 1`.

With `d` of order `c₂`, the sets are split into their residue classes modulo `d`. The sample of `X`
is the largest class of `X` together with `t` random dense classes. For a dense class `x` of `X` and
a dense class `y` of `Y`, Theorem 5, in the form `FewTranslatesInt` for a single set `A`, gives a
bounded subset `G x y` of the class `y` of `Y` that is good for the class `x`. The paper uses one
family of subsets for each class `y`, good for every `x`. Here the sample of `Y` is the union of the
sets `G x y` over the classes `x` of the sample of `X` and the dense classes `y` of `Y`, which
multiplies its size by `t + 1`. Every class of the sumset is then large in expectation, and `d - 1`
more elements of `X` and of `Y` complete the sumset.

## Main definitions

* `denseResidues d a m X θ`: the residues `r` modulo `d` such that the class `r` of `X` is dense at
  level `θ`, that is, misses at most `θ` points of the class `r` of `Ico a (a + m)`.
* `liftFrom x`: the lift `u ↦ (u - x).val` of `ZMod p` to `ℤ`.

## Main statements

* `exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico`: Theorem 8 in `ℤ`.
* `exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg`: Theorem 8 for
  intervals of `ZMod p` with `#I + #J ≤ p`.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-! ### Elementary bounds -/

/-- If `128 ≤ γ₀ * l` with `0 < γ₀ ≤ 1`, then `γ₀ * l ≤ l`. -/
lemma mul_le_self_of_le_mul {γ₀ l : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hl : 128 ≤ γ₀ * l) :
    γ₀ * l ≤ l :=
  mul_le_of_le_one_left (pos_of_mul_pos_right (by linarith) hγ₀.le).le hγ₀₁

/-- If `128 / γ₀ ≤ K` and `(K + 1) * d` is at most `m` and `n`, then `128 ≤ γ₀ * (min m n / d)`. -/
lemma le_mul_min_div_of_mul_le {γ₀ : ℝ} {K d m n : ℕ} (hγ₀ : 0 < γ₀) (hd : 0 < d)
    (hK : 128 / γ₀ ≤ K) (hm : (K + 1) * d ≤ m) (hn : (K + 1) * d ≤ n) :
    128 ≤ γ₀ * (min (m : ℝ) n / d) := by
  have h : ((K : ℝ) + 1) * d ≤ min (m : ℝ) n := le_min (by exact_mod_cast hm) (by exact_mod_cast hn)
  rw [← le_div_iff₀ (by exact_mod_cast hd)] at h
  rw [div_le_iff₀ hγ₀] at hK
  nlinarith [mul_le_mul_of_nonneg_left h hγ₀.le]

/-- The arithmetic of the hypotheses of Theorem 5 in a dense class. Let `0 < γ₀ ≤ 1`, `0 < α ≤ 1`,
`α * v ≤ u`, `α * u ≤ v` and `128 ≤ γ₀ * min u v`. If `u - 1 ≤ μ ≤ u` and
`v - 2 - γ₀ * min u v / 4 ≤ ν ≤ v + 2`, then `γ₀ * min u v / 4 ≤ γ₀ * min μ ν`, `α / 2 * ν ≤ μ` and
`μ ≤ (α / 2)⁻¹ * ν`. -/
lemma le_mul_min_and_mul_le {α γ₀ u v μ ν : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α)
    (hα₁ : α ≤ 1) (hαv : α * v ≤ u) (hαu : α * u ≤ v) (hl : 128 ≤ γ₀ * min u v) (hμ₁ : u - 1 ≤ μ)
    (hμ₂ : μ ≤ u) (hν₁ : v - 2 - γ₀ * min u v / 4 ≤ ν) (hν₂ : ν ≤ v + 2) :
    γ₀ * min u v / 4 ≤ γ₀ * min μ ν ∧ α / 2 * ν ≤ μ ∧ μ ≤ (α / 2)⁻¹ * ν := by
  have hγl := mul_le_self_of_le_mul hγ₀ hγ₀₁ hl
  refine ⟨?_, by nlinarith [mul_le_mul_of_nonneg_left hν₂ hα.le, min_le_left u v], ?_⟩
  · linarith [mul_le_mul_of_nonneg_left (le_min (by linarith [min_le_left u v])
      (by linarith [min_le_right u v]) : min u v / 4 ≤ min μ ν) hγ₀.le]
  · rw [inv_div, div_mul_eq_mul_div, le_div_iff₀ hα]
    linarith [mul_le_mul_of_nonneg_left hμ₂ hα.le, min_le_right u v]

/-! ### Sizes of the classes -/

variable {d : ℕ} [NeZero d] {a b : ℤ} {m n : ℕ} {X Y : Finset ℤ} {r : ZMod d} {θ : ℝ}

/-- The quotient `m / d` in `ℕ` is within `1` of the quotient in `ℝ`. -/
lemma div_sub_one_le_natCast_div (m : ℕ) : m / d - 1 ≤ ((m / d : ℕ) : ℝ) := by
  rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast Nat.pos_of_neZero d), add_one_mul]
  exact_mod_cast (Nat.lt_div_mul_add (Nat.pos_of_neZero d)).le

omit [NeZero d] in
/-- The condition `α * n ≤ m ≤ α⁻¹ * n` passes to the quotients by `d`. -/
lemma mul_div_le_div_of_mul_le {α : ℝ} (hα : 0 < α) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n) :
    α * (n / d) ≤ m / d ∧ α * (m / d) ≤ n / d := by
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact ⟨by gcongr, by grw [(le_inv_mul_iff₀ hα).1 hαm]⟩

omit [NeZero d] in
/-- A set `X ⊆ Ico a (a + m)` missing at most `γ₀ / 256 * min m n` points of the interval, with
`γ₀ ≤ 1`, has at least `m / 2` elements. -/
lemma le_two_mul_card {γ₀ : ℝ} (hX : X ⊆ Ico a (a + m)) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1)
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n) : m ≤ 2 * #X := by
  rify
  nlinarith [card_Ico_sdiff_add_card hX, min_le_left (m : ℝ) n,
    (by positivity : 0 ≤ min (m : ℝ) n)]

/-- A class of `Ico a (a + m)` modulo `d` has at least `m / d - 2` elements. -/
lemma sub_two_le_card_rescaledClass_Ico :
    (m : ℝ) / d - 2 ≤ #(rescaledClass d r (Ico a (a + m))) := by
  linarith [div_sub_one_le_natCast_div (d := d) m,
    (by exact_mod_cast le_card_rescaledClass_Ico_add_one :
      ((m / d : ℕ) : ℝ) ≤ #(rescaledClass d r (Ico a (a + m))) + 1)]

/-- A class of `Ico a (a + m)` modulo `d` has at most `m / d + 2` elements. -/
lemma card_rescaledClass_Ico_le_add_two :
    (#(rescaledClass d r (Ico a (a + m))) : ℝ) ≤ m / d + 2 := by
  linarith [(Nat.cast_div_le : ((m / d : ℕ) : ℝ) ≤ m / d),
    (by exact_mod_cast card_rescaledClass_Ico_le :
      (#(rescaledClass d r (Ico a (a + m))) : ℝ) ≤ (m / d : ℕ) + 2)]

/-- A class of `X ⊆ Ico a (a + m)` has at most `m / d + 2` elements. -/
lemma card_rescaledClass_le_of_subset_Ico (hX : X ⊆ Ico a (a + m)) :
    (#(rescaledClass d r X) : ℝ) ≤ m / d + 2 := by
  grw [rescaledClass_mono hX]
  exact card_rescaledClass_Ico_le_add_two

/-- The class `r` of `Ico a (a + m)` is the disjoint union of the class `r` of `X` and the points of
the class missed by `X`. -/
lemma card_rescaledClass_sdiff_add (hX : X ⊆ Ico a (a + m)) :
    (#(rescaledClass d r (Ico a (a + m)) \ rescaledClass d r X) : ℝ) + #(rescaledClass d r X) =
      #(rescaledClass d r (Ico a (a + m))) := by
  exact_mod_cast card_sdiff_add_card_eq_card (rescaledClass_mono hX)

/-! ### Dense classes -/

/-- The residues `r` modulo `d` such that the class `r` of `X` is dense at level `θ`: it misses at
most `θ` points of the class `r` of `Ico a (a + m)`. -/
noncomputable def denseResidues (d : ℕ) [NeZero d] (a : ℤ) (m : ℕ) (X : Finset ℤ) (θ : ℝ) :
    Finset (ZMod d) :=
  {r | #(rescaledClass d r (Ico a (a + m)) \ rescaledClass d r X) ≤ θ}

/-- A residue `r` is in `denseResidues d a m X θ` when `X` misses at most `θ` points of the class
`r` of `Ico a (a + m)`. -/
lemma mem_denseResidues : r ∈ denseResidues d a m X θ ↔
    #(rescaledClass d r (Ico a (a + m)) \ rescaledClass d r X) ≤ θ := by
  simp [denseResidues]

/-- More classes are dense for a larger threshold. -/
lemma denseResidues_mono {θ' : ℝ} (h : θ ≤ θ') :
    denseResidues d a m X θ ⊆ denseResidues d a m X θ' :=
  fun _ hr ↦ mem_denseResidues.2 ((mem_denseResidues.1 hr).trans h)

/-- A dense class of `X` has at least `m / d - 2 - θ` elements. -/
lemma le_card_rescaledClass_of_mem_denseResidues (hX : X ⊆ Ico a (a + m))
    (hr : r ∈ denseResidues d a m X θ) : m / d - 2 - θ ≤ #(rescaledClass d r X) := by
  linarith [mem_denseResidues.1 hr, card_rescaledClass_sdiff_add (r := r) hX,
    sub_two_le_card_rescaledClass_Ico (r := r) (a := a) (m := m)]

/-- A class of `X` which is not dense has at most `m / d + 2 - θ` elements. -/
lemma card_rescaledClass_le_of_notMem_denseResidues (hX : X ⊆ Ico a (a + m))
    (hr : r ∉ denseResidues d a m X θ) : #(rescaledClass d r X) ≤ m / d + 2 - θ := by
  rw [mem_denseResidues, not_le] at hr
  linarith [card_rescaledClass_sdiff_add (r := r) hX,
    card_rescaledClass_Ico_le_add_two (r := r) (a := a) (m := m)]

/-- Markov's inequality: few classes are not dense. -/
lemma card_univ_sdiff_denseResidues_le (hθ : 0 < θ) (h : #(Ico a (a + m) \ X) ≤ d * θ / 16) :
    (#(univ \ denseResidues d a m X θ) : ℝ) ≤ d / 16 := by
  refine le_of_mul_le_mul_right ?_ hθ
  grw [div_mul_eq_mul_div, ← h, ← sum_card_rescaledClass (d := d) (Ico a (a + m) \ X),
    ← sum_le_sum_of_subset (subset_univ (univ \ denseResidues d a m X θ)), Nat.cast_sum,
    ← nsmul_eq_mul]
  apply card_nsmul_le_sum
  intro r hr
  simp only [mem_sdiff, mem_univ, mem_denseResidues, not_le, true_and] at hr
  rw [rescaledClass_sdiff]
  exact hr.le

/-- If `X` misses at most `γ₀ / 256 * L` points of `Ico a (a + m)`, at most `d / 16` classes miss
more than `γ₀ * (L / d) / 16` points. -/
lemma card_univ_sdiff_denseResidues_le_of_le {γ₀ L : ℝ} (hL : 0 < γ₀ * (L / d))
    (h : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * L) :
    (#(univ \ denseResidues d a m X (γ₀ * (L / d) / 16)) : ℝ) ≤ d / 16 := by
  apply card_univ_sdiff_denseResidues_le (by positivity)
  convert h using 1
  field_simp [NeZero.ne d]
  ring

/-- If `X ⊆ Ico a (a + m)` misses at most `γ₀ / 256 * L` points of the interval and the class `r₀`
of `X` is the largest, then the class `r₀` has at least `m / d - γ₀ * (L / d) / 256` elements. -/
lemma sub_le_card_rescaledClass_of_forall_le {γ₀ L : ℝ} {r₀ : ZMod d} (hX : X ⊆ Ico a (a + m))
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * L)
    (hmax : ∀ r, #(rescaledClass d r X) ≤ #(rescaledClass d r₀ X)) :
    m / d - γ₀ * (L / d) / 256 ≤ #(rescaledClass d r₀ X) := by
  rw [(by ring : γ₀ * (L / d) / 256 = γ₀ / 256 * L / d), ← sub_div,
    div_le_iff₀ (by exact_mod_cast Nat.pos_of_neZero d)]
  linarith [card_Ico_sdiff_add_card hX, card_le_mul_card_rescaledClass hmax]

/-- The largest class of `X` is dense. -/
lemma mem_denseResidues_of_forall_le {γ₀ : ℝ} {r₀ : ZMod d} (hX : X ⊆ Ico a (a + m))
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n) (hl : 128 ≤ γ₀ * (min (m : ℝ) n / d))
    (hmax : ∀ r, #(rescaledClass d r X) ≤ #(rescaledClass d r₀ X)) :
    r₀ ∈ denseResidues d a m X (γ₀ * (min (m : ℝ) n / d) / 16) := by
  rw [mem_denseResidues]
  linarith [card_rescaledClass_sdiff_add (r := r₀) hX,
    card_rescaledClass_Ico_le_add_two (r := r₀) (a := a) (m := m),
    sub_le_card_rescaledClass_of_forall_le hX hXI hmax]

/-- The classes in `EX` and `EY'` are larger than the classes outside `EY` by `θ / 16`. -/
lemma add_le_card_rescaledClass_add (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n))
    (hθ : 128 ≤ θ) {r₀ x y y' : ZMod d} (hx : x ∈ denseResidues d a m X (θ / 16))
    (hy : y ∈ denseResidues d b n Y (θ / 16)) (hy' : y' ∉ denseResidues d b n Y (θ / 4)) :
    #(rescaledClass d r₀ X) + #(rescaledClass d y' Y) + θ / 16 ≤
      #(rescaledClass d x X) + #(rescaledClass d y Y) := by
  linarith [card_rescaledClass_le_of_subset_Ico (r := r₀) hX,
    card_rescaledClass_le_of_notMem_denseResidues hY hy',
    le_card_rescaledClass_of_mem_denseResidues hX hx,
    le_card_rescaledClass_of_mem_denseResidues hY hy]

/-- For `ξ` uniform in `EX ^ t`, the probability that every `z - ξ i` is outside `EY'` is at most
`2 ^ (-t)`. -/
lemma card_filter_sub_notMem_pow_le {EX EY' : Finset (ZMod d)} (hX : (#(univ \ EX) : ℝ) ≤ d / 16)
    (hY : (#(univ \ EY') : ℝ) ≤ d / 16) (z : ZMod d) (t : ℕ) :
    (#{x ∈ EX | z - x ∉ EY'} : ℝ) ^ t ≤ (1 / 2) ^ t * #EX ^ t := by
  have h : #{x ∈ EX | z - x ∉ EY'} ≤ #(univ \ EY') := by
    refine card_le_card_of_injOn (fun x ↦ z - x) ?_ fun x _ y _ h ↦ sub_right_injective h
    intro x hx
    simp_all
  have hEX : (#(univ \ EX) : ℝ) + #EX = d := by
    exact_mod_cast (card_compl_add_card EX).trans (ZMod.card d)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).2 h]) t

/-- If `α * n ≤ m ≤ α⁻¹ * n` with `α ≤ 1` and `2 ≤ min m n / d`, then `α` times the sum of the sizes
of a class of `X ⊆ Ico a (a + m)` and of a class of `Y ⊆ Ico b (b + n)` is at most
`4 * (min m n / d)`. -/
lemma mul_card_rescaledClass_add_le {α : ℝ} (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n))
    (hα : 0 < α) (hα₁ : α ≤ 1) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n) (hl : 2 ≤ min (m : ℝ) n / d)
    (r y : ZMod d) :
    α * (#(rescaledClass d r X) + #(rescaledClass d y Y)) ≤ 4 * (min (m : ℝ) n / d) := by
  rw [← min_div_div_right (Nat.cast_nonneg d)] at hl ⊢
  obtain ⟨hαv, hαu⟩ := mul_div_le_div_of_mul_le (d := d) hα hαn hαm
  linarith [mul_le_mul_of_nonneg_left
    (add_le_add (card_rescaledClass_le_of_subset_Ico (r := r) hX)
      (card_rescaledClass_le_of_subset_Ico (r := y) hY)) hα.le,
    le_min (mul_le_of_le_one_left (by positivity) hα₁) hαu,
    le_min hαv (mul_le_of_le_one_left (by positivity) hα₁)]

/-- The loss `2 ^ (-t)` on the sizes of two classes is smaller than the gain. -/
lemma half_pow_mul_card_add_le {α γ₀ : ℝ} {t : ℕ} (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n))
    (hα : 0 < α) (hα₁ : α ≤ 1) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (ht : (1 / 2) ^ t ≤ α * γ₀ / 128) (hl : 2 ≤ min (m : ℝ) n / d) (r y : ZMod d) :
    (1 / 2) ^ t * (#(rescaledClass d r X) + #(rescaledClass d y Y)) ≤
      (1 - (1 / 2) ^ t) * (γ₀ * (min (m : ℝ) n / d) / 16) := by
  nlinarith [mul_le_mul_of_nonneg_right ht
      (by positivity : (0 : ℝ) ≤ #(rescaledClass d r X) + #(rescaledClass d y Y)),
    mul_le_mul_of_nonneg_left (mul_card_rescaledClass_add_le hX hY hα hα₁ hαn hαm hl r y) hγ₀.le,
    mul_le_mul_of_nonneg_right (by nlinarith : (1 / 2 : ℝ) ^ t ≤ 1 / 128)
      (by positivity : 0 ≤ γ₀ * (min (m : ℝ) n / d))]

/-! ### The subsets given by Theorem 5 -/

/-- A dense class `y` of `Y ⊆ Ico b (b + n)` lies in an interval of length `n'` with
`n / d - 2 - θ ≤ n' ≤ n / d + 2` whose endpoints belong to the class and of which the class misses
at most `θ` points. -/
lemma exists_Ico_of_mem_denseResidues {y : ZMod d} (hY : Y ⊆ Ico b (b + n))
    (hy : y ∈ denseResidues d b n Y θ) (hθ : θ < n / d - 2) :
    ∃ (y₀ : ℤ) (n' : ℕ), rescaledClass d y Y ⊆ Ico y₀ (y₀ + n') ∧ y₀ ∈ rescaledClass d y Y ∧
      y₀ + n' - 1 ∈ rescaledClass d y Y ∧ n / d - 2 - θ ≤ n' ∧ (n' : ℝ) ≤ n / d + 2 ∧
      #(Ico y₀ (y₀ + n') \ rescaledClass d y Y) ≤ θ := by
  have hYy := le_card_rescaledClass_of_mem_denseResidues hY hy
  obtain ⟨y₀, n', hB, hy₀, hy₁, hn₂, hn₁, hmiss⟩ := exists_Ico_subset_rescaledClass_Ico
    (card_pos.1 ((Nat.cast_pos (α := ℝ)).1 (by linarith))) (rescaledClass_mono hY)
  refine ⟨y₀, n', hB, hy₀, hy₁, ?_, ?_, ?_⟩
  · grw [hYy, hn₂]
  · grw [hn₁]
    exact card_rescaledClass_Ico_le_add_two
  · grw [hmiss]
    exact mem_denseResidues.1 hy

/-- For a dense class `y` of `Y` and a dense class `x` of `X`, Theorem 5 gives a subset of the class
`y` of `Y` with at most `c₀` elements whose sumset with the class `x` of `X` has at least
`#(rescaledClass d x X) + #(rescaledClass d y Y) - 1` elements. -/
lemma exists_subset_of_mem_denseResidues {γ₀ α : ℝ} {c₀ : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (hl₀ : 128 ≤ γ₀ * (min (m : ℝ) n / d)) {x y : ZMod d}
    (hy : y ∈ denseResidues d b n Y (γ₀ * (min (m : ℝ) n / d) / 4))
    (hx : x ∈ denseResidues d a m X (γ₀ * (min (m : ℝ) n / d) / 16)) :
    ∃ G ⊆ rescaledClass d y Y, #G ≤ c₀ ∧
      #(rescaledClass d x X) + #(rescaledClass d y Y) - 1 ≤ (#(rescaledClass d x X + G) : ℝ) := by
  rw [← min_div_div_right (Nat.cast_nonneg d)] at hl₀ hy hx
  obtain ⟨hαv, hαu⟩ := mul_div_le_div_of_mul_le (d := d) hα hαn hαm
  obtain ⟨y₀, n', hB, hy₀, hy₁, hn'₁, hn'₂, hmiss⟩ := exists_Ico_of_mem_denseResidues hY hy
    (by linarith [mul_le_self_of_le_mul hγ₀ hγ₀₁ hl₀, min_le_right ((m : ℝ) / d) (n / d)])
  obtain ⟨hmin, hμν, hνμ⟩ := le_mul_min_and_mul_le hγ₀ hγ₀₁ hα hα₁ hαv hαu hl₀
    (div_sub_one_le_natCast_div m) Nat.cast_div_le hn'₁ hn'₂
  refine hT (a / d) y₀ (m / d) n' 2 _ hμν hνμ hB hy₀ hy₁ (hmiss.trans hmin) _ ?_ ?_
  · grw [rescaledClass_mono hX, rescaledClass_Ico_subset]
    exact Ico_subset_Ico (by grind) (by grind)
  · grw [card_symmDiff_Ico_le (rescaledClass_mono (r := x) hX), ← hmin]
    push_cast
    linarith [mem_denseResidues.1 hx]

/-- For all residues `x` and `y` there is a subset of the class `y` of `Y` with at most `c₀`
elements, which is good for the class `x` of `X` when both classes are dense. -/
lemma exists_subset_rescaledClass {γ₀ α : ℝ} {c₀ : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (hl₀ : 128 ≤ γ₀ * (min (m : ℝ) n / d)) (x y : ZMod d) :
    ∃ G ⊆ rescaledClass d y Y, #G ≤ c₀ ∧
      (y ∈ denseResidues d b n Y (γ₀ * (min (m : ℝ) n / d) / 4) →
        x ∈ denseResidues d a m X (γ₀ * (min (m : ℝ) n / d) / 16) →
          #(rescaledClass d x X) + #(rescaledClass d y Y) - 1 ≤
            (#(rescaledClass d x X + G) : ℝ)) := by
  by_cases h : y ∈ denseResidues d b n Y (γ₀ * (min (m : ℝ) n / d) / 4) ∧
      x ∈ denseResidues d a m X (γ₀ * (min (m : ℝ) n / d) / 16)
  · obtain ⟨hy, hx⟩ := h
    obtain ⟨G, hG, hGc, hGA⟩ :=
      exists_subset_of_mem_denseResidues hT hγ₀ hγ₀₁ hα hα₁ hX hY hαn hαm hl₀ hy hx
    exact ⟨G, hG, hGc, fun _ _ ↦ hGA⟩
  · exact ⟨∅, empty_subset _, by simp, fun hy hx ↦ absurd ⟨hy, hx⟩ h⟩

/-! ### The samples -/

/-- If `min m n / d` is large, there are `X' ⊆ X` with at most `(t + 1) * (m / d + 2)` elements and
`Y' ⊆ Y` with at most `d * ((t + 1) * c₀)` elements whose sumset has at least `#X + #Y - d`
elements. -/
lemma exists_subset_card_add_le_card_add {γ₀ α : ℝ} {c₀ t : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (ht : (1 / 2) ^ t ≤ α * γ₀ / 128)
    (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : #(Ico b (b + n) \ Y) ≤ γ₀ / 256 * min (m : ℝ) n) (hl : 128 ≤ γ₀ * (min (m : ℝ) n / d)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' ≤ (t + 1) * (m / d + 2) ∧ #Y' ≤ d * ((t + 1) * c₀) ∧
      #X + #Y ≤ #(X' + Y') + d := by
  obtain ⟨r₀, hmax⟩ := Finite.exists_max fun r ↦ #(rescaledClass d r X)
  have hr₀ := mem_denseResidues_of_forall_le hX hXI hl hmax
  choose G hGY hGc hGA using exists_subset_rescaledClass hT hγ₀ hγ₀₁ hα hα₁ hX hY hαn hαm hl
  obtain ⟨ξ, -, hξ⟩ := exists_le_of_le_expect (piFinset_nonempty.2 fun _ ↦ ⟨r₀, hr₀⟩)
    (le_expect_card_sampleX_add_sampleY (t := t) (G := G) hr₀ hmax
      (denseResidues_mono (by linarith)) (fun y hy x hx ↦ hGA x y hy hx)
      (fun x hx y hy y' hy' ↦ add_le_card_rescaledClass_add hX hY hl hx hy hy')
      (fun z ↦ card_filter_sub_notMem_pow_le
        (card_univ_sdiff_denseResidues_le_of_le (by linarith) hXI)
        (card_univ_sdiff_denseResidues_le_of_le (by linarith) hYJ) z t)
      (half_pow_mul_card_add_le hX hY hα hα₁ hγ₀ hγ₀₁ hαn hαm ht
        (by linarith [mul_le_self_of_le_mul hγ₀ hγ₀₁ hl]) r₀) (by positivity) (by linarith))
  refine ⟨sampleX d X r₀ ξ, sampleX_subset,
    sampleY d (denseResidues d b n Y (γ₀ * (min (m : ℝ) n / d) / 4)) G r₀ ξ, sampleY_subset hGY,
    card_sampleX_le ?_, ?_, ?_⟩
  · intro r
    rw [← card_rescaledClass]
    grw [rescaledClass_mono hX]
    exact card_rescaledClass_Ico_le
  · grw [card_sampleY_le hGc, card_le_univ, ZMod.card]
  · rify
    linarith

/-- If `16 * (t + 1) * (K + 1) * x ≤ c₁ * c₂`, `x` is large and `d` is about `c₂ / (K + 1)`, then
`(t + 1) * (m / d + 2) + (d - 1) ≤ c₁`: the arithmetic of the sizes of the samples of `X`. -/
lemma add_le_of_mul_le_mul {t K d m c₁ c₂ x : ℕ} (hd : 0 < d) (hK : 1 ≤ K)
    (h₁ : 16 * (t + 1) * (K + 1) * x ≤ c₁ * c₂) (h₂ : m ≤ 2 * x) (h₃ : c₂ < (K + 1) * d + (K + 1))
    (h₄ : 16 * (t + 1) * (K + 1) ≤ c₂) (h₅ : c₂ ≤ c₁) (h₆ : d * (K + 1) ≤ c₂) :
    (t + 1) * (m / d + 2) + (d - 1) ≤ c₁ := by
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
    (hT : FewTranslatesInt γ₀ (α / 2) c₀) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1)
    (ht : (1 / 2) ^ t ≤ α * γ₀ / 128) (hc₀ : (t + 1) * c₀ ≤ K) (hK : 128 / γ₀ ≤ K) {c₁ c₂ : ℕ}
    (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : #(Ico b (b + n) \ Y) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁X : c₁ ≤ #X) (hc₂Y : c₂ ≤ #Y)
    (hc₂₁ : c₂ ≤ c₁) (h₁ : 16 * (t + 1) * (K + 1) * #X ≤ c₁ * c₂) (h₄ : 16 * (t + 1) * (K + 1) ≤ c₂)
    (hd₁ : d * (K + 1) ≤ c₂) (hd₂ : c₂ < (K + 1) * d + (K + 1)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  have hd := Nat.pos_of_neZero d
  obtain ⟨X', hX', Y', hY', hX'c, hY'c, hsum⟩ :=
    exists_subset_card_add_le_card_add hT hγ₀ hγ₀₁ hα hα₁ ht hX hY hαn hαm hXI hYJ
      (le_mul_min_div_of_mul_le hγ₀ hd hK (by grind [card_le_of_subset_Ico hX])
        (by grind [card_le_of_subset_Ico hY]))
  refine exists_subset_card_eq_of_le_card_add (j := d - 1) (card_pos.1 (by grind))
    (card_pos.1 (by grind)) hX' hY' ?_ hc₁X ?_ hc₂Y (by grind)
  · grw [hX'c]
    exact add_le_of_mul_le_mul hd
      (by exact_mod_cast ((one_le_div hγ₀).2 (by linarith)).trans hK) h₁
      (le_two_mul_card hX hγ₀ hγ₀₁ hXI) hd₂ h₄ hc₂₁ hd₁
  · nlinarith [Nat.mul_le_mul_left d hc₀, Nat.sub_le d 1]

/-- Theorem 8 for `c₂ ≤ c₁`, with explicit constants. -/
lemma exists_subset_card_eq_of_le {γ₀ α : ℝ} {c₀ t K : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀)
    (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α) (hα₁ : α ≤ 1) (ht : (1 / 2) ^ t ≤ α * γ₀ / 128)
    (hc₀ : (t + 1) * c₀ ≤ K) (hK : 128 / γ₀ ≤ K) {c₁ c₂ : ℕ} (hX : X ⊆ Ico a (a + m))
    (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m) (hαm : m ≤ α⁻¹ * n)
    (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : #(Ico b (b + n) \ Y) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁X : c₁ ≤ #X) (hc₂ : 1 ≤ c₂)
    (hc₂Y : c₂ ≤ #Y) (hc₂₁ : c₂ ≤ c₁) (hc : 16 * ((t : ℝ) + 1) * (K + 1) * #X ≤ c₁ * c₂) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  have h₁ : 16 * (t + 1) * (K + 1) * #X ≤ c₁ * c₂ := by exact_mod_cast hc
  have h₄ : 16 * (t + 1) * (K + 1) ≤ c₂ := by nlinarith
  have : NeZero (c₂ / (K + 1)) := ⟨(Nat.div_pos (by nlinarith) (by grind)).ne'⟩
  exact exists_subset_card_eq_of_le_of_mul_le hT hγ₀ hγ₀₁ hα hα₁ ht hc₀ hK hX hY hαn hαm hXI hYJ
    hc₁X hc₂Y hc₂₁ h₁ h₄ (Nat.div_mul_le_self c₂ (K + 1)) (Nat.lt_mul_div_self_add (by grind))

/-- Theorem 8 with explicit constants. -/
lemma exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_fewTranslatesInt {γ₀ α : ℝ}
    {c₀ t K : ℕ} (hT : FewTranslatesInt γ₀ (α / 2) c₀) (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ 1) (hα : 0 < α)
    (hα₁ : α ≤ 1) (ht : (1 / 2) ^ t ≤ α * γ₀ / 128) (hc₀ : (t + 1) * c₀ ≤ K) (hK : 128 / γ₀ ≤ K)
    {c₁ c₂ : ℕ} (hX : X ⊆ Ico a (a + m)) (hY : Y ⊆ Ico b (b + n)) (hαn : α * n ≤ m)
    (hαm : m ≤ α⁻¹ * n) (hXI : #(Ico a (a + m) \ X) ≤ γ₀ / 256 * min (m : ℝ) n)
    (hYJ : #(Ico b (b + n) \ Y) ≤ γ₀ / 256 * min (m : ℝ) n) (hc₁ : 1 ≤ c₁) (hc₁X : c₁ ≤ #X)
    (hc₂ : 1 ≤ c₂) (hc₂Y : c₂ ≤ #Y) (hc : 16 * (t + 1) * (K + 1) * max (#X : ℝ) #Y ≤ c₁ * c₂) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  rcases le_total c₂ c₁ with hc₂₁ | hc₁₂
  · exact exists_subset_card_eq_of_le hT hγ₀ hγ₀₁ hα hα₁ ht hc₀ hK hX hY hαn hαm hXI hYJ hc₁X
      hc₂ hc₂Y hc₂₁ (by grw [le_max_left (#X : ℝ) #Y, hc])
  · obtain ⟨Y', hY', X', hX', hY'c, hX'c, hYX⟩ := exists_subset_card_eq_of_le hT hγ₀ hγ₀₁ hα
      hα₁ ht hc₀ hK hY hX ((le_inv_mul_iff₀ hα).1 hαm) ((le_inv_mul_iff₀ hα).2 hαn)
      (by rwa [min_comm (n : ℝ)]) (by rwa [min_comm (n : ℝ)]) hc₂Y hc₁ hc₁X hc₁₂
      (by grw [le_max_right (#X : ℝ) #Y, hc, mul_comm])
    exact ⟨X', hX', Y', hY', hX'c, hY'c, by rwa [add_comm #X, add_comm X']⟩

/-- **Theorem 8** of Bollobás, Leader and Tiba for intervals of integers. -/
lemma exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ (a b : ℤ) (m n : ℕ) (X Y : Finset ℤ) (c₁ c₂ : ℕ),
      X ⊆ Ico a (a + m) → Y ⊆ Ico b (b + n) → α * n ≤ m → m ≤ α⁻¹ * n →
      #(Ico a (a + m) \ X) ≤ γ * min (m : ℝ) n → #(Ico b (b + n) \ Y) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  obtain ⟨γ₀, hγ₀, hT⟩ := exists_fewTranslatesInt
  refine ⟨min γ₀ 1 / 256, by positivity, ?_⟩
  intro α hα
  obtain ⟨c₀, hc₀⟩ := hT (min α 1 / 2) (by positivity)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < min α 1 * min γ₀ 1 / 128)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨16 * (t + 1) * (max ((t + 1) * c₀) ⌈128 / min γ₀ 1⌉₊ + 1), ?_⟩
  intro a b m n X Y c₁ c₂ hX hY hαn hαm hXI hYJ hc₁ hc₁X hc₂ hc₂Y hc
  exact exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_fewTranslatesInt
    (hc₀.mono (min_le_left _ _)) (by positivity) (min_le_right _ _) (by positivity)
    (min_le_right _ _) ht.le (le_max_left _ _) (Nat.ceil_le.1 (le_max_right _ _)) hX hY
    (by grw [min_le_left α 1, hαn]) (by grw [hαm, min_le_left α 1]) hXI hYJ hc₁ hc₁X hc₂ hc₂Y hc

/-! ### Intervals of `ZMod p` -/

section ZMod

variable {p : ℕ} [NeZero p]

/-- The lift `u ↦ (u - x).val` of `ZMod p` to `ℤ`, which maps the interval of length `m` starting at
`x` onto `Ico 0 m`. -/
def liftFrom (x u : ZMod p) : ℤ := ((u - x).val : ℤ)

/-- The lift `u ↦ (u - x).val` is injective. -/
lemma liftFrom_injective (x : ZMod p) : (liftFrom x).Injective :=
  fun _ _ h ↦ sub_left_injective (ZMod.val_injective p (Nat.cast_injective h))

/-- The lift `u ↦ (u - x).val` maps the interval of `ZMod p` of length `m ≤ p` starting at `x` onto
`Ico 0 m`. -/
lemma image_liftFrom_arithProg (x : ZMod p) {m : ℕ} (hm : m ≤ p) :
    (arithProg x 1 m).image (liftFrom x) = Ico (0 : ℤ) (0 + m) := by
  ext q
  simp only [mem_image, mem_Ico, liftFrom, mem_arithProg_one_iff hm, zero_add]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by positivity, by exact_mod_cast hu⟩
  · rintro ⟨h₀, hq⟩
    refine ⟨x + (q.toNat : ZMod p), ?_, ?_⟩ <;>
      rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by grind)] <;> grind

/-- The lift of a subset of the interval of length `m ≤ p` starting at `x` lies in `Ico 0 m`. -/
lemma image_liftFrom_subset_Ico {x : ZMod p} {m : ℕ} (hm : m ≤ p) {X : Finset (ZMod p)}
    (hX : X ⊆ arithProg x 1 m) : X.image (liftFrom x) ⊆ Ico (0 : ℤ) (0 + m) := by
  grw [hX, image_liftFrom_arithProg x hm]

/-- The lift of `X` misses as many points of `Ico 0 m` as `X` misses of the interval of length
`m ≤ p` starting at `x`. -/
lemma card_Ico_sdiff_image_liftFrom (x : ZMod p) {m : ℕ} (hm : m ≤ p) (X : Finset (ZMod p)) :
    #(Ico (0 : ℤ) (0 + m) \ X.image (liftFrom x)) = #(arithProg x 1 m \ X) := by
  rw [← image_liftFrom_arithProg x hm, ← image_sdiff _ _ (liftFrom_injective x),
    card_image_of_injective _ (liftFrom_injective x)]

/-- The lift of a sumset of subsets of intervals `I` and `J` with `#I + #J ≤ p` contains the sumset
of the lifts. -/
lemma card_image_liftFrom_add_le {x y : ZMod p} {m n : ℕ} (hmn : m + n ≤ p) {X Y : Finset (ZMod p)}
    (hX : X ⊆ arithProg x 1 m) (hY : Y ⊆ arithProg y 1 n) :
    #(X.image (liftFrom x) + Y.image (liftFrom y)) ≤ #(X + Y) := by
  grw [← card_image_le (s := X + Y) (f := liftFrom (x + y))]
  apply card_le_card
  intro q hq
  obtain ⟨_, hu', _, hv', rfl⟩ := mem_add.1 hq
  obtain ⟨u, hu, rfl⟩ := mem_image.1 hu'
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hv'
  refine mem_image.2 ⟨u + v, add_mem_add hu hv, ?_⟩
  have h₁ := (mem_arithProg_one_iff (by grind)).1 (hX hu)
  have h₂ := (mem_arithProg_one_iff (by grind)).1 (hY hv)
  rw [liftFrom, liftFrom, liftFrom, add_sub_add_comm, ZMod.val_add_of_lt (by grind)]
  push_cast
  rfl

end ZMod

/-- **Theorem 8** of Bollobás, Leader and Tiba, for intervals written as arithmetic progressions.
There is `γ > 0` such that for `α > 0` there is `c` with the following property. Let `X` and `Y` be
subsets of intervals `I` and `J` of `ZMod p` with `m` and `n` elements, `m + n ≤ p`,
`α * n ≤ m ≤ α⁻¹ * n`, missing at most `γ * min m n` points of `I` and of `J`. For `1 ≤ c₁ ≤ #X` and
`1 ≤ c₂ ≤ #Y` with `c₁ * c₂ ≥ c * max #X #Y` there are `X' ⊆ X` and `Y' ⊆ Y` with `c₁` and `c₂`
elements and `#(X' + Y') ≥ #X + #Y - 1`. -/
lemma exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_arithProg :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (x y : ZMod p) (m n : ℕ) (X Y : Finset (ZMod p)) (c₁ c₂ : ℕ),
      X ⊆ arithProg x 1 m → Y ⊆ arithProg y 1 n → m + n ≤ p → α * n ≤ m → m ≤ α⁻¹ * n →
      #(arithProg x 1 m \ X) ≤ γ * min (m : ℝ) n → #(arithProg y 1 n \ Y) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') := by
  obtain ⟨γ, hγ, hZ⟩ := exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_Ico
  refine ⟨γ, hγ, ?_⟩
  intro α hα
  obtain ⟨c, hc⟩ := hZ α hα
  refine ⟨c, ?_⟩
  intro p hp x y m n X Y c₁ c₂ hX hY hmn hαn hαm hXI hYJ hc₁ hc₁X hc₂ hc₂Y hcc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hXc := card_image_of_injective X (liftFrom_injective x)
  have hYc := card_image_of_injective Y (liftFrom_injective y)
  obtain ⟨X₁, hX₁, Y₁, hY₁, hX₁c, hY₁c, hsum⟩ := hc 0 0 m n (X.image (liftFrom x))
    (Y.image (liftFrom y)) c₁ c₂ (image_liftFrom_subset_Ico (by grind) hX)
    (image_liftFrom_subset_Ico (by grind) hY) hαn hαm
    (by rwa [card_Ico_sdiff_image_liftFrom x (by grind)])
    (by rwa [card_Ico_sdiff_image_liftFrom y (by grind)])
    hc₁ (hXc ▸ hc₁X) hc₂ (hYc ▸ hc₂Y) (by rwa [hXc, hYc])
  obtain ⟨X', hX', rfl⟩ := subset_image_iff.1 hX₁
  obtain ⟨Y', hY', rfl⟩ := subset_image_iff.1 hY₁
  refine ⟨X', hX', Y', hY', by rwa [card_image_of_injective _ (liftFrom_injective x)] at hX₁c,
    by rwa [card_image_of_injective _ (liftFrom_injective y)] at hY₁c, ?_⟩
  grw [← hXc, ← hYc, hsum, card_image_liftFrom_add_le hmn (hX'.trans hX) (hY'.trans hY)]

end LargeSumsetsFromSubsets
