/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.IntervalSumsets.Fibers
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Samples of residue classes with large sumsets

The probabilistic heart of Theorem 8 of Bollobás, Leader and Tiba, *Large sumsets from medium-sized
subsets* (their Lemma on the families `𝓕` and `𝓖`), in an abstract form.

Fix `d ≥ 1`, sets `X` and `Y` of integers, sets `EX` and `EY' ⊆ E` of residues modulo `d`, a residue
`r₀ ∈ EX` and, for all residues `x` and `y`, a subset `G x y` of the rescaled class
`modFiber d y Y`. The sample of `X` for `ξ : Fin t → ZMod d` is the union of the classes `r₀` and
`ξ i` of `X`. The sample of `Y` for `ξ` is the union over `y ∈ E` of the sets `G x y` for the
classes `x` of the sample of `X`, put back in the class `y`. Suppose that
`#(modFiber d x X) + #(modFiber d y Y) - 1 ≤ #(modFiber d x X + G x y)` for `x ∈ EX` and `y ∈ E`,
and that the classes in `EX` and `EY'` are larger than the others by a margin `g`. Then for `ξ`
uniform in `EX ^ t` the expected size of the sumset of the samples is at least `#X + #Y - d`.

In the paper the sample of `Y` is drawn from families given by Theorem 5, which depend only on the
classes of `Y`. Here the sample of `Y` depends on the sample of `X`. This multiplies its size by
`t + 1`, and needs only one set `G x y` for each pair of classes.

The file also proves the two padding facts used to complete samples: in `ℤ`, `j` more elements of
each set raise the size of a sumset to `#X + #Y - 1` when it misses that by `j`, and supersets of
prescribed sizes have larger sumsets.

## Main definitions

* `sampleX`: the sample of `X`.
* `sampleY`: the sample of `Y` adapted to the sample of `X`.

## Main statements

* `le_expect_card_sampleX_add_sampleY`: the expected size of the sumset of the samples is at least
  `#X + #Y - d`.
* `exists_subset_card_eq_of_le_card_add`: padding samples to prescribed sizes.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

/-! ### Padding -/

/-- If `X' + Y'` misses `#X + #Y - 1` by at most `j`, then adding at most `j` elements of `X` to
`X'` and of `Y` to `Y'` gives a sumset of size at least `#X + #Y - 1`. -/
lemma exists_superset_card_add_le_card_add {X Y X' Y' : Finset ℤ} (hX : X.Nonempty)
    (hY : Y.Nonempty) (j : ℕ) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (h : #X + #Y ≤ #(X' + Y') + j + 1) :
    ∃ X'' Y'', X' ⊆ X'' ∧ X'' ⊆ X ∧ #X'' ≤ #X' + j ∧ Y' ⊆ Y'' ∧ Y'' ⊆ Y ∧
      #Y'' ≤ #Y' + j ∧ #X + #Y ≤ #(X'' + Y'') + 1 := by
  induction j generalizing X' Y' with
  | zero => exact ⟨X', Y', subset_rfl, hX', le_rfl, subset_rfl, hY', le_rfl, h⟩
  | succ j ih =>
    by_cases h' : #X + #Y ≤ #(X' + Y') + 1
    · exact ⟨X', Y', subset_rfl, hX', by grind, subset_rfl, hY', by grind, h'⟩
    obtain ⟨s, hs, hs'⟩ : ∃ s ∈ X + Y, s ∉ X' + Y' := by
      by_contra! hc
      grind [card_le_card hc, cauchy_davenport_add_of_linearOrder_isCancelAdd hX hY]
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hs
    have hcard := card_le_card (insert_subset
      (add_mem_add (mem_insert_self x X') (mem_insert_self y Y'))
      (add_subset_add (subset_insert _ _) (subset_insert _ _)))
    rw [card_insert_of_notMem hs'] at hcard
    obtain ⟨X'', Y'', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
      ih (insert_subset hx hX') (insert_subset hy hY') (by grind)
    exact ⟨X'', Y'', (subset_insert _ _).trans h₁, h₂, by grind [card_insert_le],
      (subset_insert _ _).trans h₄, h₅, by grind [card_insert_le], h₇⟩

/-- Subsets `X' ⊆ X` and `Y' ⊆ Y` with `#X' + j ≤ c₁ ≤ #X`, `#Y' + j ≤ c₂ ≤ #Y` and
`#X + #Y ≤ #(X' + Y') + j + 1` extend to subsets of sizes `c₁` and `c₂` whose sumset has at least
`#X + #Y - 1` elements. -/
lemma exists_subset_card_eq_of_le_card_add {X Y X' Y' : Finset ℤ} {c₁ c₂ j : ℕ} (hX : X.Nonempty)
    (hY : Y.Nonempty) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (hc₁ : #X' + j ≤ c₁) (hc₁X : c₁ ≤ #X)
    (hc₂ : #Y' + j ≤ c₂) (hc₂Y : c₂ ≤ #Y) (h : #X + #Y ≤ #(X' + Y') + j + 1) :
    ∃ X'' ⊆ X, ∃ Y'' ⊆ Y, #X'' = c₁ ∧ #Y'' = c₂ ∧ #X + #Y - 1 ≤ #(X'' + Y'') := by
  obtain ⟨X₁, Y₁, -, hX₁, hX₁c, -, hY₁, hY₁c, h₁⟩ :=
    exists_superset_card_add_le_card_add hX hY j hX' hY' h
  obtain ⟨X₂, hX₁₂, hX₂, hX₂c⟩ := exists_subsuperset_card_eq hX₁ (by grind) hc₁X
  obtain ⟨Y₂, hY₁₂, hY₂, hY₂c⟩ := exists_subsuperset_card_eq hY₁ (by grind) hc₂Y
  exact ⟨X₂, hX₂, Y₂, hY₂, hX₂c, hY₂c, by grind [card_le_card (add_subset_add hX₁₂ hY₁₂)]⟩

/-! ### Expectations -/

/-- A nonnegative function which is at least `V` outside `t ⊆ s` has expectation over `s` at least
`(#s - #t) / #s * V`. -/
lemma mul_le_expect_of_le_of_mem_sdiff {ι : Type*} [DecidableEq ι] {s t : Finset ι} {f : ι → ℝ}
    {V : ℝ} (hts : t ⊆ s) (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s \ t, V ≤ f i) :
    (#s - #t) / #s * V ≤ 𝔼 i ∈ s, f i := by
  rw [Finset.expect_eq_sum_div_card, div_mul_eq_mul_div]
  gcongr
  rw [← Nat.cast_sub (card_le_card hts), ← card_sdiff_of_subset hts, ← nsmul_eq_mul]
  grw [card_nsmul_le_sum _ _ _ hf]
  apply sum_le_sum_of_subset_of_nonneg sdiff_subset
  intro i hi _
  exact hf₀ i hi

/-! ### The samples -/

variable {d t : ℕ} {X Y : Finset ℤ} {r₀ : ZMod d} {ξ : Fin t → ZMod d}

/-- The sample of `X`: the union of the classes `r₀` and `ξ i` of `X` modulo `d`. -/
def sampleX (d : ℕ) (X : Finset ℤ) (r₀ : ZMod d) (ξ : Fin t → ZMod d) : Finset ℤ :=
  modClass d r₀ X ∪ univ.biUnion fun i ↦ modClass d (ξ i) X

/-- The sample of `X` is a subset of `X`. -/
lemma sampleX_subset : sampleX d X r₀ ξ ⊆ X :=
  union_subset (modClass_subset _ _) (biUnion_subset.2 fun _ _ ↦ modClass_subset _ _)

/-- The class `r₀` of `X` lies in every sample of `X`. -/
lemma modClass_subset_sampleX_left : modClass d r₀ X ⊆ sampleX d X r₀ ξ :=
  subset_union_left

/-- The class `ξ i` of `X` lies in the sample of `X` for `ξ`. -/
lemma modClass_subset_sampleX (i : Fin t) : modClass d (ξ i) X ⊆ sampleX d X r₀ ξ :=
  (subset_biUnion_of_mem (fun i ↦ modClass d (ξ i) X) (mem_univ i)).trans subset_union_right

/-- If the classes of `X` have at most `M` elements, a sample of `X` has at most `(t + 1) * M`. -/
lemma card_sampleX_le {M : ℕ} (h : ∀ r, #(modClass d r X) ≤ M) :
    #(sampleX d X r₀ ξ) ≤ (t + 1) * M := by
  rw [sampleX]
  grw [card_union_le, card_biUnion_le, sum_le_card_nsmul univ _ M fun i _ ↦ h _, h r₀]
  grind [card_univ, Fintype.card_fin, smul_eq_mul]

/-- The classes of `X` in the sample for `ξ`: `r₀` and the `ξ i`. -/
def sampleRes (r₀ : ZMod d) (ξ : Fin t → ZMod d) : Finset (ZMod d) := insert r₀ (univ.image ξ)

/-- The class `r₀` is in the sample of `X`. -/
lemma mem_sampleRes_self : r₀ ∈ sampleRes r₀ ξ := mem_insert_self _ _

/-- The classes `ξ i` are in the sample of `X`. -/
lemma mem_sampleRes (i : Fin t) : ξ i ∈ sampleRes r₀ ξ :=
  mem_insert_of_mem (mem_image_of_mem ξ (mem_univ i))

/-- The sample of `X` has at most `t + 1` classes. -/
lemma card_sampleRes_le : #(sampleRes r₀ ξ) ≤ t + 1 := by
  grw [sampleRes, card_insert_le, card_image_le, card_univ, Fintype.card_fin]

variable {E EX EY' : Finset (ZMod d)} {G : ZMod d → ZMod d → Finset ℤ}

/-- The sample of `Y` adapted to the sample `ξ` of `X`: for each `y ∈ E`, the union of the sets
`G x y` over the classes `x` of the sample of `X`, put back in the class `y`. -/
def sampleY (d : ℕ) (E : Finset (ZMod d)) (G : ZMod d → ZMod d → Finset ℤ) (r₀ : ZMod d)
    (ξ : Fin t → ZMod d) : Finset ℤ :=
  E.biUnion fun y ↦ modLift d y ((sampleRes r₀ ξ).biUnion fun x ↦ G x y)

/-- For `y ∈ E` and a class `x` of the sample of `X`, the set `G x y` put back in the class `y` lies
in the sample of `Y`. -/
lemma modLift_subset_sampleY {x y : ZMod d} (hy : y ∈ E) (hx : x ∈ sampleRes r₀ ξ) :
    modLift d y (G x y) ⊆ sampleY d E G r₀ ξ := by
  grw [subset_biUnion_of_mem (fun x ↦ G x y) hx]
  exact subset_biUnion_of_mem (fun y ↦ modLift d y ((sampleRes r₀ ξ).biUnion fun x ↦ G x y)) hy

variable [NeZero d]

/-- If the sets `G x y` are subsets of the classes of `Y`, the sample of `Y` is a subset of `Y`. -/
lemma sampleY_subset (hG : ∀ x y, G x y ⊆ modFiber d y Y) : sampleY d E G r₀ ξ ⊆ Y :=
  biUnion_subset.2 fun y _ ↦ modLift_subset (biUnion_subset.2 fun x _ ↦ hG x y)

/-- If the sets `G x y` have at most `c` elements, then a sample of `Y` has at most
`#E * ((t + 1) * c)` elements. -/
lemma card_sampleY_le {c : ℕ} (hG : ∀ x y, #(G x y) ≤ c) :
    #(sampleY d E G r₀ ξ) ≤ #E * ((t + 1) * c) := by
  rw [sampleY, ← smul_eq_mul]
  grw [card_biUnion_le]
  apply sum_le_card_nsmul
  intro y _
  grw [card_modLift, card_biUnion_le, sum_le_card_nsmul _ _ c fun x _ ↦ hG x y, smul_eq_mul,
    card_sampleRes_le]

/-- If the class `x` of `X` lies in `S` and is a class of the sample of `X`, and `y ∈ E`, the bound
for `G x y` bounds the class `x + y` of `S + sampleY d E G r₀ ξ`. -/
lemma le_card_modClass_add_sampleY {S : Finset ℤ} {x y : ZMod d} (hS : modClass d x X ⊆ S)
    (hy : y ∈ E) (hx : x ∈ sampleRes r₀ ξ)
    (hG : #(modFiber d x X) + #(modFiber d y Y) - 1 ≤ (#(modFiber d x X + G x y) : ℝ)) :
    #(modFiber d x X) + #(modFiber d y Y) - 1 ≤
      (#(modClass d (x + y) (S + sampleY d E G r₀ ξ)) : ℝ) := by
  grw [hG, ← card_modLift_add_modLift (x := x) (y := y),
    modLift_add_modLift_subset (S := S) (by rwa [modLift_modFiber]) (modLift_subset_sampleY hy hx)]

/-- The bound for a residue `z` with `z - r₀ ∈ E`: the class `r₀` of `X` is in every sample. -/
lemma le_expect_card_modClass_of_sub_mem (hr₀ : r₀ ∈ EX) {z : ZMod d} (hz : z - r₀ ∈ E)
    (hG : ∀ y ∈ E, ∀ x ∈ EX,
      #(modFiber d x X) + #(modFiber d y Y) - 1 ≤ (#(modFiber d x X + G x y) : ℝ)) :
    #(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) - 1 ≤
      𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX,
        (#(modClass d z (sampleX d X r₀ ξ + sampleY d E G r₀ ξ)) : ℝ) := by
  apply le_expect (piFinset_nonempty.2 fun _ ↦ ⟨r₀, hr₀⟩)
  intro ξ _
  simpa using le_card_modClass_add_sampleY modClass_subset_sampleX_left hz mem_sampleRes_self
    (hG _ hz _ hr₀)

/-- If `1 - ε ≤ ρ`, `0 ≤ ε`, `0 ≤ S`, `ε * S ≤ (1 - ε) * g` and `1 ≤ g`, then
`S - 1 ≤ ρ * (S + g - 1)`. -/
lemma sub_one_le_mul_add_sub_one {ρ ε S g : ℝ} (hρ : 1 - ε ≤ ρ) (hS : 0 ≤ S)
    (hε : ε * S ≤ (1 - ε) * g) (hε₀ : 0 ≤ ε) (hg : 1 ≤ g) : S - 1 ≤ ρ * (S + g - 1) := by
  nlinarith [mul_le_mul_of_nonneg_right hρ (by linarith : (0 : ℝ) ≤ S + g - 1)]

/-- If `z - ξ i ∈ EY'` for some `i`, the class `z` of the sumset of the samples gains `g`. -/
lemma add_sub_one_le_card_modClass (hEY : EY' ⊆ E) {z : ZMod d} {g : ℝ}
    (hG : ∀ y ∈ E, ∀ x ∈ EX,
      #(modFiber d x X) + #(modFiber d y Y) - 1 ≤ (#(modFiber d x X + G x y) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY',
      #(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) + g ≤ #(modFiber d x X) + #(modFiber d y Y))
    {i : Fin t} (hi : ξ i ∈ EX) (hz : z - ξ i ∈ EY') :
    #(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) + g - 1 ≤
      (#(modClass d z (sampleX d X r₀ ξ + sampleY d E G r₀ ξ)) : ℝ) := by
  have := le_card_modClass_add_sampleY (modClass_subset_sampleX (r₀ := r₀) i) (hEY hz)
    (mem_sampleRes (r₀ := r₀) i) (hG _ (hEY hz) _ hi)
  rw [add_sub_cancel] at this
  linarith [hgain _ hi _ hz]

/-- The bound for a residue `z` with `z - r₀ ∉ E`. With probability at least `1 - ε` some `ξ i` has
`z - ξ i ∈ EY'`, and then the class `z` of the sumset gains `g`. -/
lemma le_expect_card_modClass_of_sub_notMem (hr₀ : r₀ ∈ EX) (hEY : EY' ⊆ E) {z : ZMod d} {g ε : ℝ}
    (hG : ∀ y ∈ E, ∀ x ∈ EX,
      #(modFiber d x X) + #(modFiber d y Y) - 1 ≤ (#(modFiber d x X + G x y) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY',
      #(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) + g ≤ #(modFiber d x X) + #(modFiber d y Y))
    (hbad : #{x ∈ EX | z - x ∉ EY'} ^ t ≤ ε * #EX ^ t)
    (hε : ε * (#(modFiber d r₀ X) + #(modFiber d (z - r₀) Y)) ≤ (1 - ε) * g) (hε₀ : 0 ≤ ε)
    (hg : 1 ≤ g) :
    #(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) - 1 ≤
      𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX,
        (#(modClass d z (sampleX d X r₀ ξ + sampleY d E G r₀ ξ)) : ℝ) := by
  grw [sub_one_le_mul_add_sub_one ?_ (by positivity) hε hε₀ hg]
  · apply mul_le_expect_of_le_of_mem_sdiff (t := piFinset fun _ : Fin t ↦ {x ∈ EX | z - x ∉ EY'})
      (piFinset_subset _ _ fun _ ↦ filter_subset (fun x ↦ z - x ∉ EY') EX)
      (fun _ _ ↦ by positivity)
    intro ξ hξ
    simp only [mem_sdiff, mem_piFinset, mem_filter, not_forall, not_and, not_not] at hξ
    obtain ⟨hξ, i, hi⟩ := hξ
    exact add_sub_one_le_card_modClass hEY hG hgain (hξ i) (hi (hξ i))
  · rw [card_piFinset_const, card_piFinset_const]
    push_cast
    rw [le_div_iff₀ (pow_pos (by exact_mod_cast card_pos.2 ⟨r₀, hr₀⟩) t)]
    linarith

/-- If the class `r₀` of `X` is the largest, then `#X ≤ d * #(modFiber d r₀ X)`. -/
lemma card_le_mul_card_modFiber (hmax : ∀ r, #(modFiber d r X) ≤ #(modFiber d r₀ X)) :
    (#X : ℝ) ≤ d * #(modFiber d r₀ X) := by
  rw [← sum_card_modFiber (d := d) X]
  grw [sum_le_card_nsmul _ _ _ fun r _ ↦ hmax r]
  simp

/-- The sizes of the classes `z - r₀` of `Y` add up to `#Y`. -/
lemma sum_card_modFiber_sub (r₀ : ZMod d) (Y : Finset ℤ) :
    ∑ z, (#(modFiber d (z - r₀) Y) : ℝ) = #Y := by
  rw [← sum_card_modFiber (d := d) Y, Nat.cast_sum]
  exact Fintype.sum_equiv (Equiv.subRight r₀) _ _ fun _ ↦ rfl

/-- If the class `r₀` of `X` is the largest, then `#X + #Y - d` is at most the sum over `z` of
`#(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) - 1`. -/
lemma card_add_card_sub_le_sum (hmax : ∀ r, #(modFiber d r X) ≤ #(modFiber d r₀ X)) :
    #X + #Y - d ≤ ∑ z, (#(modFiber d r₀ X) + #(modFiber d (z - r₀) Y) - 1 : ℝ) := by
  rw [sum_sub_distrib, sum_add_distrib, sum_card_modFiber_sub]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  linarith [card_le_mul_card_modFiber hmax]

/-- **Lemma F&G** of Bollobás, Leader and Tiba, with the sample of `Y` adapted to the sample of `X`:
the expected size of the sumset of the samples is at least `#X + #Y - d`. -/
lemma le_expect_card_sampleX_add_sampleY (hr₀ : r₀ ∈ EX)
    (hmax : ∀ r, #(modFiber d r X) ≤ #(modFiber d r₀ X)) (hEY : EY' ⊆ E) {g ε : ℝ}
    (hG : ∀ y ∈ E, ∀ x ∈ EX,
      #(modFiber d x X) + #(modFiber d y Y) - 1 ≤ (#(modFiber d x X + G x y) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY', ∀ y' ∉ E,
      #(modFiber d r₀ X) + #(modFiber d y' Y) + g ≤ #(modFiber d x X) + #(modFiber d y Y))
    (hbad : ∀ z, #{x ∈ EX | z - x ∉ EY'} ^ t ≤ ε * #EX ^ t)
    (hε : ∀ y', ε * (#(modFiber d r₀ X) + #(modFiber d y' Y)) ≤ (1 - ε) * g) (hε₀ : 0 ≤ ε)
    (hg : 1 ≤ g) :
    #X + #Y - d ≤ 𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX,
      (#(sampleX d X r₀ ξ + sampleY d E G r₀ ξ) : ℝ) := by
  have h (ξ : Fin t → ZMod d) : (#(sampleX d X r₀ ξ + sampleY d E G r₀ ξ) : ℝ) =
      ∑ z, (#(modClass d z (sampleX d X r₀ ξ + sampleY d E G r₀ ξ)) : ℝ) := by
    exact_mod_cast (sum_card_modClass _).symm
  simp_rw [h, expect_sum_comm]
  grw [card_add_card_sub_le_sum hmax]
  gcongr with z
  by_cases hz : z - r₀ ∈ E
  · exact le_expect_card_modClass_of_sub_mem hr₀ hz hG
  · exact le_expect_card_modClass_of_sub_notMem hr₀ hEY hG
      (fun x hx y hy ↦ hgain x hx y hy _ hz) (hbad z) (hε _) hε₀ hg

end LargeSumsetsFromSubsets
