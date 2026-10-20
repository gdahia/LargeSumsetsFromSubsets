/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.IntervalSumsets.Fibres
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

The probabilistic heart of Theorem 8 of Bollobás, Leader and Tiba, *Large sumsets from
medium-sized subsets* (their Lemma on the families `𝓕` and `𝓖`), in an abstract form.

Fix `d ≥ 1`, sets `X` and `Y` of integers, sets `EX`, `EY' ⊆ EY` of residues modulo `d`, a
residue `r₀ ∈ EX` and, for every residue `y`, a family `F y` of subsets of the rescaled class
`modFibre d y Y`. The sample of `X` for `ξ : Fin t → ZMod d` is the union of the classes `r₀`
and `ξ i` of `X`; the sample of `Y` for a choice `ω` of a member of each family is the union of
the members `F y (ω y)` for `y ∈ EY`, put back in their classes. If the families satisfy the
conclusion of Theorem 5 for the classes `x ∈ EX`, and the classes in `EX` and `EY'` are larger
than the others by a margin `g`, then for `ξ` uniform in `EX ^ t` and `ω` uniform the expected
size of the sumset of the samples is at least `#X + #Y - d`.

The file also proves the two padding facts used to complete samples: in `ℤ`, `j` more elements
of each set raise the size of a sumset to `#X + #Y - 1` when it misses that by `j`, and
supersets of prescribed sizes have larger sumsets.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators Pointwise

namespace LargeSumsetsFromSubsets

/-! ### Padding -/

/-- If `X' + Y'` misses `#X + #Y - 1` by at most `j`, then adding at most `j` elements of `X`
to `X'` and of `Y` to `Y'` gives a sumset of size at least `#X + #Y - 1`. -/
lemma exists_superset_card_add_le_card_add {X Y X' Y' : Finset ℤ} (hX : X.Nonempty)
    (hY : Y.Nonempty) (j : ℕ) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y)
    (h : #X + #Y ≤ #(X' + Y') + j + 1) :
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
`#X + #Y ≤ #(X' + Y') + j + 1` extend to subsets of sizes `c₁` and `c₂` whose sumset has at
least `#X + #Y - 1` elements. -/
lemma exists_subset_card_eq_of_le_card_add {X Y X' Y' : Finset ℤ} {c₁ c₂ j : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (hc₁ : #X' + j ≤ c₁)
    (hc₁X : c₁ ≤ #X) (hc₂ : #Y' + j ≤ c₂) (hc₂Y : c₂ ≤ #Y)
    (h : #X + #Y ≤ #(X' + Y') + j + 1) :
    ∃ X'' ⊆ X, ∃ Y'' ⊆ Y, #X'' = c₁ ∧ #Y'' = c₂ ∧ #X + #Y - 1 ≤ #(X'' + Y'') := by
  obtain ⟨X₁, Y₁, -, hX₁, hX₁c, -, hY₁, hY₁c, h₁⟩ :=
    exists_superset_card_add_le_card_add hX hY j hX' hY' h
  obtain ⟨X₂, hX₁₂, hX₂, hX₂c⟩ := exists_subsuperset_card_eq hX₁ (by grind) hc₁X
  obtain ⟨Y₂, hY₁₂, hY₂, hY₂c⟩ := exists_subsuperset_card_eq hY₁ (by grind) hc₂Y
  have := card_le_card (add_subset_add hX₁₂ hY₁₂)
  exact ⟨X₂, hX₂, Y₂, hY₂, hX₂c, hY₂c, by grind⟩

/-! ### Expectations -/

/-- The expectation over a product of a function of one coordinate is the expectation over that
coordinate. -/
lemma expect_apply_eval {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)] (i : ι) (f : κ i → ℝ) :
    𝔼 ω : (∀ j, κ j), f (ω i) = 𝔼 a, f a := by
  rw [Fintype.expect_equiv (Equiv.piSplitAt i κ) (fun ω ↦ f (ω i)) (fun p ↦ f p.1) fun _ ↦ rfl,
    ← univ_product_univ, expect_product]
  simp

/-- A nonnegative function which is at least `V` outside `t ⊆ s` has expectation over `s` at
least `(#s - #t) / #s * V`. -/
lemma mul_le_expect_of_le_of_mem_sdiff {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    {f : ι → ℝ} {V : ℝ} (hts : t ⊆ s) (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s \ t, V ≤ f i) :
    (#s - #t) / #s * V ≤ 𝔼 i ∈ s, f i := by
  rw [Finset.expect_eq_sum_div_card, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have := card_nsmul_le_sum _ _ _ hf
  rw [card_sdiff_of_subset hts, nsmul_eq_mul, Nat.cast_sub (card_le_card hts)] at this
  exact this.trans (sum_le_sum_of_subset_of_nonneg sdiff_subset fun i hi _ ↦ hf₀ i hi)

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

/-- If the classes of `X` have at most `M` elements, a sample of `X` has at most
`(t + 1) * M`. -/
lemma card_sampleX_le {M : ℕ} (h : ∀ r, #(modClass d r X) ≤ M) :
    #(sampleX d X r₀ ξ) ≤ (t + 1) * M := by
  refine (card_union_le _ _).trans ?_
  have := card_biUnion_le.trans
    (sum_le_card_nsmul univ (fun i ↦ #(modClass d (ξ i) X)) M fun i _ ↦ h _)
  simp only [card_univ, Fintype.card_fin, smul_eq_mul] at this
  grind [h r₀]

variable [NeZero d] {k : ZMod d → ℕ} {F : ∀ y, Fin (k y + 1) → Finset ℤ}
  {E : Finset (ZMod d)} {ω : ∀ y, Fin (k y + 1)}

/-- The sample of `Y`: the union over `y ∈ E` of the member `F y (ω y)` of the family `F y`, put
back in the class `y`. -/
def sampleY (d : ℕ) (E : Finset (ZMod d)) {k : ZMod d → ℕ} (F : ∀ y, Fin (k y + 1) → Finset ℤ)
    (ω : ∀ y, Fin (k y + 1)) : Finset ℤ :=
  E.biUnion fun y ↦ modLift d y (F y (ω y))

/-- If the families consist of subsets of the classes of `Y`, the sample of `Y` is a subset of
`Y`. -/
lemma sampleY_subset (hF : ∀ y i, F y i ⊆ modFibre d y Y) : sampleY d E F ω ⊆ Y :=
  biUnion_subset.2 fun y _ ↦ modLift_subset (hF y _)

/-- If the members of the families have at most `c` elements, a sample of `Y` has at most
`#E * c`. -/
lemma card_sampleY_le {c : ℕ} (hF : ∀ y i, #(F y i) ≤ c) : #(sampleY d E F ω) ≤ #E * c := by
  refine card_biUnion_le.trans ?_
  simpa [card_modLift] using sum_le_card_nsmul E _ c fun y _ ↦ hF y (ω y)

omit [NeZero d] in
/-- For `y ∈ E`, the chosen member of the family `F y` lies in the sample of `Y`. -/
lemma modLift_subset_sampleY {y : ZMod d} (hy : y ∈ E) :
    modLift d y (F y (ω y)) ⊆ sampleY d E F ω :=
  subset_biUnion_of_mem (fun y ↦ modLift d y (F y (ω y))) hy

/-- If the class `x` of `X` lies in `S` and `y ∈ E`, the conclusion of Theorem 5 for the class
`x` and the family `F y` bounds the expected size of the class `x + y` of `S + sampleY`. -/
lemma le_expect_card_modClass {S : Finset ℤ} {x y : ZMod d} (hS : modClass d x X ⊆ S)
    (hy : y ∈ E)
    (hF : (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 i, (#(modFibre d x X + F y i) : ℝ)) :
    (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 ω, (#(modClass d (x + y) (S + sampleY d E F ω)) : ℝ) := by
  refine hF.trans ((expect_apply_eval (κ := fun y ↦ Fin (k y + 1)) y
    fun i ↦ (#(modFibre d x X + F y i) : ℝ)).symm.le.trans (expect_le_expect ?_))
  intro ω _
  rw [← card_modLift_add_modLift (x := x) (y := y)]
  exact_mod_cast card_le_card
    (modLift_add_modLift_subset (by rwa [modLift_modFibre]) (modLift_subset_sampleY hy))

variable {EX EY' : Finset (ZMod d)}

/-- The bound for a residue `z` with `z - r₀ ∈ E`: the class `r₀` of `X` is in every sample. -/
lemma le_expect_card_modClass_of_sub_mem (hr₀ : r₀ ∈ EX) {z : ZMod d} (hz : z - r₀ ∈ E)
    (hF : ∀ y ∈ E, ∀ x ∈ EX, (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 i, (#(modFibre d x X + F y i) : ℝ)) :
    (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) - 1 : ℝ) ≤
      𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX, 𝔼 ω,
        (#(modClass d z (sampleX d X r₀ ξ + sampleY d E F ω)) : ℝ) := by
  refine (expect_const (piFinset_nonempty.2 fun _ ↦ ⟨r₀, hr₀⟩) _).symm.le.trans
    (expect_le_expect ?_)
  intro ξ _
  simpa using le_expect_card_modClass modClass_subset_sampleX_left hz (hF _ hz _ hr₀)

/-- If `1 - ε ≤ ρ`, `0 ≤ ε`, `0 ≤ S`, `ε * S ≤ (1 - ε) * g` and `1 ≤ g`, then
`S - 1 ≤ ρ * (S + g - 1)`. -/
lemma sub_one_le_mul_add_sub_one {ρ ε S g : ℝ} (hρ : 1 - ε ≤ ρ) (hS : 0 ≤ S)
    (hε : ε * S ≤ (1 - ε) * g) (hε₀ : 0 ≤ ε) (hg : 1 ≤ g) : S - 1 ≤ ρ * (S + g - 1) := by
  nlinarith [mul_le_mul_of_nonneg_right hρ (by linarith : (0 : ℝ) ≤ S + g - 1)]

/-- If `z - ξ i ∈ EY'` for some `i`, the class `z` of the sumset of the samples gains `g` on
average over `ω`. -/
lemma add_sub_one_le_expect_card_modClass (hEY : EY' ⊆ E) {z : ZMod d} {g : ℝ}
    (hF : ∀ y ∈ E, ∀ x ∈ EX, (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 i, (#(modFibre d x X + F y i) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY',
      (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) : ℝ) + g ≤
        #(modFibre d x X) + #(modFibre d y Y))
    {i : Fin t} (hi : ξ i ∈ EX) (hz : z - ξ i ∈ EY') :
    (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) + g - 1 : ℝ) ≤
      𝔼 ω, (#(modClass d z (sampleX d X r₀ ξ + sampleY d E F ω)) : ℝ) := by
  have := le_expect_card_modClass (modClass_subset_sampleX (r₀ := r₀) i) (hEY hz)
    (hF _ (hEY hz) _ hi)
  rw [add_sub_cancel] at this
  linarith [hgain _ hi _ hz]

/-- The bound for a residue `z` with `z - r₀ ∉ E`. With probability at least `1 - ε` some
`ξ i` has `z - ξ i ∈ EY'`, and then the class `z` of the sumset gains `g` on average. -/
lemma le_expect_card_modClass_of_sub_notMem (hr₀ : r₀ ∈ EX) (hEY : EY' ⊆ E) {z : ZMod d}
    {g ε : ℝ}
    (hF : ∀ y ∈ E, ∀ x ∈ EX, (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 i, (#(modFibre d x X + F y i) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY',
      (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) : ℝ) + g ≤
        #(modFibre d x X) + #(modFibre d y Y))
    (hbad : (#{x ∈ EX | z - x ∉ EY'} : ℝ) ^ t ≤ ε * #EX ^ t)
    (hε : ε * (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y)) ≤ (1 - ε) * g)
    (hε₀ : 0 ≤ ε) (hg : 1 ≤ g) :
    (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) - 1 : ℝ) ≤
      𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX, 𝔼 ω,
        (#(modClass d z (sampleX d X r₀ ξ + sampleY d E F ω)) : ℝ) := by
  refine (sub_one_le_mul_add_sub_one ?_ (by positivity) hε hε₀ hg).trans
    (mul_le_expect_of_le_of_mem_sdiff (t := piFinset fun _ : Fin t ↦ {x ∈ EX | z - x ∉ EY'})
      (piFinset_subset _ _ fun _ ↦ filter_subset (fun x ↦ z - x ∉ EY') EX)
      (fun _ _ ↦ expect_nonneg fun _ _ ↦ by simp) ?_)
  · rw [card_piFinset_const, card_piFinset_const]
    push_cast
    rw [le_div_iff₀ (pow_pos (by exact_mod_cast card_pos.2 ⟨r₀, hr₀⟩) t)]
    linarith
  · intro ξ hξ
    simp only [mem_sdiff, mem_piFinset, mem_filter, not_forall, not_and, not_not] at hξ
    obtain ⟨hξ, i, hi⟩ := hξ
    exact add_sub_one_le_expect_card_modClass hEY hF hgain (hξ i) (hi (hξ i))

/-- If the class `r₀` of `X` is the largest, then `#X ≤ d * #(modFibre d r₀ X)`. -/
lemma card_le_mul_card_modFibre (hmax : ∀ r, #(modFibre d r X) ≤ #(modFibre d r₀ X)) :
    (#X : ℝ) ≤ d * #(modFibre d r₀ X) := by
  rw [← sum_card_modFibre (d := d) X]
  exact_mod_cast (sum_le_card_nsmul _ _ _ fun r _ ↦ hmax r).trans (by simp)

/-- The sizes of the classes `z - r₀` of `Y` add up to `#Y`. -/
lemma sum_card_modFibre_sub (r₀ : ZMod d) (Y : Finset ℤ) :
    ∑ z, (#(modFibre d (z - r₀) Y) : ℝ) = #Y := by
  exact (Equiv.sum_comp (Equiv.subRight r₀) fun z ↦ (#(modFibre d z Y) : ℝ)).trans
    (by exact_mod_cast sum_card_modFibre Y)

/-- If the class `r₀` of `X` is the largest, then `#X + #Y - d` is at most the sum over `z` of
`#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) - 1`. -/
lemma card_add_card_sub_le_sum (hmax : ∀ r, #(modFibre d r X) ≤ #(modFibre d r₀ X)) :
    (#X + #Y - d : ℝ) ≤ ∑ z, (#(modFibre d r₀ X) + #(modFibre d (z - r₀) Y) - 1 : ℝ) := by
  rw [sum_sub_distrib, sum_add_distrib, sum_card_modFibre_sub]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  linarith [card_le_mul_card_modFibre hmax]

/-- **Lemma F&G** of Bollobás, Leader and Tiba: the expected size of the sumset of the samples
is at least `#X + #Y - d`. -/
lemma le_expect_card_sampleX_add_sampleY (hr₀ : r₀ ∈ EX)
    (hmax : ∀ r, #(modFibre d r X) ≤ #(modFibre d r₀ X)) (hEY : EY' ⊆ E) {g ε : ℝ}
    (hF : ∀ y ∈ E, ∀ x ∈ EX, (#(modFibre d x X) + #(modFibre d y Y) - 1 : ℝ) ≤
      𝔼 i, (#(modFibre d x X + F y i) : ℝ))
    (hgain : ∀ x ∈ EX, ∀ y ∈ EY', ∀ y' ∉ E,
      (#(modFibre d r₀ X) + #(modFibre d y' Y) : ℝ) + g ≤
        #(modFibre d x X) + #(modFibre d y Y))
    (hbad : ∀ z, (#{x ∈ EX | z - x ∉ EY'} : ℝ) ^ t ≤ ε * #EX ^ t)
    (hε : ∀ y', ε * (#(modFibre d r₀ X) + #(modFibre d y' Y)) ≤ (1 - ε) * g)
    (hε₀ : 0 ≤ ε) (hg : 1 ≤ g) :
    (#X + #Y - d : ℝ) ≤ 𝔼 ξ ∈ piFinset fun _ : Fin t ↦ EX, 𝔼 ω,
      (#(sampleX d X r₀ ξ + sampleY d E F ω) : ℝ) := by
  have h : ∀ (ξ : Fin t → ZMod d) ω, (#(sampleX d X r₀ ξ + sampleY d E F ω) : ℝ) =
      ∑ z, (#(modClass d z (sampleX d X r₀ ξ + sampleY d E F ω)) : ℝ) := by
    intro ξ ω
    exact_mod_cast (sum_card_modClass _).symm
  simp_rw [h, expect_sum_comm]
  refine (card_add_card_sub_le_sum hmax).trans ?_
  gcongr with z
  by_cases hz : z - r₀ ∈ E
  · exact le_expect_card_modClass_of_sub_mem hr₀ hz hF
  · exact le_expect_card_modClass_of_sub_notMem hr₀ hEY hF
      (fun x hx y hy ↦ hgain x hx y hy _ hz) (hbad z) (hε _) hε₀ hg

end LargeSumsetsFromSubsets
