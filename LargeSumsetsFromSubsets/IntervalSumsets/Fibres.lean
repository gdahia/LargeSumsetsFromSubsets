/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Residue classes of sets of integers

For `d ≥ 1` and a residue `r` modulo `d`, the map `q ↦ d * q + r.val` is a bijection from `ℤ`
onto the residue class `r`. This file defines

* `modClass d r S`: the elements of `S` congruent to `r` modulo `d`;
* `modFibre d r S`: the same class rescaled to `ℤ`, the `q` with `d * q + r.val ∈ S`;
* `modLift d r T`: the image of `T` in the residue class `r`.

The sum of a set in the class `x` and a set in the class `y` lies in the class `x + y` and has
the size of the sumset of the rescaled sets. The rescaled classes of an interval of length `m`
are intervals of length about `m / d`.
-/

@[expose] public section

open Finset
open scoped Pointwise symmDiff

namespace LargeSumsetsFromSubsets

variable {d : ℕ}

/-- The elements of `S` congruent to `r` modulo `d`. -/
def modClass (d : ℕ) (r : ZMod d) (S : Finset ℤ) : Finset ℤ := {s ∈ S | (s : ZMod d) = r}

/-- Membership in a residue class. -/
@[simp]
lemma mem_modClass {r : ZMod d} {S : Finset ℤ} {s : ℤ} :
    s ∈ modClass d r S ↔ s ∈ S ∧ (s : ZMod d) = r :=
  mem_filter

/-- A residue class of `S` is a subset of `S`. -/
lemma modClass_subset (r : ZMod d) (S : Finset ℤ) : modClass d r S ⊆ S :=
  filter_subset _ _

/-- The map `q ↦ d * q + r.val`, a bijection from `ℤ` onto the residue class `r` modulo `d`. -/
def modEmbed (d : ℕ) (r : ZMod d) (q : ℤ) : ℤ := d * q + r.val

/-- The image of `T` in the residue class `r` modulo `d`. -/
def modLift (d : ℕ) (r : ZMod d) (T : Finset ℤ) : Finset ℤ := T.image (modEmbed d r)

variable [NeZero d]

/-- The map `q ↦ d * q + r.val` is injective. -/
lemma modEmbed_injective (r : ZMod d) : (modEmbed d r).Injective := by
  intro q q' h
  simpa [modEmbed, NeZero.ne d] using h

/-- The map `q ↦ d * q + r.val` takes values in the residue class `r`. -/
@[simp]
lemma intCast_modEmbed (r : ZMod d) (q : ℤ) : ((modEmbed d r q : ℤ) : ZMod d) = r := by
  simp [modEmbed]

/-- Every integer `s` is `d * (s / d)` plus the representative of its residue. -/
lemma modEmbed_intCast_ediv (s : ℤ) : modEmbed d (s : ZMod d) (s / d) = s := by
  rw [modEmbed, ZMod.val_intCast]
  exact Int.mul_ediv_add_emod s d

/-- The residue class `r` of `S` modulo `d`, rescaled: the `q` with `d * q + r.val ∈ S`. -/
noncomputable def modFibre (d : ℕ) [NeZero d] (r : ZMod d) (S : Finset ℤ) : Finset ℤ :=
  S.preimage (modEmbed d r) (modEmbed_injective r).injOn

variable {r x y : ZMod d} {S T A B : Finset ℤ} {q : ℤ}

/-- Membership in a rescaled residue class. -/
@[simp]
lemma mem_modFibre : q ∈ modFibre d r S ↔ modEmbed d r q ∈ S :=
  mem_preimage

/-- Putting a set in a residue class preserves its size. -/
lemma card_modLift : #(modLift d r T) = #T :=
  card_image_of_injective _ (modEmbed_injective r)

/-- Putting the rescaled class `r` of `S` back in the class `r` gives the class `r` of `S`. -/
lemma modLift_modFibre : modLift d r (modFibre d r S) = modClass d r S := by
  ext s
  simp only [modLift, mem_image, mem_modFibre, mem_modClass]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp [hq]
  · rintro ⟨hs, rfl⟩
    exact ⟨s / d, by rwa [modEmbed_intCast_ediv], modEmbed_intCast_ediv s⟩

/-- Rescaling a residue class preserves its size. -/
lemma card_modFibre : #(modFibre d r S) = #(modClass d r S) := by
  rw [← modLift_modFibre, card_modLift]

/-- A set is the disjoint union of its residue classes. -/
lemma sum_card_modClass (S : Finset ℤ) : ∑ r, #(modClass d r S) = #S :=
  (card_eq_sum_card_fiberwise (f := (Int.cast : ℤ → ZMod d)) (t := univ) (by simp)).symm

/-- The sizes of the rescaled residue classes of `S` add up to `#S`. -/
lemma sum_card_modFibre (S : Finset ℤ) : ∑ r, #(modFibre d r S) = #S := by
  simp_rw [card_modFibre, sum_card_modClass]

/-- Rescaled residue classes are monotone in the set. -/
lemma modFibre_mono (h : S ⊆ T) : modFibre d r S ⊆ modFibre d r T :=
  fun _ hq ↦ mem_modFibre.2 (h (mem_modFibre.1 hq))

/-- Rescaled residue classes commute with set differences. -/
lemma modFibre_sdiff : modFibre d r (S \ T) = modFibre d r S \ modFibre d r T := by
  ext
  simp

/-- A subset of the rescaled class `r` of `S`, put back in the class `r`, is a subset of `S`. -/
lemma modLift_subset (h : T ⊆ modFibre d r S) : modLift d r T ⊆ S := by
  intro s hs
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hs
  exact mem_modFibre.1 (h hq)

omit [NeZero d] in
/-- A sum of images in the classes `x` and `y` is an affine image of the sumset. -/
lemma modLift_add_modLift (x y : ZMod d) (A B : Finset ℤ) :
    modLift d x A + modLift d y B = (A + B).image fun q : ℤ ↦ d * q + (x.val + y.val) := by
  ext s
  simp only [modLift, mem_add, mem_image, modEmbed]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, _, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', ⟨q, hq, q', hq', rfl⟩, by ring⟩
  · rintro ⟨_, ⟨q, hq, q', hq', rfl⟩, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, _, ⟨q', hq', rfl⟩, by ring⟩

/-- Rescaling residue classes preserves the sizes of sumsets. -/
lemma card_modLift_add_modLift : #(modLift d x A + modLift d y B) = #(A + B) := by
  rw [modLift_add_modLift]
  exact card_image_of_injective _ fun q q' h ↦ by simpa [NeZero.ne d] using h

/-- The sum of subsets of the classes `x` and `y` of `S` and `T` lies in the class `x + y` of
`S + T`. -/
lemma modLift_add_modLift_subset (hA : modLift d x A ⊆ S) (hB : modLift d y B ⊆ T) :
    modLift d x A + modLift d y B ⊆ modClass d (x + y) (S + T) := by
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.1 hs
  refine mem_modClass.2 ⟨add_mem_add (hA hu) (hB hv), ?_⟩
  obtain ⟨q, -, rfl⟩ := mem_image.1 hu
  obtain ⟨q', -, rfl⟩ := mem_image.1 hv
  push_cast
  simp

/-! ### Residue classes of intervals -/

variable {a b : ℤ} {m n : ℕ}

/-- Membership in a rescaled residue class of an interval. -/
lemma mem_modFibre_Ico :
    q ∈ modFibre d r (Ico a (a + m)) ↔ a ≤ d * q + r.val ∧ d * q + r.val < a + m := by
  simp [modEmbed]

/-- The representative of a residue modulo `d` is less than `d`. -/
private lemma val_lt_cast (r : ZMod d) : (r.val : ℤ) < d := by
  exact_mod_cast ZMod.val_lt r

/-- The modulus `d` is positive as an integer. -/
private lemma intCast_pos : (0 : ℤ) < d := by
  exact_mod_cast Nat.pos_of_neZero d

/-- Integer division by `d` rounds down by less than `d`. -/
private lemma mul_ediv_bounds (a : ℤ) : d * (a / d) ≤ a ∧ a < d * (a / d) + d :=
  ⟨Int.mul_ediv_self_le (by simp [NeZero.ne d]), Int.lt_mul_ediv_self_add intCast_pos⟩

/-- Natural division by `d` rounds down by less than `d`. -/
private lemma mul_div_bounds (m : ℕ) :
    (d : ℤ) * (m / d : ℕ) ≤ m ∧ (m : ℤ) < d * (m / d : ℕ) + d := by
  constructor
  · exact_mod_cast Nat.mul_div_le m d
  · exact_mod_cast Nat.lt_mul_div_self_add (Nat.pos_of_neZero d)

/-- The rescaled class of `Ico a (a + m)` lies in an interval of length `m / d + 2`. -/
lemma modFibre_Ico_subset :
    modFibre d r (Ico a (a + m)) ⊆ Ico (a / d) (a / d + (m / d : ℕ) + 2) := by
  intro q hq
  obtain ⟨h₁, h₂⟩ := mem_modFibre_Ico.1 hq
  obtain ⟨h₃, h₄⟩ := mul_ediv_bounds (d := d) a
  obtain ⟨h₅, h₆⟩ := mul_div_bounds (d := d) m
  rw [mem_Ico]
  constructor <;> nlinarith [val_lt_cast r, intCast_pos (d := d)]

/-- The rescaled class of `Ico a (a + m)` contains an interval of length `m / d - 1`. -/
lemma Ico_subset_modFibre_Ico :
    Ico (a / d + 1) (a / d + (m / d : ℕ)) ⊆ modFibre d r (Ico a (a + m)) := by
  intro q hq
  obtain ⟨h₁, h₂⟩ := mem_Ico.1 hq
  obtain ⟨h₃, h₄⟩ := mul_ediv_bounds (d := d) a
  obtain ⟨h₅, h₆⟩ := mul_div_bounds (d := d) m
  rw [mem_modFibre_Ico]
  constructor <;> nlinarith [val_lt_cast r, intCast_pos (d := d)]

/-- A residue class of `Ico a (a + m)` has at most `m / d + 2` elements. -/
lemma card_modFibre_Ico_le : #(modFibre d r (Ico a (a + m))) ≤ m / d + 2 := by
  have := card_le_card (modFibre_Ico_subset (d := d) (r := r) (a := a) (m := m))
  rw [Int.card_Ico] at this
  grind

/-- A residue class of `Ico a (a + m)` has at least `m / d - 1` elements. -/
lemma le_card_modFibre_Ico_add_one : m / d ≤ #(modFibre d r (Ico a (a + m))) + 1 := by
  have := card_le_card (Ico_subset_modFibre_Ico (d := d) (r := r) (a := a) (m := m))
  rw [Int.card_Ico] at this
  grind

/-- The rescaled class of an interval is an interval. -/
lemma Icc_subset_modFibre_Ico {q₁ q₂ : ℤ} (h₁ : q₁ ∈ modFibre d r (Ico b (b + n)))
    (h₂ : q₂ ∈ modFibre d r (Ico b (b + n))) : Icc q₁ q₂ ⊆ modFibre d r (Ico b (b + n)) := by
  intro q hq
  rw [mem_Icc] at hq
  rw [mem_modFibre_Ico] at *
  constructor <;> nlinarith [intCast_pos (d := d)]

/-- A subset of the rescaled class of `Ico a (a + m)` has at most two points outside
`Ico (a / d) (a / d + m / d)`. -/
lemma card_sdiff_Ico_le_two (hA : A ⊆ modFibre d r (Ico a (a + m))) :
    #(A \ Ico (a / d) (a / d + (m / d : ℕ))) ≤ 2 := by
  refine (card_le_card (t := Ico (a / d + (m / d : ℕ)) (a / d + (m / d : ℕ) + 2)) ?_).trans
    (by simp)
  intro q hq
  obtain ⟨hqA, hq⟩ := mem_sdiff.1 hq
  have := modFibre_Ico_subset (hA hqA)
  grind

/-- The interval `Ico (a / d) (a / d + m / d)` has at most one point outside the rescaled class
of `Ico a (a + m)`. -/
lemma card_Ico_sdiff_le_add_one :
    #(Ico (a / d) (a / d + (m / d : ℕ)) \ A) ≤ #(modFibre d r (Ico a (a + m)) \ A) + 1 := by
  refine (card_le_card (t := (modFibre d r (Ico a (a + m)) \ A) ∪ {a / d}) ?_).trans
    ((card_union_le _ _).trans (by simp))
  intro q hq
  obtain ⟨hq, hqA⟩ := mem_sdiff.1 hq
  rw [mem_union, mem_sdiff, mem_singleton]
  by_cases hq' : q = a / d
  · exact Or.inr hq'
  · exact Or.inl ⟨Ico_subset_modFibre_Ico (by grind), hqA⟩

/-- A subset of the rescaled class of `Ico a (a + m)` differs from `Ico (a / d) (a / d + m / d)`
in at most three points more than it misses of the class. -/
lemma card_symmDiff_Ico_le (hA : A ⊆ modFibre d r (Ico a (a + m))) :
    #(A ∆ Ico (a / d) (a / d + (m / d : ℕ))) ≤ #(modFibre d r (Ico a (a + m)) \ A) + 3 := by
  rw [symmDiff_def, sup_eq_union]
  exact (card_union_le _ _).trans
    ((add_le_add (card_sdiff_Ico_le_two hA) card_Ico_sdiff_le_add_one).trans_eq (by ring))

/-- A nonempty finite set of integers lies in an interval whose endpoints belong to it. -/
lemma exists_subset_Ico_of_nonempty (hB : B.Nonempty) :
    ∃ (y : ℤ) (n : ℕ), B ⊆ Ico y (y + n) ∧ y ∈ B ∧ y + n - 1 ∈ B := by
  have := min'_le B _ (max'_mem B hB)
  refine ⟨B.min' hB, (B.max' hB - B.min' hB + 1).toNat, ?_, min'_mem _ _, ?_⟩
  · intro s hs
    rw [mem_Ico]
    grind [min'_le B s hs, le_max' B s hs]
  · convert max'_mem B hB using 1
    grind

/-- A nonempty subset `B` of a rescaled class of `Ico b (b + n)` lies in an interval inside the
class whose endpoints belong to `B`. -/
lemma exists_Ico_subset_modFibre_Ico (hB : B.Nonempty)
    (hBJ : B ⊆ modFibre d r (Ico b (b + n))) :
    ∃ (y : ℤ) (n' : ℕ), B ⊆ Ico y (y + n') ∧ y ∈ B ∧ y + n' - 1 ∈ B ∧ #B ≤ n' ∧
      n' ≤ #(modFibre d r (Ico b (b + n))) ∧
      #(Ico y (y + n') \ B) ≤ #(modFibre d r (Ico b (b + n)) \ B) := by
  obtain ⟨y, n', hB', hy₀, hy₁⟩ := exists_subset_Ico_of_nonempty hB
  have hJ : Ico y (y + n') ⊆ modFibre d r (Ico b (b + n)) := by
    refine subset_trans ?_ (Icc_subset_modFibre_Ico (hBJ hy₀) (hBJ hy₁))
    intro q hq
    grind
  refine ⟨y, n', hB', hy₀, hy₁, ?_, ?_, card_le_card (sdiff_subset_sdiff hJ subset_rfl)⟩
  · simpa using card_le_card hB'
  · simpa using card_le_card hJ

end LargeSumsetsFromSubsets
