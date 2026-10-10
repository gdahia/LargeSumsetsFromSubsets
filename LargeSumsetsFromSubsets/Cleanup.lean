/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticRemoval
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

/-!
# Cleaning up a pair of sets almost all of whose sums are popular

Let `X` and `Y` be finite subsets of an abelian group and let `P` be a set of sums, and suppose
that all but a `δ` proportion of the pairs `(u, v) ∈ X × Y` satisfy `u + v ∈ P`. This file provides
the two ways of passing to large subsets `X₀ ⊆ X` and `Y₀ ⊆ Y` whose whole sumset is close to `P`.

* `LargeSumsetsFromSubsets.Cleanup.exists_cleanup` is the sharp one and applies when
  `#(X + Y)` is at most a constant multiple of `min #X #Y`. It removes from `X`, `Y` and
  `(X + Y) \ P` a few elements so that no sum survives outside `P`, by the arithmetic removal
  lemma applied inside a translate of `X + Y`, whose doubling is bounded by the Plünnecke–Ruzsa
  inequality. It is a variant of Shao's almost-all Balog–Szemerédi–Gowers theorem
  (arXiv:1811.10707, Theorem 1.1), which assumes instead that the sums of the pairs in a set
  `Γ ⊆ X ×ˢ Y` of density `1 - δ` are few. Here `Γ` is the set of pairs with sum in `P`, and the
  hypothesis on `#(X + Y)` is an additional one.
* `LargeSumsetsFromSubsets.Cleanup.exists_covering` is the crude one but has no restriction
  on `#(X + Y)`. It only gives `#(X₀ + Y₀) ≤ 2 * #P ^ 3 / (#X * #Y)`, but it is elementary:
  every `z ∈ X₀ + Y₀` has many representations as `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`.
-/

@[expose] public section

open Finset

open scoped Pointwise

namespace LargeSumsetsFromSubsets.Cleanup

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-! ### Translates

Translates are Mathlib's pointwise `t +ᵥ s`; only the membership criterion in the form used
throughout this file needs to be spelled out.
-/

lemma mem_vadd_finset_iff_sub_mem {t a : G} {s : Finset G} : a ∈ t +ᵥ s ↔ a - t ∈ s := by
  simp only [mem_vadd_finset, vadd_eq_add]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro h
    exact ⟨a - t, h, by abel⟩

/-! ### A bound for the fourfold sumset -/

/-- The Ruzsa triangle inequality bounds the doubling of `X` by the square of `#(X + Y)`. -/
lemma card_self_add_mul_le (X Y : Finset G) : #(X + X) * #Y ≤ #(X + Y) * #(X + Y) := by
  have h := ruzsa_triangle_inequality_add_add_add X Y X
  rwa [add_comm Y X] at h

/-- The fourfold sumset `2X + 2Y` is controlled by `#(X + Y)`: this is the Plünnecke–Ruzsa
inequality applied to the union of translates of `X` and of `Y` to the origin. -/
lemma card_add_add_le (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty) :
    #((X + Y) + (X + Y)) * (#X ^ 3 * #Y ^ 4) ≤ 16 * #(X + Y) ^ 8 := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨v, hv⟩ := hY
  set X' := (-u) +ᵥ X with hX'
  set Y' := (-v) +ᵥ Y with hY'
  have hX'ne : X'.Nonempty := Finset.Nonempty.vadd_finset ⟨u, hu⟩
  have hzeroX : (0 : G) ∈ X' := mem_vadd_finset_iff_sub_mem.2 (by simpa using hu)
  have hzeroY : (0 : G) ∈ Y' := mem_vadd_finset_iff_sub_mem.2 (by simpa using hv)
  set U := X' ∪ Y' with hU
  have hsub : X' + Y' ⊆ U + U := add_subset_add subset_union_left subset_union_right
  have hfour : (4 : ℕ) • U = U + U + (U + U) := by
    have h4 : (4 : ℕ) = 2 + 2 := rfl
    rw [h4, add_nsmul, two_nsmul]
  have hZZ : (X' + Y') + (X' + Y') ⊆ (4 : ℕ) • U := by
    rw [hfour]
    exact add_subset_add hsub hsub
  -- The Plünnecke--Ruzsa inequality for the fourfold sumset of `U`.
  have hpr := pluennecke_ruzsa_inequality_nsmul_add hX'ne U 4
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hpr
  have hpr' : #((4 : ℕ) • U) * #X' ^ 4 ≤ #(X' + U) ^ 4 * #X' := by exact_mod_cast hpr
  have hXpos : 0 < #X' := card_pos.2 hX'ne
  have hcancel : #((4 : ℕ) • U) * #X' ^ 3 ≤ #(X' + U) ^ 4 := by
    refine Nat.le_of_mul_le_mul_right ?_ hXpos
    have hrw : #((4 : ℕ) • U) * #X' ^ 3 * #X' = #((4 : ℕ) • U) * #X' ^ 4 := by ring
    rw [hrw]
    exact hpr'.trans_eq (by ring)
  -- The set `X' + U` is contained in the union of `X' + X'` and `X' + Y'`.
  have hXU : #(X' + U) ≤ #(X' + X') + #(X' + Y') := by
    have : X' + U = (X' + X') ∪ (X' + Y') := by rw [hU, add_union]
    rw [this]
    exact card_union_le _ _
  -- Translate everything back.
  have hcardX' : #X' = #X := card_vadd_finset _ _
  have hcardY' : #Y' = #Y := card_vadd_finset _ _
  have hcardXY : #(X' + Y') = #(X + Y) := by rw [hX', hY', vadd_add_vadd_comm, card_vadd_finset]
  have hcardXX : #(X' + X') = #(X + X) := by rw [hX', vadd_add_vadd_comm, card_vadd_finset]
  have hcardZZ : #((X' + Y') + (X' + Y')) = #((X + Y) + (X + Y)) := by
    rw [hX', hY', vadd_add_vadd_comm, vadd_add_vadd_comm, card_vadd_finset]
  -- Assemble.
  have hYle : #Y ≤ #(X + Y) := card_le_card_add_left ⟨u, hu⟩
  have hruzsa : #(X + X) * #Y ≤ #(X + Y) * #(X + Y) := card_self_add_mul_le X Y
  have hkey : #(X' + U) * #Y ≤ 2 * #(X + Y) ^ 2 := by
    have h := Nat.mul_le_mul_right #Y hXU
    rw [add_mul, hcardXX, hcardXY] at h
    nlinarith [hruzsa, hYle, Nat.zero_le (#(X + Y))]
  have hmain : #((4 : ℕ) • U) * (#X ^ 3 * #Y ^ 4) ≤ 16 * #(X + Y) ^ 8 := by
    have h := Nat.mul_le_mul_right (#Y ^ 4) hcancel
    have hpow : #(X' + U) ^ 4 * #Y ^ 4 = (#(X' + U) * #Y) ^ 4 := by ring
    rw [hpow] at h
    have h2 : (#(X' + U) * #Y) ^ 4 ≤ (2 * #(X + Y) ^ 2) ^ 4 := Nat.pow_le_pow_left hkey 4
    have hrw : #((4 : ℕ) • U) * #X' ^ 3 * #Y ^ 4 = #((4 : ℕ) • U) * (#X ^ 3 * #Y ^ 4) := by
      rw [hcardX']
      ring
    rw [hrw] at h
    refine (h.trans (h2.trans_eq ?_))
    ring
  refine le_trans (Nat.mul_le_mul_right _ ?_) hmain
  rw [← hcardZZ]
  exact card_le_card hZZ

/-! ### The sharp cleanup, via arithmetic removal -/

/-- The pairs of `X ×ˢ Y` whose sum misses `P`. -/
def badPairs (X Y P : Finset G) : Finset (G × G) := (X ×ˢ Y).filter fun p => p.1 + p.2 ∉ P

lemma mem_badPairs {X Y P : Finset G} {p : G × G} :
    p ∈ badPairs X Y P ↔ p.1 ∈ X ∧ p.2 ∈ Y ∧ p.1 + p.2 ∉ P := by
  simp [badPairs, and_assoc]

/-- The solutions of `a + b = c` in the translated sets are exactly the bad pairs. -/
lemma card_sumTriples_eq (X Y P : Finset G) (u v : G) :
    #(ArithmeticRemoval.sumTriples ((-u) +ᵥ X) ((-v) +ᵥ Y) ((-(u + v)) +ᵥ ((X + Y) \ P)))
      = #(badPairs X Y P) := by
  symm
  apply card_bij (fun p _ => (p.1 - u, p.2 - v, p.1 + p.2 - (u + v)))
  · intro p hp
    rw [mem_badPairs] at hp
    refine ArithmeticRemoval.mem_sumTriples.2
      ⟨mem_vadd_finset_iff_sub_mem.2 ?_, mem_vadd_finset_iff_sub_mem.2 ?_,
        mem_vadd_finset_iff_sub_mem.2 ?_, sub_add_sub_comm _ _ _ _⟩
    · simpa using hp.1
    · simpa using hp.2.1
    · have hrw : p.1 + p.2 - (u + v) - -(u + v) = p.1 + p.2 := by abel
      rw [hrw]
      exact mem_sdiff.2 ⟨add_mem_add hp.1 hp.2.1, hp.2.2⟩
  · intro p _ q _ h
    simp only [Prod.mk_inj] at h
    exact Prod.ext (sub_left_injective h.1) (sub_left_injective h.2.1)
  · intro t ht
    obtain ⟨ha, hb, hc, habc⟩ := ArithmeticRemoval.mem_sumTriples.1 ht
    rw [mem_vadd_finset_iff_sub_mem] at ha hb hc
    refine ⟨(t.1 + u, t.2.1 + v), mem_badPairs.2 ⟨by simpa using ha, by simpa using hb, ?_⟩, ?_⟩
    · have hrw : t.1 + u + (t.2.1 + v) = t.2.2 - -(u + v) := by rw [← habc]; abel
      rw [hrw]
      exact (mem_sdiff.1 hc).2
    · have h₃ : t.1 + u + (t.2.1 + v) - (u + v) = t.2.2 := by rw [← habc]; abel
      simp only [add_sub_cancel_right, h₃]

/-- **The cleanup lemma.** If all but a `δ` proportion of the pairs of `X ×ˢ Y` have their sum in
`P`, and if `#(X + Y)` is at most `D * min #X #Y`, then removing a `ρ`-fraction of `min #X #Y`
elements from `X` and from `Y` leaves a pair whose whole sumset exceeds `P` by at most
`ρ * min #X #Y` elements. -/
theorem exists_cleanup {X Y P : Finset G} (hX : X.Nonempty) (hY : Y.Nonempty)
    {D ρ δ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ)
    (hS : (#(X + Y) : ℝ) ≤ D * min (#X : ℝ) (#Y : ℝ))
    (hδ : 0 ≤ δ) (hδ' : δ ≤ ArithmeticRemoval.removalConst (16 * D ^ 7) (ρ / D))
    (hbad : (#(badPairs X Y P) : ℝ) ≤ δ * ((#X : ℝ) * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y,
      (#(X \ X₀) : ℝ) ≤ ρ * min (#X : ℝ) (#Y : ℝ) ∧
      (#(Y \ Y₀) : ℝ) ≤ ρ * min (#X : ℝ) (#Y : ℝ) ∧
      (#(X₀ + Y₀) : ℝ) ≤ #P + ρ * min (#X : ℝ) (#Y : ℝ) := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨v, hv⟩ := hY
  have hXne : X.Nonempty := ⟨u, hu⟩
  have hYne : Y.Nonempty := ⟨v, hv⟩
  have hXYne : (X + Y).Nonempty := ⟨u + v, add_mem_add hu hv⟩
  have hSpos : (0 : ℝ) < #(X + Y) := by exact_mod_cast card_pos.2 hXYne
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hXne
  have hypos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hYne
  have hnpos : (0 : ℝ) < min (#X : ℝ) (#Y : ℝ) := lt_min hxpos hypos
  have hxS : (#X : ℝ) ≤ #(X + Y) := by exact_mod_cast card_le_card_add_right hYne
  have hyS : (#Y : ℝ) ≤ #(X + Y) := by exact_mod_cast card_le_card_add_left hXne
  set Z := (-(u + v)) +ᵥ (X + Y) with hZdef
  set A₁ := (-u) +ᵥ X with hA₁def
  set B₁ := (-v) +ᵥ Y with hB₁def
  set C₁ := (-(u + v)) +ᵥ ((X + Y) \ P) with hC₁def
  have hA₁Z : A₁ ⊆ Z := by
    intro a ha
    rw [hA₁def, mem_vadd_finset_iff_sub_mem] at ha
    rw [hZdef, mem_vadd_finset_iff_sub_mem]
    have hrw : a - -(u + v) = a - -u + v := by abel
    rw [hrw]
    exact add_mem_add ha hv
  have hB₁Z : B₁ ⊆ Z := by
    intro b hb
    rw [hB₁def, mem_vadd_finset_iff_sub_mem] at hb
    rw [hZdef, mem_vadd_finset_iff_sub_mem]
    have hrw : b - -(u + v) = u + (b - -v) := by abel
    rw [hrw]
    exact add_mem_add hu hb
  have hC₁Z : C₁ ⊆ Z := vadd_finset_subset_vadd_finset sdiff_subset
  have hcardZ : (#Z : ℝ) = #(X + Y) := by rw [hZdef, card_vadd_finset]
  -- The doubling of the ambient set is bounded, by the Plünnecke--Ruzsa inequality.
  have hZZ : (#(Z + Z) : ℝ) ≤ 16 * D ^ 7 * #Z := by
    have hZZeq : (#(Z + Z) : ℝ) = #((X + Y) + (X + Y)) := by
      rw [hZdef, vadd_add_vadd_comm, card_vadd_finset]
    have hfour : (#((X + Y) + (X + Y)) : ℝ) * ((#X : ℝ) ^ 3 * (#Y : ℝ) ^ 4)
        ≤ 16 * (#(X + Y) : ℝ) ^ 8 := by exact_mod_cast card_add_add_le X Y hXne hYne
    have hminpow : (min (#X : ℝ) (#Y : ℝ)) ^ 7 ≤ (#X : ℝ) ^ 3 * (#Y : ℝ) ^ 4 := by
      have h₁ : (min (#X : ℝ) (#Y : ℝ)) ^ 3 ≤ (#X : ℝ) ^ 3 :=
        pow_le_pow_left₀ hnpos.le (min_le_left _ _) 3
      have h₂ : (min (#X : ℝ) (#Y : ℝ)) ^ 4 ≤ (#Y : ℝ) ^ 4 :=
        pow_le_pow_left₀ hnpos.le (min_le_right _ _) 4
      have hrw : (min (#X : ℝ) (#Y : ℝ)) ^ 7
          = (min (#X : ℝ) (#Y : ℝ)) ^ 3 * (min (#X : ℝ) (#Y : ℝ)) ^ 4 := by ring
      rw [hrw]
      exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have hSpow : (#(X + Y) : ℝ) ^ 7 ≤ D ^ 7 * (min (#X : ℝ) (#Y : ℝ)) ^ 7 := by
      have hrw : D ^ 7 * (min (#X : ℝ) (#Y : ℝ)) ^ 7 = (D * min (#X : ℝ) (#Y : ℝ)) ^ 7 := by ring
      rw [hrw]
      exact pow_le_pow_left₀ hSpos.le hS 7
    rw [hZZeq, hcardZ]
    refine le_of_mul_le_mul_right ?_ (pow_pos hSpos 7)
    have hTnn : (0 : ℝ) ≤ #((X + Y) + (X + Y)) := by positivity
    have hDnn : (0 : ℝ) < D ^ 7 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hSpow hTnn,
      mul_le_mul_of_nonneg_left hminpow (mul_nonneg hTnn hDnn.le),
      mul_le_mul_of_nonneg_left hfour hDnn.le]
  -- There are few solutions of `a + b = c`.
  have hsol : (#(ArithmeticRemoval.sumTriples A₁ B₁ C₁) : ℝ) ≤ δ * (#Z : ℝ) ^ 2 := by
    rw [hA₁def, hB₁def, hC₁def, card_sumTriples_eq, hcardZ]
    refine hbad.trans (mul_le_mul_of_nonneg_left ?_ hδ)
    nlinarith
  obtain ⟨A', hA'sub, B', hB'sub, C', hC'sub, hAdel, hBdel, hCdel, hfree⟩ :=
    ArithmeticRemoval.arithmetic_removal (K := 16 * D ^ 7) (ε := ρ / D) hA₁Z hB₁Z hC₁Z
      (by positivity) hZZ (by positivity) hδ hδ' hsol
  have hdel : (ρ / D) * (#Z : ℝ) ≤ ρ * min (#X : ℝ) (#Y : ℝ) := by
    rw [hcardZ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hsubX : u +ᵥ A' ⊆ X := by
    apply (vadd_finset_subset_vadd_finset hA'sub).trans
    rw [hA₁def, vadd_vadd]
    simp
  have hsubY : v +ᵥ B' ⊆ Y := by
    apply (vadd_finset_subset_vadd_finset hB'sub).trans
    rw [hB₁def, vadd_vadd]
    simp
  refine ⟨u +ᵥ A', hsubX, v +ᵥ B', hsubY, ?_, ?_, ?_⟩
  · have hcards : #(X \ (u +ᵥ A')) = #(A₁ \ A') := by
      rw [card_sdiff_of_subset hsubX, card_sdiff_of_subset hA'sub, card_vadd_finset, hA₁def,
        card_vadd_finset]
    rw [hcards]
    exact hAdel.trans hdel
  · have hcards : #(Y \ (v +ᵥ B')) = #(B₁ \ B') := by
      rw [card_sdiff_of_subset hsubY, card_sdiff_of_subset hB'sub, card_vadd_finset, hB₁def,
        card_vadd_finset]
    rw [hcards]
    exact hBdel.trans hdel
  · have hcover : (u +ᵥ A') + (v +ᵥ B') ⊆ P ∪ ((u + v) +ᵥ (C₁ \ C')) := by
      intro z hz
      by_cases hzP : z ∈ P
      · exact mem_union_left _ hzP
      apply mem_union_right _
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
      rw [mem_vadd_finset_iff_sub_mem, mem_sdiff]
      constructor
      · rw [hC₁def, mem_vadd_finset_iff_sub_mem]
        have hrw : a + b - (u + v) - -(u + v) = a + b := by abel
        rw [hrw]
        exact mem_sdiff.2 ⟨add_mem_add (hsubX ha) (hsubY hb), hzP⟩
      intro hmem
      have hA : a - u ∈ A' := by
        rw [mem_vadd_finset_iff_sub_mem] at ha
        exact ha
      have hB : b - v ∈ B' := by
        rw [mem_vadd_finset_iff_sub_mem] at hb
        exact hb
      have heq : a - u + (b - v) = a + b - (u + v) := by abel
      exact hfree _ hA _ hB _ hmem heq
    have hcard : (#((u +ᵥ A') + (v +ᵥ B')) : ℝ) ≤ (#P : ℝ) + #(C₁ \ C') := by
      have h := card_le_card hcover
      have h2 := card_union_le P ((u + v) +ᵥ (C₁ \ C'))
      rw [card_vadd_finset] at h2
      have : #((u +ᵥ A') + (v +ᵥ B')) ≤ #P + #(C₁ \ C') := h.trans h2
      exact_mod_cast this
    exact hcard.trans (by linarith [hCdel.trans hdel])

/-! ### The crude covering bound -/

/-- Counting the bad pairs one first coordinate at a time. -/
lemma sum_card_bad_left (X Y P : Finset G) :
    ∑ u ∈ X, #(Y.filter fun w => u + w ∉ P) = #(badPairs X Y P) := by
  refine Eq.trans (sum_congr rfl ?_)
    (card_eq_sum_card_fiberwise (f := fun p : G × G => p.1) (s := badPairs X Y P) (t := X)
      fun p hp => (mem_badPairs.1 hp).1).symm
  · intro u hu
    apply card_bij (fun w _ => (u, w))
    · intro w hw
      rw [mem_filter] at hw ⊢
      exact ⟨mem_badPairs.2 ⟨hu, hw.1, hw.2⟩, rfl⟩
    · intro w _ w' _ h
      exact (Prod.mk_inj.1 h).2
    · intro p hp
      rw [mem_filter, mem_badPairs] at hp
      refine ⟨p.2, mem_filter.2 ⟨hp.1.2.1, ?_⟩, ?_⟩
      · rw [← hp.2]
        exact hp.1.2.2
      · rw [← hp.2]

/-- Counting the bad pairs one second coordinate at a time. -/
lemma sum_card_bad_right (X Y P : Finset G) :
    ∑ v ∈ Y, #(X.filter fun w => w + v ∉ P) = #(badPairs X Y P) := by
  refine Eq.trans (sum_congr rfl ?_)
    (card_eq_sum_card_fiberwise (f := fun p : G × G => p.2) (s := badPairs X Y P) (t := Y)
      fun p hp => (mem_badPairs.1 hp).2.1).symm
  · intro v hv
    apply card_bij (fun w _ => (w, v))
    · intro w hw
      rw [mem_filter] at hw ⊢
      exact ⟨mem_badPairs.2 ⟨hw.1, hv, hw.2⟩, rfl⟩
    · intro w _ w' _ h
      exact (Prod.mk_inj.1 h).1
    · intro p hp
      rw [mem_filter, mem_badPairs] at hp
      refine ⟨p.1, mem_filter.2 ⟨hp.1.1, ?_⟩, ?_⟩
      · rw [← hp.2]
        exact hp.1.2.2
      · rw [← hp.2]

omit [AddCommGroup G] in
/-- The fibres of a map over a set of values are disjoint subsets of the domain. -/
lemma sum_card_fiber_le {α : Type*} (Q : Finset α) (φ : α → G) (T : Finset G) :
    ∑ z ∈ T, #(Q.filter fun q => φ q = z) ≤ #Q := by
  refine Eq.trans_le (sum_congr rfl ?_)
    ((card_eq_sum_card_fiberwise (f := φ) (s := Q.filter fun q => φ q ∈ T) (t := T)
      fun q hq => (mem_filter.1 hq).2).symm.trans_le (card_le_card (filter_subset _ _)))
  intro z hz
  congr 1
  ext q
  simp only [mem_filter, and_assoc]
  constructor
  · rintro ⟨hq, rfl⟩
    exact ⟨hq, hz, rfl⟩
  · rintro ⟨hq, -, hqz⟩
    exact ⟨hq, hqz⟩

/-- **The covering bound.** If all but a `δ` proportion of the pairs of `X ×ˢ Y` have their sum in
`P`, then after deleting a `ρ`-fraction of `X` and of `Y` every remaining sum has at least
`#X * #Y / 2` representations as `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`, whence the remaining sumset
has at most `2 * #P ^ 3 / (#X * #Y)` elements. -/
theorem exists_covering {X Y P : Finset G} (hX : X.Nonempty) (hY : Y.Nonempty)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1) (hδρ : 8 * δ ≤ ρ)
    (hbad : (#(badPairs X Y P) : ℝ) ≤ δ * ((#X : ℝ) * #Y)) :
    ∃ X₁ ⊆ X, ∃ Y₁ ⊆ Y,
      (#(X \ X₁) : ℝ) ≤ ρ * #X ∧ (#(Y \ Y₁) : ℝ) ≤ ρ * #Y ∧
      (#(X₁ + Y₁) : ℝ) * ((#X : ℝ) * #Y) ≤ 2 * (#P : ℝ) ^ 3 := by
  classical
  have hρ : 0 < ρ := by linarith
  have hxpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hX
  have hypos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hY
  have hηpos : 0 < δ / ρ := by positivity
  have hη8 : 8 * (δ / ρ) ≤ 1 := by
    have hrw : 8 * (δ / ρ) = 8 * δ / ρ := by ring
    rw [hrw, div_le_one hρ]
    exact hδρ
  set X₁ := X.filter fun u => ((#(Y.filter fun w => u + w ∉ P) : ℝ)) ≤ δ / ρ * #Y with hX₁def
  set Y₁ := Y.filter fun v => ((#(X.filter fun w => w + v ∉ P) : ℝ)) ≤ δ / ρ * #X with hY₁def
  have hX₁sub : X₁ ⊆ X := filter_subset _ _
  have hY₁sub : Y₁ ⊆ Y := filter_subset _ _
  -- The two sets of deleted elements are small.
  have hdelX : (#(X \ X₁) : ℝ) ≤ ρ * #X := by
    have hfil : X \ X₁
        = X.filter fun u => ¬ ((#(Y.filter fun w => u + w ∉ P) : ℝ)) ≤ δ / ρ * #Y := by
      rw [hX₁def, ← filter_not]
    have hlow : (#(X \ X₁) : ℝ) * (δ / ρ * #Y)
        ≤ ∑ u ∈ X \ X₁, ((#(Y.filter fun w => u + w ∉ P) : ℝ)) := by
      rw [← nsmul_eq_mul]
      apply card_nsmul_le_sum _ _ _
      intro u hu
      rw [hfil, mem_filter] at hu
      exact le_of_not_ge hu.2
    have hup : ∑ u ∈ X \ X₁, ((#(Y.filter fun w => u + w ∉ P) : ℝ))
        ≤ δ * ((#X : ℝ) * #Y) := by
      apply le_trans (sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => by positivity)
      have := sum_card_bad_left X Y P
      have hcast : ∑ u ∈ X, ((#(Y.filter fun w => u + w ∉ P) : ℝ)) = (#(badPairs X Y P) : ℝ) := by
        exact_mod_cast this
      rw [hcast]
      exact hbad
    have hkey : (#(X \ X₁) : ℝ) * (δ / ρ * #Y) ≤ δ * ((#X : ℝ) * #Y) := hlow.trans hup
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < δ * #Y)
    have hrw₁ : (#(X \ X₁) : ℝ) * (δ * #Y) = ρ * ((#(X \ X₁) : ℝ) * (δ / ρ * #Y)) := by
      field_simp
    have hrw₂ : ρ * (#X : ℝ) * (δ * #Y) = ρ * (δ * ((#X : ℝ) * #Y)) := by ring
    rw [hrw₁, hrw₂]
    exact mul_le_mul_of_nonneg_left hkey hρ.le
  have hdelY : (#(Y \ Y₁) : ℝ) ≤ ρ * #Y := by
    have hfil : Y \ Y₁
        = Y.filter fun v => ¬ ((#(X.filter fun w => w + v ∉ P) : ℝ)) ≤ δ / ρ * #X := by
      rw [hY₁def, ← filter_not]
    have hlow : (#(Y \ Y₁) : ℝ) * (δ / ρ * #X)
        ≤ ∑ v ∈ Y \ Y₁, ((#(X.filter fun w => w + v ∉ P) : ℝ)) := by
      rw [← nsmul_eq_mul]
      apply card_nsmul_le_sum _ _ _
      intro v hv
      rw [hfil, mem_filter] at hv
      exact le_of_not_ge hv.2
    have hup : ∑ v ∈ Y \ Y₁, ((#(X.filter fun w => w + v ∉ P) : ℝ))
        ≤ δ * ((#X : ℝ) * #Y) := by
      apply le_trans (sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => by positivity)
      have := sum_card_bad_right X Y P
      have hcast : ∑ v ∈ Y, ((#(X.filter fun w => w + v ∉ P) : ℝ)) = (#(badPairs X Y P) : ℝ) := by
        exact_mod_cast this
      rw [hcast]
      exact hbad
    have hkey : (#(Y \ Y₁) : ℝ) * (δ / ρ * #X) ≤ δ * ((#X : ℝ) * #Y) := hlow.trans hup
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < δ * #X)
    have hrw₁ : (#(Y \ Y₁) : ℝ) * (δ * #X) = ρ * ((#(Y \ Y₁) : ℝ) * (δ / ρ * #X)) := by
      field_simp
    have hrw₂ : ρ * (#Y : ℝ) * (δ * #X) = ρ * (δ * ((#X : ℝ) * #Y)) := by ring
    rw [hrw₁, hrw₂]
    exact mul_le_mul_of_nonneg_left hkey hρ.le
  -- Every remaining sum has many representations as `p₁ + p₂ - p₃`.
  have hfiber : ∀ z ∈ X₁ + Y₁,
      (#X : ℝ) * #Y ≤ 2 * #((P ×ˢ P ×ˢ P).filter fun t => t.1 + t.2.1 - t.2.2 = z) := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.1 hz
    rw [hX₁def, mem_filter] at hu
    rw [hY₁def, mem_filter] at hv
    set Good := (X ×ˢ Y).filter fun q => u + q.2 ∈ P ∧ q.1 + v ∈ P ∧ q.1 + q.2 ∈ P with hGood
    have hcover : (X ×ˢ Y) \ Good
        ⊆ (X ×ˢ Y.filter fun w => u + w ∉ P) ∪ ((X.filter fun w => w + v ∉ P) ×ˢ Y)
          ∪ badPairs X Y P := by
      intro q hq
      rw [mem_sdiff] at hq
      obtain ⟨hqXY, hnot⟩ := hq
      obtain ⟨hq₁, hq₂⟩ := mem_product.1 hqXY
      by_cases h₁ : u + q.2 ∈ P
      · by_cases h₂ : q.1 + v ∈ P
        · by_cases h₃ : q.1 + q.2 ∈ P
          · rw [hGood] at hnot
            exact absurd (mem_filter.2 ⟨hqXY, h₁, h₂, h₃⟩) hnot
          · exact mem_union_right _ (mem_badPairs.2 ⟨hq₁, hq₂, h₃⟩)
        · exact mem_union_left _ (mem_union_right _
            (mem_product.2 ⟨mem_filter.2 ⟨hq₁, h₂⟩, hq₂⟩))
      · exact mem_union_left _ (mem_union_left _
          (mem_product.2 ⟨hq₁, mem_filter.2 ⟨hq₂, h₁⟩⟩))
    have hcards : #(X ×ˢ Y) ≤ #Good + (#X * #(Y.filter fun w => u + w ∉ P)
        + #((X.filter fun w => w + v ∉ P)) * #Y + #(badPairs X Y P)) := by
      have hsplit := card_sdiff_add_card_eq_card (s := Good) (t := X ×ˢ Y) (filter_subset _ _)
      have hle := (card_le_card hcover).trans ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _))
      rw [card_product, card_product] at hle
      omega
    have hGoodlow : (#X : ℝ) * #Y ≤ 2 * #Good := by
      have hcast : (#(X ×ˢ Y) : ℝ) = (#X : ℝ) * #Y := by rw [card_product]; push_cast; ring
      have hcards' : (#(X ×ˢ Y) : ℝ) ≤ (#Good : ℝ) + ((#X : ℝ) * #(Y.filter fun w => u + w ∉ P)
          + (#((X.filter fun w => w + v ∉ P)) : ℝ) * #Y + #(badPairs X Y P)) := by
        exact_mod_cast hcards
      rw [hcast] at hcards'
      nlinarith [hu.2, hv.2, hbad, hη8, hxpos, hypos, hδ]
    -- The good pairs inject into the triples of `P` representing `u + v`.
    have hinj : #Good ≤ #((P ×ˢ P ×ˢ P).filter fun t => t.1 + t.2.1 - t.2.2 = u + v) := by
      apply card_le_card_of_injOn (fun q => (u + q.2, q.1 + v, q.1 + q.2))
      · intro q hq
        rw [mem_coe, hGood, mem_filter] at hq
        rw [mem_coe, mem_filter, mem_product, mem_product]
        constructor
        · exact ⟨hq.2.1, hq.2.2.1, hq.2.2.2⟩
        have hrw : u + q.2 + (q.1 + v) = u + v + (q.1 + q.2) := by abel
        rw [hrw, add_sub_cancel_right]
      · intro q _ q' _ h
        simp only [Prod.mk_inj] at h
        exact Prod.ext (add_right_cancel h.2.1) (add_left_cancel h.1)
    have : (#Good : ℝ) ≤ #((P ×ˢ P ×ˢ P).filter fun t => t.1 + t.2.1 - t.2.2 = u + v) := by
      exact_mod_cast hinj
    linarith
  -- Summing over the remaining sums.
  have hsum : (#(X₁ + Y₁) : ℝ) * ((#X : ℝ) * #Y)
      ≤ 2 * ∑ z ∈ X₁ + Y₁, (#((P ×ˢ P ×ˢ P).filter fun t => t.1 + t.2.1 - t.2.2 = z) : ℝ) := by
    rw [mul_sum, ← nsmul_eq_mul]
    exact card_nsmul_le_sum _ _ _ hfiber
  have hle : ∑ z ∈ X₁ + Y₁, (#((P ×ˢ P ×ˢ P).filter fun t => t.1 + t.2.1 - t.2.2 = z) : ℝ)
      ≤ (#P : ℝ) ^ 3 := by
    have h := sum_card_fiber_le (P ×ˢ P ×ˢ P) (fun t : G × G × G => t.1 + t.2.1 - t.2.2) (X₁ + Y₁)
    have hcard : #(P ×ˢ P ×ˢ P) = #P ^ 3 := by rw [card_product, card_product]; ring
    rw [hcard] at h
    exact_mod_cast h
  exact ⟨X₁, hX₁sub, Y₁, hY₁sub, hdelX, hdelY, by linarith⟩

end LargeSumsetsFromSubsets.Cleanup
