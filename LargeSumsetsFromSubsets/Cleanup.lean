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

* `LargeSumsetsFromSubsets.Cleanup.exists_subset_card_sdiff_le_card_add_le` is the sharp one
  and applies when
  `#(X + Y)` is at most a constant multiple of `min #X #Y`. It removes from `X`, `Y` and
  `(X + Y) \ P` a few elements so that no sum survives outside `P`, by the arithmetic removal
  lemma applied inside a translate of `X + Y`, whose doubling is bounded by the Plünnecke–Ruzsa
  inequality. It is a variant of Shao's almost-all Balog–Szemerédi–Gowers theorem
  (arXiv:1811.10707, Theorem 1.1), which assumes instead that the sums of the pairs in a set
  `Γ ⊆ X ×ˢ Y` of density `1 - δ` are few. Here `Γ` is the set of pairs with sum in `P`, and the
  hypothesis on `#(X + Y)` is an additional one.
* `LargeSumsetsFromSubsets.Cleanup.exists_subset_card_sdiff_le_card_add_mul_le` is the crude
  one but has no restriction on `#(X + Y)`. It only gives
  `#(X₀ + Y₀) ≤ 2 * #P ^ 3 / (#X * #Y)`, but it is elementary: every `z ∈ X₀ + Y₀` has many
  representations as `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`.

The form of the sharp cleanup with an unspecified threshold is
`LargeSumsetsFromSubsets.exists_forall_exists_subset_card_sdiff_le_card_add_le`.
-/

@[expose] public section

open Finset

open scoped Pointwise

namespace LargeSumsetsFromSubsets.Cleanup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ### Translates

Translates are Mathlib's pointwise `t +ᵥ s`; only the membership criterion in the form used
throughout this file needs to be spelled out.
-/

/-- An element lies in the translate `t +ᵥ s` when its difference with `t` lies in `s`. -/
lemma mem_vadd_finset_iff_sub_mem {t a : G} {s : Finset G} : a ∈ t +ᵥ s ↔ a - t ∈ s := by
  rw [← Finset.neg_vadd_mem_iff, vadd_eq_add, neg_add_eq_sub]

/-- A translate of `X` sits inside the corresponding translate of `X + Y`. -/
private lemma neg_vadd_subset_left {X Y : Finset G} {u v : G} (hv : v ∈ Y) :
    (-u) +ᵥ X ⊆ (-(u + v)) +ᵥ (X + Y) := by
  intro a ha
  rw [mem_vadd_finset_iff_sub_mem] at ha ⊢
  convert add_mem_add ha hv using 1
  abel

/-- A translate of `Y` sits inside the corresponding translate of `X + Y`. -/
private lemma neg_vadd_subset_right {X Y : Finset G} {u v : G} (hu : u ∈ X) :
    (-v) +ᵥ Y ⊆ (-(u + v)) +ᵥ (X + Y) := by
  intro b hb
  rw [mem_vadd_finset_iff_sub_mem] at hb ⊢
  convert add_mem_add hu hb using 1
  abel

/-- Translating back a subset `A'` of a translate `-u +ᵥ X` deletes as many elements of `X` as
`A'` deletes from the translate. -/
private lemma card_sdiff_vadd {X A' : Finset G} (u : G) :
    #(X \ (u +ᵥ A')) = #(((-u) +ᵥ X) \ A') := by
  rw [← card_vadd_finset u ((-u +ᵥ X) \ A'), vadd_finset_sdiff, vadd_neg_vadd]

/-! ### A bound for the fourfold sumset -/

/-- The Ruzsa triangle inequality bounds the doubling of `X` by the square of `#(X + Y)`. -/
lemma card_self_add_mul_le (X Y : Finset G) : #(X + X) * #Y ≤ #(X + Y) * #(X + Y) := by
  simpa [add_comm Y X] using ruzsa_triangle_inequality_add_add_add X Y X

/-- The Plünnecke–Ruzsa inequality for the fourfold sumset, cleared of denominators. -/
private lemma card_four_nsmul_mul_le {X : Finset G} (hX : X.Nonempty) (U : Finset G) :
    #((4 : ℕ) • U) * #X ^ 3 ≤ #(X + U) ^ 4 := by
  have hpr := pluennecke_ruzsa_inequality_nsmul_add hX U 4
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hpr
  refine Nat.le_of_mul_le_mul_right ?_ hX.card_pos
  rw [mul_assoc, ← pow_succ]
  exact_mod_cast hpr

/-- The fourfold sumset `2X + 2Y` is controlled by `#(X + Y)`: this is the Plünnecke–Ruzsa
inequality applied to `X ∪ Y` with base `X`, together with the Ruzsa triangle inequality. -/
lemma card_add_add_le (X Y : Finset G) (hX : X.Nonempty) :
    #((X + Y) + (X + Y)) * (#X ^ 3 * #Y ^ 4) ≤ 16 * #(X + Y) ^ 8 := by
  have hXU : #(X + (X ∪ Y)) * #Y ≤ 2 * #(X + Y) ^ 2 := by
    rw [add_union]
    nlinarith [Nat.mul_le_mul_right #Y (card_union_le (X + X) (X + Y)), card_self_add_mul_le X Y,
      Nat.mul_le_mul_left #(X + Y) (card_le_card_add_left hX : #Y ≤ #(X + Y))]
  have hsub : (X + Y) + (X + Y) ⊆ (4 : ℕ) • (X ∪ Y) := by
    rw [(by norm_num : 4 = 2 + 2), add_nsmul, two_nsmul]
    gcongr <;> simp
  refine le_trans ?_ ((Nat.pow_le_pow_left hXU 4).trans_eq (by ring))
  rw [mul_pow, ← mul_assoc]
  gcongr
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans (card_four_nsmul_mul_le hX _)

/-- If `#(X + Y) ≤ D * min #X #Y`, then the doubling of `X + Y` is at most `16 * D ^ 7`. -/
private lemma card_add_add_le_mul {X Y : Finset G} (hX : X.Nonempty) (hY : Y.Nonempty) {D : ℝ}
    (hD : 0 ≤ D) (hS : (#(X + Y) : ℝ) ≤ D * min (#X : ℝ) (#Y : ℝ)) :
    (#((X + Y) + (X + Y)) : ℝ) ≤ 16 * D ^ 7 * #(X + Y) := by
  have hS7 : (#(X + Y) : ℝ) ^ 7 ≤ D ^ 7 * (#X ^ 3 * #Y ^ 4) :=
    calc (#(X + Y) : ℝ) ^ 7 ≤ (D * min (#X : ℝ) (#Y : ℝ)) ^ 7 := by gcongr
      _ = D ^ 7 * (min (#X : ℝ) (#Y : ℝ) ^ 3 * min (#X : ℝ) (#Y : ℝ) ^ 4) := by ring
      _ ≤ D ^ 7 * (#X ^ 3 * #Y ^ 4) := by
        gcongr
        exacts [min_le_left _ _, min_le_right _ _]
  have h16 : (#((X + Y) + (X + Y)) : ℝ) * (#X ^ 3 * #Y ^ 4) ≤ 16 * #(X + Y) ^ 8 := by
    exact_mod_cast card_add_add_le X Y hX
  refine le_of_mul_le_mul_right ?_
    (pow_pos (by exact_mod_cast (hX.add hY).card_pos : (0 : ℝ) < #(X + Y)) 7)
  nlinarith [mul_le_mul_of_nonneg_left hS7 (by positivity : (0 : ℝ) ≤ #((X + Y) + (X + Y))),
    mul_le_mul_of_nonneg_left h16 (pow_nonneg hD 7)]

/-! ### The sharp cleanup, via arithmetic removal -/

/-- The pairs of `X ×ˢ Y` whose sum misses `P`. -/
def badPairs (X Y P : Finset G) : Finset (G × G) := (X ×ˢ Y).filter fun p => p.1 + p.2 ∉ P

/-- A pair is bad when its entries lie in `X` and `Y` and its sum misses `P`. -/
lemma mem_badPairs {X Y P : Finset G} {p : G × G} :
    p ∈ badPairs X Y P ↔ p.1 ∈ X ∧ p.2 ∈ Y ∧ p.1 + p.2 ∉ P := by
  simp [badPairs, and_assoc]

/-- The solutions of `a + b = c` in the translated sets are exactly the bad pairs. -/
lemma card_sumTriples_neg_vadd_eq_card_badPairs (X Y P : Finset G) (u v : G) :
    #(ArithmeticRemoval.sumTriples ((-u) +ᵥ X) ((-v) +ᵥ Y) ((-(u + v)) +ᵥ ((X + Y) \ P)))
      = #(badPairs X Y P) := by
  symm
  apply card_bij (fun p _ ↦ (p.1 - u, p.2 - v, p.1 + p.2 - (u + v)))
  · rintro ⟨x, y⟩ hp
    rw [mem_badPairs] at hp
    obtain ⟨hx, hy, hxy⟩ := hp
    refine ArithmeticRemoval.mem_sumTriples.2 ⟨?_, ?_, ?_, sub_add_sub_comm _ _ _ _⟩ <;>
      rw [mem_vadd_finset_iff_sub_mem]
    · simpa using hx
    · simpa using hy
    · rw [sub_neg_eq_add, sub_add_cancel]
      exact mem_sdiff.2 ⟨add_mem_add hx hy, hxy⟩
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
    simp_all
  · rintro ⟨a, b, c⟩ ht
    simp only [ArithmeticRemoval.mem_sumTriples, mem_vadd_finset_iff_sub_mem, mem_sdiff,
      sub_neg_eq_add] at ht
    obtain ⟨ha, hb, ⟨-, hc⟩, rfl⟩ := ht
    refine ⟨(a + u, b + v), mem_badPairs.2 ⟨ha, hb, ?_⟩, ?_⟩
    · rwa [add_add_add_comm]
    · simp only [Prod.mk.injEq]
      refine ⟨by abel, by abel, by abel⟩

/-- If no solution of `a + b = c` survives with `a ∈ A'`, `b ∈ B'` and `c ∈ C'`, then translating
`A'` and `B'` back gives sums that lie in `P` or come from an element of the translate of
`(X + Y) \ P` deleted in `C'`. -/
private lemma vadd_add_vadd_subset {X Y P A' B' C' : Finset G} {u v : G} (hA' : A' ⊆ (-u) +ᵥ X)
    (hB' : B' ⊆ (-v) +ᵥ Y) (hfree : ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c) :
    (u +ᵥ A') + (v +ᵥ B') ⊆ P ∪ ((u + v) +ᵥ (((-(u + v)) +ᵥ ((X + Y) \ P)) \ C')) := by
  rw [vadd_add_vadd_comm]
  intro z hz
  obtain ⟨_, hw, rfl⟩ := mem_vadd_finset.1 hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hw
  by_cases hP : (u + v) +ᵥ (a + b) ∈ P
  · exact mem_union_left _ hP
  refine mem_union_right _ ((vadd_mem_vadd_finset_iff _).2
    (mem_sdiff.2 ⟨?_, fun hc ↦ hfree a ha b hb _ hc rfl⟩))
  rw [mem_neg_vadd_finset_iff, mem_sdiff, vadd_eq_add, add_add_add_comm]
  exact ⟨add_mem_add (mem_neg_vadd_finset_iff.1 (hA' ha)) (mem_neg_vadd_finset_iff.1 (hB' hb)),
    by rwa [vadd_eq_add, add_add_add_comm] at hP⟩

/-- **The cleanup lemma.** If all but a `δ` proportion of the pairs of `X ×ˢ Y` have their sum in
`P`, and if `#(X + Y)` is at most `D * min #X #Y`, then removing a `ρ`-fraction of `min #X #Y`
elements from `X` and from `Y` leaves a pair whose whole sumset exceeds `P` by at most
`ρ * min #X #Y` elements.

The proof translates `X` and `Y` by `-u` and `-v` for some `u ∈ X` and `v ∈ Y`, so that both land
in the translate `Z` of `X + Y` by `-(u + v)`, whose doubling is bounded by `card_add_add_le_mul`.
The bad pairs are the solutions of `a + b = c` with `c` in the translate of `(X + Y) \ P`, so the
arithmetic removal lemma inside `Z` deletes few elements from the three translates and destroys all
of these solutions. -/
theorem exists_subset_card_sdiff_le_card_add_le {X Y P : Finset G} (hX : X.Nonempty)
    (hY : Y.Nonempty) {D ρ δ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ)
    (hS : #(X + Y) ≤ D * min (#X : ℝ) #Y) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ ArithmeticRemoval.removalConst (16 * D ^ 7) (ρ / D))
    (hbad : #{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} ≤ δ * (#X * #Y)) :
    ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, #(X \ X₀) ≤ ρ * min (#X : ℝ) #Y ∧ #(Y \ Y₀) ≤ ρ * min (#X : ℝ) #Y ∧
      #(X₀ + Y₀) ≤ #P + ρ * min (#X : ℝ) #Y := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨v, hv⟩ := hY
  have hZ : #((-(u + v)) +ᵥ (X + Y)) = #(X + Y) := card_vadd_finset _ _
  have hXY : #X * #Y ≤ #(X + Y) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (card_le_card_add_right ⟨v, hv⟩) (card_le_card_add_left ⟨u, hu⟩)
  obtain ⟨A', hA', B', hB', C', -, hAdel, hBdel, hCdel, hfree⟩ :=
    ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne (K := 16 * D ^ 7) (ε := ρ / D)
      (neg_vadd_subset_left hv) (neg_vadd_subset_right hu)
      (vadd_finset_subset_vadd_finset sdiff_subset) (by positivity)
      (by
        rw [vadd_add_vadd_comm, card_vadd_finset, hZ]
        exact card_add_add_le_mul ⟨u, hu⟩ ⟨v, hv⟩ (by linarith) hS)
      (by positivity) hδ hδ'
      (by
        rw [← ArithmeticRemoval.sumTriples, card_sumTriples_neg_vadd_eq_card_badPairs, hZ]
        exact hbad.trans (by gcongr; exact_mod_cast hXY))
  have hdel : ρ / D * #((-(u + v)) +ᵥ (X + Y)) ≤ ρ * min (#X : ℝ) (#Y : ℝ) := by
    rw [hZ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨u +ᵥ A', vadd_finset_subset_iff.2 hA', v +ᵥ B', vadd_finset_subset_iff.2 hB', ?_, ?_, ?_⟩
  · rw [card_sdiff_vadd]
    exact hAdel.trans hdel
  · rw [card_sdiff_vadd]
    exact hBdel.trans hdel
  refine (Nat.cast_le.2 ((card_le_card (vadd_add_vadd_subset (P := P) hA' hB' hfree)).trans
    (card_union_le _ _))).trans ?_
  push_cast
  rw [card_vadd_finset]
  linarith [hCdel.trans hdel]

/-! ### The crude covering bound -/

/-- Counting the bad pairs one first coordinate at a time. -/
lemma sum_card_filter_eq_card_badPairs_left (X Y P : Finset G) :
    ∑ u ∈ X, #(Y.filter fun w => u + w ∉ P) = #(badPairs X Y P) := by
  simp only [badPairs, card_filter, sum_product]

/-- Counting the bad pairs one second coordinate at a time. -/
lemma sum_card_filter_eq_card_badPairs_right (X Y P : Finset G) :
    ∑ v ∈ Y, #(X.filter fun w => w + v ∉ P) = #(badPairs X Y P) := by
  simp only [badPairs, card_filter, sum_product_right]

omit [AddCommGroup G] in
/-- Markov's inequality for a count: if `∑ u ∈ X, f u ≤ δ * (#X * n)`, then at most `ρ * #X`
elements `u` of `X` have `f u > δ / ρ * n`. -/
private lemma card_sdiff_filter_le {X : Finset G} {f : G → ℕ} {δ ρ n : ℝ} (hδ : 0 < δ)
    (hρ : 0 < ρ) (hn : 0 < n) (hf : ∑ u ∈ X, (f u : ℝ) ≤ δ * (#X * n)) :
    (#(X \ {u ∈ X | (f u : ℝ) ≤ δ / ρ * n}) : ℝ) ≤ ρ * #X := by
  rw [← filter_not]
  have hlow : (#{u ∈ X | ¬ (f u : ℝ) ≤ δ / ρ * n} : ℝ) * (δ / ρ * n) ≤ δ * (#X * n) := by
    rw [← nsmul_eq_mul]
    refine (card_nsmul_le_sum _ _ _ ?_).trans ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ ↦ by positivity).trans hf)
    intro u hu
    obtain ⟨-, hu⟩ := mem_filter.1 hu
    exact (not_le.1 hu).le
  have hρlow := mul_le_mul_of_nonneg_right hlow hρ.le
  rw [mul_assoc, (by field_simp : δ / ρ * n * ρ = δ * n)] at hρlow
  refine le_of_mul_le_mul_right ?_ (mul_pos hδ hn)
  linarith

/-- The pairs `(x, y) ∈ X ×ˢ Y` such that `u + y`, `x + v` and `x + y` all lie in `P`. Each of them
gives the representation `u + v = (u + y) + (x + v) - (x + y)`. -/
private def goodPairs (X Y P : Finset G) (u v : G) : Finset (G × G) :=
  {q ∈ X ×ˢ Y | u + q.2 ∈ P ∧ q.1 + v ∈ P ∧ q.1 + q.2 ∈ P}

/-- The good pairs inject into the representations of `u + v` as `p₁ + p₂ - p₃`. -/
private lemma card_goodPairs_le (X Y P : Finset G) (u v : G) :
    #(goodPairs X Y P u v) ≤ #{t ∈ P ×ˢ P ×ˢ P | t.1 + t.2.1 - t.2.2 = u + v} := by
  apply card_le_card_of_injOn (fun q ↦ (u + q.2, q.1 + v, q.1 + q.2))
  · rintro ⟨x, y⟩ hq
    simp only [goodPairs, mem_coe, mem_filter, mem_product] at hq
    obtain ⟨-, hy, hx, hxy⟩ := hq
    simp only [mem_coe, mem_filter, mem_product]
    exact ⟨⟨hy, hx, hxy⟩, by abel⟩
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
    simp_all

/-- A pair of `X ×ˢ Y` that is not good is bad, or has a bad partner of `u` or of `v`. -/
private lemma card_le_card_goodPairs_add (X Y P : Finset G) (u v : G) :
    #X * #Y ≤ #(goodPairs X Y P u v) + #X * #{w ∈ Y | u + w ∉ P}
      + #{w ∈ X | w + v ∉ P} * #Y + #(badPairs X Y P) := by
  have hcover : X ×ˢ Y ⊆ goodPairs X Y P u v ∪ X ×ˢ {w ∈ Y | u + w ∉ P}
      ∪ {w ∈ X | w + v ∉ P} ×ˢ Y ∪ badPairs X Y P := by
    rintro ⟨x, y⟩ hq
    simp only [mem_product] at hq
    simp only [goodPairs, mem_union, mem_filter, mem_product, mem_badPairs, hq]
    tauto
  rw [← card_product, ← card_product, ← card_product]
  exact (card_le_card hcover).trans ((card_union_le _ _).trans (add_le_add_left
    ((card_union_le _ _).trans (add_le_add_left (card_union_le _ _) _)) _))

/-- If `u` and `v` have few bad partners and there are few bad pairs, then `u + v` has at least
`#X * #Y / 2` representations as `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`. -/
private lemma card_mul_le_two_mul_card {X Y P : Finset G} {u v : G} {δ η : ℝ}
    (hδ : 8 * δ ≤ 1) (hη : 8 * η ≤ 1)
    (hu : (#{w ∈ Y | u + w ∉ P} : ℝ) ≤ η * #Y) (hv : (#{w ∈ X | w + v ∉ P} : ℝ) ≤ η * #X)
    (hbad : (#(badPairs X Y P) : ℝ) ≤ δ * ((#X : ℝ) * #Y)) :
    (#X : ℝ) * #Y ≤ 2 * #{t ∈ P ×ˢ P ×ˢ P | t.1 + t.2.1 - t.2.2 = u + v} := by
  have hgood : (#X : ℝ) * #Y ≤ #(goodPairs X Y P u v) + #X * #{w ∈ Y | u + w ∉ P}
      + #{w ∈ X | w + v ∉ P} * #Y + #(badPairs X Y P) := by
    exact_mod_cast card_le_card_goodPairs_add X Y P u v
  have hrepr : (#(goodPairs X Y P u v) : ℝ)
      ≤ #{t ∈ P ×ˢ P ×ˢ P | t.1 + t.2.1 - t.2.2 = u + v} := by
    exact_mod_cast card_goodPairs_le X Y P u v
  nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ #X),
    mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℝ) ≤ #Y),
    mul_nonneg (by positivity : (0 : ℝ) ≤ #X) (by positivity : (0 : ℝ) ≤ #Y)]

/-- If every element of `S` has at least `m / 2` representations as `p₁ + p₂ - p₃` with
`p₁, p₂, p₃ ∈ P`, then `#S * m ≤ 2 * #P ^ 3`. -/
private lemma card_mul_le_of_forall_le {S P : Finset G} {m : ℝ}
    (h : ∀ z ∈ S, m ≤ 2 * #{t ∈ P ×ˢ P ×ˢ P | t.1 + t.2.1 - t.2.2 = z}) :
    (#S : ℝ) * m ≤ 2 * (#P : ℝ) ^ 3 := by
  rw [← nsmul_eq_mul]
  refine (card_nsmul_le_sum _ _ _ h).trans ?_
  rw [← mul_sum, ← Nat.cast_sum]
  gcongr
  exact_mod_cast ((sum_card_fiberwise_eq_card_filter (P ×ˢ P ×ˢ P) S
    fun t ↦ t.1 + t.2.1 - t.2.2).trans_le (card_filter_le _ _)).trans_eq
      (by rw [card_product, card_product]; ring)

/-- **The covering bound.** If all but a `δ` proportion of the pairs of `X ×ˢ Y` have their sum in
`P`, then after deleting a `ρ`-fraction of `X` and of `Y` every remaining sum has at least
`#X * #Y / 2` representations as `p₁ + p₂ - p₃` with `p₁, p₂, p₃ ∈ P`, whence the remaining sumset
has at most `2 * #P ^ 3 / (#X * #Y)` elements. The deleted elements are those with more than a
`δ / ρ` proportion of bad partners. -/
lemma exists_subset_card_sdiff_le_card_add_mul_le {X Y P : Finset G} (hX : X.Nonempty)
    (hY : Y.Nonempty) {δ ρ : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1) (hδρ : 8 * δ ≤ ρ)
    (hbad : (#(badPairs X Y P) : ℝ) ≤ δ * ((#X : ℝ) * #Y)) :
    ∃ X₁ ⊆ X, ∃ Y₁ ⊆ Y,
      (#(X \ X₁) : ℝ) ≤ ρ * #X ∧ (#(Y \ Y₁) : ℝ) ≤ ρ * #Y ∧
      (#(X₁ + Y₁) : ℝ) * ((#X : ℝ) * #Y) ≤ 2 * (#P : ℝ) ^ 3 := by
  have hρ : 0 < ρ := by linarith
  refine ⟨{u ∈ X | (#{w ∈ Y | u + w ∉ P} : ℝ) ≤ δ / ρ * #Y}, filter_subset _ _,
    {v ∈ Y | (#{w ∈ X | w + v ∉ P} : ℝ) ≤ δ / ρ * #X}, filter_subset _ _,
    card_sdiff_filter_le hδ hρ (by exact_mod_cast hY.card_pos) ?_,
    card_sdiff_filter_le hδ hρ (by exact_mod_cast hX.card_pos) ?_, ?_⟩
  · rw [← Nat.cast_sum, sum_card_filter_eq_card_badPairs_left]
    exact hbad
  · rw [← Nat.cast_sum, sum_card_filter_eq_card_badPairs_right, mul_comm (#Y : ℝ)]
    exact hbad
  apply card_mul_le_of_forall_le
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.1 hz
  obtain ⟨-, hu⟩ := mem_filter.1 hu
  obtain ⟨-, hv⟩ := mem_filter.1 hv
  exact card_mul_le_two_mul_card (by linarith) (by rw [mul_div_assoc', div_le_one hρ]; linarith)
    hu hv hbad

end LargeSumsetsFromSubsets.Cleanup

namespace LargeSumsetsFromSubsets

/-- **Almost all sums in a small set.** For $D \ge 1$ and $\rho > 0$ there is $\delta > 0$ with
the following property. Let $X$ and $Y$ be finite nonempty subsets of an abelian group with
$|X + Y| \le D \min(|X|, |Y|)$, and let $P$ be a finite set. If at most $\delta |X| |Y|$ pairs in
$X \times Y$ have their sum outside $P$, then one can remove at most $\rho \min(|X|, |Y|)$ elements
from each of $X$ and $Y$ so that the sumset of the remaining sets has at most
$|P| + \rho \min(|X|, |Y|)$ elements. -/
theorem exists_forall_exists_subset_card_sdiff_le_card_add_le {D ρ : ℝ} (hD : 1 ≤ D)
    (hρ : 0 < ρ) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X Y P : Finset G},
      X.Nonempty → Y.Nonempty → #(X + Y) ≤ D * min (#X : ℝ) #Y →
      #{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} ≤ δ * (#X * #Y) →
      ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y, #(X \ X₀) ≤ ρ * min (#X : ℝ) #Y ∧ #(Y \ Y₀) ≤ ρ * min (#X : ℝ) #Y ∧
        #(X₀ + Y₀) ≤ #P + ρ * min (#X : ℝ) #Y := by
  have hδ := ArithmeticRemoval.removalConst_pos (by positivity : (0 : ℝ) ≤ 16 * D ^ 7)
    (div_pos hρ (by linarith : (0 : ℝ) < D))
  exact ⟨_, hδ, fun hX hY hS hbad ↦
    Cleanup.exists_subset_card_sdiff_le_card_add_le hX hY hD hρ hS hδ.le le_rfl hbad⟩

end LargeSumsetsFromSubsets
