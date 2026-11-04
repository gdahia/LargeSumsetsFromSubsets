/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticRemoval.TripartiteGraph
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.Rify

/-!
# The arithmetic removal lemma in a set of small doubling

Let `X` be a finite subset of an abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C` be
subsets of `X`. If the equation `a + b = c` has at most `δ * #X ^ 2` solutions with `a ∈ A`,
`b ∈ B`, `c ∈ C`, and `δ ≤ removalBound K ε`, then one may delete at most `ε * #X` elements from
each of `A`, `B`, `C` so that no solution remains.

The proof is the combinatorial argument of Král, Serra and Vena. The triangles of the tripartite
graph of `LargeSumsetsFromSubsets.ArithmeticRemoval.TripartiteGraph`, built over the ambient set
`W = X ∪ (X + X)`, are the solutions of `a + b = c` together with a translation parameter, so the
solution bound makes the graph have few triangles and the triangle removal lemma deletes few edges.
An edge between two parts of the graph carries a label, namely the difference of its endpoints, and
the labels of the edges deleted between two fixed parts are counted by `removedLabelCard`. The
labels for which many edges were deleted are few, and discarding them from `A`, `B` and `C` destroys
every solution, since a surviving solution would produce `#X` triangles of which at most
`3 / 4 * #X` could have been hit.

The small doubling hypothesis enters only through the comparison of `#W` with `#X`: it is what makes
a triangle count of order `#X ^ 3` small compared to the cube of the number of vertices.

## Main definitions

* `LargeSumsetsFromSubsets.ArithmeticRemoval.removalBound K ε`: the threshold for `δ`, a fixed
  multiple of Mathlib's `triangleRemovalBound`.
* `LargeSumsetsFromSubsets.ArithmeticRemoval.removedLabelCard H H' p q a`: the number of edges of
  `H` with label `a` between the parts `p` and `q` that are deleted in the subgraph `H'`.

## Main statements

* `LargeSumsetsFromSubsets.ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne`: the
  arithmetic removal lemma in a set of small doubling.
* `LargeSumsetsFromSubsets.ArithmeticRemoval.card_filter_lt_mul_le_sum`: Markov's inequality for a
  finite sum of nonnegative terms.
-/

@[expose] public section

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum3
open scoped Pointwise

namespace LargeSumsetsFromSubsets.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {W : Finset G}

/-- **Markov's inequality** for a finite sum of nonnegative terms: the terms exceeding `m` number
at most `(∑ a ∈ s, f a) / m`. -/
lemma card_filter_lt_mul_le_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ a ∈ s, 0 ≤ f a)
    (m : ℝ) : #{a ∈ s | m < f a} * m ≤ ∑ a ∈ s, f a := by
  rw [← nsmul_eq_mul]
  grw [← sum_le_sum_of_subset_of_nonneg (filter_subset (m < f ·) s) fun a ha _ ↦ hf a ha]
  apply card_nsmul_le_sum
  intro a ha
  obtain ⟨-, ha⟩ := mem_filter.1 ha
  exact ha.le

section RemovedEdges

variable {V : Type*} [Fintype V] (H H' : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel H'.Adj]

/-- The pairs `(u, v)` of elements of the ambient set `W` such that the edge joining `p u` to `q v`
belongs to `H` but not to the subgraph `H'`. -/
def removedPairs (p q : ↥W → V) : Finset (↥W × ↥W) :=
  {(u, v) | H.Adj (p u) (q v) ∧ ¬ H'.Adj (p u) (q v)}

/-- The number of edges of `H` between the parts `p` and `q` that are deleted in `H'` and carry the
label `a`, that is, whose endpoints differ by `a`. -/
def removedLabelCard (p q : ↥W → V) (a : G) : ℕ :=
  #((removedPairs H H' p q).filter fun (u, v) ↦ (v : G) - u = a)

variable {H H'}

omit [AddCommGroup G] [DecidableEq G] in
/-- Between two disjoint parts, distinct deleted pairs give distinct deleted edges, so they number
at most the edges of `H` missing from `H'`. -/
lemma card_removedPairs_add_le (hle : H' ≤ H) {p q : ↥W → V} (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) :
    #(removedPairs H H' p q) + #H'.edgeFinset ≤ #H.edgeFinset := by
  classical
  rw [← card_sdiff_add_card_eq_card (edgeFinset_mono hle)]
  gcongr
  apply card_le_card_of_injOn fun (u, v) ↦ s(p u, q v)
  · rintro ⟨u, v⟩ hz
    simp_all [removedPairs]
  · rintro ⟨u, v⟩ - ⟨u', v'⟩ - h
    obtain ⟨h₁, h₂⟩ | ⟨h₁, -⟩ := Sym2.eq_iff.1 h
    · exact Prod.ext (hp h₁) (hq h₂)
    · exact absurd h₁ (hpq _ _)

omit [Fintype V] in
/-- Every deleted edge between two parts has a label, so the labelwise counts add up to the number
of deleted edges. -/
lemma sum_removedLabelCard {p q : ↥W → V} {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) :
    ∑ a ∈ L, removedLabelCard H H' p q a = #(removedPairs H H' p q) := by
  unfold removedLabelCard
  refine (card_eq_sum_card_fiberwise (f := fun ((u, v) : ↥W × ↥W) ↦ (v : G) - u) ?_).symm
  rintro ⟨u, v⟩ hz
  simp_all [removedPairs]

/-- Few labels can have many deleted edges: the labels with more than `m` deleted edges number at
most `(#H.edgeFinset - #H'.edgeFinset) / m`. -/
lemma card_filter_lt_removedLabelCard_mul_le (hle : H' ≤ H) {p q : ↥W → V}
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) (m : ℝ) :
    #{a ∈ L | m < removedLabelCard H H' p q a} * m ≤ #H.edgeFinset - #H'.edgeFinset := by
  grw [← card_removedPairs_add_le hle hp hq hpq]
  push_cast
  rw [add_sub_cancel_right, ← sum_removedLabelCard hL, Nat.cast_sum]
  exact card_filter_lt_mul_le_sum L (fun _ _ ↦ by positivity) m

/-- If at most `ε * x ^ 2 / 4` edges are deleted, then keeping the labels with at most `x / 4`
deleted edges discards at most `ε * x` labels. -/
lemma card_sdiff_filter_removedLabelCard_le (hle : H' ≤ H) {p q : ↥W → V}
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) {x ε : ℝ} (hx : 0 < x)
    (hedge : #H.edgeFinset - #H'.edgeFinset ≤ ε * x ^ 2 / 4) :
    #(L \ {a ∈ L | removedLabelCard H H' p q a ≤ x / 4}) ≤ ε * x := by
  rw [← filter_not]
  simp only [not_le]
  refine le_of_mul_le_mul_right ?_ hx
  nlinarith [(card_filter_lt_removedLabelCard_mul_le hle hp hq hpq hL (x / 4)).trans hedge]

omit [Fintype V] in
/-- Along an injective family of pairs `(f i, g i)` of `H`-adjacent vertices with label `a`, the
pairs whose edge is missing from `H'` are counted by `removedLabelCard H H' p q a`. -/
lemma card_filter_not_adj_le_removedLabelCard {ι : Type*} [Fintype ι] {p q : ↥W → V}
    {f g : ι → ↥W} (hf : Function.Injective f) {a : G} (hadj : ∀ i, H.Adj (p (f i)) (q (g i)))
    (hlab : ∀ i, (g i : G) - f i = a) :
    #{i | ¬ H'.Adj (p (f i)) (q (g i))} ≤ removedLabelCard H H' p q a := by
  apply card_le_card_of_injOn fun i ↦ (f i, g i)
  · intro i hi
    simp_all [removedPairs]
  · intro i _ j _ h
    exact hf (congrArg Prod.fst h)

end RemovedEdges

/-- The threshold below which the number of solutions of `a + b = c` must lie in the arithmetic
removal lemma, `exists_subset_card_sdiff_le_forall_add_ne`. It is a fixed multiple of the triangle
removal bound. -/
noncomputable def removalBound (K ε : ℝ) : ℝ := triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2

/-- The removal threshold is positive. -/
lemma removalBound_pos {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : 0 < removalBound K ε :=
  half_pos (triangleRemovalBound_pos (div_pos hε (by positivity)))

omit [AddCommGroup G] [DecidableEq G] in
/-- The tripartite graph over `W` has `3 * #W` vertices. -/
private lemma card_vertices : (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) = 3 * #W := by
  simp only [Fintype.card_sum, Fintype.card_coe, Nat.cast_add]
  ring

/-- Few solutions make few triangles: if `a + b = c` has at most `δ * #X ^ 2` solutions, with `δ` at
most `removalBound K ε`, then the tripartite graph over `W ⊇ X` has fewer triangles than the
triangle removal lemma requires. -/
private lemma card_cliqueFinset_lt {X A B C : Finset G} {K ε δ : ℝ} (hXW : X ⊆ W) (hK : 0 ≤ K)
    (hε : 0 < ε) (hX : X.Nonempty) (hδ : δ ≤ removalBound K ε)
    (hsol : #(sumTriples A B C) ≤ δ * #X ^ 2) :
    #((tripartiteGraph W A B C).cliqueFinset 3)
      < triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) * Fintype.card (↥W ⊕ ↥W ⊕ ↥W) ^ 3 := by
  have hW : (0 : ℝ) < #W := by exact_mod_cast (hX.mono hXW).card_pos
  have hbound := triangleRemovalBound_pos (div_pos hε (by positivity : (0 : ℝ) < 36 * (1 + K) ^ 2))
  grw [card_cliqueFinset_le, card_triangleIndices_le, card_vertices]
  push_cast
  grw [hsol, hδ, removalBound, card_le_card hXW]
  linarith [mul_pos hbound (pow_pos hW 3)]

omit [AddCommGroup G] [DecidableEq G] in
/-- The removal parameter is chosen so that the triangle removal lemma deletes at most
`ε * #X ^ 2 / 4` edges, as long as `#W ≤ (1 + K) * #X`. -/
private lemma div_mul_card_vertices_sq_le {X : Finset G} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hW : #W ≤ (1 + K) * #X) :
    ε / (36 * (1 + K) ^ 2) * ((Fintype.card (↥W ⊕ ↥W ⊕ ↥W) ^ 2 : ℕ) : ℝ) ≤ ε * #X ^ 2 / 4 := by
  push_cast
  grw [card_vertices, hW]
  apply le_of_eq
  field_simp
  ring

/-- The map `x ↦ x + t` from `X` to the ambient set `W`. -/
private def shiftIn {X : Finset G} {t : G} (h : ∀ x ∈ X, x + t ∈ W) : ↥X → ↥W :=
  Subtype.map (· + t) h

omit [DecidableEq G] in
/-- The map `shiftIn` adds `t`. -/
@[simp]
private lemma coe_shiftIn {X : Finset G} {t : G} (h : ∀ x ∈ X, x + t ∈ W) (x : ↥X) :
    (shiftIn h x : G) = x + t := rfl

omit [DecidableEq G] in
/-- Translation is injective. -/
private lemma shiftIn_injective {X : Finset G} {t : G} (h : ∀ x ∈ X, x + t ∈ W) :
    Function.Injective (shiftIn h) :=
  Subtype.map_injective h (add_left_injective t)

/-- A solution `a + b = c` gives the `#X` triangle indices `(x, x + a, x + c)` with `x ∈ X`. A
triangle-free subgraph `H'` misses an edge of each of them, so the labels `a`, `b` and `c` together
carry at least `#X` deleted edges. -/
private lemma card_le_removedLabelCard_add {X A B C : Finset G}
    {H' : SimpleGraph (↥W ⊕ ↥W ⊕ ↥W)} [DecidableRel H'.Adj] (hfree : H'.CliqueFree 3)
    {a b c : G} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (habc : a + b = c)
    (hu : ∀ x ∈ X, x + 0 ∈ W) (hv : ∀ x ∈ X, x + a ∈ W) (hw : ∀ x ∈ X, x + c ∈ W) :
    #X ≤ removedLabelCard (tripartiteGraph W A B C) H' in₀ in₁ a
      + removedLabelCard (tripartiteGraph W A B C) H' in₁ in₂ b
      + removedLabelCard (tripartiteGraph W A B C) H' in₀ in₂ c := by
  subst habc
  have hmem (x : ↥X) : (shiftIn hu x, shiftIn hv x, shiftIn hw x) ∈ triangleIndices W A B C := by
    simp [ha, hb, hc]
  have hcover : (univ : Finset ↥X)
      ⊆ ({x | ¬ H'.Adj (in₀ (shiftIn hu x)) (in₁ (shiftIn hv x))} : Finset ↥X)
        ∪ ({x | ¬ H'.Adj (in₁ (shiftIn hv x)) (in₂ (shiftIn hw x))} : Finset ↥X)
        ∪ ({x | ¬ H'.Adj (in₀ (shiftIn hu x)) (in₂ (shiftIn hw x))} : Finset ↥X) := by
    intro x _
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_contra! ⟨⟨h₀₁, h₁₂⟩, h₀₂⟩
    exact hfree _ (is3Clique_triple_iff.2 ⟨h₀₁, h₀₂, h₁₂⟩)
  rw [← Fintype.card_coe, ← card_univ]
  grw [hcover, card_union_le, card_union_le]
  gcongr ?_ + ?_ + ?_
  · exact card_filter_not_adj_le_removedLabelCard (shiftIn_injective hu)
      (fun x ↦ adj_in₀_in₁ (hmem x)) (by simp)
  · exact card_filter_not_adj_le_removedLabelCard (shiftIn_injective hv)
      (fun x ↦ adj_in₁_in₂ (hmem x)) (by simp)
  · exact card_filter_not_adj_le_removedLabelCard (shiftIn_injective hu)
      (fun x ↦ adj_in₀_in₂ (hmem x)) (by simp)

/-- The arithmetic removal lemma, with the ambient set `W` supplied by hand: it need only contain
`X` and all the sums `x + y` with `x, y ∈ X`, and be comparable in size to `X`. The middle set `B`
is unconstrained, since an element of `B` outside `X - X` takes part in no solution anyway. The sets
`A'`, `B'`, `C'` keep the labels carrying at most `#X / 4` deleted edges. -/
private lemma exists_subset_card_sdiff_le_forall_add_ne_of_subset {X A B C W : Finset G}
    {K ε δ : ℝ} (hA : A ⊆ X) (hC : C ⊆ X) (hXW : X ⊆ W) (hXXW : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ W)
    (hW : #W ≤ (1 + K) * #X) (hK : 0 ≤ K) (hε : 0 < ε) (hX : X.Nonempty)
    (hδ : δ ≤ removalBound K ε) (hsol : #(sumTriples A B C) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C, #(A \ A') ≤ ε * #X ∧ #(B \ B') ≤ ε * #X ∧ #(C \ C') ≤ ε * #X ∧
      ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  obtain ⟨H', hle, _, hedge, hfree⟩ :=
    triangle_removal (card_cliqueFinset_lt hXW hK hε hX hδ hsol)
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hedge' : #(tripartiteGraph W A B C).edgeFinset - #H'.edgeFinset ≤ ε * #X ^ 2 / 4 :=
    hedge.le.trans (div_mul_card_vertices_sq_le hK hε hW)
  refine ⟨{a ∈ A | removedLabelCard (tripartiteGraph W A B C) H' in₀ in₁ a ≤ (#X : ℝ) / 4},
    filter_subset _ _,
    {b ∈ B | removedLabelCard (tripartiteGraph W A B C) H' in₁ in₂ b ≤ (#X : ℝ) / 4},
    filter_subset _ _,
    {c ∈ C | removedLabelCard (tripartiteGraph W A B C) H' in₀ in₂ c ≤ (#X : ℝ) / 4},
    filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · exact card_sdiff_filter_removedLabelCard_le hle Sum.inl_injective
      (Sum.inr_injective.comp Sum.inl_injective) (by simp) (fun _ _ ↦ sub_mem_of_adj_in₀_in₁)
      hXpos hedge'
  · exact card_sdiff_filter_removedLabelCard_le hle (Sum.inr_injective.comp Sum.inl_injective)
      (Sum.inr_injective.comp Sum.inr_injective) (by simp) (fun _ _ ↦ sub_mem_of_adj_in₁_in₂)
      hXpos hedge'
  · exact card_sdiff_filter_removedLabelCard_le hle Sum.inl_injective
      (Sum.inr_injective.comp Sum.inr_injective) (by simp) (fun _ _ ↦ sub_mem_of_adj_in₀_in₂)
      hXpos hedge'
  intro a ha b hb c hc habc
  obtain ⟨ha, ha'⟩ := mem_filter.1 ha
  obtain ⟨hb, hb'⟩ := mem_filter.1 hb
  obtain ⟨hc, hc'⟩ := mem_filter.1 hc
  have hcard := card_le_removedLabelCard_add hfree ha hb hc habc
    (fun x hx ↦ by simpa using hXW hx) (fun x hx ↦ hXXW x hx a (hA ha))
    (fun x hx ↦ hXXW x hx c (hC hc))
  rify at hcard
  linarith

/-- **Arithmetic removal lemma in a set of small doubling.** Let `X` be a finite subset of an
abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C ⊆ X`. If `a + b = c` has at most
`δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `δ ≤ removalBound K ε`, then one can
remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no solution remains. -/
lemma exists_subset_card_sdiff_le_forall_add_ne {X A B C : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X) (hK : 0 ≤ K) (hXX : #(X + X) ≤ K * #X) (hε : 0 < ε)
    (hδ : δ ≤ removalBound K ε) (hsol : #(sumTriples A B C) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C, #(A \ A') ≤ ε * #X ∧ #(B \ B') ≤ ε * #X ∧ #(C \ C') ≤ ε * #X ∧
      ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp_all
  refine exists_subset_card_sdiff_le_forall_add_ne_of_subset (W := X ∪ (X + X)) hA hC
    subset_union_left (fun x hx y hy ↦ mem_union_right _ (add_mem_add hx hy)) ?_ hK hε hX hδ hsol
  grw [card_union_le]
  push_cast
  linarith

end LargeSumsetsFromSubsets.ArithmeticRemoval
