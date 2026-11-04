/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# The tripartite graph of the equation `a + b = c`

Following Král, Serra and Vena, we attach to three subsets `A`, `B`, `C` of an abelian group `G` and
to a finite ambient set `W` a tripartite graph on `W ⊕ W ⊕ W`. Its triangle indices are the triples
`(u, v, w)` of elements of `W` with `v - u ∈ A`, `w - v ∈ B` and `w - u ∈ C`, that is, the triples
`(u, u + a, u + c)` with `a ∈ A`, `b ∈ B`, `c ∈ C` and `a + b = c`. Two vertices are joined exactly
when they both belong to some triangle index, so an edge between the first and the second part
carries a label in `A`, an edge between the second and the third part a label in `B`, and an edge
between the first and the third part a label in `C`.

The graph is tripartite by construction: the three parts are copies of `W` in a sum type, so all
triangles are transversal and each edge knows which two parts it joins. This is why the ordinary,
uncolored triangle removal lemma suffices, with no need for a directed or colored variant.

## Main definitions

* `LargeSumsetsFromSubsets.ArithmeticRemoval.sumTriples A B C`: the solutions of `a + b = c` with
  `a ∈ A`, `b ∈ B` and `c ∈ C`.
* `LargeSumsetsFromSubsets.ArithmeticRemoval.triangleIndices W A B C`: the triples `(u, v, w)` of
  elements of `W` with `v - u ∈ A`, `w - v ∈ B` and `w - u ∈ C`.
* `LargeSumsetsFromSubsets.ArithmeticRemoval.tripartiteGraph W A B C`: the tripartite graph on
  `W ⊕ W ⊕ W` built from these triangle indices.

## Main statements

* `LargeSumsetsFromSubsets.ArithmeticRemoval.card_cliqueFinset_le`: every triangle of the graph is
  a triangle index.
* `LargeSumsetsFromSubsets.ArithmeticRemoval.card_triangleIndices_le`: there are at most `#W`
  triangle indices per solution of `a + b = c`.
-/

@[expose] public section

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum3

namespace LargeSumsetsFromSubsets.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {W A B C : Finset G}

/-- The solutions of `a + b = c` with `a ∈ A`, `b ∈ B` and `c ∈ C`. -/
def sumTriples (A B C : Finset G) : Finset (G × G × G) :=
  (A ×ˢ B ×ˢ C).filter fun (a, b, c) ↦ a + b = c

/-- A triple belongs to `sumTriples A B C` when its entries lie in `A`, `B`, `C` and the first two
add up to the third. -/
@[simp]
lemma mem_sumTriples {a b c : G} :
    (a, b, c) ∈ sumTriples A B C ↔ a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ a + b = c := by
  simp [sumTriples, and_assoc]

/-- The triangle indices of the Král–Serra–Vena graph: triples `(u, v, w)` of elements of `W` whose
differences `v - u`, `w - v` and `w - u` lie in `A`, `B` and `C`. -/
def triangleIndices (W A B C : Finset G) : Finset (↥W × ↥W × ↥W) :=
  {(u, v, w) | (v : G) - u ∈ A ∧ (w : G) - v ∈ B ∧ (w : G) - u ∈ C}

/-- A triple `(u, v, w)` is a triangle index when `v - u ∈ A`, `w - v ∈ B` and `w - u ∈ C`. -/
@[simp]
lemma mem_triangleIndices {u v w : ↥W} :
    (u, v, w) ∈ triangleIndices W A B C ↔ (v : G) - u ∈ A ∧ (w : G) - v ∈ B ∧ (w : G) - u ∈ C := by
  simp [triangleIndices]

/-- The Král–Serra–Vena tripartite graph of `A`, `B`, `C` inside the ambient set `W`. -/
abbrev tripartiteGraph (W A B C : Finset G) : SimpleGraph (↥W ⊕ ↥W ⊕ ↥W) :=
  graph (triangleIndices W A B C)

/-- The first two vertices of a triangle index are adjacent. -/
lemma adj_in₀_in₁ {u v w : ↥W} (h : (u, v, w) ∈ triangleIndices W A B C) :
    (tripartiteGraph W A B C).Adj (in₀ u) (in₁ v) := Rel.in₀₁ h

/-- The last two vertices of a triangle index are adjacent. -/
lemma adj_in₁_in₂ {u v w : ↥W} (h : (u, v, w) ∈ triangleIndices W A B C) :
    (tripartiteGraph W A B C).Adj (in₁ v) (in₂ w) := Rel.in₁₂ h

/-- The first and the last vertex of a triangle index are adjacent. -/
lemma adj_in₀_in₂ {u v w : ↥W} (h : (u, v, w) ∈ triangleIndices W A B C) :
    (tripartiteGraph W A B C).Adj (in₀ u) (in₂ w) := Rel.in₀₂ h

/-- An edge between the first and the second part is labeled by an element of `A`. -/
lemma sub_mem_of_adj_in₀_in₁ {u v : ↥W} (h : (tripartiteGraph W A B C).Adj (in₀ u) (in₁ v)) :
    (v : G) - u ∈ A := by
  grind [Graph.in₀₁_iff, mem_triangleIndices]

/-- An edge between the second and the third part is labeled by an element of `B`. -/
lemma sub_mem_of_adj_in₁_in₂ {v w : ↥W} (h : (tripartiteGraph W A B C).Adj (in₁ v) (in₂ w)) :
    (w : G) - v ∈ B := by
  grind [Graph.in₁₂_iff, mem_triangleIndices]

/-- An edge between the first and the third part is labeled by an element of `C`. -/
lemma sub_mem_of_adj_in₀_in₂ {u w : ↥W} (h : (tripartiteGraph W A B C).Adj (in₀ u) (in₂ w)) :
    (w : G) - u ∈ C := by
  grind [Graph.in₀₂_iff, mem_triangleIndices]

/-- There is no accidental triangle: a triangle of the graph is a triangle index. Indeed, its three
edges force the three defining conditions of `triangleIndices` separately. -/
lemma card_cliqueFinset_le :
    #((tripartiteGraph W A B C).cliqueFinset 3) ≤ #(triangleIndices W A B C) := by
  apply card_le_card_of_surjOn toTriangle
  intro s hs
  rw [mem_coe, mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  obtain ⟨u, v, w, huvw, huv, huw, hvw⟩ := graph_triple hxy hxz hyz
  exact ⟨(u, v, w), mem_triangleIndices.2
    ⟨sub_mem_of_adj_in₀_in₁ huv, sub_mem_of_adj_in₁_in₂ hvw, sub_mem_of_adj_in₀_in₂ huw⟩, huvw⟩

/-- Every triangle index is a solution of `a + b = c` together with a translation parameter in `W`,
so there are at most `#W` triangle indices per solution. -/
lemma card_triangleIndices_le : #(triangleIndices W A B C) ≤ #W * #(sumTriples A B C) := by
  rw [← card_product]
  apply card_le_card_of_injOn fun (u, v, w) ↦ ((u : G), (v : G) - u, (w : G) - v, (w : G) - u)
  · rintro ⟨u, v, w⟩ hx
    simp_all
  · rintro ⟨u, v, w⟩ - ⟨u', v', w'⟩ - h
    simp only [Prod.mk.injEq, Subtype.ext_iff] at h ⊢
    grind

end LargeSumsetsFromSubsets.ArithmeticRemoval
