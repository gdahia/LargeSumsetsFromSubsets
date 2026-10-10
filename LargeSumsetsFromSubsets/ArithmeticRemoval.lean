/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ArithmeticRemoval.TripartiteGraph
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# The arithmetic removal lemma in a set of small doubling

Let `X` be a finite subset of an abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C` be
subsets of `X`. If the equation `a + b = c` has at most `δ * #X ^ 2` solutions with `a ∈ A`,
`b ∈ B`, `c ∈ C`, and `δ` is small enough in terms of `K` and `ε`, then one may delete at most
`ε * #X` elements from each of `A`, `B`, `C` so that no solution remains. This is
`LargeSumsetsFromSubsets.ArithmeticRemoval.arithmetic_removal`, whose threshold for `δ` is the
explicit constant `removalConst K ε`, a fixed multiple of Mathlib's `triangleRemovalBound`.

The proof is the combinatorial argument of Král, Serra and Vena. The triangles of the tripartite
graph of `LargeSumsetsFromSubsets.ArithmeticRemoval.TripartiteGraph`, built over the ambient
set `W = X ∪ (X + X)`, are the solutions of `a + b = c` together with a translation parameter, so
the solution bound makes the graph have few triangles and the triangle removal lemma deletes few
edges. An edge between two parts of the graph carries a label, namely the difference of its
endpoints, and the labels of the edges deleted between two fixed parts are counted by
`removedLabelCard`; the labels for which many edges were deleted are few, and discarding them from
`A`, `B` and `C` destroys every solution, since a surviving solution would produce `#X` triangles
of which at most `3 / 4 * #X` could have been hit.

The small doubling hypothesis enters only through the comparison of `#W` with `#X`: it is what
makes a triangle count of order `#X ^ 3` small compared to the cube of the number of vertices.
-/

@[expose] public section

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum3
open scoped Pointwise

namespace LargeSumsetsFromSubsets.ArithmeticRemoval

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {W : Finset G}

section RemovedEdges

variable {V : Type*} [Fintype V] (H H' : SimpleGraph V)
  [DecidableRel H.Adj] [DecidableRel H'.Adj]

/-- The pairs `(u, v)` of elements of the ambient set `W` such that the edge joining `p u` to `q v`
belongs to `H` but not to the subgraph `H'`. -/
def removedPairs (p q : ↥W → V) : Finset (↥W × ↥W) :=
  {z ∈ univ | H.Adj (p z.1) (q z.2) ∧ ¬ H'.Adj (p z.1) (q z.2)}

/-- The number of edges of `H` between the parts `p` and `q` that are deleted in `H'` and carry the
label `a`, that is, whose endpoints differ by `a`. -/
def removedLabelCard (p q : ↥W → V) (a : G) : ℕ :=
  #{z ∈ removedPairs H H' p q | (z.2 : G) - z.1 = a}

variable {H H'}

omit [AddCommGroup G] [DecidableEq G] in
lemma card_removedPairs_add_le (hle : H' ≤ H) {p q : ↥W → V} (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) :
    #(removedPairs H H' p q) + #H'.edgeFinset ≤ #H.edgeFinset := by
  classical
  rw [← card_sdiff_add_card_eq_card (edgeFinset_mono hle)]
  apply Nat.add_le_add_right
  apply card_le_card_of_injOn (fun z => s(p z.1, q z.2))
  · intro z hz
    simp only [removedPairs, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
    simp [hz.1, hz.2]
  · intro z _ z' _ h
    rw [Sym2.eq_iff] at h
    obtain ⟨h₁, h₂⟩ | ⟨h₁, -⟩ := h
    · exact Prod.ext (hp h₁) (hq h₂)
    · exact absurd h₁ (hpq _ _)

omit [Fintype V] in
/-- Every deleted edge between two parts has a label, so the labelwise counts add up to the number
of deleted edges. -/
lemma sum_removedLabelCard {p q : ↥W → V} {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) :
    ∑ a ∈ L, removedLabelCard H H' p q a = #(removedPairs H H' p q) := by
  refine (card_eq_sum_card_fiberwise ?_).symm
  intro z hz
  simp only [removedPairs, mem_coe, mem_filter, mem_univ, true_and] at hz
  exact hL _ _ hz.1

/-- Few labels can have many deleted edges: the labels with more than `m` deleted edges number at
most `(#H.edgeFinset - #H'.edgeFinset) / m`. -/
lemma card_filter_lt_removedLabelCard_mul_le (hle : H' ≤ H) {p q : ↥W → V}
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) (m : ℝ) :
    (#{a ∈ L | m < (removedLabelCard H H' p q a : ℝ)} : ℝ) * m
      ≤ (#H.edgeFinset : ℝ) - #H'.edgeFinset := by
  have hsum : ((#(removedPairs H H' p q) : ℝ)) ≤ (#H.edgeFinset : ℝ) - #H'.edgeFinset := by
    have := card_removedPairs_add_le hle hp hq hpq
    rw [← Nat.cast_le (α := ℝ)] at this
    push_cast at this
    linarith
  have hlab : (#{a ∈ L | m < (removedLabelCard H H' p q a : ℝ)} : ℝ) * m
      ≤ ∑ a ∈ L, (removedLabelCard H H' p q a : ℝ) := by
    rw [← nsmul_eq_mul]
    apply le_trans (card_nsmul_le_sum _ _ _ fun a ha => (mem_filter.1 ha).2.le)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  rw [← Nat.cast_sum, sum_removedLabelCard hL] at hlab
  linarith

end RemovedEdges

/-- The threshold below which the number of solutions of `a + b = c` must lie in the arithmetic
removal lemma, `arithmetic_removal`. It is a fixed multiple of the triangle removal
bound, so in practice it is minuscule. -/
noncomputable def removalConst (K ε : ℝ) : ℝ := triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2

lemma removalConst_pos {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : 0 < removalConst K ε :=
  half_pos (triangleRemovalBound_pos (div_pos hε (by nlinarith)))

/-- The arithmetic removal lemma, with the ambient set `W` supplied by hand: it need only contain
`X` and all the sums `x + y` with `x, y ∈ X`, and be comparable in size to `X`. The middle set `B`
is unconstrained, since an element of `B` outside `X - X` takes part in no solution anyway. -/
private lemma arithmetic_removal_aux {X A B C W : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (_hB : B ⊆ X) (hC : C ⊆ X) (hXW : X ⊆ W)
    (hXXW : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ W) (hW : (#W : ℝ) ≤ (1 + K) * #X)
    (hK : 0 ≤ K) (hε : 0 < ε) (hX : X.Nonempty) (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : (#(sumTriples A B C) : ℝ) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hXW' : (#X : ℝ) ≤ #W := by exact_mod_cast card_le_card hXW
  have hKpos : (0 : ℝ) < 1 + K := by linarith
  have hεpos : 0 < ε / (36 * (1 + K) ^ 2) := div_pos hε (by positivity)
  have hn : (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) = 3 * #W := by
    simp only [Fintype.card_sum, Fintype.card_coe, Nat.cast_add]
    ring
  have hnpos : (0 : ℝ) < Fintype.card (↥W ⊕ ↥W ⊕ ↥W) := by rw [hn]; linarith
  -- The graph has few triangles, so the triangle removal lemma applies to it.
  have hclique : (#((tripartiteGraph W A B C).cliqueFinset 3) : ℝ)
      < triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) * (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) ^ 3 := by
    have hcount : (#((tripartiteGraph W A B C).cliqueFinset 3) : ℝ)
        ≤ (#W : ℝ) * #(sumTriples A B C) :=
      mod_cast card_cliqueFinset_le.trans card_triangleIndices_le
    have hcube : (#W : ℝ) * #(sumTriples A B C)
        ≤ δ * (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) ^ 3 := by
      rw [hn]
      nlinarith [mul_le_mul_of_nonneg_left hsol (le_trans hXpos.le hXW'),
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hXpos.le hXW' 2) (mul_nonneg hδ (by linarith)),
        mul_nonneg (mul_nonneg hδ (by linarith : (0:ℝ) ≤ (#W : ℝ))) (sq_nonneg (#W : ℝ))]
    have hstrict : δ < triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) := by
      rw [removalConst] at hδ'
      linarith [triangleRemovalBound_pos hεpos]
    linarith [mul_lt_mul_of_pos_right hstrict (pow_pos hnpos 3)]
  obtain ⟨H', hle, hdec, hedge, hfree⟩ := triangle_removal hclique
  -- Discard the labels carrying many deleted edges.
  set m : ℝ := #X / 4 with hm
  set A' := {a ∈ A | (removedLabelCard (tripartiteGraph W A B C) H' in₀ in₁ a : ℝ) ≤ m} with hA'
  set B' := {b ∈ B | (removedLabelCard (tripartiteGraph W A B C) H' in₁ in₂ b : ℝ) ≤ m} with hB'
  set C' := {c ∈ C | (removedLabelCard (tripartiteGraph W A B C) H' in₀ in₂ c : ℝ) ≤ m} with hC'
  have hedge' : (#(tripartiteGraph W A B C).edgeFinset : ℝ) - #H'.edgeFinset
      ≤ ε * #X ^ 2 / 4 := by
    apply hedge.le.trans
    push_cast
    rw [hn, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ #W) hW 2) hε.le,
      sq_nonneg (#W : ℝ)]
  have hfew : ∀ {L : Finset G} {p q : ↥W → (↥W ⊕ ↥W ⊕ ↥W)}, Function.Injective p →
      Function.Injective q → (∀ u v, p u ≠ q v) →
      (∀ u v : ↥W, (tripartiteGraph W A B C).Adj (p u) (q v) → (v : G) - u ∈ L) →
      (#{a ∈ L | m < (removedLabelCard (tripartiteGraph W A B C) H' p q a : ℝ)} : ℝ) ≤ ε * #X := by
    intro L p q hp hq hpq hL
    have hkey := (card_filter_lt_removedLabelCard_mul_le hle hp hq hpq hL m).trans hedge'
    rw [hm] at hkey
    refine le_of_mul_le_mul_right ?_ hXpos
    nlinarith [hkey]
  refine ⟨A', filter_subset _ _, B', filter_subset _ _, C', filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · rw [hA', ← filter_not]
    simpa only [not_le] using hfew (p := in₀) (q := in₁) Sum.inl_injective
      (Sum.inr_injective.comp Sum.inl_injective) (fun _ _ => Sum.inl_ne_inr)
      fun _ _ => sub_mem_of_adj_in₀_in₁
  · rw [hB', ← filter_not]
    simpa only [not_le] using hfew (p := in₁) (q := in₂)
      (Sum.inr_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inr_injective)
      (fun _ _ h => by simp at h) fun _ _ => sub_mem_of_adj_in₁_in₂
  · rw [hC', ← filter_not]
    simpa only [not_le] using hfew (p := in₀) (q := in₂) Sum.inl_injective
      (Sum.inr_injective.comp Sum.inr_injective) (fun _ _ => Sum.inl_ne_inr)
      fun _ _ => sub_mem_of_adj_in₀_in₂
  -- No solution survives: it would give `#X` triangles, too many to have all been hit.
  intro a ha b hb c hc habc
  rw [hA', mem_filter] at ha
  rw [hB', mem_filter] at hb
  rw [hC', mem_filter] at hc
  have hba : c - a = b := by rw [← habc]; simp
  set u : ↥X → ↥W := fun x => ⟨(x : G), hXW x.2⟩ with hu
  set v : ↥X → ↥W := fun x => ⟨(x : G) + a, hXXW _ x.2 _ (hA ha.1)⟩ with hv
  set w : ↥X → ↥W := fun x => ⟨(x : G) + c, hXXW _ x.2 _ (hC hc.1)⟩ with hw
  have hmem : ∀ x : ↥X, (u x, v x, w x) ∈ triangleIndices W A B C := by
    intro x
    simp only [mem_triangleIndices, hu, hv, hw, add_sub_cancel_left, add_sub_add_left_eq_sub, hba]
    exact ⟨ha.1, hb.1, hc.1⟩
  set S₁ := {x ∈ (univ : Finset ↥X) | ¬ H'.Adj (in₀ (u x)) (in₁ (v x))} with hS₁
  set S₂ := {x ∈ (univ : Finset ↥X) | ¬ H'.Adj (in₁ (v x)) (in₂ (w x))} with hS₂
  set S₃ := {x ∈ (univ : Finset ↥X) | ¬ H'.Adj (in₀ (u x)) (in₂ (w x))} with hS₃
  have hcover : (univ : Finset ↥X) ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro x _
    by_contra hx
    simp only [hS₁, hS₂, hS₃, mem_union, mem_filter, mem_univ, true_and, not_or, not_not] at hx
    exact hfree {in₀ (u x), in₁ (v x), in₂ (w x)}
      (is3Clique_triple_iff.2 ⟨hx.1.1, hx.2, hx.1.2⟩)
  have hS₁card : #S₁ ≤ removedLabelCard (tripartiteGraph W A B C) H' in₀ in₁ a := by
    apply card_le_card_of_injOn (fun x => (u x, v x))
    · intro x hx
      simp only [hS₁, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [mem_coe, mem_filter, removedPairs, mem_univ, true_and, hu, hv]
      exact ⟨⟨adj_in₀_in₁ (hmem x), hx⟩, add_sub_cancel_left _ _⟩
    · intro x _ y _ h
      exact Subtype.ext (congrArg (fun z : ↥W × ↥W => (z.1 : G)) h)
  have hS₂card : #S₂ ≤ removedLabelCard (tripartiteGraph W A B C) H' in₁ in₂ b := by
    apply card_le_card_of_injOn (fun x => (v x, w x))
    · intro x hx
      simp only [hS₂, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [mem_coe, mem_filter, removedPairs, mem_univ, true_and, hv, hw]
      exact ⟨⟨adj_in₁_in₂ (hmem x), hx⟩, by rw [add_sub_add_left_eq_sub, hba]⟩
    · intro x _ y _ h
      have h₁ : (x : G) + a = (y : G) + a := congrArg (fun z : ↥W × ↥W => (z.1 : G)) h
      exact Subtype.ext (add_right_cancel h₁)
  have hS₃card : #S₃ ≤ removedLabelCard (tripartiteGraph W A B C) H' in₀ in₂ c := by
    apply card_le_card_of_injOn (fun x => (u x, w x))
    · intro x hx
      simp only [hS₃, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [mem_coe, mem_filter, removedPairs, mem_univ, true_and, hu, hw]
      exact ⟨⟨adj_in₀_in₂ (hmem x), hx⟩, add_sub_cancel_left _ _⟩
    · intro x _ y _ h
      exact Subtype.ext (congrArg (fun z : ↥W × ↥W => (z.1 : G)) h)
  have hcard : (#X : ℝ) ≤ #S₁ + #S₂ + #S₃ := by
    have : #X = #(univ : Finset ↥X) := by simp
    rw [this]
    exact_mod_cast (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  linarith [hcard, hm, le_trans (mod_cast hS₁card : (#S₁ : ℝ) ≤ _) ha.2,
    le_trans (mod_cast hS₂card : (#S₂ : ℝ) ≤ _) hb.2,
    le_trans (mod_cast hS₃card : (#S₃ : ℝ) ≤ _) hc.2]

/-- **Arithmetic removal lemma in a set of small doubling.** Let `X` be a finite subset of an
abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C ⊆ X`. If `a + b = c` has at most
`δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `δ` is small enough in terms of `K`
and `ε`, then one can remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no
solution remains. -/
theorem arithmetic_removal {X A B C : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X) (hK : 0 ≤ K) (hXX : (#(X + X) : ℝ) ≤ K * #X)
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : (#(sumTriples A B C) : ℝ) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · rw [subset_empty] at hA hB hC
    subst hA; subst hB; subst hC
    exact ⟨∅, Subset.refl _, ∅, Subset.refl _, ∅, Subset.refl _, by simp, by simp, by simp, by simp⟩
  refine arithmetic_removal_aux (W := X ∪ (X + X)) hA hB hC subset_union_left ?_ ?_ hK hε
    hX hδ hδ' hsol
  · exact fun x hx y hy => mem_union_right _ (add_mem_add hx hy)
  · have hunion := card_union_le X (X + X)
    rw [← Nat.cast_le (α := ℝ)] at hunion
    push_cast at hunion
    linarith

end LargeSumsetsFromSubsets.ArithmeticRemoval
