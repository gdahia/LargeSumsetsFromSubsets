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
`LargeSumsetsFromSubsets.ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne`, whose
threshold for `δ` is the explicit constant `removalConst K ε`, a fixed multiple of Mathlib's
`triangleRemovalBound`. The form with an unspecified threshold is
`LargeSumsetsFromSubsets.exists_forall_exists_subset_card_sdiff_le_forall_add_ne`.

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
/-- Between two disjoint parts, distinct deleted pairs give distinct deleted edges, so they number
at most the edges of `H` missing from `H'`. -/
lemma card_removedPairs_add_le (hle : H' ≤ H) {p q : ↥W → V} (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) :
    #(removedPairs H H' p q) + #H'.edgeFinset ≤ #H.edgeFinset := by
  classical
  rw [← card_sdiff_add_card_eq_card (edgeFinset_mono hle)]
  gcongr
  apply card_le_card_of_injOn (fun z ↦ s(p z.1, q z.2))
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
  refine (card_eq_sum_card_fiberwise ?_).symm
  rintro ⟨u, v⟩ hz
  simp only [removedPairs, mem_coe, mem_filter, mem_univ, true_and] at hz
  obtain ⟨hadj, -⟩ := hz
  exact hL u v hadj

/-- Few labels can have many deleted edges: the labels with more than `m` deleted edges number at
most `(#H.edgeFinset - #H'.edgeFinset) / m`. -/
lemma card_filter_lt_removedLabelCard_mul_le (hle : H' ≤ H) {p q : ↥W → V}
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) (m : ℝ) :
    (#{a ∈ L | m < (removedLabelCard H H' p q a : ℝ)} : ℝ) * m
      ≤ (#H.edgeFinset : ℝ) - #H'.edgeFinset := by
  have hsum : ((∑ a ∈ L, removedLabelCard H H' p q a : ℕ) : ℝ) + #H'.edgeFinset
      ≤ #H.edgeFinset := by
    rw [sum_removedLabelCard hL]
    exact_mod_cast card_removedPairs_add_le hle hp hq hpq
  rw [le_sub_iff_add_le, ← nsmul_eq_mul]
  refine le_trans (add_le_add_left ?_ _) hsum
  push_cast
  refine (card_nsmul_le_sum _ _ _ ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity)
  intro a ha
  obtain ⟨-, ha⟩ := mem_filter.1 ha
  exact ha.le

/-- If at most `ε * x ^ 2 / 4` edges are deleted, then at most `ε * x` labels carry more than
`x / 4` deleted edges. -/
lemma card_filter_lt_removedLabelCard_le (hle : H' ≤ H) {p q : ↥W → V}
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ u v, p u ≠ q v) {L : Finset G}
    (hL : ∀ u v : ↥W, H.Adj (p u) (q v) → (v : G) - u ∈ L) {x ε : ℝ} (hx : 0 < x)
    (hedge : (#H.edgeFinset : ℝ) - #H'.edgeFinset ≤ ε * x ^ 2 / 4) :
    (#{a ∈ L | x / 4 < (removedLabelCard H H' p q a : ℝ)} : ℝ) ≤ ε * x := by
  refine le_of_mul_le_mul_right ?_ hx
  nlinarith [(card_filter_lt_removedLabelCard_mul_le hle hp hq hpq hL (x / 4)).trans hedge]

omit [Fintype V] in
/-- Along an injective family of pairs `(f i, g i)` of `H`-adjacent vertices with label `a`, the
pairs whose edge is missing from `H'` are counted by `removedLabelCard H H' p q a`. -/
lemma card_filter_not_adj_le_removedLabelCard {ι : Type*} [Fintype ι] {p q : ↥W → V}
    {f g : ι → ↥W} (hf : Function.Injective f) {a : G} (hadj : ∀ i, H.Adj (p (f i)) (q (g i)))
    (hlab : ∀ i, (g i : G) - f i = a) :
    #{i | ¬ H'.Adj (p (f i)) (q (g i))} ≤ removedLabelCard H H' p q a := by
  apply card_le_card_of_injOn (fun i ↦ (f i, g i))
  · intro i hi
    simp_all [removedPairs]
  · intro i _ j _ h
    exact hf (congrArg Prod.fst h)

end RemovedEdges

/-- The threshold below which the number of solutions of `a + b = c` must lie in the arithmetic
removal lemma, `exists_subset_card_sdiff_le_forall_add_ne`. It is a fixed multiple of the
triangle removal bound, so in practice it is minuscule. -/
noncomputable def removalConst (K ε : ℝ) : ℝ := triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2

/-- The removal threshold is positive. -/
lemma removalConst_pos {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : 0 < removalConst K ε :=
  half_pos (triangleRemovalBound_pos (div_pos hε (by nlinarith)))

omit [AddCommGroup G] [DecidableEq G] in
/-- The tripartite graph over `W` has `3 * #W` vertices. -/
private lemma card_vertices : (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) = 3 * #W := by
  simp only [Fintype.card_sum, Fintype.card_coe, Nat.cast_add]
  ring

/-- Few solutions make few triangles: if `a + b = c` has at most `δ * #X ^ 2` solutions, with `δ`
at most `removalConst K ε`, then the tripartite graph over `W ⊇ X` has fewer triangles than the
triangle removal lemma requires. -/
private lemma card_cliqueFinset_lt {X A B C : Finset G} {K ε δ : ℝ} (hXW : X ⊆ W) (hK : 0 ≤ K)
    (hε : 0 < ε) (hX : X.Nonempty) (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : (#(sumTriples A B C) : ℝ) ≤ δ * #X ^ 2) :
    (#((tripartiteGraph W A B C).cliqueFinset 3) : ℝ)
      < triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) * (Fintype.card (↥W ⊕ ↥W ⊕ ↥W) : ℝ) ^ 3 := by
  have hXW' : (#X : ℝ) ≤ #W := by exact_mod_cast card_le_card hXW
  have hW : (0 : ℝ) < #W := hXW'.trans_lt' (by exact_mod_cast hX.card_pos)
  have hbound := triangleRemovalBound_pos (div_pos hε (by positivity : (0 : ℝ) < 36 * (1 + K) ^ 2))
  rw [removalConst] at hδ'
  rw [card_vertices]
  refine (Nat.cast_le.2 (card_cliqueFinset_le.trans card_triangleIndices_le)).trans_lt ?_
  push_cast
  calc (#W : ℝ) * #(sumTriples A B C) ≤ #W * (δ * #W ^ 2) := by
        gcongr
        exact hsol.trans (by gcongr)
    _ ≤ #W * (triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) / 2 * #W ^ 2) := by gcongr
    _ < triangleRemovalBound (ε / (36 * (1 + K) ^ 2)) * (3 * #W) ^ 3 := by
        nlinarith [mul_pos hbound (pow_pos hW 3)]

omit [AddCommGroup G] [DecidableEq G] in
/-- The removal parameter is chosen so that the triangle removal lemma deletes at most
`ε * #X ^ 2 / 4` edges, as long as `#W ≤ (1 + K) * #X`. -/
private lemma removal_mul_card_sq_le {X : Finset G} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hW : (#W : ℝ) ≤ (1 + K) * #X) :
    ε / (36 * (1 + K) ^ 2) * ((Fintype.card (↥W ⊕ ↥W ⊕ ↥W) ^ 2 : ℕ) : ℝ) ≤ ε * #X ^ 2 / 4 := by
  push_cast
  rw [card_vertices, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hW 2) hε.le]

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
    Function.Injective (shiftIn h) := by
  intro x y hxy
  exact Subtype.ext (add_right_cancel (congrArg Subtype.val hxy))

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
    have := hfree {in₀ (shiftIn hu x), in₁ (shiftIn hv x), in₂ (shiftIn hw x)}
    simp only [is3Clique_triple_iff, not_and_or] at this
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  rw [← Fintype.card_coe, ← card_univ]
  refine (card_le_card hcover).trans <| (card_union_le _ _).trans <|
    (add_le_add_left (card_union_le _ _) _).trans (add_le_add (add_le_add
    (card_filter_not_adj_le_removedLabelCard (shiftIn_injective hu)
      (fun x ↦ adj_in₀_in₁ (hmem x)) (by simp))
    (card_filter_not_adj_le_removedLabelCard (shiftIn_injective hv)
      (fun x ↦ adj_in₁_in₂ (hmem x)) (by simp)))
    (card_filter_not_adj_le_removedLabelCard (shiftIn_injective hu)
      (fun x ↦ adj_in₀_in₂ (hmem x)) (by simp)))

/-- The arithmetic removal lemma, with the ambient set `W` supplied by hand: it need only contain
`X` and all the sums `x + y` with `x, y ∈ X`, and be comparable in size to `X`. The middle set `B`
is unconstrained, since an element of `B` outside `X - X` takes part in no solution anyway. The
sets `A'`, `B'`, `C'` keep the labels carrying at most `#X / 4` deleted edges. -/
private lemma exists_subset_card_sdiff_le_forall_add_ne_aux {X A B C W : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hC : C ⊆ X) (hXW : X ⊆ W)
    (hXXW : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ W) (hW : (#W : ℝ) ≤ (1 + K) * #X)
    (hK : 0 ≤ K) (hε : 0 < ε) (hX : X.Nonempty) (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : (#(sumTriples A B C) : ℝ) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  obtain ⟨H', hle, _, hedge, hfree⟩ :=
    triangle_removal (card_cliqueFinset_lt hXW hK hε hX hδ hδ' hsol)
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hedge' : (#(tripartiteGraph W A B C).edgeFinset : ℝ) - #H'.edgeFinset
      ≤ ε * #X ^ 2 / 4 :=
    hedge.le.trans (removal_mul_card_sq_le hK hε hW)
  refine ⟨{a ∈ A | (removedLabelCard (tripartiteGraph W A B C) H' in₀ in₁ a : ℝ) ≤ #X / 4},
    filter_subset _ _,
    {b ∈ B | (removedLabelCard (tripartiteGraph W A B C) H' in₁ in₂ b : ℝ) ≤ #X / 4},
    filter_subset _ _,
    {c ∈ C | (removedLabelCard (tripartiteGraph W A B C) H' in₀ in₂ c : ℝ) ≤ #X / 4},
    filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · rw [← filter_not]
    simpa only [not_le] using card_filter_lt_removedLabelCard_le (p := in₀) (q := in₁) hle
      Sum.inl_injective (Sum.inr_injective.comp Sum.inl_injective) (fun _ _ ↦ Sum.inl_ne_inr)
      (fun _ _ ↦ sub_mem_of_adj_in₀_in₁) hXpos hedge'
  · rw [← filter_not]
    simpa only [not_le] using card_filter_lt_removedLabelCard_le (p := in₁) (q := in₂) hle
      (Sum.inr_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inr_injective)
      (fun _ _ h ↦ by simp at h) (fun _ _ ↦ sub_mem_of_adj_in₁_in₂) hXpos hedge'
  · rw [← filter_not]
    simpa only [not_le] using card_filter_lt_removedLabelCard_le (p := in₀) (q := in₂) hle
      Sum.inl_injective (Sum.inr_injective.comp Sum.inr_injective) (fun _ _ ↦ Sum.inl_ne_inr)
      (fun _ _ ↦ sub_mem_of_adj_in₀_in₂) hXpos hedge'
  intro a ha b hb c hc habc
  simp only [mem_filter] at ha hb hc
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  obtain ⟨hc, hc'⟩ := hc
  have hcard := card_le_removedLabelCard_add hfree ha hb hc habc
    (fun x hx ↦ by simpa using hXW hx) (fun x hx ↦ hXXW x hx a (hA ha))
    (fun x hx ↦ hXXW x hx c (hC hc))
  rw [← Nat.cast_le (α := ℝ)] at hcard
  push_cast at hcard
  linarith

/-- **Arithmetic removal lemma in a set of small doubling.** Let `X` be a finite subset of an
abelian group with `#(X + X) ≤ K * #X`, and let `A`, `B`, `C ⊆ X`. If `a + b = c` has at most
`δ * #X ^ 2` solutions with `a ∈ A`, `b ∈ B`, `c ∈ C`, where `δ` is small enough in terms of `K`
and `ε`, then one can remove at most `ε * #X` elements from each of `A`, `B` and `C` so that no
solution remains. -/
theorem exists_subset_card_sdiff_le_forall_add_ne {X A B C : Finset G} {K ε δ : ℝ}
    (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X) (hK : 0 ≤ K) (hXX : (#(X + X) : ℝ) ≤ K * #X)
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ' : δ ≤ removalConst K ε)
    (hsol : (#(sumTriples A B C) : ℝ) ≤ δ * #X ^ 2) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
        ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp_all
  refine exists_subset_card_sdiff_le_forall_add_ne_aux (W := X ∪ (X + X)) hA hC subset_union_left
    (fun x hx y hy ↦ mem_union_right _ (add_mem_add hx hy)) ?_ hK hε hX hδ hδ' hsol
  linarith [(by exact_mod_cast card_union_le X (X + X) :
    (#(X ∪ (X + X)) : ℝ) ≤ #X + #(X + X))]

end LargeSumsetsFromSubsets.ArithmeticRemoval

namespace LargeSumsetsFromSubsets

/-- **Arithmetic removal lemma in a set of small doubling.** For $K \ge 0$ and $\varepsilon > 0$
there is $\delta > 0$ with the following property. Let $X$ be a finite subset of an abelian group
with $|X + X| \le K |X|$ and let $A, B, C \subseteq X$. If $a + b = c$ has at most
$\delta |X|^2$ solutions with $a \in A$, $b \in B$, $c \in C$, then one can remove at most
$\varepsilon |X|$ elements from each of $A$, $B$ and $C$ so that no solution remains. -/
theorem exists_forall_exists_subset_card_sdiff_le_forall_add_ne {K ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X A B C : Finset G},
      A ⊆ X → B ⊆ X → C ⊆ X → (#(X + X) : ℝ) ≤ K * #X →
      (#{x ∈ A ×ˢ B ×ˢ C | x.1 + x.2.1 = x.2.2} : ℝ) ≤ δ * #X ^ 2 →
      ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
        (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
          ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c :=
  ⟨ArithmeticRemoval.removalConst K ε, ArithmeticRemoval.removalConst_pos hK hε,
    fun hA hB hC hXX hsol ↦ ArithmeticRemoval.exists_subset_card_sdiff_le_forall_add_ne hA hB hC
      hK hXX hε (ArithmeticRemoval.removalConst_pos hK hε).le le_rfl hsol⟩

end LargeSumsetsFromSubsets
