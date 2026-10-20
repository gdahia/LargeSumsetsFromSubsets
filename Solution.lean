/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LargeSumsetsFromSubsets.ZModStability
public import LargeSumsetsFromSubsets.IntervalSumsets.FewTranslates
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LargeSumsetsFromSubsets.CauchyDavenportBound
import LargeSumsetsFromSubsets.Cleanup
import LargeSumsetsFromSubsets.IntervalSumsets
import LargeSumsetsFromSubsets.MediumSizedSubsets

/-!
# Large sumsets from medium-sized subsets

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime. The definitions `CauchyDavenportStability` and `FewTranslatesNearIntervals`
are those of `ZModStability.lean` and `IntervalSumsets/FewTranslates.lean`.
-/

public section

open Finset
open scoped BigOperators Pointwise symmDiff

namespace LargeSumsetsFromSubsets

/-- **Theorem 2** of Bollobás, Leader and Tiba. For $\sigma, \varepsilon > 0$ there is $c$ with
the following property. Let $A$ and $B$ be finite nonempty subsets of an abelian group and let
$1 \le c_1 \le |A|$ and $1 \le c_2 \le |B|$ satisfy $c_1 c_2 > c \max(|A|, |B|)$. There are
$A_0 \subseteq A$ and $B_0 \subseteq B$ with $|A_0| > (1 - \varepsilon)|A|$ and
$|B_0| > (1 - \varepsilon)|B|$ such that, for $c_1$ points of $A_0$ and $c_2$ points of $B_0$
chosen independently and uniformly at random, the sets $A'$ and $B'$ of chosen points satisfy
$\mathbb{E} |A' + B'| > \min((1 - \varepsilon)|A_0 + B_0|, \sigma |A_0|, \sigma |B_0|)$. -/
theorem exists_forall_exists_subset_min_lt_expect_card_add' {σ ε : ℝ} (hσ : 0 < σ)
    (hε : 0 < ε) :
    ∃ c : ℝ, ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G} {c₁ c₂ : ℕ},
      A.Nonempty → B.Nonempty → 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B →
      c * max (#A : ℝ) #B < c₁ * c₂ →
      ∃ A₀ ⊆ A, ∃ B₀ ⊆ B, A₀.Nonempty ∧ B₀.Nonempty ∧
        (1 - ε) * #A < #A₀ ∧ (1 - ε) * #B < #B₀ ∧
        min (min ((1 - ε) * #(A₀ + B₀)) (σ * #A₀)) (σ * #B₀) <
          𝔼 ab : (Fin c₁ → A₀) × (Fin c₂ → B₀),
            (#(univ.image (fun i ↦ (ab.1 i : G)) + univ.image (fun i ↦ (ab.2 i : G))) : ℝ) :=
  exists_forall_exists_subset_min_lt_expect_card_add hσ hε

/-- **Arithmetic removal lemma in a set of small doubling.** For $K \ge 0$ and $\varepsilon > 0$
there is $\delta > 0$ with the following property. Let $X$ be a finite subset of an abelian group
with $|X + X| \le K |X|$ and let $A, B, C \subseteq X$. If $a + b = c$ has at most
$\delta |X|^2$ solutions with $a \in A$, $b \in B$, $c \in C$, then one can remove at most
$\varepsilon |X|$ elements from each of $A$, $B$ and $C$ so that no solution remains. -/
theorem exists_forall_exists_subset_card_sdiff_le_forall_add_ne' {K ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X A B C : Finset G},
      A ⊆ X → B ⊆ X → C ⊆ X → (#(X + X) : ℝ) ≤ K * #X →
      (#{x ∈ A ×ˢ B ×ˢ C | x.1 + x.2.1 = x.2.2} : ℝ) ≤ δ * #X ^ 2 →
      ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
        (#(A \ A') : ℝ) ≤ ε * #X ∧ (#(B \ B') : ℝ) ≤ ε * #X ∧ (#(C \ C') : ℝ) ≤ ε * #X ∧
          ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', a + b ≠ c :=
  exists_forall_exists_subset_card_sdiff_le_forall_add_ne hK hε

/-- **Almost all sums in a small set.** For $D \ge 1$ and $\rho > 0$ there is $\delta > 0$ with
the following property. Let $X$ and $Y$ be finite nonempty subsets of an abelian group with
$|X + Y| \le D \min(|X|, |Y|)$, and let $P$ be a finite set. If at most $\delta |X| |Y|$ pairs in
$X \times Y$ have their sum outside $P$, then one can remove at most $\rho \min(|X|, |Y|)$ elements
from each of $X$ and $Y$ so that the sumset of the remaining sets has at most
$|P| + \rho \min(|X|, |Y|)$ elements. -/
theorem exists_forall_exists_subset_card_sdiff_le_card_add_le' {D ρ : ℝ} (hD : 1 ≤ D)
    (hρ : 0 < ρ) :
    ∃ δ > (0 : ℝ), ∀ {G : Type*} [AddCommGroup G] [DecidableEq G] {X Y P : Finset G},
      X.Nonempty → Y.Nonempty → (#(X + Y) : ℝ) ≤ D * min (#X : ℝ) #Y →
      (#{p ∈ X ×ˢ Y | p.1 + p.2 ∉ P} : ℝ) ≤ δ * (#X * #Y) →
      ∃ X₀ ⊆ X, ∃ Y₀ ⊆ Y,
        (#(X \ X₀) : ℝ) ≤ ρ * min (#X : ℝ) #Y ∧ (#(Y \ Y₀) : ℝ) ≤ ρ * min (#X : ℝ) #Y ∧
          (#(X₀ + Y₀) : ℝ) ≤ #P + ρ * min (#X : ℝ) #Y :=
  exists_forall_exists_subset_card_sdiff_le_card_add_le hD hρ

/-- **Theorem 6** of Bollobás, Leader and Tiba, assuming their Theorem 4. For $\beta, \gamma > 0$
there is $\varepsilon > 0$ such that for $\alpha > 0$ there is $c$ with the following property.
Let $A, B \subseteq \mathbb{Z}_p$ have at least two elements, $\alpha |B| \le |A| \le
\alpha^{-1} |B|$ and $|A| + |B| \le (1 - \beta) p$, and let $1 \le c_1 \le |A|$ and
$1 \le c_2 \le |B|$ satisfy $c_1 c_2 \ge c \max(|A|, |B|)$. If the sumset of uniformly random
subsets of $A$ and $B$ with $c_1$ and $c_2$ elements has expected size at most
$|A| + |B| - 1 + \varepsilon \min(|A|, |B|)$, then $A$ and $B$ differ in at most
$\gamma \min(|A|, |B|)$ points from arithmetic progressions with the same nonzero common
difference. -/
theorem exists_arithProg_card_symmDiff_le_of_expect_card_add_le'
    (h : CauchyDavenportStability) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    ∃ ε > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (A B : Finset (ZMod p)) (c₁ c₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
      2 ≤ #A → 2 ≤ #B → α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      𝔼 A' ∈ powersetCard c₁ A, 𝔼 B' ∈ powersetCard c₂ B, (#(A' + B') : ℝ) ≤
        #A + #B - 1 + ε * min (#A : ℝ) #B →
      ∃ a b d : ZMod p, d ≠ 0 ∧ ∃ m n : ℕ,
        (#(A ∆ (range m).image (fun i ↦ a + i • d)) : ℝ) ≤ γ * min (#A : ℝ) #B ∧
        (#(B ∆ (range n).image (fun i ↦ b + i • d)) : ℝ) ≤ γ * min (#A : ℝ) #B :=
  exists_arithProg_card_symmDiff_le_of_expect_card_add_le h hβ hγ

/-- **Theorem 8** of Bollobás, Leader and Tiba, assuming their Theorem 5. There is $\gamma > 0$
such that for $\alpha > 0$ there is $c$ with the following property. Let $X$ and $Y$ be subsets of
intervals $I$ and $J$ of $\mathbb{Z}_p$ with $m$ and $n$ elements, where $m + n \le p$ and
$\alpha n \le m \le \alpha^{-1} n$, each missing at most $\gamma \min(m, n)$ points of its
interval. If $1 \le c_1 \le |X|$ and $1 \le c_2 \le |Y|$ satisfy $c_1 c_2 \ge c \max(|X|, |Y|)$,
there are $X' \subseteq X$ and $Y' \subseteq Y$ with $c_1$ and $c_2$ elements and
$|X' + Y'| \ge |X| + |Y| - 1$. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range'
    (h : FewTranslatesNearIntervals) :
    ∃ γ > (0 : ℝ), ∀ α > (0 : ℝ), ∃ c : ℝ, ∀ p : ℕ, p.Prime →
      ∀ (x y : ZMod p) (m n : ℕ) (X Y : Finset (ZMod p)) (c₁ c₂ : ℕ),
      X ⊆ (range m).image (fun i : ℕ ↦ x + i) → Y ⊆ (range n).image (fun i : ℕ ↦ y + i) →
      m + n ≤ p → α * n ≤ m → (m : ℝ) ≤ α⁻¹ * n →
      (#((range m).image (fun i : ℕ ↦ x + i) \ X) : ℝ) ≤ γ * min (m : ℝ) n →
      (#((range n).image (fun i : ℕ ↦ y + i) \ Y) : ℝ) ≤ γ * min (m : ℝ) n →
      1 ≤ c₁ → c₁ ≤ #X → 1 ≤ c₂ → c₂ ≤ #Y → c * max (#X : ℝ) #Y ≤ c₁ * c₂ →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X' = c₁ ∧ #Y' = c₂ ∧ #X + #Y - 1 ≤ #(X' + Y') :=
  exists_subset_card_eq_card_add_card_sub_one_le_card_add_of_subset_image_range h

/-- **Theorem 1** of Bollobás, Leader and Tiba, assuming their Theorems 4 and 5. For
$\alpha, \beta > 0$ there is $c > 0$ with the following property. Let $A, B \subseteq \mathbb{Z}_p$
be nonempty with $\alpha |B| \le |A| \le \alpha^{-1} |B|$ and $|A| + |B| \le (1 - \beta) p$. For
all $1 \le c_1 \le |A|$ and $1 \le c_2 \le |B|$ with $c_1 c_2 \ge c \max(|A|, |B|)$ there are
$A' \subseteq A$ and $B' \subseteq B$ with $c_1$ and $c_2$ elements and
$|A' + B'| \ge |A| + |B| - 1$. -/
theorem exists_subset_card_eq_card_add_card_sub_one_le_card_add'
    (h₄ : CauchyDavenportStability) (h₅ : FewTranslatesNearIntervals) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) :
    ∃ c > (0 : ℝ), ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), A.Nonempty → B.Nonempty →
      α * #B ≤ #A → (#A : ℝ) ≤ α⁻¹ * #B → (#A + #B : ℝ) ≤ (1 - β) * p →
      ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ ≤ #A → 1 ≤ c₂ → c₂ ≤ #B → c * max (#A : ℝ) #B ≤ c₁ * c₂ →
        ∃ A' ⊆ A, ∃ B' ⊆ B, #A' = c₁ ∧ #B' = c₂ ∧ #A + #B - 1 ≤ #(A' + B') :=
  exists_subset_card_eq_card_add_card_sub_one_le_card_add h₄ h₅ hα hβ

end LargeSumsetsFromSubsets
