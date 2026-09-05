import PaperCV282.TwoWindowParity
import PaperCV282.ValueSquareRelations

/-!
# Unrestricted square-product hosts for two windows

With positive starts and an adequate prime cylinder, the correction in the
finite two-window comparison counts precisely the pairs admitting a nonempty
square-product subset of the full vertex occurrences. No even-cardinality
condition is imposed on either block. This identifies the host term in the
finite inequality; its quantitative arithmetic bound remains separate.
-/

namespace PaperC.V282.TwoWindowSquareHosts

open Affine TwoWindowParity ValueSquareRelations
open scoped BigOperators

noncomputable section

/-- Hosts defined directly by a nonempty square-product subset, without a prime cutoff. -/
def squareProductHosts (L : ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact s.filter fun xy =>
    ∃ t : Finset (Sum (Fin (L + 1)) (Fin (L + 1))), t.Nonempty ∧
      ∃ r : ℕ, ∏ i ∈ t, twoStartCompleteVertexLabel xy.1 xy.2 L i = r ^ 2

/-- Positivity and cylinder adequacy for every occurrence in both windows. -/
theorem complete_vertex_pos_le {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxc : x + L ≤ M + 1) (hyc : y + L ≤ M + 1)
    (i : Sum (Fin (L + 1)) (Fin (L + 1))) :
    0 < twoStartCompleteVertexLabel x y L i ∧
      twoStartCompleteVertexLabel x y L i ≤ M := by
  cases i with
  | inl i =>
      change 0 < startCompleteVertexLabel x L i ∧ startCompleteVertexLabel x L i ≤ M
      rw [start_label_eq_consecutive (by omega)]
      have hi := i.isLt
      unfold WindowValues.vertex
      omega
  | inr i =>
      change 0 < startCompleteVertexLabel y L i ∧ startCompleteVertexLabel y L i ≤ M
      rw [start_label_eq_consecutive (by omega)]
      have hi := i.isLt
      unfold WindowValues.vertex
      omega

/-- The full relation host has exactly the unrestricted arithmetic meaning in the article. -/
theorem value_relationRho_ne_zero_iff_square_product {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxc : x + L ≤ M + 1) (hyc : y + L ≤ M + 1) :
    relationRho (twoValueSystem M x y L) ≠ 0 ↔
      ∃ t : Finset (Sum (Fin (L + 1)) (Fin (L + 1))), t.Nonempty ∧
        ∃ r : ℕ, ∏ i ∈ t, twoStartCompleteVertexLabel x y L i = r ^ 2 :=
  relationRho_ne_zero_iff_exists_nonempty_square_product M _
    (fun i => (complete_vertex_pos_le hx hy hxc hyc i).1)
    (fun i => (complete_vertex_pos_le hx hy hxc hyc i).2)

/-- Adequate cylinders count exactly the unrestricted square-product hosts. -/
theorem valueRelationalHosts_eq_squareProductHosts (M L : ℕ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hcut : ∀ xy ∈ s, xy.1 + L ≤ M + 1 ∧ xy.2 + L ≤ M + 1) :
    valueRelationalHosts M L s = squareProductHosts L s := by
  classical
  ext xy
  simp only [valueRelationalHosts, squareProductHosts, Finset.mem_filter]
  constructor
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, (value_relationRho_ne_zero_iff_square_product
      (hpos xy hxy).1 (hpos xy hxy).2 (hcut xy hxy).1 (hcut xy hxy).2).mp h⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, (value_relationRho_ne_zero_iff_square_product
      (hpos xy hxy).1 (hpos xy hxy).2 (hcut xy hxy).1 (hcut xy hxy).2).mpr h⟩

/-- The finite inequality (3.24) with actual, unrestricted square-product hosts.
The set `I` may be an interval or a deterministic mask. This does not estimate the host count. -/
theorem finite_equation_three_twenty_four_square_hosts (M L : ℕ) (I : Finset ℕ)
    (hpos : ∀ x ∈ I, 2 ≤ x) (hcut : ∀ x ∈ I, x + L ≤ M + 1) :
    ∑ xy ∈ separatedPairs I L, (2 ^ relationRho (twoValueSystem M xy.1 xy.2 L) - 1) ≤
      4 * (∑ xy ∈ separatedPairs I L,
        (2 ^ relationRho (twoStartSystem M xy.1 xy.2 L) - 1)) +
          3 * (squareProductHosts L (separatedPairs I L)).card := by
  have hpairs : ∀ xy ∈ separatedPairs I L, xy.1 ∈ I ∧ xy.2 ∈ I := by
    intro xy hxy
    have h := (mem_separatedPairs I L xy.1 xy.2).mp hxy
    exact ⟨h.1, h.2.1⟩
  rw [← valueRelationalHosts_eq_squareProductHosts M L (separatedPairs I L)
    (fun xy hxy => ⟨hpos xy.1 (hpairs xy hxy).1, hpos xy.2 (hpairs xy hxy).2⟩)
    (fun xy hxy => ⟨hcut xy.1 (hpairs xy hxy).1, hcut xy.2 (hpairs xy hxy).2⟩)]
  exact finite_equation_three_twenty_four M L I

end
end PaperC.V282.TwoWindowSquareHosts
