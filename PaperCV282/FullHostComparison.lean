import PaperCV282.TwoWindowSquareHosts

/-!
# Start-relation hosts are unrestricted full-value hosts

The two block-parity equations cut out the start relations inside the
full-value relation space. Thus every nonzero start relation supplies a
full-value relation. For positive vertices in an adequate prime cylinder,
the latter has the exact arithmetic meaning of a nonempty square product.
The pair mask in this module carries no implicit separation condition.
-/

namespace PaperC.V282.FullHostComparison

open Affine TwoWindowParity TwoWindowSquareHosts

noncomputable section

/-- Hosts with a nonzero start relation, on exactly the supplied pair mask. -/
def startRelationHosts (K L : ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact s.filter fun xy => relationRho (twoStartSystem K xy.1 xy.2 L) ≠ 0

/-- Removing the two block-parity restrictions cannot decrease the nullity. -/
theorem start_relationRho_le_value_relationRho (K x y L : ℕ) :
    relationRho (twoStartSystem K x y L) ≤ relationRho (twoValueSystem K x y L) := by
  rw [← parityNullity_eq_start_relationRho]
  exact ValueRelations.parityNullity_le (twoValueSystem K x y L) (blockParity L)

/-- Every start-relation host has an unrestricted nonempty square-product witness. -/
theorem startRelationHosts_subset_squareProductHosts
    (K L : ℕ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hcut : ∀ xy ∈ s, xy.1 + L ≤ K + 1 ∧ xy.2 + L ≤ K + 1) :
    startRelationHosts K L s ⊆ squareProductHosts L s := by
  classical
  intro xy hxy
  obtain ⟨hxy, hstart⟩ := Finset.mem_filter.mp hxy
  have hvalue : relationRho (twoValueSystem K xy.1 xy.2 L) ≠ 0 := by
    have hle := start_relationRho_le_value_relationRho K xy.1 xy.2 L
    omega
  exact Finset.mem_filter.mpr ⟨hxy,
    (value_relationRho_ne_zero_iff_square_product
      (hpos xy hxy).1 (hpos xy hxy).2
      (hcut xy hxy).1 (hcut xy hxy).2).mp hvalue⟩

/-- The finite host comparison underlying the first inequality of Proposition 3.7. -/
theorem card_startRelationHosts_le_squareProductHosts
    (K L : ℕ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hcut : ∀ xy ∈ s, xy.1 + L ≤ K + 1 ∧ xy.2 + L ≤ K + 1) :
    (startRelationHosts K L s).card ≤ (squareProductHosts L s).card :=
  Finset.card_le_card (startRelationHosts_subset_squareProductHosts K L s hpos hcut)

end
end PaperC.V282.FullHostComparison
