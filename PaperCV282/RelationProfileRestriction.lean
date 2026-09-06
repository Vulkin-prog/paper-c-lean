import PaperCV282.CappedRelationMass
import PaperCV282.TouchingPairGeometry

/-!
# Exact restriction and cylinder transport of relation masses

Once both complete vertex blocks lie in the prime cylinder, both nullities
are independent of the cutoff. The full-value proof uses literal square
products without either block-parity equation. This permits restriction of
the proved macroscopic profiles to arbitrary separated masks.
-/

namespace PaperC.V282.RelationProfileRestriction

open Affine TwoWindowParity TwoWindowSquareHosts ValueSquareRelations
open CappedRelationMass HostRankMass MacroscopicGeometry

noncomputable section

/-- The uncapped full-value mass on a literal finite pair mask. -/
def valueWeightMass (K L : ℕ) (s : Finset (ℕ × ℕ)) : ℕ :=
  ∑ xy ∈ s, (2 ^ relationRho (twoValueSystem K xy.1 xy.2 L) - 1)

/-- Full-value nullity is independent of any adequate prime cutoff. -/
theorem value_relationRho_cutoff_eq {K K' x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hK : x + L ≤ K + 1 ∧ y + L ≤ K + 1)
    (hK' : x + L ≤ K' + 1 ∧ y + L ≤ K' + 1) :
    relationRho (twoValueSystem K x y L) = relationRho (twoValueSystem K' x y L) := by
  have hspace : RelationSpace (twoValueSystem K x y L) =
      RelationSpace (twoValueSystem K' x y L) := by
    ext u
    exact (mem_value_relation_iff_square_product K _
      (fun i => (complete_vertex_pos_le hx hy hK.1 hK.2 i).1)
      (fun i => (complete_vertex_pos_le hx hy hK.1 hK.2 i).2) u).trans
      (mem_value_relation_iff_square_product K' _
        (fun i => (complete_vertex_pos_le hx hy hK'.1 hK'.2 i).1)
        (fun i => (complete_vertex_pos_le hx hy hK'.1 hK'.2 i).2) u).symm
  unfold relationRho
  rw [hspace]

/-- The same real ceiling can be transported between adequate start cylinders. -/
theorem cappedStartMass_cutoff_eq {K K' L : ℕ} (T : ℝ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ p ∈ s, 2 ≤ p.1 ∧ 2 ≤ p.2)
    (hK : ∀ p ∈ s, p.1 + L ≤ K ∧ p.2 + L ≤ K)
    (hK' : ∀ p ∈ s, p.1 + L ≤ K' ∧ p.2 + L ≤ K') :
    cappedStartMass K L T s = cappedStartMass K' L T s := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [TouchingPairGeometry.relationRho_cutoff_eq (hpos p hp).1 (hpos p hp).2
    (hK p hp) (hK' p hp)]

/-- The same real ceiling can also be transported for unrestricted value relations. -/
theorem cappedValueMass_cutoff_eq {K K' L : ℕ} (T : ℝ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ p ∈ s, 2 ≤ p.1 ∧ 2 ≤ p.2)
    (hK : ∀ p ∈ s, p.1 + L ≤ K + 1 ∧ p.2 + L ≤ K + 1)
    (hK' : ∀ p ∈ s, p.1 + L ≤ K' + 1 ∧ p.2 + L ≤ K' + 1) :
    cappedValueMass K L T s = cappedValueMass K' L T s := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [value_relationRho_cutoff_eq (hpos p hp).1 (hpos p hp).2 (hK p hp) (hK' p hp)]

/-- Choosing the total mass as ceiling leaves every nonnegative start summand unchanged. -/
theorem cappedStartMass_self (K L : ℕ) (s : Finset (ℕ × ℕ)) :
    cappedStartMass K L (relationWeightMass K L s) s = (relationWeightMass K L s : ℝ) := by
  unfold cappedStartMass relationWeightMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply min_eq_right
  exact_mod_cast (Finset.single_le_sum (f := fun q : ℕ × ℕ =>
    2 ^ relationRho (twoStartSystem K q.1 q.2 L) - 1) (fun q _ => Nat.zero_le _) hp)

/-- The corresponding identity for full-value mass has no parity restriction. -/
theorem cappedValueMass_self (K L : ℕ) (s : Finset (ℕ × ℕ)) :
    cappedValueMass K L (valueWeightMass K L s) s = (valueWeightMass K L s : ℝ) := by
  unfold cappedValueMass valueWeightMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply min_eq_right
  exact_mod_cast (Finset.single_le_sum (f := fun q : ℕ × ℕ =>
    2 ^ relationRho (twoValueSystem K q.1 q.2 L) - 1) (fun q _ => Nat.zero_le _) hp)

/-- Every bounded-ratio block lies in a square-root macroscopic interval eventually. -/
theorem boundedRatioBlock_subset_macroscopic {N c : ℕ} (hcN : c ≤ N) :
    Finset.Ico N (c * N) ⊆ macroscopicStarts (c * N) (1 / (2 : ℝ)) := by
  intro x hx
  obtain ⟨hNx, hxZ⟩ := Finset.mem_Ico.mp hx
  apply (mem_macroscopicStarts_iff_real _ _ _).mpr
  refine ⟨?_, hxZ⟩
  rw [← Real.sqrt_eq_rpow]
  have hNreal : (0 : ℝ) ≤ N := by positivity
  have hcNreal : (c : ℝ) ≤ N := by exact_mod_cast hcN
  have hroot : Real.sqrt ((c * N : ℕ) : ℝ) ≤ (N : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hNreal, ?_⟩
    push_cast
    nlinarith
  exact hroot.trans (by exact_mod_cast hNx)

end
end PaperC.V282.RelationProfileRestriction
