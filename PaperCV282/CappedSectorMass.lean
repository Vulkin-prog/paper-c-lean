import PaperCV282.ResidualSectorMasks
import PaperCV282.CappedRelationMass

/-!
# Capping the exact eight-sector residual decomposition

The cap is a real parameter and the factors in the final finite estimate
are chosen independently of it. These results preserve the terminal
ceiling needed for the future proof of Proposition 3.27.
-/

namespace PaperC.V282.CappedSectorMass

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass ResidualSectorMasks
open CappedRelationMass MacroscopicGeometry MacroscopicRelationProfile TwoWindowParity
open scoped BigOperators

noncomputable section

/-- The genuine residual weight of one sector capped at the real ceiling. -/
def cappedSectorMass (A : ℕ) (sector : Fin 8) (T : ℝ) (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    ∑ p ∈ sectorPairs N M A L hN sector, min T (residualWeight A hN p : ℝ)
  else 0

/-- The capped residual mass before splitting into sectors. -/
def cappedResidualMass (A : ℕ) (T : ℝ) (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    ∑ p : SeparatedBoundedRatioPair N M L, min T (residualWeight A hN p : ℝ)
  else 0

theorem cappedSectorMass_nonneg (A : ℕ) (sector : Fin 8) {T : ℝ}
    (hT : 0 ≤ T) (N M L : ℕ) : 0 ≤ cappedSectorMass A sector T N M L := by
  unfold cappedSectorMass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => le_min hT (Nat.cast_nonneg _)
  · rfl

/-- Sector masses increase monotonically with the common ceiling. -/
theorem cappedSectorMass_mono_cap (A : ℕ) (sector : Fin 8) {S T : ℝ}
    (hST : S ≤ T) (N M L : ℕ) :
    cappedSectorMass A sector S N M L ≤ cappedSectorMass A sector T N M L := by
  unfold cappedSectorMass
  split_ifs
  · exact Finset.sum_le_sum fun _ _ => min_le_min_right _ hST
  · rfl

/-- Leaving any sector uncapped is a valid upper bound. -/
theorem cappedSectorMass_le_sectorMass (A : ℕ) (sector : Fin 8) (T : ℝ) (N M L : ℕ) :
    cappedSectorMass A sector T N M L ≤ sectorMass A sector N M L := by
  unfold cappedSectorMass sectorMass
  split_ifs with hN
  · unfold sectorMassNat
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun _ _ => min_le_right _ _
  · rfl

/-- The cap times the exact number of pairs gives a second, independent bound. -/
theorem cappedSectorMass_le_cap_mul_card {N M A L : ℕ} (hN : 2 ≤ N)
    (sector : Fin 8) (T : ℝ) :
    cappedSectorMass A sector T N M L ≤ T * ((sectorPairs N M A L hN sector).card : ℝ) := by
  simp only [cappedSectorMass, dif_pos hN]
  calc
    _ ≤ ∑ _p ∈ sectorPairs N M A L hN sector, T := Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ = _ := by simp [mul_comm]

/-- An empty sector has zero capped mass for every real ceiling. -/
theorem cappedSectorMass_eq_zero_of_empty {N M A L : ℕ} (hN : 2 ≤ N)
    (sector : Fin 8) (T : ℝ) (hempty : sectorPairs N M A L hN sector = ∅) :
    cappedSectorMass A sector T N M L = 0 := by
  simp [cappedSectorMass, dif_pos hN, hempty]

/-- Disjoint partitioning commutes exactly with capping the residual weight. -/
theorem cappedResidualMass_eq_sum_sectors (A : ℕ) (T : ℝ) (N M L : ℕ) :
    cappedResidualMass A T N M L =
      ∑ sector : Fin 8, cappedSectorMass A sector T N M L := by
  classical
  by_cases hN : 2 ≤ N
  · simp only [cappedResidualMass, cappedSectorMass, dif_pos hN]
    have hfiber := Finset.sum_fiberwise
      (Finset.univ : Finset (SeparatedBoundedRatioPair N M L))
      (sectorOf A hN) (fun p => min T (residualWeight A hN p : ℝ))
    simpa only [sectorPairs] using hfiber.symm
  · simp [cappedResidualMass, cappedSectorMass, hN]

/-- Finite transfer of the capped start mass to the historical interval subtype. -/
theorem cappedStartMass_eq_subtype_sum (N M L : ℕ) (T : ℝ) :
    cappedStartMass (M + L) L T (separatedBoundedRatioPairs N M L) =
      ∑ p : SeparatedBoundedRatioPair N M L, min T (homogeneousWeight p : ℝ) := by
  classical
  exact Finset.sum_subtype (separatedBoundedRatioPairs N M L)
    (fun _ => Iff.rfl) (fun xy =>
      min T ((2 ^ Affine.relationRho (Affine.twoStartSystem (M + L) xy.1 xy.2 L) - 1 : ℕ) : ℝ))

/-- The rational weight is uncapped, while all eight residual ceilings remain intact. -/
theorem cappedStartMass_le_systematic_add_capped_sectors
    {N M A L : ℕ} (hN : 2 ≤ N) (T : ℝ) :
    cappedStartMass (M + L) L T (separatedBoundedRatioPairs N M L) ≤
      systematicMass A N M L + ∑ sector : Fin 8, cappedSectorMass A sector T N M L := by
  rw [← cappedResidualMass_eq_sum_sectors, cappedStartMass_eq_subtype_sum]
  simp only [systematicMass, cappedResidualMass, dif_pos hN]
  unfold systematicMassNat
  rw [Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  rw [homogeneousWeight_eq_systematic_add_residual (A := A) hN p, Nat.cast_add]
  exact min_add_le_left_add_min (Nat.cast_nonneg _)

/-- The finite capped sector mechanism keeps the same envelope for every ceiling. -/
theorem cappedSectorMass_le_card_mul_envelope_min
    {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8)
    {E Q T : ℝ} (hE : 1 ≤ E) (hT : 0 ≤ T)
    (hweight : ∀ p ∈ sectorPairs N M A L hN sector, (residualWeight A hN p : ℝ) ≤ E * Q) :
    cappedSectorMass A sector T N M L ≤
      ((sectorPairs N M A L hN sector).card : ℝ) * E * min T Q := by
  simp only [cappedSectorMass, dif_pos hN]
  calc
    _ ≤ ∑ _p ∈ sectorPairs N M A L hN sector, E * min T Q := by
      apply Finset.sum_le_sum
      intro p hp
      exact (min_le_min_left T (hweight p hp)).trans (min_mul_le_mul_min hE hT)
    _ = _ := by simp [mul_assoc]

/-- Exact macroscopic specialization of the finite capped decomposition. -/
theorem macroscopic_cappedStartMass_le_systematic_add_sectors
    (A : ℕ) {M L : ℕ} {delta : ℝ} (hM : 2 ≤ M) (hdelta : 0 < delta) (T : ℝ) :
    cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
      systematicMass A ⌈(M : ℝ) ^ delta⌉₊ M L +
        ∑ sector : Fin 8, cappedSectorMass A sector T ⌈(M : ℝ) ^ delta⌉₊ M L :=
  cappedStartMass_le_systematic_add_capped_sectors (two_le_macroscopic_lowerEndpoint hM hdelta) T

/-- Full values keep the same ceiling after the finite four-to-one comparison. -/
theorem macroscopic_cappedValueMass_le_four_systematic_add_sectors_add_hosts
    (A : ℕ) {M L : ℕ} {delta T : ℝ}
    (hM : 2 ≤ M) (hdelta : 0 < delta) (hT : 0 ≤ T) :
    cappedValueMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
      4 * (systematicMass A ⌈(M : ℝ) ^ delta⌉₊ M L +
        ∑ sector : Fin 8, cappedSectorMass A sector T ⌈(M : ℝ) ^ delta⌉₊ M L) +
      3 * ((TwoWindowSquareHosts.squareProductHosts L
        (separatedPairs (macroscopicStarts M delta) L)).card : ℝ) := by
  have hs := separatedPairs_macroscopicStarts_subset_Icc_product hM hdelta L
  have hcomp := cappedValueMass_le_four_start_add_square_hosts (M + L) L hT
    (separatedPairs (macroscopicStarts M delta) L) (by
      intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
      exact ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hy).1⟩) (by
      intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hs hxy)
      have hxM := (Finset.mem_Icc.mp hx).2
      have hyM := (Finset.mem_Icc.mp hy).2
      constructor <;> omega)
  have hsum := macroscopic_cappedStartMass_le_systematic_add_sectors A (L := L) hM hdelta T
  linarith

end
end PaperC.V282.CappedSectorMass
