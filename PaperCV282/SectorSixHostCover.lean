import PaperCV282.SizeTwoHostCounting

/-!
# The actual two-defect and size-two cover of residual sector 6

The new sixth-sector tests imply that one start window has two defective
values and that the canonical core has a size-two component. Fixing that
start and the component shape leaves only a degree-one square equation
in the other start. All finite cover and fibre bounds here are internal.
-/

namespace PaperC.V282.SectorSixHostCover

open Affine PropositionSixteenOne ResidualSectorPartition ResidualComponentCounts
open SizeTwoHostCounting BoundedRatioComponentHosts
open BoundedRatioManyDefectsFibers BoundedRatioManyDefectsFixedFibers
open SquarefreeSmoothCount
open scoped BigOperators

noncomputable section

/-- The literal sixth-sector host has both arithmetic certificates. -/
theorem sector_six_arithmetic_certificates
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hsix : sectorOf A hN pair = 5) :
    pair ∈ boundedComponentHosts N M A L 2 ∧
      (pair.1.1 - 1 ∈ twoDefectBaseCover N M (L + 1) ∨
        pair.1.2 - 1 ∈ twoDefectBaseCover N M (L + 1)) := by
  have htests := sectorOf_eq_six_iff.mp hsix
  have hmoderate := htests.2.2.2.2.1
  have hdefects := htests.2.2.2.2.2
  have hdense : 2 * (L + 1) < 3 * canonicalResidualComponentCount A pair.1.1 pair.1.2 L := by
    simpa only [moderateCore, not_le] using hmoderate
  refine ⟨mem_sizeTwoHosts_of_dense_core hN pair hdense, ?_⟩
  have hcoords := pair_coordinates_two_le hN pair
  have hwindows := PropositionNineNineHostGeometry.two_le_one_defectInterval_of_three_le_corrected
    A (by omega : 1 ≤ pair.1.1) (by omega : 1 ≤ pair.1.2) hdefects
  have hpair := (mem_separatedBoundedRatioPairs.mp pair.property)
  rcases hwindows with hleft | hright
  · exact Or.inl (shiftedBase_mem_twoDefectBaseCover_of_two_defects
      (Finset.mem_Ico.mp hpair.1).1 (Finset.mem_Ico.mp hpair.1).2 (by omega) hleft)
  · exact Or.inr (shiftedBase_mem_twoDefectBaseCover_of_two_defects
      (Finset.mem_Ico.mp hpair.2.1).1 (Finset.mem_Ico.mp hpair.2.1).2 (by omega) hright)

/-- The finite cover retains the two actual shifted starts and every size-two offset shape. -/
def orientedSizeTwoCover (N M A L : ℕ) : Finset (SeparatedBoundedRatioPair N M L) :=
  (twoDefectBaseCover N M (L + 1)).biUnion fun base =>
    (boundedOffsetShapes L 2).biUnion fun shape =>
      leftBaseShapeFiber N M A L 2 base shape ∪ rightBaseShapeFiber N M A L 2 base shape

/-- Every new sixth-sector pair belongs to that concrete finite union. -/
theorem sector_six_subset_orientedCover
    {N M A L : ℕ} (hN : 2 ≤ N) :
    sectorPairs N M A L hN 5 ⊆ orientedSizeTwoCover N M A L := by
  classical
  intro pair hpair
  obtain ⟨hhost, hbase⟩ := sector_six_arithmetic_certificates hN pair (mem_sectorPairs.mp hpair)
  obtain ⟨shape, hshape, hshapeHost⟩ := Finset.mem_biUnion.mp
    (boundedComponentHosts_subset_shapeUnion hN hhost)
  rcases hbase with hleft | hright
  · apply Finset.mem_biUnion.mpr
    refine ⟨pair.1.1 - 1, hleft, Finset.mem_biUnion.mpr ⟨shape, hshape, ?_⟩⟩
    exact Finset.mem_union_left _ (mem_leftBaseShapeFiber.mpr ⟨hshapeHost, rfl⟩)
  · apply Finset.mem_biUnion.mpr
    refine ⟨pair.1.2 - 1, hright, Finset.mem_biUnion.mpr ⟨shape, hshape, ?_⟩⟩
    exact Finset.mem_union_right _ (mem_rightBaseShapeFiber.mpr ⟨hshapeHost, rfl⟩)

/-- Each orientation has mobile degree one, so the retained fibre bound is a square-root count. -/
theorem card_orientedSizeTwoCover_le
    {N M A L : ℕ} (hN : 2 ≤ N) :
    (orientedSizeTwoCover N M A L).card ≤
      2 * (twoDefectBaseCover N M (L + 1)).card * ((3 * (L + 1) ^ 2) ^ 2) *
        (squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card * (Nat.sqrt (M + L) + 1) := by
  classical
  let W := (squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card * (Nat.sqrt (M + L) + 1)
  have hlocal : ∀ base : ℕ, ∀ shape ∈ boundedOffsetShapes L 2,
      (leftBaseShapeFiber N M A L 2 base shape ∪
        rightBaseShapeFiber N M A L 2 base shape).card ≤ 2 * W := by
    intro base shape hshape
    have hdata := mem_boundedOffsetShapes.mp hshape
    have hleftpos := Finset.card_pos.mpr hdata.1
    have hrightpos := Finset.card_pos.mpr hdata.2.1
    have hleft : shape.1.card = 1 := by omega
    have hright : shape.2.card = 1 := by omega
    have hcl : (leftBaseShapeFiber N M A L 2 base shape).card ≤ W :=
      card_leftBaseShapeFiber_degree_one hN shape hright
    have hcr : (rightBaseShapeFiber N M A L 2 base shape).card ≤ W :=
      card_rightBaseShapeFiber_degree_one hN shape hleft
    exact (Finset.card_union_le _ _).trans (by omega)
  have hunion : (orientedSizeTwoCover N M A L).card ≤
      (twoDefectBaseCover N M (L + 1)).card * ((boundedOffsetShapes L 2).card * (2 * W)) := by
    apply Finset.card_biUnion_le_card_mul
    intro base _hbase
    exact Finset.card_biUnion_le_card_mul _ _ _ (hlocal base)
  have hshapes := card_boundedOffsetShapes_le L 2
  calc
    _ ≤ _ := hunion
    _ ≤ (twoDefectBaseCover N M (L + 1)).card * (((3 * (L + 1) ^ 2) ^ 2) * (2 * W)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hshapes)
    _ = _ := by dsimp only [W]; ring

/-- The resulting finite host count for exactly the sixth new sector. -/
theorem card_sector_six_le
    {N M A L : ℕ} (hN : 2 ≤ N) :
    (sectorPairs N M A L hN 5).card ≤
      2 * (twoDefectBaseCover N M (L + 1)).card * ((3 * (L + 1) ^ 2) ^ 2) *
        (squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card * (Nat.sqrt (M + L) + 1) :=
  (Finset.card_le_card (sector_six_subset_orientedCover hN)).trans (card_orientedSizeTwoCover_le hN)

end
end PaperC.V282.SectorSixHostCover
