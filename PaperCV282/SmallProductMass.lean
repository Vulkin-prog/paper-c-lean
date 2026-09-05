import PaperCV282.ResidualSectorMasks
import PaperCV282.MacroscopicSmallHeightSector

/-!
# A finite host-and-rational bound for residual sector mass

A uniform bound on `2^tau` pays once for each active zero-sigma host and
twice for the rational systematic mass in the positive-sigma branch.
The result applies to every exact sector. It makes no assertion about
the size of the residual factor or of an individual sector.
-/

namespace PaperC.V282.SmallProductMass

open Affine PropositionSixteenOne ResidualSectorPartition ResidualSectorMass
open ResidualSectorMasks FullHostComparison
open scoped BigOperators

noncomputable section

/-- Forgetting subtype proofs counts each relation host exactly once. -/
theorem sum_host_indicator_eq_card {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) :
    (∑ pair ∈ sectorPairs N M A L hN sector,
      if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then 1 else 0) =
      (startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector)).card := by
  classical
  let hosts := startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector)
  have hfilter : (sectorMask (M := M) (L := L) A hN sector).filter
      (fun xy => xy ∈ hosts) = hosts := by
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hxy
      exact ⟨(Finset.mem_filter.mp hxy).1, hxy⟩
  have hsum : (∑ pair ∈ sectorPairs N M A L hN sector,
      if pair.1 ∈ hosts then 1 else 0) =
      ∑ xy ∈ sectorMask (M := M) (L := L) A hN sector,
        if xy ∈ hosts then 1 else 0 := by
    unfold sectorMask
    rw [Finset.sum_image]
    intro p _ q _ hpq
    exact Subtype.ext hpq
  change (∑ pair ∈ sectorPairs N M A L hN sector, if pair.1 ∈ hosts then 1 else 0) = hosts.card
  rw [hsum, ← Finset.sum_filter, hfilter]
  simp

/-- The actual residual weight is charged to active hosts when sigma is
zero and to the rational weight when sigma is positive. -/
theorem residualWeight_le_factor_host_indicator_add_systematic
    {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) {W : ℝ} (hW : 0 ≤ W)
    (pair : SeparatedBoundedRatioPair N M L)
    (hpair : pair ∈ sectorPairs N M A L hN sector)
    (htau : (2 : ℝ) ^ pairTau A hN pair ≤ W) :
    (residualWeight A hN pair : ℝ) ≤ W *
      ((if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then 1 else 0) +
        2 * (systematicWeight A pair : ℝ)) := by
  classical
  by_cases hsigma : pairSigma A pair = 0
  · by_cases hzero : pairTau A hN pair = 0
    · simp only [residualWeight, hzero, pow_zero, Nat.sub_self, Nat.mul_zero, Nat.cast_zero]
      split_ifs <;> positivity
    · have hrho : relationRho (twoStartSystem (M + L) pair.1.1 pair.1.2 L) ≠ 0 := by
        have h := pairRho_eq_pairSigma_add_pairTau (A := A) hN pair
        change relationRho (twoStartSystem (M + L) pair.1.1 pair.1.2 L) =
          pairSigma A pair + pairTau A hN pair at h
        omega
      have hmask : pair.1 ∈ sectorMask (M := M) (L := L) A hN sector :=
        mem_sectorMask.mpr ⟨pair.2, mem_sectorPairs.mp hpair⟩
      have hhost : pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) :=
        Finset.mem_filter.mpr ⟨hmask, hrho⟩
      have hnat : residualWeight A hN pair ≤ 2 ^ pairTau A hN pair := by
        simpa only [residualWeight, hsigma, pow_zero, one_mul] using
          Nat.sub_le (2 ^ pairTau A hN pair) 1
      have hreal : (residualWeight A hN pair : ℝ) ≤ (2 : ℝ) ^ pairTau A hN pair := by
        exact_mod_cast hnat
      simpa only [if_pos hhost, systematicWeight, hsigma, pow_zero, Nat.sub_self,
        Nat.cast_zero, mul_zero, add_zero, mul_one] using hreal.trans htau
  · have hsig : 2 ^ pairSigma A pair ≤ 2 * systematicWeight A pair :=
      MacroscopicSmallHeightSector.two_pow_le_two_mul_weight (Nat.pos_of_ne_zero hsigma)
    have hnat : residualWeight A hN pair ≤
        (2 * systematicWeight A pair) * 2 ^ pairTau A hN pair :=
      Nat.mul_le_mul hsig (Nat.sub_le _ _)
    have hreal : (residualWeight A hN pair : ℝ) ≤
        (2 * (systematicWeight A pair : ℝ)) * (2 : ℝ) ^ pairTau A hN pair := by
      exact_mod_cast hnat
    have hi : (0 : ℝ) ≤
        (if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then 1 else 0) := by
      split_ifs <;> norm_num
    calc
      _ ≤ (2 * (systematicWeight A pair : ℝ)) * (2 : ℝ) ^ pairTau A hN pair := hreal
      _ ≤ (2 * (systematicWeight A pair : ℝ)) * W :=
        mul_le_mul_of_nonneg_left htau (by positivity)
      _ = W * (2 * (systematicWeight A pair : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hi]) hW

/-- A finite residual-factor bound yields a host term and a rational term,
without charging inactive zero-sigma pairs to the size of the full population. -/
theorem sectorMass_le_factor_hosts_add_rational
    {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) {W : ℝ} (hW : 0 ≤ W)
    (htau : ∀ pair ∈ sectorPairs N M A L hN sector,
      (2 : ℝ) ^ pairTau A hN pair ≤ W) :
    sectorMass A sector N M L ≤ W *
      (((startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector)).card : ℝ) +
        2 * (BoundedRatioGeometry.boundedRationalMass N M A L 2 : ℝ)) := by
  classical
  have hsysNat : (∑ pair ∈ sectorPairs N M A L hN sector, systematicWeight A pair) ≤
      BoundedRatioGeometry.boundedRationalMass N M A L 2 := by
    rw [← systematicMassNat_eq_boundedRationalMass]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsys : (∑ pair ∈ sectorPairs N M A L hN sector, (systematicWeight A pair : ℝ)) ≤
      (BoundedRatioGeometry.boundedRationalMass N M A L 2 : ℝ) := by exact_mod_cast hsysNat
  have hhosts : (∑ pair ∈ sectorPairs N M A L hN sector,
      (if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then (1 : ℝ) else 0)) =
      ((startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector)).card : ℝ) := by
    exact_mod_cast sum_host_indicator_eq_card (M := M) (A := A) (L := L) hN sector
  rw [sectorMass, dif_pos hN, sectorMassNat, Nat.cast_sum]
  calc
    _ ≤ ∑ pair ∈ sectorPairs N M A L hN sector, W *
        ((if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then 1 else 0) +
          2 * (systematicWeight A pair : ℝ)) :=
      Finset.sum_le_sum fun pair hpair =>
        residualWeight_le_factor_host_indicator_add_systematic hN sector hW pair hpair (htau pair hpair)
    _ = W * ((∑ pair ∈ sectorPairs N M A L hN sector,
        (if pair.1 ∈ startRelationHosts (M + L) L (sectorMask (M := M) (L := L) A hN sector) then (1 : ℝ) else 0)) +
          2 * ∑ pair ∈ sectorPairs N M A L hN sector, (systematicWeight A pair : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = W * (((startRelationHosts (M + L) L
        (sectorMask (M := M) (L := L) A hN sector)).card : ℝ) +
          2 * ∑ pair ∈ sectorPairs N M A L hN sector, (systematicWeight A pair : ℝ)) := by rw [hhosts]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsys (by norm_num : (0 : ℝ) ≤ 2))) hW

end
end PaperC.V282.SmallProductMass
