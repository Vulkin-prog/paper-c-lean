import PaperCV282.ResidualSectorPartition

/-!
# Exact residual-mass decomposition over the eight v2.8.2 sectors

The weight on each pair is the actual canonical residual weight
`2^sigma * (2^tau - 1)`. The partition acts on the entire population,
including zero-weight pairs, and its exact sum transfers to the literal
macroscopic domain and the finite prescribed-value comparison.
No asymptotic estimate for an individual sector is assumed or asserted.
-/

namespace PaperC.V282.ResidualSectorMass

open PropositionSixteenOne ResidualSectorPartition
open MacroscopicGeometry MacroscopicRelationProfile
open TwoWindowParity TwoWindowSquareHosts
open scoped BigOperators

noncomputable section

/-- The natural residual mass on one of the eight exact sectors. -/
def sectorMassNat {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N) (sector : Fin 8) : ℕ :=
  ∑ pair ∈ sectorPairs N M A L hN sector, residualWeight A hN pair

/-- The sector weight is literally `2^sigma * (2^tau - 1)`. -/
theorem sectorMassNat_eq_sum_weight {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (sector : Fin 8) :
    sectorMassNat (M := M) (L := L) A hN sector =
      ∑ pair ∈ sectorPairs N M A L hN sector,
        2 ^ pairSigma A pair * (2 ^ pairTau A hN pair - 1) := rfl

/-- Every sector contributes at most the full residual mass. -/
theorem sectorMassNat_le_residualMassNat {N M A L : ℕ} (hN : 2 ≤ N)
    (sector : Fin 8) :
    sectorMassNat (M := M) (L := L) A hN sector ≤
      residualMassNat (N := N) (M := M) (L := L) A hN := by
  unfold sectorMassNat residualMassNat
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Exact disintegration of the actual natural residual mass into eight sectors. -/
theorem residualMassNat_eq_sum_sectorMassNat {N M A L : ℕ} (hN : 2 ≤ N) :
    residualMassNat (N := N) (M := M) (L := L) A hN =
      ∑ sector : Fin 8, sectorMassNat (M := M) (L := L) A hN sector := by
  classical
  have hfiber := Finset.sum_fiberwise
    (Finset.univ : Finset (SeparatedBoundedRatioPair N M L))
    (sectorOf A hN) (residualWeight A hN)
  simpa only [residualMassNat, sectorMassNat, sectorPairs] using hfiber.symm

/-- Proof-independent real sector mass, with the historical zero convention below 2. -/
def sectorMass (A : ℕ) (sector : Fin 8) (N M L : ℕ) : ℝ :=
  if hN : 2 ≤ N then (sectorMassNat (M := M) (L := L) A hN sector : ℝ) else 0

theorem sectorMass_nonneg (A : ℕ) (sector : Fin 8) (N M L : ℕ) :
    0 ≤ sectorMass A sector N M L := by
  unfold sectorMass
  split_ifs <;> positivity

/-- Exact real disintegration beyond the positive-start lower endpoint. -/
theorem residualMass_eq_sum_sectorMass {N M A L : ℕ} (hN : 2 ≤ N) :
    residualMass A N M L = ∑ sector : Fin 8, sectorMass A sector N M L := by
  simp only [residualMass, sectorMass, dif_pos hN]
  exact_mod_cast residualMassNat_eq_sum_sectorMassNat (M := M) (A := A) (L := L) hN

/-- Each real sector mass is bounded by the actual residual mass. -/
theorem sectorMass_le_residualMass {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) :
    sectorMass A sector N M L ≤ residualMass A N M L := by
  simp only [sectorMass, residualMass, dif_pos hN]
  exact_mod_cast sectorMassNat_le_residualMassNat (M := M) (A := A) (L := L) hN sector

/-- The full weighted start mass is the rational part plus the eight residual masses. -/
theorem R2kappa_eq_systematic_add_sectors {N M A L : ℕ} (hN : 2 ≤ N) :
    R2κ N M L = systematicMass A N M L +
      ∑ sector : Fin 8, sectorMass A sector N M L := by
  rw [R2κ_eq_systematic_add_residual hN, residualMass_eq_sum_sectorMass hN]

/-- Exact assembly on the literal macroscopic interval; `A=3` is the paper's choice. -/
theorem macroscopicStartMass_eq_systematic_add_sectors
    (A : ℕ) {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (macroscopicStartMassNat M L δ : ℝ) =
      systematicMass A ⌈(M : ℝ) ^ δ⌉₊ M L +
        ∑ sector : Fin 8, sectorMass A sector ⌈(M : ℝ) ^ δ⌉₊ M L := by
  rw [macroscopicStartMassNat_cast_eq_R2kappa]
  exact R2kappa_eq_systematic_add_sectors (two_le_macroscopic_lowerEndpoint hM hδ)

/-- Finite value comparison with the exact eight-sector residual decomposition inserted. -/
theorem macroscopicValueMass_le_four_systematic_add_sectors_add_hosts
    (A : ℕ) {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (macroscopicValueMassNat M L δ : ℝ) ≤
      4 * (systematicMass A ⌈(M : ℝ) ^ δ⌉₊ M L +
        ∑ sector : Fin 8, sectorMass A sector ⌈(M : ℝ) ^ δ⌉₊ M L) +
      3 * ((squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) := by
  have hfinite : (macroscopicValueMassNat M L δ : ℝ) ≤
      4 * (macroscopicStartMassNat M L δ : ℝ) +
        3 * ((squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) := by
    exact_mod_cast macroscopicValueMassNat_le_four_start_add_hosts (L := L) hM hδ
  rw [macroscopicStartMass_eq_systematic_add_sectors A hM hδ] at hfinite
  exact hfinite

end
end PaperC.V282.ResidualSectorMass
