import PaperC.Asymptotics.BoundedRatioTwoSingletonHosts
import PaperC.Analysis.RelationalHostBound
import PaperCV282.SectorSevenRank

/-!
# Dense cores contain a size-two component, whose hosts are counted internally

Strict density `3*c# > 2B` forces a component of size two. The retained
singleton parametrization counts these hosts using only divisors, square
roots, a harmonic sum, and an elementary Euler-product bound. No Pell or
Evertse--Silverman input is used.
-/

namespace PaperC.V282.SizeTwoHostCounting

open PropositionSixteenOne BoundedRatioComponentHosts BoundedRatioTwoSingletonHosts
open CanonicalResidualComponents ResidualComponentCounts LargePrimeGraphResolution
open LargePrimeGraph DefectCounting
open ResidualSectorPartition ResidualSectorMass
open scoped BigOperators

noncomputable section

/-- Strict average size yields a bounded component without rounding away strictness. -/
theorem mem_boundedHosts_of_strict_average
    {N M A L K : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hdense : 2 * (L + 1) < (K + 1) * canonicalResidualComponentCount A pair.1.1 pair.1.2 L) :
    pair ∈ boundedComponentHosts N M A L K := by
  classical
  let family := canonicalResidualComponents A pair.1.1 pair.1.2 L
  have hcard : family.card = canonicalResidualComponentCount A pair.1.1 pair.1.2 L :=
    card_canonicalResidualComponents (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
  have hmass : (∑ C ∈ family, Fintype.card C.supp) ≤ 2 * (L + 1) := by
    have hh := SmallComponentExtraction.sum_component_support_sizes_le
      (largePrimeGraph pair.1.1 pair.1.2 L) family
    simpa only [card_occurrence] using hh
  obtain ⟨C, hC, hsize⟩ := DeepCoreSmallComponent.exists_member_size_le_of_mass_lt
    family (fun C => Fintype.card C.supp) K (2 * (L + 1)) hmass (by
      rw [hcard]
      simpa only [Nat.mul_comm] using hdense)
  exact mem_boundedComponentHosts.mpr ⟨C, hC, hsize⟩

/-- Strict density above two-thirds yields a component on at most two occurrences. -/
theorem mem_sizeTwoHosts_of_dense_core
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hdense : 2 * (L + 1) < 3 * canonicalResidualComponentCount A pair.1.1 pair.1.2 L) :
    pair ∈ boundedComponentHosts N M A L 2 :=
  mem_boundedHosts_of_strict_average hN pair hdense

/-- In particular, both the seventh and eighth exact sectors lie in the size-two host set. -/
theorem late_sectorPairs_subset_sizeTwoHosts
    {N M A L : ℕ} (hN : 2 ≤ N) {sector : Fin 8} (hsector : 6 ≤ sector.val) :
    sectorPairs N M A L hN sector ⊆ boundedComponentHosts N M A L 2 := by
  intro pair hpair
  apply mem_sizeTwoHosts_of_dense_core hN pair
  exact (dense_core_and_few_defects_of_sector_at_least_seven hN pair
    (by rwa [mem_sectorPairs.mp hpair])).1

/-- The sharper prime-sensitive Euler estimate is unnecessary for a subpolynomial bound. -/
theorem twoSingletonEulerProduct_le_exp_sqrt (B : ℕ) :
    twoSingletonEulerProduct B ≤ Real.exp (4 * Real.sqrt B) := by
  have hp := prod_smallPrimesUpTo_one_add_inv_sqrt_le B
  calc
    _ ≤ (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 :=
      twoSingletonEulerProduct_le_square B
    _ ≤ (Real.exp (2 * Real.sqrt B)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp 2
    _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring

/-- Explicit global interval count for all actual size-two component hosts. -/
theorem card_sizeTwoHosts_cast_le_exp_bound
    {N M A L : ℕ} (hN : 2 ≤ N) :
    ((boundedComponentHosts N M A L 2).card : ℝ) ≤
      9 * (L + 1 : ℝ) ^ 4 * (M + L : ℝ) *
        (1 + Real.log (M + L : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
  have hcount : ((boundedComponentHosts N M A L 2).card : ℝ) ≤
      (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) * (twoSingletonParameterCount M L 2 : ℝ) := by
    exact_mod_cast card_boundedComponentHosts_two_le_parameterCount (M := M) (A := A) (L := L) hN
  have hparam := twoSingletonParameterCount_cast_le_logEuler M L 2
  have hlog : 0 ≤ 1 + Real.log (M + L : ℝ) := by
    have hh := harmonic_le_one_add_log (M + L)
    have hnonneg : (0 : ℝ) ≤ (harmonic (M + L) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      positivity
    exact hnonneg.trans (by simpa only [Nat.cast_add] using hh)
  have hparam' : (twoSingletonParameterCount M L 2 : ℝ) ≤
      (M + L : ℝ) * (1 + Real.log (M + L : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    refine hparam.trans ?_
    simp only [boundedRatioCutoff, Nat.cast_add]
    exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using
      twoSingletonEulerProduct_le_exp_sqrt (L + 1)) (mul_nonneg (by positivity) hlog)
  calc
    _ ≤ _ := hcount
    _ ≤ (((3 * (L + 1) ^ 2) ^ 2 : ℕ) : ℝ) *
        ((M + L : ℝ) * (1 + Real.log (M + L : ℝ)) *
          Real.exp (4 * Real.sqrt (L + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hparam' (by positivity)
    _ = _ := by push_cast; ring

/-- The finite host count applies directly to either of the final two exact sectors. -/
theorem card_late_sectorPairs_cast_le_exp_bound
    {N M A L : ℕ} (hN : 2 ≤ N) {sector : Fin 8} (hsector : 6 ≤ sector.val) :
    ((sectorPairs N M A L hN sector).card : ℝ) ≤
      9 * (L + 1 : ℝ) ^ 4 * (M + L : ℝ) *
        (1 + Real.log (M + L : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
  have hcard : (sectorPairs N M A L hN sector).card ≤
      (boundedComponentHosts N M A L 2).card :=
    Finset.card_le_card (late_sectorPairs_subset_sizeTwoHosts hN hsector)
  have hcast : ((sectorPairs N M A L hN sector).card : ℝ) ≤
      ((boundedComponentHosts N M A L 2).card : ℝ) := by exact_mod_cast hcard
  exact hcast.trans (card_sizeTwoHosts_cast_le_exp_bound hN)

end
end PaperC.V282.SizeTwoHostCounting
