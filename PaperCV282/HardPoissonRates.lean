import PaperCV282.HardPoissonBounds
import PaperCV282.SaddleArithmeticBounds

/-!
# The hard-deletion rate on the entire logarithmic band

Both arithmetic inputs are instantiated on their actual objects. The
threshold precedes the length, and the intensity multiplies the entire
sum of exponential and polynomial errors. The same bound holds for the
true F_Y conditional average and the unconditional infinite source law.
-/

namespace PaperC.V282.HardPoissonRates

open MeasureTheory Set InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open ConditionalStartProbability ConditionalAGGAverage
open ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open SaddleCutoffAdmissibility SaddleArithmeticBounds
open MaskedArithmeticGeometry MaskedPairGeometry AllStartSoftPoisson
open FullBandArithmetic HardPoissonBounds DyadicPoissonDistance

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The manuscript's integer hard cutoff, with the exact floor. -/
def hardCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊

/-- The intensity multiplies both summands in equation (4.8). -/
def hardRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  (fullRate N L : ℝ) *
    (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon))

/-- Hard deletion before the final minimum, with a fixed numerical constant. -/
theorem hard_conditional_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      hardCutoff N ≤ dyadicCutoff N L ∧
        conditionalDistance N L (hardCutoff N) ≤ 20 * hardRate N L epsilon eta := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  obtain ⟨Nm, hm⟩ := fullDefectMass_div_block_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Nr, hr⟩ := normalized_relation_mass_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  obtain ⟨Na, ha⟩ := saddleCutoff_nat_admissible_eventually 1 betaMax (by norm_num) hbetaMax
  obtain ⟨Nh, hh⟩ := fullBadStarts_fraction_le_half_eventually hPNT 1 betaMax (by norm_num) hbetaMax
  obtain ⟨Nd, hd⟩ := normalized_fullBadMask_saddle_cost_le_eventually
    hPNT 1 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Ne, he⟩ := normalized_degree_and_edges_saddle_le_eventually
    1 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Nl, hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nm (max Nr (max Na (max Nh (max Nd (max Ne (max Nl 2)))))), ?_⟩
  intro N hN L hlo hhi
  have hNtwo : 2 ≤ N := by omega
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := hl N (by omega) L hlo
  obtain ⟨_,_,hYlo,hYhi⟩ := ha N (by omega) L hhi
  refine ⟨hYhi, ?_⟩
  have hm' : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) :=
    (hm N (by omega) L hlo hhi _ (Finset.Subset.refl _)).trans
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith))
  have hd' := hd N (by omega) L hhi (dyadicBlock N)
  rw [fullBadMask_block_eq] at hd'
  simp only [div_one] at hd'
  have he' := (he N (by omega) L hhi _ (Finset.Subset.refl _)).2
  have hu : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
    calc
      _ = (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hbound := conditionalDistance_le_of_arithmetic hStein hNtwo hL hYlo
    (Real.exp_nonneg _) (Real.rpow_nonneg hNpos.le _)
    (hh N (by omega) L hhi) hm' hd' he' hu (hr N (by omega) L hlo hhi)
  simpa only [hardCutoff, hardRate, mul_assoc] using hbound

/-- Equation (4.8), including the mean conditional and unconditional true-law bounds. -/
theorem theorem_four_three_hard
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      smallPrimeSigmaAlgebra (dyadicCutoff N L) (hardCutoff N) =
          MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance ∧
      conditionalDistance N L (hardCutoff N) ≤ 20 * min 1 (hardRate N L epsilon eta) ∧
      countDistance N L ≤ 20 * min 1 (hardRate N L epsilon eta) := by
  obtain ⟨Nzero,hzero⟩ := hard_conditional_rate_eventually
    hStein hPNT betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi
  obtain ⟨hY, hbound⟩ := hzero N hN L hlo hhi
  have hmin := le_mul_min_one_of_le (by norm_num : (1 : ℝ) ≤ 20)
    (conditionalDistance_le_one N L (hardCutoff N)) hbound
  exact ⟨conditioningSigma_eq_full_FY hY, hmin,
    (countDistance_le_conditionalDistance N L (hardCutoff N)).trans hmin⟩

end
end PaperC.V282.HardPoissonRates
