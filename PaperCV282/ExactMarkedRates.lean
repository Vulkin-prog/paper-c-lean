import PaperCV282.ExactMarkedFieldBounds
import PaperCV282.ExactMarkedArithmeticRates
import PaperCV282.SaddleCutoffAdmissibility

/-!
# Equation (5.14) for actual signed exact marks on the full logarithmic band

The same threshold precedes the base length and the maximal excess. The
exponential remainder is quantified by every positive eta. Full F_Y is
represented by a cylinder covering both the observation and Y.
-/
namespace PaperC.V282.ExactMarkedRates

open ExactMarkedFieldBounds ExactMarkedArithmeticRates ExactMarkedLedger
open HardPoissonRates SaddleCutoffAdmissibility SaddleParameters SaddleScales
open PrimeEulerPNT ProcessAGGInput ConditionalStartProbability AllStartSoftPoisson
open InfiniteConditionalWords InfiniteCylinderTransfer

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The intensity factor of (5.14) multiplies the whole error. -/
def exactMarkedRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  (fullRate N L : ℝ)*(1+(fullRate N L : ℝ))*
    (Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
      (N : ℝ)^(-(1/(3 : ℝ))+epsilon))

/-- Signed (5.14), for both the mean full-F_Y conditional distance and the actual infinite law. -/
theorem theorem_five_six_signed_full_band (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      smallPrimeSigmaAlgebra (max (hardCutoff N) (dyadicCutoff N (L+E+1))) (hardCutoff N) =
        MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance ∧
      exactSignedConditionalDistance (max (hardCutoff N) (dyadicCutoff N (L+E+1))) N L E (hardCutoff N)
        (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta ∧
      exactSignedDistance N L E (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta := by
  obtain ⟨Nr,hr⟩ := exact_marked_arithmetic_rate_eventually hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (2*betaMax) (by norm_num)
    (by have hh := hbetaMin.trans hbeta; positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nr (max Na (max Nl 2)),?_⟩
  intro N hN L E hlo hhi
  have hL : 1 ≤ L := hl N (by omega) L hlo
  have hhi' : ((L+E+2 : ℕ)+1 : ℝ) ≤ (2*betaMax)*Real.log N := by
    push_cast
    have he : (0 : ℝ) ≤ E := by positivity
    have hll : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+E+2) ≤ hardCutoff N := (ha N (by omega) (L+E+2) hhi').2.2.1
  obtain ⟨hFY,hcond,huncond⟩ := signed_field_fullFY_bound hAGG (by omega : 2 ≤ N) hL hY
    (dyadicBlock N) (Finset.Subset.refl _)
  have harith : exactMarkedLedger N L E (hardCutoff N) (dyadicBlock N) ≤
      32*exactMarkedRate N L epsilon eta := by
    simpa only [exactMarkedRate,mul_assoc] using hr N (by omega) L E hlo hhi
  exact ⟨hFY,hcond.trans harith,huncond.trans harith⟩

end
end PaperC.V282.ExactMarkedRates
