import PaperCV282.PrefixVoidBounds
import PaperCV282.PrefixEnvelopeConclusion

/-! # Corollary 7.5: asymmetric almost-sure envelopes of the true longest run

The finite-prefix void estimate is proved from the five explicit literature
inputs below. Error summability, Borel--Cantelli and interpolation to every
integer prefix size are internal proofs; no independence between scales is used.
-/
namespace PaperC.V282.PrefixAlmostSureEnvelopes

open Filter Topology MeasureTheory InfiniteRademacher CorollaryPrefixLaw
open ScalarSteinInput PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature
open PrefixVoidBounds PrefixEnvelopeConclusion PrefixEnvelopeInterpolation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Equations 7.12 and 7.13, with explicit additive constants and the actual longest run. -/
theorem theorem_seven_five
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ M : ℕ in atTop,
      -Real.log (Real.log (Real.log M))/Real.log 2-4 ≤
        (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ∧
      (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2 ≤
        Real.log (Real.log M)/Real.log 2+
        (1+epsilon)*Real.log (Real.log (Real.log M))/Real.log 2+upperAdditiveConstant epsilon := by
  have hlow : 0<1/(2*Real.log (2 : ℝ)) := by positivity
  have hband : 1/(2*Real.log (2 : ℝ))<2/Real.log 2 :=
    CriticalRunWindow.lowerConstant_lt_upperConstant
  have hc : 0<(1/(2*Real.log (2 : ℝ)))*Real.log 2/8 := by positivity
  exact asymmetric_envelopes_of_prefix_bound hPNT 100 _ 1 epsilon hc hepsilon
    (prefix_budget_bound_eventually hStein hLS hShorey hPNT hNR
      _ _ 1 hlow hband (by norm_num))

/-- In particular, R_M=log_2 M+O(loglog M) almost surely. -/
theorem theorem_seven_five_loglog
    (hStein : ScalarSteinFactorsStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      (fun M : ℕ => (infinitePrefixLongestConstantStretch M omega : ℝ)-Real.log M/Real.log 2)
        =O[atTop] (fun M : ℕ => Real.log (Real.log M)) := by
  filter_upwards [theorem_seven_five hStein hLS hShorey hPNT hNR 1 (by norm_num)] with omega h
  exact loglog_envelope_of_asymmetric 1 (by norm_num) _ h

end
end PaperC.V282.PrefixAlmostSureEnvelopes
