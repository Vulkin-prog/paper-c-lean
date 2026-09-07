import PaperCV282.ExactMarkedRates
import PaperCV282.ExactMarkedSignProjection

/-!
# Theorem 5.6 for both actual finite exact-mark fields

Forgetting signs preserves the full position/excess vector and its exact
product target. All four distances use true source laws. The countable
spatial field and diffuse limit are separate from this finite theorem.
-/
namespace PaperC.V282.ExactMarkedFiniteComparison

open ExactMarkedModel ExactMarkedFieldTransfer ExactMarkedFieldBounds ExactMarkedRates
open ExactMarkedLedger ExactMarkedSignProjection MaskedArithmeticGeometry MaskedPairGeometry
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ConditionalStartProbability ConditionalAGGAverage
open SectionThirteenFiniteBound ProcessAGGInput PrimeEulerPNT AllStartSoftPoisson HardPoissonRates
open InfiniteConditionalWords InfiniteCylinderTransfer SectionTwelveMoments TwoWindowParity

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Mean conditional distance of the true unsigned field on represented prime atoms. -/
def exactConditionalDistance (C N L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample C Y =>
    massTotalVariation (sourceConditionalExactLaw C N L E Y mask sigma)
      (poissonFieldMass (allExactRates N L E mask)))

def exactDistance (N L E : ℕ) (mask : Finset ℕ) : ℝ :=
  massTotalVariation (infiniteExactLaw N L E mask) (poissonFieldMass (allExactRates N L E mask))

/-- The literal five terms in (5.13), with the two support lengths kept distinct. -/
def paperExactMarkedError (N L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  (1/(2 : ℝ)^L)*((fullDefectMass L mask : ℝ)+(fullBadMask N (L+E+1) Y mask).card)+
  (1/(2 : ℝ)^L)^2*((N : ℝ)*(L+E+1)+(maskedSupportEdges (L+E+1) Y mask).card+
    (jointDefectMass N L (separatedPairs mask L) : ℝ))

/-- An explicit absolute constant replaces the harmless Q+1 by the printed Q. -/
theorem exactMarkedLedger_le_paperError (N L E Y : ℕ) (mask : Finset ℕ) :
    exactMarkedLedger N L E Y mask ≤ 40*paperExactMarkedError N L E Y mask := by
  unfold exactMarkedLedger paperExactMarkedError
  have hp : 0 ≤ 1/(2 : ℝ)^L := by positivity
  have hp2 : 0 ≤ (1/(2 : ℝ)^L)^2 := sq_nonneg _
  have hm : 0 ≤ (fullDefectMass L mask : ℝ) := by positivity
  have hd : 0 ≤ ((fullBadMask N (L+E+1) Y mask).card : ℝ) := by positivity
  have hg : 0 ≤ ((maskedSupportEdges (L+E+1) Y mask).card : ℝ) := by positivity
  have ht : 0 ≤ (jointDefectMass N L (separatedPairs mask L) : ℝ) := by positivity
  have hlocal : 20*(N : ℝ)*(L+E+2) ≤ 40*(N : ℝ)*(L+E+1) := by
    have hN : 0 ≤ (N : ℝ) := by positivity
    have hL : 0 ≤ (L : ℝ) := by positivity
    have hE : 0 ≤ (E : ℝ) := by positivity
    nlinarith
  have hsmall := mul_nonneg hp (by positivity : 0 ≤ 39*(fullDefectMass L mask : ℝ)+38*(fullBadMask N (L+E+1) Y mask).card)
  have hgraph := mul_le_mul_of_nonneg_left hlocal hp2
  have hrest := mul_nonneg hp2 (by positivity : 0 ≤ 36*((maskedSupportEdges (L+E+1) Y mask).card : ℝ)+38*(jointDefectMass N L (separatedPairs mask L) : ℝ))
  nlinarith only [hsmall,hgraph,hrest]

/-- Equation (5.13), including both signs and all unsigned position/excess labels. -/
theorem equation_five_thirteen (hAGG : ProcessAGGStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hYC : Y ≤ C) (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    smallPrimeSigmaAlgebra C Y = MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    exactConditionalDistance C N L E Y mask ≤ 40*paperExactMarkedError N L E Y mask ∧
    exactSignedConditionalDistance C N L E Y mask ≤ 40*paperExactMarkedError N L E Y mask ∧
    exactDistance N L E mask ≤ 40*paperExactMarkedError N L E Y mask ∧
    exactSignedDistance N L E mask ≤ 40*paperExactMarkedError N L E Y mask := by
  obtain ⟨hc,hu⟩ := signed_source_field_le_ledger hAGG hN hL hC hY mask hmask
  have he := exactMarkedLedger_le_paperError N L E Y mask
  exact ⟨smallPrimeSigmaAlgebra_eq_primeCylinder hYC,
    (average_exact_distance_le_signed hC mask).trans (hc.trans he),hc.trans he,
    (infinite_exact_distance_le_signed N L E mask).trans (hu.trans he),hu.trans he⟩

/-- Theorem 5.6 and (5.14): one threshold, both complete fields, and the literal full F_Y. -/
theorem theorem_five_six (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      smallPrimeSigmaAlgebra (max (hardCutoff N) (dyadicCutoff N (L+E+1))) (hardCutoff N) =
        MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance ∧
      exactConditionalDistance (max (hardCutoff N) (dyadicCutoff N (L+E+1))) N L E (hardCutoff N)
        (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta ∧
      exactSignedConditionalDistance (max (hardCutoff N) (dyadicCutoff N (L+E+1))) N L E (hardCutoff N)
        (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta ∧
      exactDistance N L E (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta ∧
      exactSignedDistance N L E (dyadicBlock N) ≤ 32*exactMarkedRate N L epsilon eta := by
  obtain ⟨Nzero,hzero⟩ := theorem_five_six_signed_full_band hAGG hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero,?_⟩
  intro N hN L E hlo hhi
  obtain ⟨hFY,hc,hu⟩ := hzero N hN L E hlo hhi
  exact ⟨hFY,(average_exact_distance_le_signed (le_max_right _ _) (dyadicBlock N)).trans hc,hc,
    (infinite_exact_distance_le_signed N L E (dyadicBlock N)).trans hu,hu⟩

end
end PaperC.V282.ExactMarkedFiniteComparison
