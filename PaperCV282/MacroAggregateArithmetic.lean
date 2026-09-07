import PaperCV282.MacroAggregateCosts
import PaperCV282.SignedDirectionalFactors
import PaperCV282.FiniteStartMaskAverages
import PaperCV282.MaskedBadMass

/-! # Directional arithmetic at the actual population intensity -/
namespace PaperC.V282.MacroAggregateArithmetic

open Affine MacroAggregateCosts SignedDirectionalFactors SignedGeometricWeights
open ExactMarkedModel ExactMarkedDependency BulkSupportGraph BulkProcessCosts
open DirectionalHessian DirectionalSteinComparison ConditionalStartProbability
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments ConditionalAGGInstantiation
open MaskedArithmeticGeometry MaskedPairGeometry TwoWindowParity RelationProfileRestriction
open MacroscopicMaskGeometry FiniteStartMaskAverages MaskedBadMass
open scoped BigOperators NNReal

noncomputable section

/-- No lower bound by one is required for either the actual or ambient intensity. -/
theorem directional_factor_le_ambient {lambda mu : ℝ} (hlambda : 0<lambda)
    (hhalf : lambda/2≤mu) (hupper : mu≤lambda) :
    signedDirectionalFactor mu ≤ 24*(1+max 0 (Real.log (2*lambda)))/lambda := by
  have hmu : 0<mu := by linarith
  have hlog := Real.log_le_log (by positivity : 0<2*mu) (by linarith : 2*mu≤2*lambda)
  have hm := max_le_max_left 0 hlog
  have hnum : 0≤1+max 0 (Real.log (2*lambda)) := by positivity
  apply (min_le_right _ _).trans
  apply (le_div_iff₀ hlambda).mpr
  have hdiv := (div_le_div_of_nonneg_left hnum (by positivity : 0<lambda/2) hhalf)
  have hfirst := div_le_div_of_nonneg_right (show 1+max 0 (Real.log (2*mu))≤
    1+max 0 (Real.log (2*lambda)) by linarith) hmu.le
  have hh : (1+max 0 (Real.log (2*mu)))/mu≤2*(1+max 0 (Real.log (2*lambda)))/lambda := by
    exact hfirst.trans (hdiv.trans_eq (by ring))
  have h := (le_div_iff₀ hlambda).mp hh
  nlinarith

/-- The full-value profile remains at Q+1 vertices and the cylinder used by the source. -/
theorem average_typedCost_directional_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L)
    (hC : ∀ x ∈ sites, x+L+E+1 ≤ C) (hY : 2*(L+E+2) ≤ Y)
    (mask : Finset ℕ) (hmask : mask ⊆ sites) (lambda : ℝ≥0) (hlambda : 0<lambda) :
    finiteUniformAverage (fun sigma : SmallSample C Y => typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      Prod.snd (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))
      (entryFactor (signedAggregateRates lambda E))) ≤
      (1/(2 : ℝ)^L)^2 * signedDirectionalFactor lambda *
        (10*(sites.card : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
          (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)) := by
  have h := average_typedCost_signed_le hsite hL hC hY mask hmask
    (entryFactor (signedAggregateRates lambda E)) (entryFactor_nonneg _)
  have hw := signedRatePairSum_le (L := L) (entryFactor (signedAggregateRates lambda E))
    (by positivity) (entryFactor_le_one _) (entryFactor_signed_le hlambda E)
  exact h.trans (mul_le_mul_of_nonneg_right hw (by positivity))

/-- The actual signed aggregate ledger, including deletion and full-value relations. -/
def aggregateLedger (C L E Y : ℕ) (sites : Finset ℕ) : ℝ :=
  (1/(2 : ℝ)^L)*((fullDefectMass L sites : ℝ)+2*(badMask (L+E+1) Y sites).card)+
    (1/(2 : ℝ)^L)^2*signedDirectionalFactor (maskRate L sites)*
      (10*(sites.card : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y sites).card+
        (valueWeightMass C (L+E+1) (separatedPairs sites (L+E+1)) : ℝ))

theorem aggregateLedger_nonneg (C L E Y : ℕ) (sites : Finset ℕ) :
    0≤aggregateLedger C L E Y sites := by
  unfold aggregateLedger
  have h := signedDirectionalFactor_nonneg (maskRate L sites).coe_nonneg
  positivity

end
end PaperC.V282.MacroAggregateArithmetic
