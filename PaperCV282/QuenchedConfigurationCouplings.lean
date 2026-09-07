import PaperCV282.QuenchedMaximalCouplings
import PaperCV282.QuenchedSpatialDomain

/-! # Couplings of the complete conditional configurations at each geometric scale -/
namespace PaperC.V282.QuenchedConfigurationCouplings

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open FinitePrimeEnvironment ConditionedCountableLaw InfiniteMassCoupling QuenchedMaximalCouplings
open QuenchedBudgetDomain QuenchedAggregateTheorem QuenchedSpatialClosure
open SignedAggregateConfiguration SignedAggregateTruncation SpatialMarkedTypes SpatialMarkedSource
open SpatialMarkedTarget SpatialMarkedFieldComparison GrowingLevelParameters AllStartSoftPoisson
open HardPoissonRates GeometricSaddleSummability SaddleParameters SaddleScales LabelledInformationBudget
open DirectionalSteinInput ProcessAGGInput PrimeEulerPNT

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Couplings for the full signed aggregate, with every mark retained. -/
theorem corollary_six_four_signed_couplings (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes) (c beta : ℝ) (hb : 0<beta) (hbc : beta<c)
    (hbudget : ∀ᶠ k in atTop,
      Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      ∃ mu : Measure (SignedAggregateConfig × SignedAggregateConfig), IsProbabilityMeasure mu ∧
        observableLaw mu Prod.fst=conditionalObservableLaw infiniteRademacherMeasure
          (infiniteSmallPrimeAtom (hardCutoff (sizes k)) (hardCutoff (sizes k))
            (smallPrimeRestriction (hardCutoff (sizes k)) (hardCutoff (sizes k)) omega))
          (signedAggregateSource (sizes k) (movingLength (sizes k) (depths k))) ∧
        observableLaw mu Prod.snd=signedAggregateTargetLaw (sizes k) (movingLength (sizes k) (depths k)) ∧
        mu.real {z | z.1≠z.2}≤Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  filter_upwards [QuenchedBudgetDomain.corollary_six_four_signed hStein hPNT sizes depths hg
    c beta hb hbc hbudget] with omega hw
  filter_upwards [hw] with k hk
  exact environment_coupling_le _ _ _ (measurable_signedAggregateSource _ _) _
    (hasSum_observableLaw _ (measurable_of_countable _)) (observableLaw_nonneg _ _) omega hk

/-- The corresponding full labelled coupling uses exactly its own printed budget. -/
theorem corollary_six_four_labelled_couplings (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes) (c beta : ℝ) (hb : 0<beta) (hbc : beta<c)
    (hbudget : ∀ᶠ k in atTop,
      labelledLogCost 0 (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      ∃ mu : Measure (SpatialMarkedConfig (sizes k) × SpatialMarkedConfig (sizes k)),
        IsProbabilityMeasure mu ∧
        observableLaw mu Prod.fst=conditionalObservableLaw infiniteRademacherMeasure
          (infiniteSmallPrimeAtom (hardCutoff (sizes k)) (hardCutoff (sizes k))
            (smallPrimeRestriction (hardCutoff (sizes k)) (hardCutoff (sizes k)) omega))
          (spatialMarkedSource (sizes k) (movingLength (sizes k) (depths k))) ∧
        observableLaw mu Prod.snd=spatialTargetLaw (sizes k) (movingLength (sizes k) (depths k)) ∧
        mu.real {z | z.1≠z.2}≤Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  filter_upwards [QuenchedSpatialDomain.corollary_six_four_labelled hAGG hPNT sizes depths hg
    c beta hb hbc hbudget] with omega hw
  filter_upwards [hw] with k hk
  exact environment_coupling_le _ _ _ (measurable_spatialMarkedSource _ _) _
    (hasSum_spatialTargetLaw _ _) (spatialTargetLaw_nonneg _ _) omega hk

end
end PaperC.V282.QuenchedConfigurationCouplings
