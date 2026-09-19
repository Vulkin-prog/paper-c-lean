import PaperCPrel8.PalmNormalizationRate
import PaperCPrel8.MicroscopicReadouts
import PaperCPrel8.ArithmeticPalmAvoidance

/-! # Completion of the arithmetic one-sided Palm deficit

Every retained mask is allowed. The bound comes from the already proved
microscopic comparison and the explicit normalization cost; regular-target
probability is not needed for this one-sided implication.
-/
namespace PaperC.Prel8.ArithmeticPalmCompletion
open MeasureTheory ProbabilityTheory Finset Filter Topology InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedSource V282.BulkMarkedTarget V282.BulkMarkedComparison
open V282.FiniteFieldTotalVariation V282.ConditionedCountableLaw V282.InfiniteMassCoupling
open V282.CountableLawTransfer V282.MacroTransportRestriction V282.SharpConditioning
open V282.LaishramUniformInput V282.PostQuadraticLiterature V282.PrimeEulerPNT
open V282.DirectionalSteinInput V282.SaddleParameters V282.SaddleScales
open ConditionalStartProbability ArratiaGoldsteinGordonInput
open ArithmeticPalmDeficit ArithmeticPalmNormalization ArithmeticPalmMass PalmVoidAverage
open MicroscopicSiteRestoration MicroscopicRetainedTheorem MicroscopicActualGeometry
open MicroscopicProfileBudget MicroscopicPaperBudget MicroscopicConditionalSpatial ActualSignedPalm
open scoped NNReal
open MicroscopicValueProfile
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Restriction to any deterministic mask contracts the genuine conditional distance. -/
theorem retained_distance_le {C Y : ℕ} {s t : Finset ℕ} (hst : s⊆t) (L : ℕ)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    massTotalVariation (sourceMass s L A) (targetMass s L)≤
      massTotalVariation (sourceMass t L A) (targetMass t L) := by
  let mu := cond infiniteRademacherMeasure (traceEvent C Y A)
  letI : IsProbabilityMeasure mu := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hA)
  have h := observableLaw_statistic_tv_le mu (spatialTargetMeasure t L)
    (measurable_spatialMarkedSource t L) measurable_id (restrictSites hst)
  have he : (restrictSites hst) ∘ (spatialMarkedSource t L)=spatialMarkedSource s L := by
    funext w
    exact restrict_spatialMarkedSource hst L w
  rw [he,Function.comp_id,observableLaw_of_hasLaw _ _ (hasLaw_restrictSites hst L)] at h
  exact h

theorem retained_card_le {M L : ℕ} (sites : Finset ℕ) (hs : sites⊆interiorStarts M L) :
    sites.card≤M-L := by
  apply (card_le_card hs).trans
  unfold interiorStarts retainedStarts
  exact card_image_le.trans (by simp)

/-- The full G.4 finite comparison pays the actual ordinary outside-start
probability, the independent target deletion rate and the regular target exception. -/
theorem full_retained_normalized_comparison {C L E Y K : ℕ} {s t : Finset ℕ}
    (hst : s⊆t) (hL : 1≤L) (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    |massTotalVariation (sourceMass t L A) (targetMass t L)-
      voidDeficit (targetMass s L) (boundedRegular s C L E Y K) (normalizedVoid s L A)|≤
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        (IndependentScalarTail.hitEvent L (t\s))+
      (V282.FiniteStartMaskAverages.maskRate L (t\s):ℝ)+
      PalmDeficit.exceptionalMass (targetMass s L) (boundedRegular s C L E Y K)+penalty s L K := by
  have hproj := retained_distance_le hst L A hA
  have hrest := conditional_restoration_by_hit hst L (traceEvent C Y A)
    (measurableSet_traceEvent C Y A) hA
  have hcond := cond_real_apply infiniteRademacherMeasure (traceEvent C Y A)
    (measurableSet_traceEvent C Y A) (IndependentScalarTail.hitEvent L (t\s))
  have hd : massTotalVariation (sourceMass t L A) (targetMass t L)-
      massTotalVariation (sourceMass s L A) (targetMass s L)≤
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        (IndependentScalarTail.hitEvent L (t\s))+(V282.FiniteStartMaskAverages.maskRate L (t\s):ℝ) := by
    change massTotalVariation (sourceMass t L A) (targetMass t L)≤
      infiniteRademacherMeasure.real (traceEvent C Y A ∩ IndependentScalarTail.hitEvent L (t\s))/
        infiniteRademacherMeasure.real (traceEvent C Y A)+
      massTotalVariation (sourceMass s L A) (targetMass s L)+
        (V282.FiniteStartMaskAverages.maskRate L (t\s):ℝ) at hrest
    rw [hcond]
    linarith
  exact normalized_comparison s hL A hA (by linarith) hd

/-- G.5's actual retained Palm average is uniformly bounded by the microscopic
error plus M^(-1/2), under precisely the same explicit literature/Stein inputs. -/
theorem normalized_deficit_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0<betaMin)
    (hband : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ,
      1≤L → betaMin*Real.log M≤(L+1:ℝ) → (L+1:ℝ)≤betaMax*Real.log M →
      0≤I → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      0 < infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A) →
      I = -Real.log (infiniteRademacherMeasure.real
        (traceEvent (sourceCylinder M L I) (primeCutoff M) A)) →
      DirectionalSolutionBounds (rate L : Index (actualSites M L I) (paperExcess M L I) → ℝ≥0) →
      ∀ sites : Finset ℕ, sites⊆interiorStarts M L → ∀ E : ℕ,
      voidDeficit (targetMass sites L)
        (boundedRegular sites (sourceCylinder M L I) L E (primeCutoff M) ⌈2*siteRate M L⌉₊)
        (normalizedVoid sites L A)≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon)+(M:ℝ)^(-(1/(2:ℝ))) := by
  obtain ⟨Mf,hf⟩ := MicroscopicFullTheorem.full_spatial_comparison_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon
  obtain ⟨Mp,hp⟩ := PalmNormalizationRate.penalty_eventually betaMax c (by linarith) (by linarith)
  refine ⟨max Mf Mp,?_⟩
  intro M hM L I hL hlo hhi hI hr hb A hA hi hsol sites hs E
  have hfull := hf M (by omega) L I hlo hhi hI hr hb A
    (by rwa [traceEvent_probability] at hA) (by rwa [traceEvent_probability] at hi) hsol
  have hretain := retained_distance_le hs L A hA
  have hpen := hp M (by omega) L I sites hL hhi hI (retained_card_le sites hs) hr hb
  have hav := normalized_average_le (E := E) (K := ⌈2*siteRate M L⌉₊) sites hL A hA
  change massTotalVariation (sourceMass (interiorStarts M L) L A) (targetMass (interiorStarts M L) L)≤_ at hfull
  linarith

/-- The explicit majorant in the arithmetic Palm completion vanishes. -/
theorem completion_error_tendsto (c' epsilon : ℝ) (hc' : 0<c') (hepsilon : epsilon<1/3) :
    Tendsto (fun M : ℕ ↦ 10*Real.exp (-c'*saddleNu 1 (Real.log M))+
      4*(M:ℝ)^(-(1/(3:ℝ))+epsilon)+(M:ℝ)^(-(1/(2:ℝ)))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,add_zero] using
    (MicroscopicReadouts.full_error_tendsto_zero c' epsilon hc' hepsilon).add hh

end
end PaperC.Prel8.ArithmeticPalmCompletion
