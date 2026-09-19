import PaperCPrel8.StrongerDeletionTheorem
import PaperCPrel8.MicroscopicFullTheorem
import PaperCV282.SaddleRateConvergence

/-! # G.1: original deletions, all mark tails, and stronger replacement together

This is a reduction to the genuinely Poisson-replaced low field. It uses no
Stein solution or assumed comparison for that field. All original source and
target deletions are charged separately, under the original conditioning.
-/
namespace PaperC.Prel8.StrongerRestoration
open MeasureTheory InfiniteRademacher ConditionalStartProbability ArratiaGoldsteinGordonInput IndependentThinning
open StrongerDeletionTheorem SignedGoodReplacement FiniteFieldReplacement ActualSignedPalm
open MicroscopicActualGeometry MicroscopicPaperBudget MicroscopicProfileBudget MicroscopicValueProfile
open MicroscopicGoodField MicroscopicConditionalSpatial MicroscopicSiteRestoration
open MicroscopicDiscardTheorem MicroscopicSpatialRates MicroscopicDeletedTarget MicroscopicDeletedSites
open MicroscopicInfiniteField
open MicroscopicRetainedTheorem
open V282.RareConditioningRates V282.SaddleParameters V282.SaddleScales
open V282.BulkMarkedSource V282.BulkMarkedComparison V282.ConditionedCountableLaw
open V282.FiniteFieldTotalVariation V282.FiniteFieldPoissonCoupling V282.FiniteStartMaskAverages
open V282.LaishramUniformInput V282.PostQuadraticLiterature V282.PrimeEulerPNT
open V282.SaddleRateConvergence
open Filter Topology
open scoped NNReal
noncomputable section
local instance : MeasurableSpace F₂ := ⊤

/-- Distance of the actual stronger replacement from the original low-coordinate target. -/
def replacementDistance (M L : ℕ) (I theta : ℝ)
    (A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop)
    (hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
      (fun w ↦ A (restrictSmall _ _ w))) : ℝ :=
  massTotalVariation
    (replacementLaw (sourceLaw A hA) (field (sourceCylinder M L I) L (paperExcess M L I) (originalGood M L I))
      (kept (originalGood M L I) (strongerGood M L I theta) (paperExcess M L I))
      (fill (originalGood M L I) (strongerGood M L I theta) L (paperExcess M L I)))
    (poissonFieldMass (rate L))

/-- Completing all original deletions and tails costs the old rate plus exactly 2p times the extra count. -/
theorem full_restoration_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I theta : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      ∀ hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun w ↦ A (restrictSmall _ _ w)),
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun w ↦ A (restrictSmall _ _ w))) →
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
        (traceEvent (sourceCylinder M L I) (primeCutoff M) A)
        (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) ≤
      replacementDistance M L I theta A hA +
        8*Real.exp (-c'*saddleNu 1 (Real.log M)) + 2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) +
        2*(1/(2:ℝ)^L)*((added M L I theta).card:ℝ) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hmin hband (by linarith)
  obtain ⟨Md,hd⟩ := deleted_probability_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon
  obtain ⟨Mt,ht⟩ := tail_probability_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' hmin hband (by linarith) hc'
  obtain ⟨My,hy⟩ := deleted_target_rate_eventually hPNT betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon
  obtain ⟨Me,he⟩ := target_tail_eventually c' hc'
  refine ⟨max Mg (max Md (max Mt (max My Me))), ?_⟩
  intro M hM L I theta hlo hhi hI hr hb A hA hi
  let B := traceEvent (sourceCylinder M L I) (primeCutoff M) A
  have hB : 0 < infiniteRademacherMeasure.real B := by dsimp [B]; rwa [traceEvent_probability]
  have hinfo : eventInformation B = I := by
    unfold eventInformation
    dsimp [B]
    rw [traceEvent_probability]
    exact hi.symm
  have g := hg M (by omega) L I hlo hhi hI hr hb
  have hsites := actual_starts_subset (I := I) g.interior_end
  have hcard : (retainedStarts (actualSites M L I)).card ≤ M := by
    have hh := Finset.card_le_card hsites
    simp only [Nat.card_Icc] at hh
    omega
  have hdelete := hd M (by omega) L hlo hhi B hB hr (by rwa [hinfo])
  have htail := ht M (by omega) L hlo hhi B hB hr (by rwa [hinfo]) _ hsites
  rw [hinfo] at hdelete htail
  have htarget := hy M (by omega) L I hlo hhi hI hr hb
  have htargetTail := he M (by omega) L I hI _ hcard
  have hrestore := conditional_restoration_by_hit (retained_subset_interior M L I) L B
    (measurableSet_traceEvent _ _ A) hB
  rw [interior_difference] at hrestore
  have htruncate := spatial_distance_le_finite_and_tails (retainedStarts (actualSites M L I)) L
    (paperExcess M L I) B (measurableSet_traceEvent _ _ A) hB
  dsimp only [B] at htruncate
  rw [conditional_vector_distance,conditionalLaw_eq_finite (actual_goodGeometry g) A hA] at htruncate
  have hreplace := replacement_cost (actual_goodGeometry g) (strongerGood M L I theta) A hA
  let W := field (sourceCylinder M L I) L (paperExcess M L I) (originalGood M L I)
  let K := kept (originalGood M L I) (strongerGood M L I theta) (paperExcess M L I)
  let F := fill (originalGood M L I) (strongerGood M L I theta) L (paperExcess M L I)
  have htri := massTotalVariation_triangle (hasSum_finiteFieldLaw (sourceLaw A hA) W).summable
    (replacement_hasSum (sourceLaw A hA) W K F).summable
    (hasSum_poissonFieldMass (rate L : Index (originalGood M L I) (paperExcess M L I) → ℝ≥0)).summable
    (finiteFieldLaw_nonneg (sourceLaw A hA) W) (replacement_nonneg (sourceLaw A hA) W K F)
    (poissonFieldMass_nonneg (rate L))
  change massTotalVariation (finiteFieldLaw (sourceLaw A hA)
    (field (sourceCylinder M L I) L (paperExcess M L I) (originalGood M L I))) (poissonFieldMass (rate L)) ≤
      _ + replacementDistance M L I theta A hA at htri
  change _ ≤ 2*(1/(2:ℝ)^L)*((added M L I theta).card:ℝ) at hreplace
  dsimp only [B,W,K,F,actualSites,originalGood] at hrestore htruncate hdelete htail htarget htargetTail htri hreplace ⊢
  have hfinite := htri.trans (add_le_add hreplace (le_refl _))
  have hsmall := htruncate.trans (add_le_add (add_le_add htail hfinite) htargetTail)
  have hfull := hrestore.trans (add_le_add (add_le_add hdelete hsmall) htarget)
  convert hfull using 1; ring

/-- An explicit combined error rate for completing G.1. -/
def completionRate (M : ℕ) (theta c c' epsilon : ℝ) : ℝ :=
  8*Real.exp (-c'*saddleNu 1 (Real.log M)) + 2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) +
    2*Real.exp (-((c-theta)/2)*saddleNu 1 (Real.log M))

/-- The full original conditioned field is reduced to the stronger replacement,
with a single explicit uniform error tending to zero. -/
theorem full_stronger_restoration_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax theta c c' epsilon : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (htheta : 0 ≤ theta) (htc : theta < c)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      ∀ hA : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun w ↦ A (restrictSmall _ _ w)),
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun w ↦ A (restrictSmall _ _ w))) →
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
        (traceEvent (sourceCylinder M L I) (primeCutoff M) A)
        (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) ≤
      replacementDistance M L I theta A hA + completionRate M theta c c' epsilon := by
  obtain ⟨Mr,hr⟩ := full_restoration_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hmin hband hc' hcc hepsilon
  obtain ⟨Mc,hc⟩ := paper_counts hPNT betaMin betaMax theta c hmin hband htheta htc
  refine ⟨max Mr Mc, ?_⟩
  intro M hM L I hlo hhi hI hlambda hb A hA hi
  have h := hr M (by omega) L I theta hlo hhi hI hlambda hb A hA hi
  have hm := (hc M (by omega) L I hlo hhi hI hlambda hb).1
  unfold completionRate
  linarith only [h,hm]

/-- The whole restoration cost vanishes in the paper's margin regime. -/
theorem completionRate_tendsto (theta c c' epsilon : ℝ)
    (htc : theta < c) (hc' : 0 < c') (heps : epsilon < 1/3) :
    Tendsto (fun M ↦ completionRate M theta c c' epsilon) atTop (𝓝 0) := by
  have hl : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp
    (((tendsto_saddleNu_atTop (by norm_num : (0:ℝ)<1)).comp hl).const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hc'))
  have h := ((he.const_mul 8).add ((polynomial_error_nat_tendsto_zero epsilon heps).const_mul 2)).add
    (replacement_rate_tendsto theta c htc)
  simpa only [completionRate,Function.comp_def,mul_zero,add_zero] using h

end
end PaperC.Prel8.StrongerRestoration
