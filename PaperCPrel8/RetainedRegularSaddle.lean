import PaperCPrel8.RetainedRegularTarget
import PaperCPrel8.ArithmeticPalmCompletion

/-! # The retained regular target exception at the literal paper parameters -/
namespace PaperC.Prel8.RetainedRegularSaddle
open Finset MeasureTheory Filter Topology
open V282.BulkMarkedTypes V282.BulkMarkedTarget V282.PrimeEulerPNT
open V282.SaddleParameters V282.SaddleScales
open MicroscopicActualGeometry MicroscopicProfileBudget MicroscopicPaperBudget MicroscopicValueProfile
open StrongerDeletionTheorem RoughKernelGoodSet RoughKernelDeletion MicroscopicGoodField
open ArithmeticPalmNormalization RegularTargetSaddle RetainedRegularTarget
noncomputable section

def paperRetainedRegular (M L : ℕ) (I theta : ℝ) :
    SpatialMarkedConfig (retainedStarts (strongerGood M L I theta)) → Prop :=
  boundedRegular (retainedStarts (strongerGood M L I theta)) (sourceCylinder M L I)
    L (paperExcess M L I) (primeCutoff M) ⌈2*siteRate M L⌉₊

theorem strongerGood_subset_grid (M L : ℕ) (I theta : ℝ) :
    strongerGood M L I theta⊆Icc 1 (M-L) :=
  (strongGood_subset _ _ _ _).trans (goodSites_subset _ _ _ _ _)

/-- This is the exact named G.4 target exception, on the original first-site coordinates. -/
theorem paper_exception_le (M L : ℕ) (I theta : ℝ) :
    (spatialTargetMeasure (retainedStarts (strongerGood M L I theta)) L).real
      {z | ¬paperRetainedRegular M L I theta z}≤
    (spatialTargetMeasure (Icc 1 (M-L)) L).real {z | ¬paperRegular M L I theta z} := by
  apply exceptional_probability_le (strongerGood_subset_grid M L I theta)
  unfold sourceCylinder
  omega

/-- The literal retained target exceptional probability tends to zero by actual restriction. -/
theorem paper_exception_tendsto (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c theta : ℝ) (hmin : 0<betaMin) (hband : betaMin<betaMax)
    (htheta : 0<theta) (htc : theta<c) (L : ℕ → ℕ) (I : ℕ → ℝ)
    (hrate : Tendsto (fun M ↦ siteRate M (L M)) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop, betaMin*Real.log M≤(L M+1:ℝ) ∧
      (L M+1:ℝ)≤betaMax*Real.log M ∧ 0≤I M ∧ 1≤siteRate M (L M) ∧
      I M+Real.log (siteRate M (L M))≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M)) :
    Tendsto (fun M ↦ (spatialTargetMeasure (retainedStarts (strongerGood M (L M) (I M) theta)) (L M)).real
      {z | ¬paperRetainedRegular M (L M) (I M) theta z}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
    (Eventually.of_forall (fun M ↦ paper_exception_le M (L M) (I M) theta))
  exact RegularTargetCompletion.target_failure_tendsto hPNT betaMin betaMax c theta hmin hband
    htheta htc L I hrate hregime

/-- The paper-order normalization cost uses the actual n=M-L, with its subtraction justified by Lambda>=1. -/
theorem paper_penalty_le (M L : ℕ) (I theta : ℝ) (hL : 1≤L) (hr : 1≤siteRate M L) :
    penalty (retainedStarts (strongerGood M L I theta)) L ⌈2*siteRate M L⌉₊≤
      5*(siteRate M L)^2/(M-L:ℕ) := by
  have hrate : siteRate M L=((M-L:ℕ):ℝ)*baseRate L := by unfold siteRate baseRate; ring
  have hn : M-L≠0 := by
    intro hz
    rw [hrate,hz] at hr
    norm_num at hr
  have hnR : ((M-L:ℕ):ℝ)≠0 := by exact_mod_cast hn
  have hcard : (retainedStarts (strongerGood M L I theta)).card≤M-L := by
    apply ArithmeticPalmCompletion.retained_card_le
    exact Finset.image_subset_image (strongerGood_subset_grid M L I theta)
  have hp := PalmNormalizationRate.penalty_le _ hL hcard (by rwa [← hrate])
  rw [← hrate] at hp
  apply hp.trans_eq
  rw [hrate]
  field_simp

/-- Exceptional masses are actual probabilities under the complete target law. -/
theorem exceptionalMass_eq (sites : Finset ℕ) (L : ℕ) (regular : SpatialMarkedConfig sites → Prop) :
    PalmDeficit.exceptionalMass (ArithmeticPalmDeficit.targetMass sites L) regular=
      (spatialTargetMeasure sites L).real {z | ¬regular z} := by
  classical
  have h := V282.InfiniteMassCoupling.restricted_observableLaw_eq_event (spatialTargetMeasure sites L)
    measurable_id {z | ¬regular z}
  simp only [Set.preimage_id] at h
  rw [← h]
  apply tsum_congr
  intro z
  by_cases hz : regular z <;>
    simp [PalmDeficit.exceptionalMass,ArithmeticPalmDeficit.targetMass,V282.InfiniteMassCoupling.observableLaw,hz]

/-- Literal G.4 bound: original source/target deletion costs, the named retained
regular target exception, and an explicit 5 Lambda^2/n normalization constant. -/
theorem paper_normalized_comparison (M L : ℕ) (I theta : ℝ) (hL : 1≤L) (hr : 1≤siteRate M L)
    (A : ConditionalStartProbability.SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop)
    (hA : 0 < InfiniteRademacher.infiniteRademacherMeasure.real
      (MicroscopicConditionalSpatial.traceEvent (sourceCylinder M L I) (primeCutoff M) A)) :
    let s := retainedStarts (strongerGood M L I theta)
    let t := MicroscopicSiteRestoration.interiorStarts M L
    |V282.FiniteFieldTotalVariation.massTotalVariation
        (ArithmeticPalmDeficit.sourceMass t L A) (ArithmeticPalmDeficit.targetMass t L)-
      PalmVoidAverage.voidDeficit (ArithmeticPalmDeficit.targetMass s L)
        (paperRetainedRegular M L I theta) (normalizedVoid s L A)|≤
      (ProbabilityTheory.cond InfiniteRademacher.infiniteRademacherMeasure
        (MicroscopicConditionalSpatial.traceEvent (sourceCylinder M L I) (primeCutoff M) A)).real
        (IndependentScalarTail.hitEvent L (t\s))+
      (V282.FiniteStartMaskAverages.maskRate L (t\s):ℝ)+
      (spatialTargetMeasure s L).real {z | ¬paperRetainedRegular M L I theta z}+
      5*(siteRate M L)^2/(M-L:ℕ) := by
  dsimp only
  have hsubset : retainedStarts (strongerGood M L I theta)⊆MicroscopicSiteRestoration.interiorStarts M L :=
    Finset.image_subset_image (strongerGood_subset_grid M L I theta)
  have h := ArithmeticPalmCompletion.full_retained_normalized_comparison
    (E := paperExcess M L I) (K := ⌈2*siteRate M L⌉₊) hsubset hL A hA
  rw [exceptionalMass_eq] at h
  exact h.trans (add_le_add (le_refl _) (paper_penalty_le M L I theta hL hr))

end
end PaperC.Prel8.RetainedRegularSaddle
