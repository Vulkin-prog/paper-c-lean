import PaperCV282.AffineCrossoverStable
import PaperCV282.CrossoverPrimeClockStable

/-! # The original prime clock and full signed bulk field under the information event

The finite-cylinder representative agrees only almost surely with the original
clock. Absolute continuity transports that equality through conditioning.
-/
namespace PaperC.V282.AffineCrossoverStableClock

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open AffineCrossoverStable AffineCrossoverBudget CrossoverPrimeClockStable CrossoverPrimeClockCylinder
open CrossoverPrimeClockCutoff BulkMarkedSource BulkMarkedTarget BulkMarkedGeometry
open RareConditioningRates HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def conditionedTruncatedJointDistance (M L K : ℕ) (delta : ℝ) (A : Set InfiniteSample) : ℝ :=
  conditionedJointDistance M L delta (actualClockRecord L K) A

/-- The actual clock, including its declared default, is restored under every conditioning event. -/
theorem representative_distance_eq (M L K : ℕ) (delta : ℝ) (A : Set InfiniteSample) :
    conditionedJointDistance M L delta (borderClockRecord L K) A =
      conditionedTruncatedJointDistance M L K delta A := by
  have habs : cond infiniteRademacherMeasure A ≪ infiniteRademacherMeasure := cond_absolutelyContinuous
  have he := habs.ae_eq (borderClockRecord_ae_eq_actual L K)
  have hj : (fun omega => (borderClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega))
      =ᵐ[cond infiniteRademacherMeasure A]
      (fun omega => (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)) := by
    filter_upwards [he] with omega h
    exact Prod.ext h rfl
  unfold conditionedTruncatedJointDistance conditionedJointDistance
  rw [Measure.map_congr hj,Measure.map_congr he]

/-- A single threshold allows every clock cap with 2^K≤L and every information event. -/
theorem conditioned_truncated_joint_rate_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L K : ℕ, 2^K≤L →
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → (fullRate M L : ℝ)≤1 →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      eventInformation A≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      conditionedTruncatedJointDistance M L K delta A≤(fullRate M L : ℝ)*relativeError M c := by
  obtain ⟨Nr,hr⟩ := conditioned_recorded_joint_rate_eventually (γ := Bool×ℕ) hAGG hPNT
    betaMin betaMax delta c hbetaMin hbeta hdelta hc
  obtain ⟨Nc,hc'⟩ := measurable_borderClockRecord_hard_eventually betaMax (hbetaMin.trans hbeta)
  refine ⟨max Nr Nc,?_⟩
  intro M hM L K hK hlo hhi hrate A hA hpos hbudget
  rw [← representative_distance_eq]
  exact hr M (by omega) L hlo hhi hrate (borderClockRecord L K)
    (hc' M (by omega) L K hK hhi) A hA hpos hbudget

/-- The cap is fixed before the sequential limit, without assuming the clock is exactly F_Y-measurable. -/
theorem conditioned_truncated_joint_relative_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,eventInformation (A n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => conditionedTruncatedJointDistance (sizes n) (lengths n) K delta (A n)/
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,hzero⟩ := measurable_borderClockRecord_hard_eventually (beta+1) (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hV : ∀ᶠ n in atTop,
      Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance]
        (borderClockRecord (lengths n) K) := by
    filter_upwards [hupper,hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hsizes.eventually (eventually_ge_atTop Mzero),hlengths.eventually (eventually_ge_atTop (2^K))]
      with n hu hl hn hL
    exact hzero (sizes n) hn (lengths n) K hL (by dsimp only [Function.comp_def] at hl;nlinarith)
  have h := conditioned_recorded_joint_relative_tendsto_zero hAGG hPNT sizes lengths hsizes
    beta delta c hbeta hdelta hc hupper hrare (fun n => borderClockRecord (lengths n) K) A hV hA hpos hbudget
  simpa only [representative_distance_eq] using h

end
end PaperC.V282.AffineCrossoverStableClock
