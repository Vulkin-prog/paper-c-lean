import PaperCV282.AffineCrossoverBudget
import PaperCV282.BulkMarkedStable
import PaperCV282.BulkMarkedConvergence
import PaperCV282.RareConditioningRates

/-! # Actual recorded bulk comparison after hard information conditioning

The product retains the distribution of the record under the conditioning
event. Only the bulk factor is replaced by the same independent Poisson law.
-/
namespace PaperC.V282.AffineCrossoverStable

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedGeometry
open BulkMarkedComparison BulkMarkedRates BulkMarkedStable BulkMarkedConvergence
open PrimeEnvironmentStableLift SharpConditioning RareConditioningRates HardPoissonRates
open ConditionedCountableLaw
open AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput AffineCrossoverBudget SaddleParameters SaddleScales

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

variable {γ : Type*} [MeasurableSpace γ]

/-- The genuine joint law and the conditioned record marginal are used on both sides. -/
def conditionedJointDistance (M L : ℕ) (delta : ℝ) (V : InfiniteSample → γ)
    (A : Set InfiniteSample) : ℝ :=
  measureTotalVariation
    ((cond infiniteRademacherMeasure A).map (fun omega =>
      (V omega,spatialMarkedSource (bulkStarts M L delta) L omega)))
    (((cond infiniteRademacherMeasure A).map V).prod
      (spatialTargetMeasure (bulkStarts M L delta) L))

theorem measurable_of_fullFY {Y : ℕ} {V : InfiniteSample → γ}
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] V) :
    Measurable V := by
  have hVm : Measurable[smallPrimeSigmaAlgebra Y Y] V := by
    rwa [smallPrimeSigmaAlgebra_eq_primeCylinder (le_refl Y)]
  exact hVm.mono (smallPrimeSigmaAlgebra_le Y Y) le_rfl

theorem conditionedJointDistance_nonneg (M L : ℕ) (delta : ℝ) (V : InfiniteSample → γ)
    (hV : Measurable V) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A) :
    0≤conditionedJointDistance M L delta V A := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityJoint : IsProbabilityMeasure
      ((cond infiniteRademacherMeasure A).map (fun omega =>
        (V omega,spatialMarkedSource (bulkStarts M L delta) L omega))) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (measurable_spatialMarkedSource _ _)).aemeasurable
  letI instProbabilityRecord : IsProbabilityMeasure ((cond infiniteRademacherMeasure A).map V) :=
    Measure.isProbabilityMeasure_map hV.aemeasurable
  exact measureTotalVariation_nonneg _ _

/-- The finite atom average gives the actual stable joint bound with one inverse event mass. -/
theorem conditioned_joint_le_average (M L : ℕ) (delta : ℝ) (V : InfiniteSample → γ)
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] V)
    (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionedJointDistance M L delta V A ≤
      bulkConditionalDistance M L delta / infiniteRademacherMeasure.real A := by
  exact (fullFY_conditioned_stable_product_lift (le_refl (hardCutoff M)) _
    (measurable_spatialMarkedSource _ _) _ (bulkConditionalDistance M L delta) (le_refl _)
    V hV A hA hpos).2

/-- The uniform threshold precedes the length, the recorded variable and the event. -/
theorem conditioned_recorded_joint_rate_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → (fullRate M L : ℝ)≤1 →
      ∀ V : InfiniteSample → γ,
      Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] V →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      eventInformation A≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      conditionedJointDistance M L delta V A≤(fullRate M L : ℝ)*relativeError M c := by
  obtain ⟨Nr,hr⟩ := theorem_seven_seven hAGG hPNT betaMin betaMax delta (1/12) (c/2)
    hbetaMin hbeta hdelta (by norm_num) (by linarith)
  obtain ⟨Nb,hb⟩ := weighted_bulk_error_eventually hc
  refine ⟨max Nr Nb,?_⟩
  intro M hM L hlo hhi hrate V hV A hA hpos hbudget
  have hraw := (conditioned_joint_le_average M L delta V hV A hA hpos).trans
    (div_le_div_of_nonneg_right (hr M (by omega) L hlo hhi hrate) hpos.le)
  rw [div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  have hnum := mul_le_mul_of_nonneg_left (hb M (by omega) (eventInformation A) hbudget)
    (show 0≤(fullRate M L : ℝ) by positivity)
  unfold bulkRelativeRate at hraw
  nlinarith only [hraw,hnum]

/-- The genuine conditional joint error is o(lambda), uniformly over recorded full-F_Y variables. -/
theorem conditioned_recorded_joint_relative_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (V : ℕ→InfiniteSample→γ) (A : ℕ→Set InfiniteSample)
    (hV : ∀ᶠ n in atTop,Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (V n))
    (hA : ∀ᶠ n in atTop,MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,eventInformation (A n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => conditionedJointDistance (sizes n) (lengths n) delta (V n) (A n)/
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,hzero⟩ := conditioned_recorded_joint_rate_eventually (γ := γ) hAGG hPNT
    (1/2) (beta+1) delta c (by norm_num) (by linarith) hdelta hc
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  apply squeeze_zero' ?_ ?_ ((relativeError_tendsto_zero hc).comp hsizes)
  · filter_upwards [hV,hpos] with n hv hp
    exact div_nonneg (conditionedJointDistance_nonneg _ _ _ _ (measurable_of_fullFY hv) _ hp) (by positivity)
  · filter_upwards [hupper,hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),hsizes.eventually (eventually_ge_atTop (max Mzero 1)),
      hV,hA,hpos,hbudget] with n hu hr hl hn hv ha hp hb
    have hband := rare_window_band (by omega) hl hbeta hu hr.le
    have hrate : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
      rw [fullRate_coe]
      have hs : 0<(sizes n : ℝ) := by exact_mod_cast (show 0<sizes n by omega)
      positivity
    apply (div_le_iff₀ hrate).mpr
    simpa only [Function.comp_def,mul_comm] using hzero (sizes n) (by omega) (lengths n) hband.1 hband.2 hr.le
      (V n) hv (A n) ha hp hb

end
end PaperC.V282.AffineCrossoverStable
