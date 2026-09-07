import PaperCV282.D4ClosureLaplaceSource
import PaperCV282.SpatialBoundedInformation
import PaperCV282.CountableExpectationTransfer
import PaperC.Probability.CriticalRunWindow

/-! # Compact centered Laplace tests under the actual arithmetic conditioning -/
namespace PaperC.V282.D4ClosureLaplaceTransfer

open MeasureTheory ProbabilityTheory Filter Topology Real InfiniteRademacher InfiniteCylinderTransfer
open D4ClosureLaplaceSource D4ClosureLaplaceParameters GrowingLevelParameters
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedFieldComparison
open SpatialMarkedTargetLaplace SpatialMarkedEventComparison CountableExpectationTransfer
open ConditionedCountableLaw SpatialBoundedInformation ProcessAGGInput PrimeEulerPNT
open AllStartSoftPoisson CriticalRunWindow HardPoissonRates RareConditioningRates SaddleParameters SaddleScales
open SpatialMarkedParameters ExactMarkedModel
open scoped BigOperators

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def finiteSourceLaplace (N L E : ℕ) (g : ℝ → ℕ → ℝ) (A : Set InfiniteSample) : ℝ :=
  ∫ omega, exp (-(∑ i : SignedMarkIndex N E,
    g ((i.1.val : ℝ)/N) i.2.1.val *
      (projectConfiguration N E (spatialMarkedSource N L omega) i : ℝ)))
    ∂cond infiniteRademacherMeasure A

theorem finite_source_laplace_error_le (N L E : ℕ) (g : ℝ → ℕ → ℝ)
    (hg : ∀ t e, 0 ≤ g t e) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    |finiteSourceLaplace N L E g A -
      finiteSpatialLaplaceExpectation N L E (fun t e _ => g t e)| ≤
        2*spatialEventDistance N L A := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hb (config : SpatialMarkedConfig N) :
      |exp (-(∑ i : SignedMarkIndex N E,
        g ((i.1.val : ℝ)/N) i.2.1.val*(projectConfiguration N E config i : ℝ)))| ≤ 1 := by
    rw [abs_of_pos (exp_pos _)]
    apply exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i hi => mul_nonneg (hg _ _) (Nat.cast_nonneg _))
  have h := integral_difference_le_tv (cond infiniteRademacherMeasure A) (spatialTargetMeasure N L)
    (measurable_spatialMarkedSource N L) measurable_id _ 1 hb
  simpa only [finiteSourceLaplace,finiteSpatialLaplaceExpectation,spatialEventDistance,
    conditionalObservableLaw,spatialTargetLaw,mul_one,id_eq] using h

theorem fixed_depth_eventually (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (d : ℕ) :
    ∀ᶠ n in atTop, d ≤ criticalBase (sizes n) := by
  have hlog := ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hsizes).atTop_div_const
    (log_pos (by norm_num : (1 : ℝ)<2))
  exact (hlog.eventually (eventually_ge_atTop (d : ℝ))).mono fun n hn => Nat.le_floor hn

theorem fixed_depth_window {N d : ℕ} (hN : 1 ≤ N) (hd : d ≤ criticalBase N) :
    InRunLengthWindow (d+1 : ℝ) N (movingLength N d) := by
  obtain ⟨h0,h1⟩ := phase_bounds hN
  unfold InRunLengthWindow movingLength
  rw [Nat.cast_sub hd]
  unfold dyadicPhase at h0 h1
  rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) d])]
  linarith

theorem fixed_depth_spatial_error (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (d : ℕ) (c : ℝ) (hc : 0 < c)
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n => spatialEventDistance (sizes n) (movingLength (sizes n) d) (A n))
      atTop (𝓝 0) := by
  obtain ⟨Nw,hw⟩ := firstMomentWindow_eventually (C := (d : ℝ)+1) (by positivity)
  have hdata : ∀ᶠ n in atTop,
      CriticalFirstMoment.FirstMomentWindow lowerConstant upperConstant (balanceConstant (d+1))
        (sizes n) (movingLength (sizes n) d) := by
    filter_upwards [hsizes.eventually (eventually_ge_atTop (max Nw 1)),
      fixed_depth_eventually sizes hsizes d] with n hn hd
    exact hw _ (by omega) _ (fixed_depth_window (by omega) hd)
  apply spatial_event_tendsto_zero hAGG hPNT sizes _ hsizes lowerConstant upperConstant
    (balanceConstant (d+1)) c lowerConstant_pos lowerConstant_lt_upperConstant hc A _ _ hA hpos hbudget
  · exact hdata.mono fun n hn => ⟨by exact_mod_cast hn.1.2.2.1,by exact_mod_cast hn.1.2.2.2⟩
  · exact hdata.mono fun n hn => hn.2.2

/-- The arithmetic error is derived from the actual all-mark comparison; it is not a premise. -/
theorem compact_source_laplace_moving_error (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (d E : ℕ) (g : ℝ × ℤ → ℝ) (hg0 : ∀ z, 0 ≤ g z)
    (hg : ∀ r, ContinuousOn (fun t => g (t,r)) (Set.Icc (1 : ℝ) 2))
    (hlo : ∀ t r, r < -(d : ℤ) → g (t,r) = 0)
    (hhi : ∀ t r, (E : ℤ)-d < r → g (t,r) = 0)
    (c : ℝ) (hc : 0 < c) (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop, eventInformation (A n) ≤
      saddleCutoff 1 (log (sizes n))-c*saddleNu 1 (log (sizes n))) :
    Tendsto (fun n =>
      (∫ omega, exp (-(∫ z, g z ∂centeredSourceMeasure (sizes n) omega))
        ∂cond infiniteRademacherMeasure (A n)) -
      exp (-(criticalSpatialScale (sizes n) (movingLength (sizes n) d) *
        ∫ t in Set.Ico (1 : ℝ) 2,
          markedRetentionIntegrand E (fun t e => g (t,(e : ℤ)-d)) t))) atTop (𝓝 0) := by
  let test : ℝ → ℕ → ℝ := fun t e => g (t,(e : ℤ)-d)
  have hd := fixed_depth_eventually sizes hsizes d
  have hbound : ∀ᶠ n in atTop,
      criticalSpatialScale (sizes n) (movingLength (sizes n) d) ≤ 2*(2 : ℝ)^d := by
    filter_upwards [hsizes.eventually (eventually_ge_atTop (1 : ℕ)),hd] with n hn hnd
    exact (fullRate_depth_bounds hn hnd).2.le
  have htarget := finite_laplace_moving_error sizes (fun n => movingLength (sizes n) d)
    hsizes (2*(2 : ℝ)^d) hbound E test (fun e he => hg _) (fun t e => hg0 _)
  have hsource : Tendsto (fun n => finiteSourceLaplace (sizes n) (movingLength (sizes n) d) E test (A n)-
      finiteSpatialLaplaceExpectation (sizes n) (movingLength (sizes n) d) E (fun t e _ => test t e))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using
      (fixed_depth_spatial_error hAGG hPNT sizes hsizes d c hc A hA hpos hbudget).const_mul 2)
    exact hpos.mono fun n hn => by simpa only [Real.norm_eq_abs] using
      finite_source_laplace_error_le (sizes n) (movingLength (sizes n) d) E test (fun t e => hg0 _) (A n) hn
  have hsum := hsource.add htarget
  simp only [zero_add,sub_add_sub_cancel] at hsum
  apply hsum.congr'
  filter_upwards [hd] with n hn
  congr 1
  unfold finiteSourceLaplace
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega => by
    dsimp only
    rw [centered_source_compact_pairing hn E g hlo hhi]

end
end PaperC.V282.D4ClosureLaplaceTransfer
