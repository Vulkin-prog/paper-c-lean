import PaperCV282.SpatialMarkedEventComparison
import PaperCV282.LabelledInformationBudget
import PaperCV282.GrowingLevelParameters
import PaperCV282.RareConditioningRates

/-!
# The hard labelled growing-field conclusion of Theorem 5.8(i)

The source is the genuine full spatial configuration, the conditioning is
an actual positive arithmetic event, and the depth is o(log N).
-/
namespace PaperC.V282.SpatialMarkedHardBudget

open Filter Topology MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open SpatialMarkedEventComparison LabelledInformationBudget GrowingMarkedTruncation
open GrowingLevelParameters RareConditioningRates HardPoissonRates SaddleParameters SaddleScales
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson ExactMarkedRates

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A uniform complete-field estimate under the literal hard labelled information margin. -/
theorem hard_labelled_event_bound (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L : ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      labelledLogCost (eventInformation A) (fullRate N L) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      spatialEventDistance N L A ≤
        32*Real.exp (-(c/2)*saddleNu 1 (Real.log N))+
        32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
  have hbmax := hbetaMin.trans hbeta
  obtain ⟨Ne,he⟩ := growing_mark_band_eventually betaMax hbmax
  obtain ⟨Nf,hf⟩ := spatial_event_full_band hAGG hPNT betaMin (2*betaMax) (1/6) (c/2)
    hbetaMin (by linarith) (by norm_num) (by positivity)
  obtain ⟨Nr,hr⟩ := labelled_budget_bound_eventually c hc
  refine ⟨max Ne (max Nf Nr),?_⟩
  intro N hN L hlo hhi hrate A hA hpos hbudget
  have hraw := hf N (by omega) L (growingMarkCutoff N) hlo (he N (by omega) L hhi) A hA hpos
  have hb := hr N (by omega) (eventInformation A) (fullRate N L) hrate hbudget
  have heI : 1 ≤ Real.exp (eventInformation A) := Real.one_le_exp_iff.mpr (eventInformation_nonneg A hpos)
  have ht0 : 0 ≤ (fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) := by positivity
  have htailmul := mul_nonneg (sub_nonneg.mpr heI) ht0
  have hpow1 : -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) := by norm_num
  have hpow2 : -(1/(2 : ℝ))+1/6= -(1/(3 : ℝ)) := by norm_num
  unfold exactMarkedRate at hraw
  rw [hpow1,hpow2,div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  apply le_trans _ hb
  nlinarith

/-- Equation (5.18) implies a full signed spatial comparison tending to zero at growing depth. -/
theorem theorem_five_eight_labelled_hard (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0 < c)
    (d : ℕ → ℕ) (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ N in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] (A N))
    (hpos : ∀ᶠ N in atTop, 0 < infiniteRademacherMeasure.real (A N))
    (hbudget : ∀ᶠ N in atTop,
      labelledLogCost (eventInformation (A N)) (fullRate N (movingLength N (d N))) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N)) :
    Tendsto (fun N => spatialEventDistance N (movingLength N (d N)) (A N)) atTop (𝓝 0) := by
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let lo : ℝ := (1/Real.log 2)/2
  let hi : ℝ := 2*(1/Real.log 2)
  have hlo : 0<lo := by dsimp [lo]; positivity
  have hlo' : lo<1/Real.log 2 := by
    dsimp [lo]
    have hh : 0<1/Real.log (2 : ℝ) := by positivity
    linarith
  have hhi : 1/Real.log 2<hi := by
    dsimp [hi]
    have hh : 0<1/Real.log (2 : ℝ) := by positivity
    linarith
  obtain ⟨Nb,hb⟩ := growing_length_band_eventually d hd lo hi hlo' hhi
  obtain ⟨Nd,hdep⟩ := growing_intensity_eventually d hd 1 (by norm_num)
  obtain ⟨Nr,hr⟩ := hard_labelled_event_bound hAGG hPNT lo hi c hlo (hlo'.trans hhi) hc
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => spatialEventDistance_nonneg _ _ _)) _
    (labelled_budget_error_tendsto_zero c hc)
  filter_upwards [hA,hpos,hbudget,eventually_ge_atTop (max Nb (max Nd (max Nr 2)))] with N hA hpos hbudget hN
  have hdepth : d N ≤ criticalBase N := by have hh := (hdep N (by omega)).1;omega
  have hrate := (fullRate_depth_bounds (by omega : 1≤N) hdepth).1
  have hpow : (1 : ℝ) ≤ 2^(d N) := one_le_pow₀ (by norm_num)
  exact hr N (by omega) (movingLength N (d N)) (hb N (by omega)).1 (hb N (by omega)).2
    (hpow.trans hrate) (A N) hA hpos hbudget

end
end PaperC.V282.SpatialMarkedHardBudget
