import PaperCV282.MacroTransportMovableComparison
import PaperCV282.MacroTransportMovableInformation
import PaperCV282.SignedAggregateHardBudget

/-! # The labelled movable clause of the macroscopic transfer theorem

The source retains the actual positions and every excess/sign at the exactly
base-contained starts. The conditioning event and moving lengths are genuine.
-/
namespace PaperC.V282.MacroTransportMovableBudget

open Filter Topology MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open MacroTransportModel MacroTransportMovableComparison MacroTransportMovableInformation
open MovableMarkedBudget MacroTransportMovableRetained GrowingLevelParameters RareConditioningRates
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson
open LaishramUniformInput PostQuadraticLiterature SignedAggregateHardBudget

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Uniform movable information estimate before the length and the actual arithmetic event. -/
theorem movable_labelled_event_bound (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      1≤(fullRate M L : ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (movableCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      movableLogCost (eventInformation A) (fullRate M L)≤
        saddleCutoff 2 (Real.log M)/2-c*saddleNu 2 (Real.log M) →
      conditionalDistance M L A≤
      2*(64*Real.exp (-(c/2)*saddleNu 2 (Real.log M))+64*(M : ℝ)^(-(1/(12 : ℝ)))+
        3*Real.exp (-saddleCutoff 2 (Real.log M)))+
        2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Nf,hf⟩ := contained_event_movable_bound_eventually hAGG hPNT hLS hShorey hNR
    betaMin betaMax (1/6) (c/2) hbetaMin hbeta (by norm_num) (by positivity)
  have hd : 0<betaMin*Real.log 2/8 := by have := Real.log_pos (by norm_num : (1 : ℝ)<2);positivity
  obtain ⟨Nb,hb⟩ := movable_restored_budget_eventually c (betaMin*Real.log 2/8) hc hd
  refine ⟨max Nf Nb,?_⟩
  intro M hM L hlo hhi hrate A hA hpos hbudget
  have hraw := hf M (by omega) L hlo hhi A hA hpos
  have hnum := hb M (by omega) (eventInformation A) (fullRate M L) (eventInformation_nonneg A hpos) hrate hbudget
  dsimp only [movableCore] at hraw
  norm_num only [show -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) by norm_num] at hraw
  rw [div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
  have he : betaMin*Real.log 2/8/2=betaMin*Real.log 2/16 := by ring
  rw [he] at hnum
  rw [mul_comm] at hraw
  exact hraw.trans hnum

/-- Arbitrary population and length sequences in the whole band. -/
theorem movable_labelled_sequence_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hband : ∀ᶠ n in atTop, betaMin*Real.log (sizes n)≤(lengths n+1 : ℝ) ∧
      (lengths n+1 : ℝ)≤betaMax*Real.log (sizes n) ∧ 1≤(fullRate (sizes n) (lengths n) : ℝ))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (movableCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      movableLogCost (eventInformation (A n)) (fullRate (sizes n) (lengths n))≤
        saddleCutoff 2 (Real.log (sizes n))/2-c*saddleNu 2 (Real.log (sizes n))) :
    Tendsto (fun n => conditionalDistance (sizes n) (lengths n) (A n)) atTop (𝓝 0) := by
  obtain ⟨Mzero,hMzero⟩ := movable_labelled_event_bound hAGG hPNT hLS hShorey hNR
    betaMin betaMax c hbetaMin hbeta hc
  have hd : 0<betaMin*Real.log 2/8 := by have := Real.log_pos (by norm_num : (1 : ℝ)<2);positivity
  have hz := (movable_restored_error_tendsto_zero c (betaMin*Real.log 2/8) hc hd).comp hsizes
  have he : betaMin*Real.log 2/8/2=betaMin*Real.log 2/16 := by ring
  rw [he] at hz
  apply squeeze_zero' (hpos.mono (fun n hn => conditionalDistance_nonneg _ _ _ hn)) _ hz
  filter_upwards [hband,hA,hpos,hbudget,hsizes.eventually (eventually_ge_atTop Mzero)] with n hb ha hp hcost hn
  exact hMzero (sizes n) hn (lengths n) hb.1 hb.2.1 hb.2.2 (A n) ha hp hcost

/-- The movable labelled information margin in 7.6, for arbitrary growing population sequences. -/
theorem theorem_seven_six_labelled_movable_sequences
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (movableCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      movableLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 2 (Real.log (sizes n))/2-c*saddleNu 2 (Real.log (sizes n))) :
    Tendsto (fun n => conditionalDistance (sizes n) (movingLength (sizes n) (depths n)) (A n))
      atTop (𝓝 0) := by
  have hl : 0<(1 : ℝ)/Real.log 2 := by have := Real.log_pos (by norm_num : (1 : ℝ)<2);positivity
  let lo : ℝ := (1/Real.log 2)/2
  let hi : ℝ := 2*(1/Real.log 2)
  have hlo : 0<lo := by dsimp [lo];positivity
  have hlo' : lo<1/Real.log 2 := by dsimp [lo];linarith
  have hhi : 1/Real.log 2<hi := by dsimp [hi];linarith
  apply movable_labelled_sequence_tendsto_zero hAGG hPNT hLS hShorey hNR lo hi c hlo (hlo'.trans hhi) hc
    sizes (fun n => movingLength (sizes n) (depths n)) hsizes _ A hA hpos hbudget
  exact (moving_sequence_domain_eventually sizes depths hsizes hdepths lo hi hlo' hhi).mono
    (fun n hn => ⟨hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2⟩)

end
end PaperC.V282.MacroTransportMovableBudget
