import PaperCV282.MacroTransportCoordinates
import PaperCV282.MacroTransportHardBudget
import PaperCV282.MacroTransportMovableBudget

/-! # Macroscopic transfer in the literal position/level/sign coordinates -/
namespace PaperC.V282.MacroTransportCoordinateRates

open Filter Topology MeasureTheory InfiniteRademacher InfiniteCylinderTransfer
open MacroTransportCoordinates MacroTransportHardBudget MacroTransportMovableBudget
open GrowingLevelParameters RareConditioningRates LabelledInformationBudget MovableMarkedBudget
open MacroTransportMovableRetained HardPoissonRates SaddleParameters SaddleScales
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson LaishramUniformInput PostQuadraticLiterature

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem theorem_seven_six_positioned_hard_sequences
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      labelledLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => positionedDistance (sizes n) (depths n) (A n))
      atTop (𝓝 0) := by
  have h := theorem_seven_six_labelled_hard_sequences hAGG hPNT hLS hShorey hNR c hc
    sizes depths hsizes hdepths A hA hpos hbudget
  apply h.congr'
  filter_upwards [hpos,hsizes.eventually (eventually_ge_atTop (1 : ℕ))] with n hp hn
  exact (positionedDistance_eq hn (depths n) (A n) hp).symm

theorem theorem_seven_six_positioned_movable_sequences
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
    Tendsto (fun n => positionedDistance (sizes n) (depths n) (A n))
      atTop (𝓝 0) := by
  have h := theorem_seven_six_labelled_movable_sequences hAGG hPNT hLS hShorey hNR c hc
    sizes depths hsizes hdepths A hA hpos hbudget
  apply h.congr'
  filter_upwards [hpos,hsizes.eventually (eventually_ge_atTop (1 : ℕ))] with n hp hn
  exact (positionedDistance_eq hn (depths n) (A n) hp).symm

end
end PaperC.V282.MacroTransportCoordinateRates
