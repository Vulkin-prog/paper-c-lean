import PaperCV282.MaskedScalarFullConditioning
import PaperCV282.AllStartSoftPoisson
import PaperCV282.FiniteFieldTotalVariation

/-!
# Actual whole-block Poisson distances and their small-prime fibres

The scalar distance is the true law of the infinite start count. The
conditional distance averages the exact positive source-atom ratios.
The represented sigma-algebra is all of F_Y when Y is covered by the
finite event cylinder, as is proved eventually at both saddle cutoffs.
-/

namespace PaperC.V282.DyadicPoissonDistance

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteMaskedScalarTransfer MaskedScalarFullConditioning
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionThirteenCouplings
open SectionTwelveMoments MaskedPoissonCritical MaskedScalarCoupling MaskedScalarTransfer
open AllStartSoftPoisson ScalarSteinInput
open scoped BigOperators NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Distance for the full block under the actual infinite source law. -/
def countDistance (N L : ℕ) : ℝ :=
  natTotalVariation (infiniteMaskedLaw L (dyadicBlock N)) (poissonMass (fullRate N L))

/-- Mean distance on the literal small-prime fibres of the event cylinder. -/
def conditionalDistance (N L Y : ℕ) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    natTotalVariation (conditionalMaskedLaw N L Y (dyadicBlock N) sigma)
      (poissonMass (fullRate N L)))

theorem maskedTargetPoissonRate_block_eq (N L : ℕ) :
    maskedTargetPoissonRate L (dyadicBlock N) = fullRate N L := by
  apply NNReal.eq
  simp [maskedTargetPoissonRate, fullRate, TouchingPairs.card_dyadicBlock]

/-- Mixing cannot increase the distance to the fixed full-block target. -/
theorem countDistance_le_conditionalDistance (N L Y : ℕ) :
    countDistance N L ≤ conditionalDistance N L Y := by
  unfold countDistance conditionalDistance
  rw [infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw _ (Finset.Subset.refl _),
    ← maskedTargetPoissonRate_block_eq]
  exact unconditional_scalar_tv_le_average N L Y (dyadicBlock N)

/-- Both laws have mass one, so the unconditional distance is at most one. -/
theorem countDistance_le_one (N L : ℕ) : countDistance N L ≤ 1 := by
  unfold countDistance
  rw [infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw _ (Finset.Subset.refl _)]
  exact FiniteFieldTotalVariation.massTotalVariation_le_one (hasSum_finiteNatLaw _ _)
    (hasSum_poissonMass _) (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _)

/-- Every conditioned law has mass one, hence the same unit bound after averaging. -/
theorem conditionalDistance_le_one (N L Y : ℕ) : conditionalDistance N L Y ≤ 1 := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    FiniteFieldTotalVariation.massTotalVariation_le_one
      (hasSum_finiteNatLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (conditionalMaskedCount N L Y (dyadicBlock N) sigma))
      (hasSum_poissonMass (fullRate N L)) (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _))
  simpa [conditionalDistance, conditionalMaskedLaw, FiniteFieldTotalVariation.massTotalVariation,
    natTotalVariation, finiteUniformAverage] using h

/-- Total variation of the actual source law is nonnegative. -/
theorem countDistance_nonneg (N L : ℕ) : 0 ≤ countDistance N L := by
  exact FiniteFieldTotalVariation.massTotalVariation_nonneg _ _

/-- The mean of the nonnegative fibre distances is nonnegative. -/
theorem conditionalDistance_nonneg (N L Y : ℕ) : 0 ≤ conditionalDistance N L Y := by
  unfold conditionalDistance finiteUniformAverage natTotalVariation
  positivity

/-- The finite average is exactly the average of conditional laws in the source model. -/
theorem conditionalDistance_eq_source_atom_average (N L Y : ℕ) :
    conditionalDistance N L Y =
      finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        natTotalVariation
          (fun k => (infiniteRademacherMeasure
            ({omega | infiniteMaskedCount L (dyadicBlock N) omega = k} ∩
              infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
            (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal)
          (poissonMass (fullRate N L))) := by
  unfold conditionalDistance
  apply congrArg finiteUniformAverage
  funext sigma
  congr 1
  funext k
  exact conditionalMaskedLaw_eq_infinite_atom_ratio _ (Finset.Subset.refl _) sigma k

/-- The represented partition is the entire small-prime sigma-algebra. -/
theorem conditioningSigma_eq_full_FY {N L Y : ℕ} (hY : Y ≤ dyadicCutoff N L) :
    smallPrimeSigmaAlgebra (dyadicCutoff N L) Y =
      MeasurableSpace.comap (restrictToFinite Y) inferInstance :=
  smallPrimeSigmaAlgebra_eq_primeCylinder hY

/-- A bound and the unit bound combine with a common multiplicative constant. -/
theorem le_mul_min_one_of_le {d t C : ℝ} (hC : 1 ≤ C)
    (hunit : d ≤ 1) (hbound : d ≤ C * t) : d ≤ C * min 1 t := by
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ C)]
  exact le_min (by simpa using hunit.trans hC) hbound

end
end PaperC.V282.DyadicPoissonDistance
