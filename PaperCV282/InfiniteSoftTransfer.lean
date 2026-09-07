import PaperCV282.SoftArithmeticTransfer
import PaperCV282.MaskedScalarFullConditioning

/-!
# Soft retention for the actual infinite count and its F_Y atoms

The finite conditional count is identified with the positive source-atom
ratio. Y below the event cutoff makes that atom partition exactly F_Y.
No asymptotic or process-AGG input is used, and the only literature premise
is the scalar Stein solution estimate. The unconditional law is the actual
infinite-source count law, obtained by the proved cylinder/mixture identity.
-/

namespace PaperC.V282.InfiniteSoftTransfer

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteMaskedScalarTransfer MaskedScalarFullConditioning
open ArratiaGoldsteinGordonInput ConditionalStartProbability
open ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound SectionThirteenCouplings
open MaskedScalarCoupling MaskedScalarTransfer MaskedPoissonCritical
open AllStartSoftPoisson ScalarSteinInput SoftArithmeticTransfer
open scoped BigOperators ENNReal NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The existing target parameter of the full mask is precisely N/2^L. -/
theorem full_block_target_rate_eq (N L : ℕ) :
    maskedTargetPoissonRate L (dyadicBlock N) = fullRate N L := by
  apply Subtype.ext
  simp only [maskedTargetPoissonRate, fullRate, TouchingPairs.card_dyadicBlock]

/-- The true conditional source law obeys the soft arithmetic budget on every adequate F_Y. -/
theorem average_infinite_conditional_soft_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (hYcut : Y ≤ dyadicCutoff N L) :
    smallPrimeSigmaAlgebra (dyadicCutoff N L) Y =
        MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation
        (fun k => (infiniteRademacherMeasure
          ({omega | infiniteMaskedCount L (dyadicBlock N) omega = k} ∩
            infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal)
        (poissonMass (fullRate N L))) ≤ softArithmeticBudget N L Y := by
  refine ⟨smallPrimeSigmaAlgebra_eq_primeCylinder hYcut, ?_⟩
  simp_rw [← conditionalMaskedLaw_eq_infinite_atom_ratio (dyadicBlock N) (Finset.Subset.refl _)]
  exact average_conditionalMaskedLaw_soft_le hStein hN hL hLY

/-- Averaging the exact finite fibres bounds the actual infinite source law. -/
theorem infinite_distance_le_conditional_average (N L Y : ℕ) :
    natTotalVariation (infiniteMaskedLaw L (dyadicBlock N)) (poissonMass (fullRate N L)) ≤
      finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        natTotalVariation (conditionalMaskedLaw N L Y (dyadicBlock N) sigma)
          (poissonMass (fullRate N L))) := by
  rw [infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw (dyadicBlock N) (Finset.Subset.refl _)]
  simpa only [full_block_target_rate_eq] using
    unconditional_scalar_tv_le_average N L Y (dyadicBlock N)

/-- The true unconditioned infinite count satisfies the same free-cutoff soft ledger. -/
theorem infinite_soft_arithmetic_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    natTotalVariation (infiniteMaskedLaw L (dyadicBlock N)) (poissonMass (fullRate N L)) ≤
      softArithmeticBudget N L Y :=
  (infinite_distance_le_conditional_average N L Y).trans
    (average_conditionalMaskedLaw_soft_le hStein hN hL hLY)

end
end PaperC.V282.InfiniteSoftTransfer
