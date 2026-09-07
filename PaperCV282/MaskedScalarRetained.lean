import PaperCV282.ScalarPoissonBounds
import PaperCV282.MaskedArithmeticCosts

/-!
# Sharp scalar transfer on the literal retained mask

The conditioning law is the actual finite large-prime fibre. The scalar
factor uses the retained mask's own mean and is independent of the small
prime assignment. Every arithmetic term keeps the original mask.
-/

namespace PaperC.V282.MaskedScalarRetained

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound LargePrimeDependencyGraph
open MaskedPoissonCritical MaskedArithmeticGeometry MaskedPairGeometry
open MaskedArithmeticAverages MaskedArithmeticCosts
open ScalarSteinInput ScalarPoissonBounds
open scoped BigOperators NNReal

noncomputable section

/-- The mask's exact retained Poisson mean, not the ambient intensity. -/
def retainedRate (N L Y : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨(fullGoodMask N L Y mask).card / (2 : ℝ) ^ L, by positivity⟩

theorem retainedRate_coe (N L Y : ℕ) (mask : Finset ℕ) :
    (retainedRate N L Y mask : ℝ) = (fullGoodMask N L Y mask).card / (2 : ℝ) ^ L := rfl

/-- The rate of every conditioned family is the same exact retained mean. -/
theorem poissonRate_fullGoodMask_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    poissonRate (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) =
        retainedRate N L Y mask := by
  apply NNReal.eq
  exact poissonParameter_fullGoodMask_eq mask hmask hN hL hLY sigma

/-- The scalar factor is correctly retained on each small-prime fibre. -/
theorem retained_scalar_tv_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    natTotalVariation
      (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)
      (poissonMass (retainedRate N L Y mask)) ≤
        firstSteinFactor (retainedRate N L Y mask) *
          (bOne (largeUniformPMF (dyadicCutoff N L) Y)
              (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
              (largePrimeDependencyGraph N L Y) +
            bTwo (largeUniformPMF (dyadicCutoff N L) Y)
              (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
              (largePrimeDependencyGraph N L Y)) := by
  have h := scalar_poisson_bound hStein (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
    (largePrimeDependencyGraph N L Y) (hasExactDependencyGraph_fullGoodMask mask hL sigma)
  rw [poissonRate_fullGoodMask_eq mask hmask hN hL hLY sigma,
    ← maskedConditionalGoodLaw_eq_finiteNatLaw] at h
  exact h

/-- Mean retained scalar error with the exact mask, edge count and relation sum. -/
theorem average_retained_scalar_tv_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation
        (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)
        (poissonMass (retainedRate N L Y mask))) ≤
      firstSteinFactor (retainedRate N L Y mask) *
        (2 * (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
          (SectionTwelveMoments.jointDefectMass N L (TwoWindowParity.separatedPairs mask L) : ℝ)) /
            (2 : ℝ) ^ (2 * L))) := by
  have hLY : L + 1 ≤ Y := by omega
  have hpoint := finiteUniformAverage_mono
    (fun sigma => retained_scalar_tv_le hStein mask hmask hN hL hLY sigma)
  have hmul (c : ℝ) (f : SmallSample (dyadicCutoff N L) Y → ℝ) :
      finiteUniformAverage (fun sigma => c * f sigma) = c * finiteUniformAverage f := by
    unfold finiteUniformAverage
    rw [← Finset.mul_sum]
    ring
  rw [hmul] at hpoint
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (average_stein_terms_le_twice mask hmask hN hL hY) (firstSteinFactor_nonneg _))

end
end PaperC.V282.MaskedScalarRetained
