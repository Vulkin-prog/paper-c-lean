import PaperCV282.SoftArithmeticCosts
import PaperCV282.MaskedScalarCoupling

/-!
# The finite soft arithmetic transfer at a free prime cutoff

The target rate is the whole population N/2^L. Both Stein factors are
retained, and the cost includes actual bad neighbours and touching pairs.
There is no asymptotic, critical-window or process-AGG hypothesis.
-/

namespace PaperC.V282.SoftArithmeticTransfer

open ArratiaGoldsteinGordonInput SectionTwelveMoments
open AllStartSoftPoisson AllStartConditionalDependency MaskedArithmeticGeometry
open SoftArithmeticCosts SoftGraphDegree CutoffGraphDegree TouchingPairMass TwoWindowParity
open ScalarSteinInput ConditionalAGGInstantiation ConditionalAGGAverage
open ConditionalStartProbability SectionThirteenFiniteBound SectionThirteenCouplings
open MaskedScalarCoupling MaskedPoissonCritical
open scoped BigOperators NNReal

noncomputable section

/-- The exact full-block soft ledger before any asymptotic estimates. -/
def softArithmeticBudget (N L Y : ℕ) : ℝ :=
  firstSteinFactor (fullRate N L) *
    ((N : ℝ) + (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) *
      ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * N) +
      (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) +
      homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N)) /
        (2 : ℝ) ^ (2 * L) +
  zeroSteinFactor (fullRate N L) *
    ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * (fullBadStarts N L Y).card) / (2 : ℝ) ^ L

/-- The good-site ledger keeps both the actual neighbour means and the actual joint laws. -/
theorem actual_good_cost_le {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (goodSiteIndices N L Y).card * (1 / (2 : ℝ) ^ L) ^ 2 +
      (1 / (2 : ℝ) ^ L) *
        (∑ i ∈ goodSiteIndices N L Y,
          ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
            (startProbability N L j.val : ℝ)) +
      (∑ i ∈ goodSiteIndices N L Y,
        ∑ j ∈ (closedNeighborhood (allStartDependencyGraph N L Y) i).erase i,
          (jointStartProbability N L i.val j.val : ℝ)) ≤
    ((N : ℝ) + (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) *
      ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * N) +
      (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) +
      homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N)) /
        (2 : ℝ) ^ (2 * L) := by
  have hdiag := mul_le_mul_of_nonneg_right (good_indices_card_le N L Y)
    (sq_nonneg (1 / (2 : ℝ) ^ L))
  have hmean := mul_le_mul_of_nonneg_left
    (actual_neighbour_marginal_sum_le_defects (Y := Y) hN hL)
    (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ L)
  have hjoint := good_all_joint_sum_le (N := N) (Y := Y) hL
  apply (add_le_add (add_le_add hdiag hmean) hjoint).trans_eq
  rw [show (2 : ℝ) ^ (2 * L) = ((2 : ℝ) ^ L) ^ 2 by rw [mul_comm 2 L, pow_mul]]
  field_simp
  ring

/-- B.4 instantiated on the complete actual count and bounded by arithmetic quantities. -/
theorem average_full_count_soft_arithmetic_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation
        (finiteNatLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorSum (conditionedAllStartIndicator N L Y sigma)))
        (poissonMass (fullRate N L))) ≤ softArithmeticBudget N L Y := by
  apply (average_full_count_soft_poisson_le hStein hN hL hLY).trans
  have hgood := mul_le_mul_of_nonneg_left (actual_good_cost_le (Y := Y) hN hL)
    (firstSteinFactor_nonneg (fullRate N L))
  have hbad := mul_le_mul_of_nonneg_left (actual_bad_cost_le (Y := Y) hN hL)
    (zeroSteinFactor_nonneg (fullRate N L))
  simpa only [softArithmeticBudget, mul_div_assoc] using add_le_add hgood hbad

/-- Exact identification with the existing literal full-block conditional count. -/
theorem full_indicatorSum_eq_conditionalMaskedCount (N L Y : ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    indicatorSum (conditionedAllStartIndicator N L Y sigma) =
      conditionalMaskedCount N L Y (dyadicBlock N) sigma := by
  classical
  funext eta
  unfold indicatorSum conditionalMaskedCount fullMaskedDyadicCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [conditionedAllStartIndicator_eq_true_iff]
  rw [← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
    (fun x => if startAt (assemble (dyadicCutoff N L) Y sigma eta) x L then 1 else 0)]

/-- The literal full-block finite conditional law satisfies the soft ledger. -/
theorem average_conditionalMaskedLaw_soft_le (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation (conditionalMaskedLaw N L Y (dyadicBlock N) sigma)
        (poissonMass (fullRate N L))) ≤ softArithmeticBudget N L Y := by
  have h := average_full_count_soft_arithmetic_le hStein hN hL hLY
  simpa only [full_indicatorSum_eq_conditionalMaskedCount, conditionalMaskedLaw] using h

end
end PaperC.V282.SoftArithmeticTransfer
