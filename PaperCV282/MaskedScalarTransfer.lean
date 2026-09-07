import PaperCV282.MaskedScalarCoupling

/-!
# The masked scalar arithmetic-to-Poisson transfer

The full conditional count is compared to the Poisson law of the complete
mask. Deleting actual sites and target coordinates keeps their true
masked costs. The retained scalar factor uses the mask's own good-site
mean, including the convention at zero. Uniform mixture gives the same
bound for the unconditional law.

The sole literature premise is the explicit scalar Stein-solution norm
statement; the coupling, graph, marginals, arithmetic and averaging steps
are proved here or in the imported checked modules.
-/

namespace PaperC.V282.MaskedScalarTransfer

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments
open LargePrimeDependencyGraph MaskedPoissonCritical MaskedArithmeticGeometry
open MaskedPairGeometry MaskedBadMass MaskedScalarRetained ScalarSteinInput
open MaskedScalarCoupling TwoWindowParity
open scoped BigOperators NNReal

noncomputable section

/-- The two genuine count laws and the exact Poisson parameter shift enter a triangle. -/
theorem conditional_scalar_tv_le_components {N L Y : ℕ} (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
      (poissonMass (maskedTargetPoissonRate L mask)) ≤
        natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
          (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma) +
        natTotalVariation (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)
          (poissonMass (retainedRate N L Y mask)) +
        (fullBadMask N L Y mask).card / (2 : ℝ) ^ L := by
  have hfirst := natTotalVariation_triangle
    (p := conditionalMaskedLaw N L Y mask sigma)
    (q := maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)
    (r := poissonMass (maskedTargetPoissonRate L mask))
    (summable_finiteNatLaw _ _) (summable_maskedConditionalGoodLaw _ _ _ _ _)
    (hasSum_poissonMass _).summable (finiteNatLaw_nonneg _ _)
    (maskedConditionalGoodLaw_nonneg _ _ _ _ _) (poissonMass_nonneg _)
  have hsecond := natTotalVariation_triangle
    (p := maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)
    (q := poissonMass (retainedRate N L Y mask))
    (r := poissonMass (maskedTargetPoissonRate L mask))
    (summable_maskedConditionalGoodLaw _ _ _ _ _) (hasSum_poissonMass _).summable
    (hasSum_poissonMass _).summable (maskedConditionalGoodLaw_nonneg _ _ _ _ _)
    (poissonMass_nonneg _) (poissonMass_nonneg _)
  have hshift := retained_target_poisson_tv_le N L Y mask
  linarith

/-- Theorem 4.1, scalar conditional form, with every mask and numerical factor explicit. -/
theorem theorem_four_one_scalar_conditional (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
        (poissonMass (maskedTargetPoissonRate L mask))) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * firstSteinFactor (retainedRate N L Y mask) *
          (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
            (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  have havg := finiteUniformAverage_mono
    (fun sigma : SmallSample (dyadicCutoff N L) Y => conditional_scalar_tv_le_components mask sigma)
  have hsplit (f g : SmallSample (dyadicCutoff N L) Y → ℝ) (c : ℝ) :
      finiteUniformAverage (fun sigma => f sigma + g sigma + c) =
        finiteUniformAverage f + finiteUniformAverage g + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,add_div,add_div]
    simp
  rw [hsplit] at havg
  have hbad := average_conditional_full_retained_tv_le (L := L) (Y := Y) mask hmask
  have hret := average_retained_scalar_tv_le hStein mask hmask hN hL hY
  have hdel := (Rat.cast_le (K := ℝ)).mpr (masked_total_deletion_cost_le (Y := Y) hN hL mask hmask)
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] at hdel
  have hcomb := havg.trans (add_le_add (add_le_add hbad hret) (le_refl _))
  apply hcomb.trans
  convert add_le_add_right hdel
    (firstSteinFactor (retainedRate N L Y mask) *
      (2 * (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)))) using 1 <;>
    first | rfl | ring

/-- Mixing the conditional count laws cannot increase total variation to a fixed target. -/
theorem unconditional_scalar_tv_le_average (N L Y : ℕ) (mask : Finset ℕ) :
    natTotalVariation (fullMaskedDyadicStartLaw N L mask)
      (poissonMass (maskedTargetPoissonRate L mask)) ≤
        finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
          natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
            (poissonMass (maskedTargetPoissonRate L mask))) := by
  rw [← average_conditionalMaskedLaw_eq_full N L Y mask]
  apply natTotalVariation_uniformMixture_le
  intro sigma
  exact summable_abs_sub_of_nonneg (summable_finiteNatLaw _ _)
    (hasSum_poissonMass _).summable (finiteNatLaw_nonneg _ _)
    (poissonMass_nonneg _)

/-- Theorem 4.1 after unconditional mixing, with the same exact mask-level budget. -/
theorem theorem_four_one_scalar (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    natTotalVariation (fullMaskedDyadicStartLaw N L mask)
      (poissonMass (maskedTargetPoissonRate L mask)) ≤
      ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L +
        2 * firstSteinFactor (retainedRate N L Y mask) *
          (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
            (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) :=
  (unconditional_scalar_tv_le_average N L Y mask).trans
    (theorem_four_one_scalar_conditional hStein mask hmask hN hL hY)

end
end PaperC.V282.MaskedScalarTransfer
