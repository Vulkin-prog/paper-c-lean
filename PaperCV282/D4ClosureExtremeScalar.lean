import PaperCV282.D4ClosureExtremeParameters
import PaperCV282.PoissonRateConvergence
import PaperC.Asymptotics.CorollaryFourteenEightMaximum

/-! # Scalar comparison at the shifted extreme level -/
namespace PaperC.V282.D4ClosureExtremeScalar

open Filter Topology Real CriticalRunWindow CriticalFirstMoment
open ScalarSteinInput PrimeEulerPNT AllStartSoftPoisson
open DyadicPoissonDistance HardPoissonRates SaddleRateConvergence
open MaskedPoissonCritical InfiniteMaskedScalarTransfer CorollaryFourteenEightMaximum
open MarkedDetruncation D4ClosureExtremeParameters

noncomputable section

theorem countDistance_eq_masked (N L : ℕ) :
    countDistance N L=maskedPoissonTotalVariation N L (dyadicBlock N) := by
  unfold countDistance maskedPoissonTotalVariation
  rw [infiniteMaskedLaw_eq_fullMaskedDyadicStartLaw _ (Finset.Subset.refl _)]
  unfold maskedTargetPoissonLaw
  rw [maskedTargetPoissonRate_block_eq,MaskedScalarCoupling.poissonMass_eq_poissonPMFReal]

/-- The maximum is a void event for the longer count, including the empty configuration. -/
theorem maximum_error_le {N L m : ℕ} (hN : 2≤N) :
    |infiniteMaximumAtMostProbability N L m-exp (-(fullRate N (L+m+1) : ℝ))| ≤
      2*countDistance N (L+m+1) := by
  simpa only [countDistance_eq_masked,fullRate_coe] using
    abs_infiniteMaximumAtMostProbability_sub_exp_le (L := L) (m := m) hN

/-- Uniform scalar convergence along arbitrary size subsequences in a bounded critical window. -/
theorem critical_count_distance_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (C : ℝ) (hC : 0≤C)
    (hwindow : ∀ᶠ k in atTop, InRunLengthWindow C (sizes k) (lengths k)) :
    Tendsto (fun k => countDistance (sizes k) (lengths k)) atTop (𝓝 0) := by
  obtain ⟨Nw,hw⟩ := firstMomentWindow_eventually hC
  obtain ⟨Nr,hr⟩ := hard_conditional_rate_eventually hStein hPNT
    lowerConstant upperConstant (1/6) 1 lowerConstant_pos lowerConstant_lt_upperConstant
    (by norm_num) (by norm_num)
  have hlim := hard_rate_tendsto_zero_of_bounded (balanceConstant C) 1 (1/6)
    (fun _ => balanceConstant C) (by norm_num)
    (Eventually.of_forall fun _ => ⟨balanceConstant_nonneg C,le_rfl⟩)
  apply squeeze_zero' (Eventually.of_forall fun _ => countDistance_nonneg _ _) _
    (by simpa only [mul_zero] using (hlim.const_mul 20).comp hsizes)
  filter_upwards [hsizes.eventually (eventually_ge_atTop (max Nw Nr)),hwindow] with k hk hkw
  have hf := hw (sizes k) (by omega) (lengths k) hkw
  have hb := (hr (sizes k) (by omega) (lengths k) (by exact_mod_cast hf.1.2.2.1) (by exact_mod_cast hf.1.2.2.2)).2
  have hrate : (fullRate (sizes k) (lengths k) : ℝ)≤balanceConstant C := hf.2.2
  apply (countDistance_le_conditionalDistance _ _ (hardCutoff (sizes k))).trans
  apply hb.trans
  unfold hardRate
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrate (by positivity)) (by norm_num)

/-- No marked comparison at the diverging base intensity is used. -/
theorem extreme_count_distance_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (j : ℤ) (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop) :
    Tendsto (fun k => countDistance (sizes k)
      (lengths k+extremeThreshold (sizes k) (lengths k) j+1)) atTop (𝓝 0) := by
  apply critical_count_distance_tendsto_zero hStein hPNT sizes _ hsizes (|(j : ℝ)|+2) (by positivity)
  filter_upwards [hsizes.eventually (eventually_ge_atTop (1 : ℕ)),
    threshold_nonnegative_eventually sizes lengths hrate j] with k hk hj
  exact shifted_length_in_window (by omega) j hj

end
end PaperC.V282.D4ClosureExtremeScalar
