import PaperCV282.D4ClosureExtremeScalar

/-! # Companion D.4: the actual lattice extreme law at a diverging base intensity -/
namespace PaperC.V282.D4ClosureExtremeTheorem

open Filter Topology Real AllStartSoftPoisson MarkedDetruncation
open ScalarSteinInput PrimeEulerPNT D4ClosureExtremeParameters D4ClosureExtremeScalar

noncomputable section

/-- The source maximum, with the manuscript convention that the empty maximum is minus infinity. -/
def extremeProbability (N L : ℕ) (j : ℤ) : ℝ :=
  infiniteMaximumAtMostProbability N L (extremeThreshold N L j)

/-- Even before phase selection, the deterministic moving extreme target is correct. -/
theorem moving_extreme_error_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (j : ℤ) (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop) :
    Tendsto (fun k => extremeProbability (sizes k) (lengths k) j-
      exp (-((2 : ℝ)^(intensityPhase (sizes k) (lengths k)-(j : ℝ)-1)))) atTop (𝓝 0) := by
  have hc := (extreme_count_distance_tendsto_zero hStein hPNT sizes lengths j hsizes hrate).const_mul 2
  have habs : Tendsto (fun k => |extremeProbability (sizes k) (lengths k) j-
      exp (-((2 : ℝ)^(intensityPhase (sizes k) (lengths k)-(j : ℝ)-1)))|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ (by simpa only [mul_zero] using hc)
    filter_upwards [hsizes.eventually (eventually_ge_atTop (2 : ℕ)),
      threshold_nonnegative_eventually sizes lengths hrate j] with k hN hj
    have hh := maximum_error_le (L := lengths k)
      (m := extremeThreshold (sizes k) (lengths k) j) hN
    rw [shifted_rate_eq_phase (by omega) j hj] at hh
    exact hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- The literal phase-subsequence limit for every fixed signed integer displacement. -/
theorem companion_D4_extreme
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (theta : ℝ) (j : ℤ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (hphase : Tendsto (fun k => intensityPhase (sizes k) (lengths k)) atTop (𝓝 theta)) :
    Tendsto (fun k => extremeProbability (sizes k) (lengths k) j) atTop
      (𝓝 (exp (-((2 : ℝ)^(theta-(j : ℝ)-1))))) := by
  have hc : Continuous (fun x : ℝ => exp (-((2 : ℝ)^(x-(j : ℝ)-1)))) := by
    fun_prop (disch := norm_num)
  have ht := hc.continuousAt.tendsto.comp hphase
  have he := moving_extreme_error_tendsto_zero hStein hPNT sizes lengths j hsizes hrate
  have hh := he.add ht
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

end
end PaperC.V282.D4ClosureExtremeTheorem
