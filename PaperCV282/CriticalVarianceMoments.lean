import PaperCV282.CriticalFactorialMoments
import PaperCV282.InfiniteCountMoments

/-!
# The first two moments in the actual infinite model

The first-moment estimate and the direct second-factorial-moment bound
give the variance by an exact centered-square identity. All three rates
hold uniformly in each fixed critical window. Infinite-model integration
is transferred exactly, with integrability established separately.
-/

namespace PaperC.V282.CriticalVarianceMoments

open SectionTwelveMoments CriticalProfileNormalization CriticalFirstMomentRate
open CriticalFactorialMoments InfiniteCountMoments

noncomputable section

/-- Finite algebra controlling variance using the two actual moment errors. -/
theorem variance_error_le_of_moment_errors {E F lam r R K : ℝ}
    (hlam : 0 ≤ lam) (hlamK : lam ≤ K)
    (hfirst : |E - lam| ≤ r) (hr : r ≤ 1) (hsecond : |F - lam ^ 2| ≤ R) :
    |F + E - E ^ 2 - lam| ≤ R + (2 * K + 2) * r := by
  have hrpos : 0 ≤ r := (abs_nonneg _).trans hfirst
  have hsum : |E + lam| ≤ 1 + 2 * K := by
    have hh := abs_add_le (E - lam) (2 * lam)
    have heq : E - lam + 2 * lam = E + lam := by ring
    rw [heq, abs_of_nonneg (by positivity : 0 ≤ 2 * lam)] at hh
    linarith
  have hfactor : |1 - (E + lam)| ≤ 2 * K + 2 := by
    have hh : |1 - (E + lam)| ≤ 1 + |E + lam| := by
      simpa only [sub_eq_add_neg, abs_neg, abs_one] using abs_add_le (1 : ℝ) (-(E + lam))
    linarith
  have hid : F + E - E ^ 2 - lam = (F - lam ^ 2) + (E - lam) * (1 - (E + lam)) := by ring
  rw [hid]
  calc
    _ ≤ |F - lam ^ 2| + |(E - lam) * (1 - (E + lam))| := abs_add_le _ _
    _ = |F - lam ^ 2| + |E - lam| * |1 - (E + lam)| := by rw [abs_mul]
    _ ≤ R + r * (2 * K + 2) := add_le_add hsecond
      (mul_le_mul hfirst hfactor (abs_nonneg _) hrpos)
    _ = _ := by ring

/-- Quantitative variance at critical lengths, proved directly from finite moments. -/
theorem critical_variance_le_eventually (C epsilon : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L →
      |(dyadicVariance N L : ℝ) - criticalMean N L| ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
  let eta : ℝ := min (epsilon / 2) (1 / 6)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaE : eta ≤ epsilon / 2 := min_le_left _ _
  have hetaSixth : eta ≤ 1 / 6 := min_le_right _ _
  let K := CriticalRunWindow.balanceConstant C
  have hK : 0 ≤ K := CriticalRunWindow.balanceConstant_nonneg C
  obtain ⟨Nfirst, hfirst⟩ := critical_first_moment_le_eventually C eta hC heta
  obtain ⟨Nsecond, hsecond⟩ := critical_second_factorial_moment_le_eventually C eta hC heta
  obtain ⟨Nwindow, hwindow⟩ := CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nconstant, hconstant⟩ := constant_le_rpow_in_criticalWindow_eventually
    C (2 * K + 3) (epsilon / 2) hC (by positivity)
  refine ⟨max Nfirst (max Nsecond (max Nwindow (max Nconstant 1))), ?_⟩
  intro N hN L hrun
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hw := hwindow N (by omega) L hrun
  have hmean : 0 ≤ criticalMean N L := by unfold criticalMean; positivity
  have hmeanK : criticalMean N L ≤ K := hw.2.2
  have hrOne : (N : ℝ) ^ (-(1 / (2 : ℝ)) + eta) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hNone
      (show -(1 / (2 : ℝ)) + eta ≤ 0 by linarith)
  have hrR : (N : ℝ) ^ (-(1 / (2 : ℝ)) + eta) ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + eta) :=
    Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hfinite := variance_error_le_of_moment_errors hmean hmeanK
    (hfirst N (by omega) L hrun) hrOne (hsecond N (by omega) L hrun)
  have hid : (dyadicVariance N L : ℝ) = (dyadicSecondFactorialMoment N L : ℝ) +
      (dyadicExpectation N L : ℝ) - (dyadicExpectation N L : ℝ) ^ 2 := by
    rw [dyadicVariance_eq_factorial_add_expectation_sub_sq]
    push_cast
    rfl
  rw [← hid] at hfinite
  have hc := hconstant N (by omega) L hrun
  calc
    _ ≤ _ := hfinite
    _ ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + eta) +
        (2 * K + 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + eta) := by gcongr
    _ = (2 * K + 3) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + eta) := by ring
    _ ≤ (N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + eta) := by gcongr
    _ = (N : ℝ) ^ (epsilon / 2 + (-(1 / (3 : ℝ)) + eta)) := (Real.rpow_add hNpos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)

/-- Corollary 4.4: the three actual infinite-model moments, with a common uniform threshold. -/
theorem corollary_four_four (C epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L →
      |infiniteCountMean N L - criticalMean N L| ≤ (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) ∧
      |infiniteCountFactorialMoment N L - criticalMean N L ^ 2| ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) ∧
      |infiniteCountVariance N L - criticalMean N L| ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
  obtain ⟨Nfirst, hfirst⟩ := critical_first_moment_le_eventually C epsilon hC hepsilon
  obtain ⟨Nsecond, hsecond⟩ := critical_second_factorial_moment_le_eventually C epsilon hC hepsilon
  obtain ⟨Nvariance, hvariance⟩ := critical_variance_le_eventually C epsilon hC hepsilon
  refine ⟨max Nfirst (max Nsecond Nvariance), ?_⟩
  intro N hN L hrun
  rw [infiniteCountMean_eq_finite, infiniteCountFactorialMoment_eq_finite, infiniteCountVariance_eq_finite]
  exact ⟨hfirst N (by omega) L hrun, hsecond N (by omega) L hrun, hvariance N (by omega) L hrun⟩

end
end PaperC.V282.CriticalVarianceMoments
